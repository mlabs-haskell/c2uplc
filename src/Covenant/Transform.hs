{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify, put, runRWS)

import Covenant.ASG (
    ASG (ASG),
    ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (ValNodeType),
    BoundTyVar,
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
    typeASGNode,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataConstructor (..),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join, when, unless)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), State, StateT, evalState, execState, gets, modify', runState)
import Covenant.ArgDict (idToName)
import Covenant.Data (DatatypeInfo, mkCataFunTy, mkMatchFunTy)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count2, intCount, intIndex, ix0, ix1, wordCount)
import Covenant.MockPlutus (
    PlutusTerm,
    constrData,
    listData,
    pApp,
    pCase,
    pConstr,
    pFst,
    pHead,
    pLam,
    pSnd,
    pTail,
    pVar,
    plutus_I,
    unConstrData,
    unIData,
    unListData,
 )
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (ForceInternal, LamInternal), Id (UnsafeMkId), ValNodeInfo (AppInternal), unsafeMkDatatypeInfos)
import Data.Foldable (
    find,
    foldl',
    traverse_,
 )
import Data.Kind (Type)
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, over, preview, review, set, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

import Covenant.JSON

import Control.Monad (foldM)
import Control.Monad.Writer.Strict (MonadWriter)
import Covenant.Concretify (countToAbstractions, getInstantiations, resolveVar, substCompT, LambdaId (LambdaId), AppId (AppId), compTArgSchema, instantiationHelper, decideConcrete, substitute)
import Covenant.ExtendedASG
import Covenant.JSON (CompilationUnit (..))
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro
import Data.Bifunctor (Bifunctor (first, second))
import Data.Row.Dictionaries qualified as R
import Data.Row.Records (HasType, Rec, Row, (.+), (.==), type (.+), type (.-), type (.==))
import Data.Row.Records qualified as R
import Data.Set qualified as Set
import GHC.TypeLits (Symbol)
import GHC.TypeLits (KnownSymbol)

transformASG :: CompilationUnit -> Rec TransformState
transformASG (CompilationUnit datatypes asg _) = flip evalState extended $ do
    let dtDict = unsafeMkDatatypeInfos (Vector.toList datatypes)
    firstPassMeta <- mkProjectionsAndEmbeddings
    let builtinHandlers = firstPassMeta R..! #builtinHandlers
    tyFixerData <- mkTypeFixerFnData dtDict builtinHandlers
    toTransform <- getASG
    let transformState :: Rec TransformState
        transformState =
            firstPassMeta
                .+ #asg .== toTransform
                .+ #dtDict .== dtDict
                .+ #visited .== S.empty
                .+ #tyFixerData .== tyFixerData
                .+ #tyFixers .== M.empty

    asgBundle1 <-  snd <$> unliftMetaM transformState transformTypeFixerNodes
    let initConcretifyCxt :: Rec ConcretifyCxt
        initConcretifyCxt = #context .== M.empty
                        .+ #callPath .== Vector.empty
                        .+ #appPath .== Vector.empty
                        .+ #tyFixers .== (asgBundle1 R..! #tyFixers)
                        .+ #builtinHandlers .== (firstPassMeta R..! #builtinHandlers)
                        .+ #identityFn .== (firstPassMeta R..! #identityFn)
                        .+ #uniqueError .== (firstPassMeta R..! #uniqueError)
    transformedASG <- getASG
    let (_,finalASG,_) = runRWS resolveRepPoly initConcretifyCxt transformedASG
    let asgBundleFinal = R.update #asg finalASG asgBundle1
    pure asgBundleFinal
  where
    extended :: ExtendedASG
    extended = wrapASG asg

    -- Prior to the final pass, we want to look up our TyFixerFnData by type name and node kind,
    -- but in the final pass need to look it up by the id of a function inside an app.
    unBundleTyFixers :: Map TyName TyFixerDataBundle -> Map Id TyFixerFnData
    unBundleTyFixers = undefined 

{- We need to keep track of:
     1. SOMETHING that serves the role of a Context of rigid concretifications along our path.
        So, a (Map AppId (Map (Index "tyvar") (ValT Void))) should work. I think?
     2. The "path" we're on. I think we really only need three things here:
          a. The "call site chain", so a Vector AppId
          b. A stack of lambdas above us

     We also need to read from our TyFixer Map (and should probably construct a reverse lookup table
     to be able to lookup by Id there to avoid a ton of duplicated and superfluous type level surgery)

-}
-- temporarily enabling purescript mode, it's much easier to prototype and iterate w/ extensible
-- records 
type ConcretifyCxt = "context" .== Map AppId (Map (Index "tyvar") (ValT Void))
                     .+ "callPath" .== Vector LambdaId
                     .+ "appPath" .== Vector AppId
                     .+ "tyFixers" .== Map Id TyFixerFnData
                     .+ "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
                     .+ "identityFn" .== ExtendedId
                     .+ "uniqueError" .== ExtendedId

instance Monoid w => MonadASG (RWS r w ExtendedASG) where
  getASG = get
  putASG = put

{- By this point the entire asg is nothing but lam, app, thunk/force, and builtins/primitives

i need some kind of example

f :: Int -> Bool -> String -> ByteString
f i b s = (g i) (g b) (g (g s))
-}
resolveRepPoly :: RWS (Rec ConcretifyCxt) () ExtendedASG ()
resolveRepPoly = eTopLevelSrcNode >>= go . fst
  where
    traceError :: forall a. String -> RWS (Rec ConcretifyCxt) () ExtendedASG a
    traceError msg = do
      callPath <- asks (R..! #callPath)
      appPath <- asks (R..! #appPath)
      context <- asks (R..! #context)
      let errMsg =  "Encountered error while resolving representational polymorphism"
                    <> "\n  CallChain: " <> show callPath
                    <> "\n AppChain:" <> show appPath
                    <> "\n Context:" <> show context
                    <> "\n Error Message: " <> msg
                    <> "\n\n"
      error errMsg

    unsafeFnTy :: forall k. (ExtendedKey k) => k -> RWS (Rec ConcretifyCxt) () ExtendedASG (CompT AbstractTy)
    unsafeFnTy k = eNodeAt k >>= \case
      ACompNode compT _ -> pure compT
      other -> traceError $ "unsafeFnTy called on " <> show other <> " which isn't a comp node"

    goRef :: Ref -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    goRef = \case
      AnId i -> resolveExtended i >>= go
      AnArg{} -> pure ()

    dbBindingSite :: DeBruijn -> RWS (Rec ConcretifyCxt) () ExtendedASG LambdaId
    dbBindingSite db = do
      let dbInt = review asInt db
      scopeStack <- asks (R..! #callPath)
      pure $ scopeStack Vector.! dbInt

    {- This will be the thing that:
         1. Replaces the function type with one that has the handlers
         2. Applies the handlers
         3. Updates the type of the corresponding synthetic function (i.e. modifies the node) to
            explicitly mention the handlers (NOTE: THIS DOES NOT CONCRETIFY THE SYNTHETIC FUNCTION NODE)
    -}
    cleanupAppNode :: ExtendedId -> ASGNode  -> Map (Index "tyvar") (ValT Void) -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    cleanupAppNode appId (AValNode retTy (App fn args instTys cFunTy)) concretifications = do
      -- The definitive test for whether this needs cleaned up is the presence of the fn Id in the
      -- collection of type fixers
      tyFixers <- asks (R..! #tyFixers)
      case M.lookup fn tyFixers of
        Nothing -> do
          -- If it's not there it's not a node we care about. We only add
          -- projection or embedding handlers to app nodes which result from
          -- our type fixer -> app node transform.
          pure ()
        Just (TyFixerFnData tn enc polyTyNoHandlers compiled schema nm kind ) -> do
          -- if the datatype the synthetic function originated from is SOP encoded, we don't need
          -- to do anything.
          when (enc == SOP) $ pure ()
          unless (enc == SOP) $ do
            -- we need to extract the "function type with handlers added" from the schema, which in this branch has to be a data schema
            (polyWithHandlers,handlerArgPosDict) <- case schema of
                                                      SOPSchema{} -> traceError $ "SOP schema mismatch in " <> show tn <> " " <> show enc
                                                      DataSchema ty dict -> pure (ty,dict)
            let CompN _ (ArgsAndResult polyArgsWithHandlers _) = polyWithHandlers
                CompN _ (ArgsAndResult concreteArgsNoHandlers _) = cFunTy
                -- we need to get at the handlers to determine their types
                handlerFnTys = Vector.drop (Vector.length concreteArgsNoHandlers) polyArgsWithHandlers
            -- while we *really* should just record the handler type order as a vector in our TyFixerFnData (TODO: Do it),
            -- we know that they are all Comp0 identity functions with only tyvar params, so we can get what we need by doing...
            handlerIndices <- Vector.forM handlerFnTys $ \case
                                ThunkT (Comp0 ((Abstraction (BoundAt _ i)) :--:> ReturnT _)) -> pure i
                                other -> traceError $ "Encountered an invalid type when adding projection/embedding handlers: " <> show other
            -- we can mash the next two steps together. they are:
            --   1. Look up the concrete type that the tyvar it "handles" is instantiated to
            --   2. check whether that type is a representationally amorphous primitive (i.e. whether it's Int or ByteString -_- all of this
            --      for those two types!) and if so, find the `Id` corresponding to its projection or embedding (we select based on the node kind
            --      in our TyFixerFnData)
            -- NOTE/IMPORTANT: Technically we are using computation types in a value type place here but that *shouldn't* matter.
            --                 If I'm wrong we need to insert some additional nodes to thunk the dummy handlers and then force them, but
            --                 since this is the last step before codegen we should be fine to not do that.
            projEmbedHandlers <- asks (R..! #builtinHandlers)
            identityFn <- forgetExtendedId <$> asks (R..! #identityFn)
            extraProjEmbArgs <- Vector.forM handlerIndices $ \hIndx ->
                                  case M.lookup hIndx concretifications of
                                    Nothing -> traceError $ "Could not locate a concretification for tyvar " <> show hIndx
                                                            <> " while resolving projection/embedding types for "
                                                            <> show tn <> " " <> show kind
                                    Just (BuiltinFlat bi) -> case M.lookup bi projEmbedHandlers of
                                      Nothing -> pure $ AnId identityFn
                                      Just repPolyHandler -> case kind of
                                        MatchNode -> pure . AnId $ project repPolyHandler
                                        CataNode -> pure . AnId $ project repPolyHandler
                                        IntroNode -> pure . AnId $ embed repPolyHandler
            -- We don't actually *have* to fix the concretified type annotation in the app node, but
            -- it doesn't really hurt if we do and might save us during debugging
            let newConcreteFunTy = cleanup $ substCompT vacuous  (M.mapKeys (BoundAt Z) concretifications) polyWithHandlers
                newNode = AValNode retTy $ AppInternal fn (args <> extraProjEmbArgs) instTys newConcreteFunTy
            -- again we don't *have* to do this but we might as well keep things correct.
            -- This just sets the synthetic function node to have the correct type.
            coerceCompNodeTy fn polyWithHandlers
            eInsert appId newNode
    cleanupAppNode _ node _ = traceError $ "Passed something that wasn't an app node to cleanupAppNode: " <> show node

    coerceCompNodeTy :: Id -> CompT AbstractTy -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    coerceCompNodeTy i compT = do
      eid <- resolveExtended i
      eNodeAt eid >>= \case
        ACompNode _compT node -> eInsert eid (ACompNode compT node)
        _ -> pure () 

    resolveRigid :: AbstractTy -> RWS (Rec ConcretifyCxt) () ExtendedASG (AbstractTy, ValT Void)
    resolveRigid rgd@(BoundAt db i) = do
      bindingLam <- dbBindingSite db
      context <- asks (R..! #context)
      findClosestAppWithFn bindingLam >>= \case
        Nothing -> traceError $ "No app node in our app path found with function id: " <> show bindingLam
        Just appId -> case M.lookup appId context >>= M.lookup i of
          Nothing -> traceError $ "Could not resolve rigid " <> show rgd <> ", no type found in context"
          Just res -> pure (rgd,res)
     where
       findClosestAppWithFn :: LambdaId -> RWS (Rec ConcretifyCxt) () ExtendedASG (Maybe AppId)
       findClosestAppWithFn lid = do
         appPath <- asks (R..! #appPath)
         appsWithNodes <- traverse (\x@(AppId i) -> (x,) <$> eNodeAt i) appPath
         let matchesLam = \case
               AValNode _ (App fn _ _ _) -> LambdaId fn == lid
               _ -> False
         pure $ fst <$> Vector.find (matchesLam . snd) appsWithNodes

    go :: ExtendedId ->  RWS (Rec ConcretifyCxt) () ExtendedASG ()
    go eid = eNodeAt eid >>= \case
      AnError -> pure ()
      ACompNode compT compNode -> case compNode of
        Lam bRef -> do
          let lamId = LambdaId $ forgetExtendedId eid
          local (mapField #callPath (Vector.cons lamId)) $ goRef bRef
        Force fRef -> goRef fRef
        _ -> pure ()
      appNode@(AValNode valT valNode) -> case valNode of
        (App fn args instTys cFunTy) -> do
          {- There have to be two branches here:
               1. If  there aren't any rigids remaining in the "concrete as possible"
                  type ('ty' here) then we just log the result and move to the children

               2. If there ARE rigids remaining, we need to resolve them.
                  The old procedure for doing this is super convoluted but I think we can take a
                  shortcut and do something like:
                    - We can get the ID of the lambda by indexing into our callPath
                    - Then we find the app that fixes the types by looking for the first
                      application above us (i.e. in the appPath) which contains that lambda as
                      a fn.

                      I am pretty sure that app has to be the one that determines the concretifications.
                      But REVIEW check with Koz.
                    - Then we look up the entry for that Lambda,App pair and we're done with the
                      "hard" part (we still have to do some annoying type/term surgery but that's just tedious)

              That should work. We have to be carefuly to only recurse with the
              current AppId cons'd onto the local reader context for the
              FUNCTION PART of the recursion. The appChain is supposed to *mean* something like:
              All of the applications above us which might determine the concrete types of our rigids.
              An application can only concretify the type of the function.
          -}
          polyFnTy  <- unsafeFnTy fn
          fnEid <- resolveExtended fn
          let CompN cnt (ArgsAndResult polyArgs _) = polyFnTy
              bVars = Vector.toList $ countToAbstractions cnt
              CompN _ (ArgsAndResult monoArgs _) = cFunTy
              subs = flip runReader 0 $ getInstantiations bVars (Vector.toList polyArgs) (Vector.toList monoArgs)
              (concrete,nonConcrete) = M.partition isConcrete subs
              here = AppId . forgetExtendedId $ eid
          if null nonConcrete
            then do
              let thisContext = M.mapKeys (\(BoundAt _ i) -> i) $ assertConcrete <$> concrete
                  localF :: Rec ConcretifyCxt -> Rec ConcretifyCxt
                  localF = mapField #context (M.insert here thisContext)
                           . mapField #appPath (Vector.cons here)
              local localF $ go fnEid
              traverse_ goRef args
              cleanupAppNode eid appNode thisContext
            else do
              let rigids = collectRigids cFunTy
              {- This is a map from the *lingering abstraction in this app node* to a concrete type.
                 That doesn't by itself, give us what we want, since the index of the tyvar bound by
                 the function of the app we're examining is totally unrelated to the index of the rigid
                 in the lambda that binds IT.

                 Another way of putting this: We know that there is a rigid in our conrete-as-possible-up-to-now type,
                 and we know what the rigid resolves to, but what we do not yet know is what exactly OUR type
                 variable gets concretified to to).

                 We cannot assume that the type variable we're trying to solve necessarily concretifies to
                 a rigid directly. For example, if have an identity function like

                 `id :: forall a. a -> a`

                 And we apply it to `Maybe r3` (where r3 is a rigid type variable bound in an enclosing lambda),
                 then. We'd end up with the substitution `a ~ Maybe r3`.

                 So what we have to do here is to substitute into the "non-concrete" types using our rigidsResolved
                 dictionary. Note that the keys in this are abstractions that occur in the function type HERE.
                 Following our example for clarity, we have:

                   nonConcrete = [a := Maybe r3]
                   rigidsResolved = [r3 := Int]   -- Int is just an example concrete type

                 And if we substitute into the elements of nonConcrete using rigidsResolved, we should get
                   [a := Maybe Int]
              -}
              rigidsResolved <- M.fromList <$> traverse resolveRigid (S.toList rigids)
              let resolvedNonConcrete = M.mapKeys (\(BoundAt _ i) -> i) $
                                          assertConcrete
                                          . runSubst 0 id (vacuous <$> rigidsResolved)
                                          <$> nonConcrete
                  sanitizedConcrete = M.mapKeys (\(BoundAt _ i) -> i) $ assertConcrete <$> concrete
                  thisContext = resolvedNonConcrete <> sanitizedConcrete
                  localF = mapField #context (M.insert here thisContext)
                               . mapField #appPath (Vector.cons here)
              local localF $ go fnEid
              traverse_ goRef args
              cleanupAppNode eid appNode thisContext

        Thunk child -> resolveExtended child >>= go
        -- This is only meant to be used on ASGs that have undergone the
        -- TypeFixerNode -> AppNode transformation, so there shouldn't be any other possibilities
        -- here. (We can ignore literals)
        _ -> pure ()

-- Just saves us the hassle of having to runReader and local a bunch
runSubst :: forall (a :: Type). Int -> (ValT a -> ValT AbstractTy) -> Map AbstractTy (ValT a) -> ValT AbstractTy -> ValT AbstractTy
runSubst dbStart f subDict val = flip runReader dbStart $  substitute f subDict val 

isConcrete :: ValT AbstractTy -> Bool
isConcrete = isJust . decideConcrete

-- unsafe, but we should only ever end up using this on things we've had to "downcast" from ValT Void to ValT AbstractTy 
assertConcrete :: ValT AbstractTy -> ValT Void
assertConcrete = fromJust . decideConcrete

collectRigids :: CompT AbstractTy -> Set AbstractTy
collectRigids =
  mconcat
      . Vector.toList
      . fmap (flip runReader 0 . go)
      . compTArgSchema
 where
  go :: ValT AbstractTy -> Reader Int (Set AbstractTy)
  go = \case
      Abstraction x -> S.singleton <$> resolveVar x
      ThunkT compT -> local (+ 1) $ do
          let argSchema = compTArgSchema compT
          mconcat <$> traverse go (Vector.toList argSchema)
      BuiltinFlat{} -> pure S.empty
      Datatype _ args -> mconcat <$> traverse go (Vector.toList args)


eLambdaTy :: forall m. MonadASG m => LambdaId -> m (CompT AbstractTy)
eLambdaTy (LambdaId l) = eNodeAt l >>= \case
    ACompNode compT _ -> pure compT
    _other -> error "Lambda id points at non-comp-node"

mapField :: forall (l :: Symbol) (a :: Type) (r :: Row Type)
        . (KnownSymbol l, HasType l a r)
       => R.Label l
       -> (a -> a)
       -> Rec r
       -> Rec r
mapField l f r = R.update l (f (r R..! l)) r




-- I didn't bill for the row stuff, I just got frustrated having to rewrite optics over and over again
-- as I iterated heavily on this module and used this out for convenience while experimenting. I can remove it all later.
unliftMetaM ::
    forall
        (m :: Type -> Type)
        (r :: Row Type)
        (a :: Type).
    (HasType "asg" ExtendedASG r, R.AllUniqueLabels r, MonadASG m, Monad m) =>
    Rec r -> MetaM r a -> m (a, Rec r)
unliftMetaM r act = do
    asg <- getASG
    let rIn = R.update #asg asg r
        (a, rOut) = runMetaM rIn act
    putASG (rOut R..! #asg)
    pure (a, rOut)

newtype MetaM r a = MetaM (State (Rec r) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState (Rec r)
        )
        via (State (Rec r))

instance (HasType "asg" ExtendedASG r) => MonadASG (MetaM r) where
    getASG = gets (R..! #asg)
    putASG asg = modify' $ R.update #asg asg

runMetaM :: forall (r :: Row Type) (a :: Type). Rec r -> MetaM r a -> (a, Rec r)
runMetaM aRec (MetaM act) = runState act aRec


-- From here on out the top level node CANNOT BE ASSUMED TO BE THE HIGHEST NODE NUMERICALLY.
-- This is annoying but there really isn't a sensible way around it.
--
-- We also have to remember to "catch" the IDs for these functions during codegen
-- since they won't have a body, so we're going to have to keep the map around for a while too.
--
-- sorry koz
type FirstPassMeta =
    "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
        .+ "identityFn" .== ExtendedId
        .+ "uniqueError" .== ExtendedId
mkProjectionsAndEmbeddings :: forall (m :: Type -> Type). (MonadASG m) => m (Rec FirstPassMeta)
mkProjectionsAndEmbeddings = do
    uniqueErrorId <- ephemeralErrorId
    identityId <- mkIdentityFn
    eInsert uniqueErrorId AnError
    polyRepHandlers <- M.unions <$> traverse (mkRepHandler uniqueErrorId) [IntegerT, ByteStringT]
    pure $
        #builtinHandlers .== polyRepHandlers
            .+ #identityFn .== identityId
            .+ #uniqueError .== uniqueErrorId
  where
    mkRepHandler :: ExtendedId -> BuiltinFlatT -> m (Map BuiltinFlatT PolyRepHandler)
    mkRepHandler errId t = do
        projT <- projectionId
        embedT <- embeddingId
        let synthFnTy = Comp0 $ BuiltinFlat t :--:> ReturnT (BuiltinFlat t)
            synthFnNode = syntheticLamNode (UniqueError . forgetExtendedId $ errId) synthFnTy
        eInsert projT synthFnNode
        eInsert embedT synthFnNode
        pure $ M.singleton t (PolyRepHandler (forgetExtendedId projT) (forgetExtendedId embedT))

    mkIdentityFn :: m ExtendedId
    mkIdentityFn = do
        idFnId <- identityFnId
        let compNode = ACompNode (Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) (LamInternal (AnArg (UnsafeMkArg Z ix0 (tyvar Z ix0))))
        eInsert idFnId compNode
        pure idFnId
unsafeNextId :: Id -> Id
unsafeNextId (UnsafeMkId i) = UnsafeMkId (i + 1)

mkTypeFixerFnData ::
    forall m.
    (MonadASG m) =>
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    m (Map TyName TyFixerDataBundle)
mkTypeFixerFnData datatypes biRepHandlers =
    liftAppTransformM $ do
        let allTyNames = M.keys datatypes
        foldM go M.empty allTyNames
  where
    liftAppTransformM :: AppTransformM a -> m a
    liftAppTransformM act = do
        asg <- getASG
        let (res, newASG) = runAppTransformM datatypes biRepHandlers asg act
        putASG newASG
        pure res

    go :: Map TyName TyFixerDataBundle -> TyName -> AppTransformM (Map TyName TyFixerDataBundle)
    go acc tn = do
        destructorData <- mkDestructorFunction tn
        constructorData <- mkConstructorFunctions tn
        -- If we have no constructor functions nor match functions, our datatype is 'void' and we can ignore it
        if null destructorData && null constructorData
            then pure acc
            else do
                cataData <- mkCatamorphism tn
                let thisBundle = TyFixerDataBundle constructorData destructorData cataData
                pure $ M.insert tn thisBundle acc

    mkTypeFixerLookupTable :: Map Id TyFixerFnData -> Map TyName Id
    mkTypeFixerLookupTable = M.foldlWithKey' (\acc i tffData -> M.insert (mfTyName tffData) i acc) M.empty

-- Just to help me keep straight all of the various IDs we need to keep track of
newtype UniqueError = UniqueError Id

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
type TransformState =
    FirstPassMeta
        .+ "asg" .== ExtendedASG
        .+ "visited" .== Set ExtendedId
        .+ "dtDict" .== Map TyName (DatatypeInfo AbstractTy)
        .+ "tyFixerData" .== Map TyName TyFixerDataBundle
        .+ "tyFixers" .== Map Id TyFixerFnData
transformTypeFixerNodes ::
    forall (m :: Type -> Type).
    MetaM TransformState ()
transformTypeFixerNodes = do
    topSrcNode <- fst <$> (eTopLevelSrcNode :: MetaM TransformState (ExtendedId, ASGNode))
    go topSrcNode --  dtDict magicErr tyFixers
  where
    conjureFunction :: CompT AbstractTy -> MetaM TransformState ASGNode
    conjureFunction compT = do
        errId <- forgetExtendedId <$> gets (R..! #uniqueError)
        pure $ syntheticLamNode (UniqueError errId) compT

    resolveCtorIx :: TyName -> ConstructorName -> MetaM TransformState (Maybe Int)
    resolveCtorIx tn cn = do
        dtInfo <- (M.! tn) <$> gets (R..! #dtDict)
        case view #originalDecl dtInfo of
            OpaqueData _ ctors -> do
                -- TODO/REVIEW: NEED TO CHECK THAT THIS NAMING IS CONSISTENT WITH ANYWHERE ELSE WE HANDLE THIS
                let (ConstructorName inner) = cn
                    mplutusDataCtor = case inner of
                        "I" -> Just PlutusI
                        "B" -> Just PlutusB
                        "Constr" -> Just PlutusConstr
                        "List" -> Just PlutusList
                        "Map" -> Just PlutusMap
                        _ -> Nothing
                case mplutusDataCtor of
                    Nothing -> pure Nothing
                    Just plutusDataCtor ->
                        pure $ Vector.findIndex (== plutusDataCtor) (Vector.fromList . Set.toList $ ctors)
            DataDeclaration _ _ ctors _ -> pure $ Vector.findIndex (\(Constructor cNm' _) -> cNm' == cn) ctors

    -- this should only be used in contexts where we must have a datatype (e.g. scrutinees in matches and catas, parts of generated functions)
    unsafeDatatypeName :: ValT AbstractTy -> TyName
    unsafeDatatypeName = \case
        Datatype tn _ -> tn
        other -> error $ "unsafeDatatypeName called on non-datatype ValT: " <> show other

    -- only use this on things that have to be a value type (i.e. scrutinees)
    unsafeRefType :: Ref -> MetaM TransformState (ValT AbstractTy)
    unsafeRefType = \case
        AnArg (UnsafeMkArg _ _ ty) -> pure ty
        AnId i ->
            eNodeAt i >>= \node -> case typeASGNode node of
                ValNodeType ty -> pure ty
                other -> error $ "UnsafeRefType called on an Id with a non-ValT type: " <> show other

    alreadyVisited :: ExtendedId -> MetaM TransformState Bool
    alreadyVisited i = S.member i <$> gets (R..! #visited)

    insertAndMarkVisited :: ExtendedId -> ASGNode -> MetaM TransformState ()
    insertAndMarkVisited eid node = do
        eInsert eid node
        oldVisited <- gets (R..! #visited)
        modify' $ R.update #visited (S.insert eid oldVisited)

    go :: ExtendedId -> MetaM TransformState ()
    go i =
        alreadyVisited i >>= \case
            True -> pure ()
            False ->
                eNodeAt i >>= \case
                    AnError -> pure ()
                    ACompNode compT compNode -> case compNode of
                        Lam ref -> goRef ref
                        Force ref -> goRef ref
                        _ -> pure ()
                    AValNode valT valNode -> case valNode of
                        Thunk child -> resolveExtended child >>= go
                        App fn args _ _ -> do
                            resolveExtended fn >>= go
                            traverse_ goRef args
                        Cata cataT handlers arg -> do
                            tyFixers <- gets (R..! #tyFixerData)
                            tn <- unsafeDatatypeName <$> unsafeRefType arg
                            case cataData =<< M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for catamorphisms on " <> show tn
                                Just dat@(TyFixerFnData _nm _enc cataFnPolyTy _compiled _schema _fnName _) -> do
                                    cataId <- tyFixerFnId
                                    modify' $ mapField #tyFixers (M.insert (forgetExtendedId cataId) dat) 
                                    handlerTypes <- traverse unsafeRefType (Vector.toList handlers)
                                    scrutTy <- unsafeRefType arg
                                    let cataFnConcrete = applyArgs cataFnPolyTy (scrutTy : handlerTypes)
                                        newValNode = AppInternal (forgetExtendedId i) (Vector.cons arg handlers) Vector.empty cataFnConcrete
                                        newASGNode = AValNode valT newValNode
                                    insertAndMarkVisited i newASGNode
                                    -- NOTE: This is just a placeholder tagged with the polymorphic function type, which we need.
                                    --       The body is a reference to a single error node that we track and will ignore/remove.
                                    --       TODO: There's only one of these for each type so add a check to save us work if we already did it
                                    syntheticCataFnNode <- conjureFunction cataFnPolyTy
                                    insertAndMarkVisited cataId syntheticCataFnNode
                            traverse_ goRef handlers
                            goRef arg
                        Match scrut handlers -> do
                            matchId <- tyFixerFnId
                            scrutTy <- unsafeRefType scrut
                            handlerTypes <- traverse unsafeRefType $ Vector.toList handlers
                            let tn = unsafeDatatypeName scrutTy
                            tyFixers <- gets (R..! #tyFixerData)
                            case matchData =<< M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for pattern matches on " <> show tn
                                Just dat@(TyFixerFnData _nm _enc matchFnPolyTy _compiled _schema _fnName _) -> do
                                    modify' $ mapField #tyFixers (M.insert (forgetExtendedId matchId) dat)
                                    let matchFnConcrete = applyArgs matchFnPolyTy (scrutTy : handlerTypes)
                                        newValNode = AppInternal (forgetExtendedId i) (Vector.cons scrut handlers) Vector.empty matchFnConcrete
                                        newASGNode = AValNode valT newValNode
                                    insertAndMarkVisited i newASGNode
                                    -- NOTE: See previous note
                                    syntheticMatchFnNode <- conjureFunction matchFnPolyTy
                                    insertAndMarkVisited matchId syntheticMatchFnNode
                            traverse_ goRef handlers
                            goRef scrut
                        DataConstructor tn ctorName ctorArgs -> do
                            argTys <- traverse unsafeRefType $ Vector.toList ctorArgs
                            tyFixers <- gets (R..! #tyFixerData)
                            case introData <$> M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for datatype introductions for type " <> show tn
                                Just constrFunctions ->
                                    resolveCtorIx tn ctorName >>= \case
                                        Nothing -> error $ "Fatal Error: No data for constructor " <> show ctorName <> " found in type " <> show tn
                                        Just ctorIx -> do
                                            ctorFnId <- tyFixerFnId
                                            let ctorFnData = constrFunctions Vector.! ctorIx
                                                dat@(TyFixerFnData _nm _enc ctorFnPolyTy _compiled _schema _fnName _) = ctorFnData
                                                ctorFnConcrete = applyArgs ctorFnPolyTy argTys
                                                newValNode = AppInternal (forgetExtendedId i) ctorArgs Vector.empty ctorFnConcrete
                                                newASGNode = AValNode valT newValNode
                                            modify' $ mapField #tyFixers (M.insert (forgetExtendedId ctorFnId) dat)
                                            insertAndMarkVisited i newASGNode
                                            -- NOTE: See previous note
                                            syntheticCtorFnNode <- conjureFunction ctorFnPolyTy
                                            insertAndMarkVisited ctorFnId syntheticCtorFnNode
                            traverse_ goRef ctorArgs
      where
        goRef :: Ref -> MetaM TransformState ()
        goRef = \case
            AnId child -> resolveExtended child >>= go
            AnArg{} -> pure ()

{- This is a kind of improvised unification where we know that one side is necessarily more polymorphic than the other
   (and that the other can only contain rigid type variables or concrete types).
-}
applyArgs :: CompT AbstractTy -> [ValT AbstractTy] -> CompT AbstractTy
applyArgs compT [] = compT
-- I *think* we ignore the result when determining the substitutions and then substitute into it to reconstruct
-- the type.
applyArgs polyFun@(CompN cnt (ArgsAndResult fnSigArgs _)) args = cleanup concreteFn
  where
    vars :: [AbstractTy]
    vars = Vector.toList $ countToAbstractions cnt

    instantiations :: Map AbstractTy (ValT AbstractTy)
    instantiations =
        flip runReader 0 $
            getInstantiations vars (Vector.toList fnSigArgs) args

    concreteFn :: CompT AbstractTy
    concreteFn = substCompT id instantiations polyFun

{- Our analogue of 'fixUp' from the unification module, but done without renaming (b/c we can't rename here, really) -}
cleanup :: CompT AbstractTy -> CompT AbstractTy
cleanup origFn@(CompN cnt (ArgsAndResult args result)) = case substCompT id substitutions origFn of
    CompN _ body -> CompN newCount body
  where
    newCount :: Count "tyvar"
    newCount = fromJust . preview intCount $ Vector.length remainingLocalVars

    fnSig :: Vector (ValT AbstractTy)
    fnSig = Vector.snoc args result

    allOriginalVars :: Set AbstractTy
    allOriginalVars = Set.fromList . Vector.toList $ countToAbstractions cnt

    substitutions :: Map AbstractTy (ValT AbstractTy)
    substitutions =
        Vector.ifoldl'
            ( \acc newIx oldTV ->
                let tvIx = fromJust $ preview intIndex newIx
                    newTv = Abstraction (BoundAt Z tvIx)
                 in M.insert oldTV newTv acc
            )
            M.empty
            remainingLocalVars

    remainingLocalVars :: Vector AbstractTy
    remainingLocalVars =
        Vector.fromList
            . Set.toList
            . Set.unions
            . flip runReader 0
            . traverse collectLocalVars
            . Vector.toList
            $ fnSig

    collectLocalVars :: ValT AbstractTy -> Reader Int (Set AbstractTy)
    collectLocalVars = \case
        Abstraction a -> do
            resolved <- resolveVar a
            if a `Set.member` allOriginalVars
                then pure $ Set.singleton a
                else pure Set.empty
        BuiltinFlat{} -> pure Set.empty
        ThunkT (CompN _ (ArgsAndResult thunkArgs thunkRes)) -> local (+ 1) $ do
            let toTraverse = Vector.toList $ Vector.snoc thunkArgs thunkRes
            Set.unions <$> traverse collectLocalVars toTraverse
        Datatype _ dtArgs -> Set.unions <$> traverse collectLocalVars (Vector.toList dtArgs)

-- Misc utils

retTy :: CompT a -> ValT a
retTy (CompN _ (ArgsAndResult _ res)) = res

intT :: ValT AbstractTy
intT = BuiltinFlat IntegerT

byteStringT :: ValT AbstractTy
byteStringT = BuiltinFlat ByteStringT

syntheticLamNode :: UniqueError -> CompT AbstractTy -> ASGNode
syntheticLamNode (UniqueError errId) funTy = ACompNode funTy (LamInternal (AnId errId))

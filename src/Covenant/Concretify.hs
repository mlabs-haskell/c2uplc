{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Concretify where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify)

import Covenant.ASG (
    ASG,
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), StateT)
import Covenant.Data (DatatypeInfo, mkMatchFunTy)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count2, intCount, intIndex, ix0, ix1, wordCount)
import Covenant.MockPlutus (PlutusTerm, constrData, listData, pApp, pLam, pVar, plutus_I)
import Covenant.Test (Id (UnsafeMkId))
import Data.Foldable (find, foldl', traverse_)
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, preview, review, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

newtype LambdaId = LambdaId {_getLamId :: Id}
    deriving newtype (Show, Eq, Ord)

newtype AppId = AppId {_getAppId :: Id}
    deriving newtype (Show, Eq, Ord)

data TyFixerId
    = AMatchId Id
    | AnAppId Id
    | ACataId Id
    | AConstrId Id
    deriving stock (Show, Eq, Ord)

-- "expands" a lambda to have additional arguments for wrappers/unwrappers.

sop2Tuple :: DataDeclaration AbstractTy
sop2Tuple = DataDeclaration "Tuple2" count2 [Constructor "Tuple2" [tyvar Z ix0, tyvar Z ix1]] SOP

{- This records the information we need for our "mock" functions for catamorphisms/datatype intro/datatype elimination

   Specifically, it contains:
     1. The type name. For catas and matches, this is the type of the "scrutinee" being matched on, for intros it is the result
     2. The encoding. This will be useful later on.
     3. The FULLY POLYMORPHIC type of the function
     4. A PLC term corresponding to the function
     5. A token indicating which "sort" of function it is (cata/match/intro). This will also contain the "true"
        function type, which takes additional wrapper/unwrapper arguments IF THE TYPE IS DATA ENCODED.
        This is the type of the PLC term, but we "lie" about it when we replace the match/cata/intro with an app so as to use the existing machinery.
     6. The name of the function.

     Some explanation for 4: For example, if we have a data encoded Maybe type, the "false" types would be:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> r
       Just :: forall a. a -> Maybe a
       Nothing :: forall a. Maybe a
       (.. maybe doesn't have a catamorphism form ...)

     But the "true" types w/ the handler arguments are:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> (a -> a) -> r
       Just :: forall a. Maybe a -> (a -> a) -> a
       Nothing :: forall a. Maybe a

     In `match_Maybe` the extra argument will be either an identity function if the type is not a representationally amorphous
     primitive, or an unwrapper like `unI` or `unB` if the parameter is a representationally amorphous primitive.

     In the constructor forms (or at least the ones for non-nullary constructors), the extra arg will be an `I` or `B` wrapper.
-}
data MagicFunction
    = MagicFunction
    { mfTyName :: TyName
    , mfEncoding :: DataEncoding
    , mfPolyType :: CompT AbstractTy
    , mfCompiled :: PlutusTerm
    , mfTypeSchema :: MagicTypeSchema
    , mfFunName :: Text
    , mfNodeKind :: TyFixerNodeKind
    }

data TyFixerNodeKind = MatchNode | IntroNode | CataNode
    deriving stock (Show, Eq, Ord)

data MagicTypeSchema
    = SOPSchema
    | -- The last arg is a "functionalized" map from type variables to the arg index of their "added as extra arguments" handlers
      -- To be more specific, it's a map from type variables *to the argument position of the ~~TERM~~, i.e. lambda arg, that
      -- handles them.
      -- We probably need this for all of the below "actually-an-application" things but I'm not 100% certain
      -- Quite possible we just need SOPSchema / DataSchema and that these variants are all redunant, keeping for now in case
      -- something requires special handling that I don't yet see
      DataSchema (CompT AbstractTy) (AbstractTy -> Maybe Int)

nextId :: RWS (Map TyName (DatatypeInfo AbstractTy)) () Id Id
nextId = do
    UnsafeMkId s <- get
    let new = UnsafeMkId (s + 1)
    modify $ const new
    pure new

{- NOTE: The type of the "function part" is just going to be the BBF (plus unwrappers),
         since we always apply the scrutinee and handler functions "all at once" with the
         match nodes we are transforming, and will therefore be able to concretify
         any type variables occuring in the fully polymorphic function type.

         So the type of the function for a SOP encoded `Maybe` would be:

         `forall a r. Maybe a -> r -> (a -> r) -> r`

         And for a data encoded maybe, it should ("eventually") be

         `forall a r. Maybe a -> r -> (a -> r) -> (r -> r) -> r`

         Though we are going to use the same "trick" here that we do for introduction, that is:
           - For our first pass, we will replace `match` nodes with a dummy function with
             no wrapper/unwrapper handlers
           - We will codegen a suitable function that *does* make use of handlers, and record that
             type seperately
           - *After* we use the "initial" ASG to fully concretify the types, we will do another pass
             where we will explicitly introduce the handlers as extra arguments to the function and
             apply the needed handler arguments.

         The reason for  doing things this way is that for our concretification analysis pass, we only really
         care about ensuring that all type variables are fully concretified (or concretified as far as possible).
         We need to know that to handle representational polymorphism. The "transform every type fixer into an app node"
         this is intended to make the analysis much easier (which it does), but we need to complete that analysis
         before we can determine *which* wrapper/unwrapper handlers the expanded function needs to be applied to.

         This is admittedly a bit strange, however I do not think there is an easier way to do things.

-}
-- this will return a singleton map
mkDestructorFunction :: TyName -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
mkDestructorFunction tn = do
    dtDict <- ask
    case M.lookup tn dtDict of
        Nothing -> error "Used a datatype we don't have declarations for. Should not be possible at this stage."
        Just dtInfo -> go dtInfo
  where
    go :: DatatypeInfo AbstractTy -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
    go dtInfo = do
        let ogDecl = view #originalDecl dtInfo
        case runExceptT (mkMatchFunTy ogDecl) of
            -- "Nothing" here means "Datatype is isomorphic to `Void`"
            Nothing -> pure M.empty
            Just eRes -> case eRes of
                Left bbfErr ->
                    error $
                        "Error: Could not create destructor function. Invalid datatype. BBF Error: "
                            <> show bbfErr
                Right matchFunTy -> do
                    newId <- nextId
                    schema <- mkMatchSchema dtInfo
                    undefined

    mkMatchSchema :: DatatypeInfo AbstractTy -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id MagicTypeSchema
    mkMatchSchema = undefined

    genElimFormPLCRec :: MagicTypeSchema -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id PlutusTerm
    genElimFormPLCRec schema =
        asks (join . preview (ix tn % #baseFunctor)) >>= \case
            Just (bfbbDecl, bfbbTy) -> undefined
            Nothing -> undefined

mkConstructorFunctions :: TyName -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
mkConstructorFunctions tn = do
    dtDict <- ask
    case M.lookup tn dtDict of
        Nothing -> error "Used a datatype we don't have declarations for. Should not be possible at this stage."
        Just dtInfo -> case view #originalDecl dtInfo of
            DataDeclaration tn cnt ctors enc -> do
                Vector.ifoldM (go dtInfo cnt enc) M.empty ctors
            OpaqueData{} -> undefined
  where
    go ::
        DatatypeInfo AbstractTy ->
        Count "tyvar" ->
        DataEncoding ->
        Map Id MagicFunction ->
        Int ->
        Constructor AbstractTy ->
        RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
    go dtInfo cnt enc acc cIx (Constructor (ConstructorName cName) argTys) = do
        let ctorFnTy = mkCtorFnTy cnt argTys
            schema = mkSchema enc ctorFnTy
            funName = cName
        newId <- nextId
        compiled <- genIntroFormPLC enc schema cIx
        let here =
                MagicFunction
                    { mfTyName = tn
                    , mfEncoding = enc
                    , mfPolyType = ctorFnTy
                    , mfCompiled = compiled
                    , mfTypeSchema = schema
                    , mfFunName = funName
                    , mfNodeKind = IntroNode
                    }
        pure $ M.insert newId here acc
      where
        genIntroFormTermVarName :: forall a. Int -> a -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id Name
        genIntroFormTermVarName pos _ = do
            uniqueId@(UnsafeMkId i) <- nextId
            let textPart = cName <> "_arg" <> T.pack (show pos)
                uniquePart = Unique (fromIntegral i)
            pure $ Name textPart uniquePart

        genIntroFormPLC ::
            DataEncoding ->
            MagicTypeSchema ->
            Int ->
            RWS (Map TyName (DatatypeInfo AbstractTy)) () Id PlutusTerm
        genIntroFormPLC dataEnc schema ctorIx = case schema of
            -- TODO/FIXME: Need to handle 0 argument constructors / Enum encodings BEFORE we do all this work
            -- REMINDER: DONT MIX UP TERM AND TYPE ARGS / CTOR ARGS VS FN ARGS
            SOPSchema -> undefined
            DataSchema (CompN _ (ArgsAndResult introFnArgs _)) getHandlerIx -> do
                -- these are the ARGUMENTS TO THE CONSTRUCTOR
                let ctorArgs = argTys
                -- These are the NAMES OF ALL THE ARGUMENT TO THE INTRO FUNCTION. In this branch
                -- this will (almost always) contain MORE NAMES than the args to the constructor
                names <- Vector.imapM genIntroFormTermVarName introFnArgs
                -- The names of arguments to the ctors
                let ctorArgNames = Vector.take (Vector.length ctorArgs) names
                    nameTyPairs = Vector.zip ctorArgNames ctorArgs
                    lamBuilder = foldl' (\g argN -> g . pLam argN) id names

                    resolveHandler :: ValT AbstractTy -> Maybe Name
                    resolveHandler = \case
                        Abstraction tv -> getHandlerIx tv >>= \hIx -> names Vector.!? hIx
                        _anythingElse -> Nothing

                    handledCtorArgs = flip fmap nameTyPairs $ \(cArgNm, cArgTy) -> case resolveHandler cArgTy of
                        Nothing -> pVar cArgNm
                        Just argHandler -> pApp (pVar argHandler) (pVar cArgNm)
                case dataEnc of
                    -- TODO: Fill in some of the helpers (plutus_I, listData, etc) and make sure you use the "right version" here
                    SOP -> error "something went horribly wrong, IntroDataSchema w/ SOP encoding"
                    BuiltinStrategy _ -> error "TODO: Remember how to handle code generation for builtin strategies"
                    PlutusData strat -> case strat of
                        EnumData -> pure $ lamBuilder (plutus_I $ fromIntegral ctorIx)
                        ProductListData -> pure $ listData handledCtorArgs
                        ConstrData -> pure $ constrData (plutus_I $ fromIntegral ctorIx) (listData handledCtorArgs)
                        NewtypeData -> pure $ handledCtorArgs Vector.! 0
            _anythingElse -> error "Schema for an introduction must be an IntroDataSchema or SOPSchema!"

        mkCtorFnTy :: Count "tyvar" -> Vector (ValT AbstractTy) -> CompT AbstractTy
        mkCtorFnTy datatypeNumParams args =
            let result = Datatype tn (countToTyVars datatypeNumParams)
             in CompN datatypeNumParams (ArgsAndResult args result)

        mkSchema :: DataEncoding -> CompT AbstractTy -> MagicTypeSchema
        mkSchema dataEnc (CompN tvCnt (ArgsAndResult args result)) = case dataEnc of
            SOP -> SOPSchema
            BuiltinStrategy _strat ->
                error $
                    "TODO: Try to remember what we would need to do here. For this (but not the codegen), "
                        <> "it's probably fine to generate the same thing as for PlutusData"
            PlutusData _strat ->
                -- strategy doesn't matter HERE though it does for codegen
                -- note that we *can't* have "external" rigids here

                -- We only care about adding wrappers for types that occur as arguments.
                -- And - extra nice for us - we can just ignore thunks becaaauusssee
                -- this is data-encoded and they can't exist as params anyway. So we really just need to
                -- look for any arg that is a tyvar
                let getTyVar :: ValT AbstractTy -> Maybe AbstractTy
                    getTyVar = \case
                        Abstraction a -> Just a
                        _ -> Nothing

                    -- We need to return *something* that indicates which extra handler arg is associated w/ a particular
                    -- tyvar. Not immediately sure what the best way to do this is.
                    usedTypeVariables :: [AbstractTy]
                    usedTypeVariables = S.toList . S.fromList . mapMaybe getTyVar . Vector.toList $ args

                    lenOrigArgs = Vector.length args

                    extraArgs' :: (Int, Map AbstractTy Int, Vector (ValT AbstractTy))
                    extraArgs' =
                        let mkHandler (BoundAt db indx) =
                                let tv = tyvar (S db) indx
                                 in ThunkT (Comp0 $ tv :--:> ReturnT tv)
                         in foldl'
                                ( \(pos, handlerDict, eArgs) tv ->
                                    let newHandlerDict = M.insert tv (pos + lenOrigArgs) handlerDict
                                        newPos = pos + 1
                                        handler = mkHandler tv
                                        newEArgs = Vector.snoc eArgs handler
                                     in (newPos, newHandlerDict, newEArgs)
                                )
                                (0, M.empty, Vector.empty)
                                usedTypeVariables

                    (_, hDict, extraArgs) = extraArgs'

                    polyFnTy :: CompT AbstractTy
                    polyFnTy = CompN tvCnt $ ArgsAndResult (args <> extraArgs) result
                 in DataSchema polyFnTy (`M.lookup` hDict)

transformMatchNode :: Id -> ValT AbstractTy -> Ref -> Vector Ref -> ()
transformMatchNode = undefined

-- Constructs all the intermediate resources and then determines the full range of concretifications for every lambda/call site in the ASG
tyVarConcretifications :: ASG -> Map LambdaId (Map AppId (Set (Map AbstractTy (ValT Void))))
tyVarConcretifications asg = trace msg $ M.fromSet (snd . getTyVarConcretifications asg asgCallChains asgCallSites asgCallSiteChains) <$> asgCallSites
  where
    msg =
        "asgLambdas:\n  "
            <> show asgLambdas
            <> "\n\nasgCallSites:\n  "
            <> show asgCallSites
            <> "\n\nasgCallChains:\n  "
            <> show asgCallChains
            <> "\n\nasgCallSiteChains:\n  "
            <> show asgCallSiteChains
            <> "\n\n"
    asgLambdas = allLambdas asg i

    asgCallSites = getCallSites asgLambdas asg i

    asgCallChains = getCallChain asg i

    asgCallSiteChains = runReader (getCallSiteChainMap asg i asgCallSites) mempty

    i = topLevelId asg

immediateConcretifications :: ASG -> Map LambdaId (Map AppId (Set (Map (Index "tyvar") (ValT Void))))
immediateConcretifications asg = M.fromSet (getImmediateConcretifications asg asgCallSites) (S.map LambdaId asgLambdas)
  where
    asgLambdas = allLambdas asg i

    asgCallSites = getCallSites asgLambdas asg i

    i = topLevelId asg

{- This returns the set of "immediate" concretifications, i.e., the set of instantiations of a polymorphic function

   For example, in:

  ```
   f :: Int -> Bool -> Int
   f i b =
    let g :: forall a. a -> Int
        g _ = 2

    in g i == g b
  ```

  The function `g` is applied twice, and the type variable is instantiated to two different concrete types
  in that application. However, it is never instantiated *to a rigid*, so the (much more complex) rigid
  concretification machinery will not pick up on it.

-}
getImmediateConcretifications ::
    ASG ->
    Map LambdaId (Set AppId) ->
    LambdaId ->
    Map AppId (Set (Map (Index "tyvar") (ValT Void)))
getImmediateConcretifications asg callSites lamId@(LambdaId i) = case M.lookup lamId callSites of
    Nothing -> M.empty
    Just lamCallSites -> M.unionsWith (<>) $ go <$> S.toList lamCallSites
  where
    lamPolyTy :: CompT AbstractTy
    lamPolyTy = case nodeAt i asg of
        ACompNode compT _ -> compT
        _ -> error "LambdaId doesn't point at a comp node"

    floppyTyVars :: [Index "tyvar"]
    floppyTyVars = case lamPolyTy of
        CompN cnt _ ->
            let cntInt = review intCount cnt
             in if cntInt <= 0
                    then []
                    else (fromJust . preview intIndex) <$> [0 .. (cntInt - 1)]

    go :: AppId -> Map AppId (Set (Map (Index "tyvar") (ValT Void)))
    go aId@(AppId appId) =
        M.singleton aId . S.singleton $
            foldr
                ( \x acc -> case concretifies asg x aId of
                    Nowhere -> M.empty
                    -- This means it's a rigid (I THINK) and will be handled by the
                    -- below machinery
                    There _ -> M.empty
                    Here concrete -> M.singleton x concrete
                )
                M.empty
                floppyTyVars

getTyVarConcretificationsv2 ::
    ASG ->
    Map LambdaId (Set LambdaId) -> -- call chains
    Map LambdaId (Set TyFixerId) -> -- type fixing sites
    Map TyFixerId (Vector LambdaId) -> -- type fixer site chains
    TyFixerId -> -- The ID of the Node we care about. Must be a type fixer, so an app/match/cata/intro
    -- The first element of the tuple is the "fully polymorphic type of the type fixer".
    -- We need this, unfortunately. It has to be threaded through recursive calls to the this
    -- function in order to determine what, exactly, the concretifications are for a given
    -- rigid type variable. Without it, the best we can do is to know that the tyvars DO concretify, but we
    -- can't say what it is they concretify TO.
    (CompT AbstractTy, Set (Map AbstractTy (ValT Void)))
getTyVarConcretificationsv2 asg callChains fixerSites fixerId = undefined

{- This gives us every possible concretification of a rigid tyvar for a given App site.

   NOTE: This ONLY tells us about rigid instantiations. This is important to keep in mind,
         because we may have to perform transformations or generate "versions" of functions
         which are polymorphic but always immediately concretified by being applied to
         concrete types.
-}
getTyVarConcretifications ::
    ASG ->
    Map LambdaId (Set LambdaId) -> -- call chains
    Map LambdaId (Set AppId) -> -- call sites
    Map AppId (Vector LambdaId) -> -- call site chains
    AppId ->
    -- I think we have to return the "as concrete as possible" function type for each
    -- call site as well. We need it in the recursive calls. If we don't have it, we can determine
    -- THAT some type concretifies a rigid, but we can't say WHICH type that is
    (CompT AbstractTy, Set (Map AbstractTy (ValT Void)))
getTyVarConcretifications asg callChains callSites callSiteChains appId@(AppId i) = case nodeAt i asg of
    -- Am reasonably certain we never actually need to examine the explicit type applications/instantiations here
    AValNode _valT (App _fn _args _instTys fnTy) -> case decideConcreteCompT fnTy of
        {-
          1. Identify all rigids
          2. Resolve them
        -}
        Nothing ->
            let rigids = collectRigids fnTy
                -- Explanation: This is a [[Map AbstractTy (ValT Void)]].
                --              Each INNER list should be a collection of concrete singleton maps of instantiation types for a given rigid we collected from
                --              our "as-concrete-as-possible" function type. (The maps are a convenience here, this is "morally" a [[(AbstractTy,ValT Void)]] - note the singleton-ey-ness)
                --
                --              The order of the outer list doesn't really indicate anything at all, it's only for grouping.
                --
                --              Just to make this clearer, suppose that `tN@rM` means: 'tN is a concrete type that can concretify some rigid r identified by M'
                --              (this is a slight simplification).
                --              resolvedRigids should look like: [ [t0@r0, t1@r0, t2@r0], [t3@r1, t4@r1], [t5@r2]  ]
                --
                --              What we want out of this is something like "every possible union of all of those singleton maps such that every map has
                --              an entry for every rigid".
                resolvedRigids = resolveRigid <$> S.toList rigids
             in -- REVIEW: We need to tag the results with `fnTy` for recursive calls. I think? ugh
                trace (show resolvedRigids) $ (fnTy,) . S.fromList . combine $ resolvedRigids
        Just _ ->
            -- This has to be empty. If the application site is fully concretified, there are no rigids, and there's nothing we can do.
            (fnTy, S.empty)
    _ -> error "AppId not an app! BOOOOOM!"
  where
    -- This really collects every *type variable* in a CompT, but at this point, the only ones left really should be rigid.
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

    -- This returns EVERY POSSIBLE INSTANTIATION FOR A GIVEN ARGPOS. Or it should anyway!
    -- NOTE: That means that this is "every possibility for a specific tyvar".
    resolveRigid :: AbstractTy -> [Map AbstractTy (ValT Void)]
    resolveRigid rigid@(BoundAt db argPos) = concatMap resolveHelper parentCallSites
      where
        -- 1. We need to find the ID of the lambda that corresponds to the DeBruijn index
        --    of our rigid (i.e. the lambda which binds that rigid)
        --    We *should* be able to get that by indexing into the entry of our
        --    call chain map for our AppId key using the DeBruijn. I think?
        --    NOTE: I'm doing unsafe indexing for convenience and to simply things, we might want to
        --          switch to safe indexing later w/ real errors
        -- FIXME/REVIEW: Is the logic right here? I think it might not be....
        parentLambdaId :: LambdaId
        parentLambdaId = case db of
            -- N.B. our call site chain map only ever has one entry, and that's super annoying to fix
            -- so we're just gonna roll w/ it for now
            Z -> (callSiteChains M.! appId) Vector.! 0
            (S x) ->
                let firstParent = (callSiteChains M.! appId) Vector.! 0
                 in chaseRigid firstParent x callChains
        -- 2. Then we need to collect all of the call sites for that lambda. I think?
        parentCallSites :: Set AppId
        parentCallSites = callSites M.! parentLambdaId

        -- 3. This is where it get complicated.
        resolveHelper :: AppId -> [Map AbstractTy (ValT Void)]
        resolveHelper parentAppId = case concretifies asg argPos parentAppId of
            -- This happens when we can't determine the instantiation of a rigid at an application of the lambda that binds it.
            -- We can't meaningfully recover - it means that we *need* a rigid (because it appears in the signature of a function)
            -- but the rigid does not appear as a bound tyvar in the (applied/instantiated) function signature at a call site of its binding lambda.
            -- (or it means we really screwed something up here!)
            Nowhere ->
                error $
                    "Something went wrong when determining type variable concretifications. This could indicate either "
                        <> " an internal compiler error, or a misuse of phantom type variables in type applications of a dependent lambda"
            -- If it's not concrete then we have more chasing to do.
            -- We should be fine to call our top level function recursively here, though an unfortunate consequence of the
            -- way I've set this up is that the only easy way to do this has HORRIBLE complexity since we'll
            -- need to call the top level function a bunch of times. Whatever, optimize it later.
            There _abstractTy ->
                let
                    -- The original polymorphic function type of the lambda that binds the rigid we care about
                    parentPolyFunTy :: CompT AbstractTy
                    parentPolyFunTy = lambdaTy asg parentLambdaId
                    -- Every transitive concretifiction of this parent lambda (the recursive call to our top level function)
                    parentAbsFnTy :: CompT AbstractTy
                    parentConcretifications :: [Map AbstractTy (ValT Void)]
                    (parentAbsFnTy, parentConcretifications) = S.toList <$> getTyVarConcretifications asg callChains callSites callSiteChains parentAppId
                    -- The concretified function types with the rigids resolved for each call site. These SHOULD REALLY BE FULLY CONCRETE.
                    -- NOTE/REVIEW: I am not sure what to do if they are *not* fully concrete. We've kind of reached the end of the line here. There's nowhere else
                    --              we could look, afaict, to further concretify them.
                    fullyConcreteParentTypes :: [CompT AbstractTy]
                    fullyConcreteParentTypes = map (\instMap -> substCompT vacuous instMap parentAbsFnTy) parentConcretifications
                    -- We need to prove the types concrete, so we do so.
                    -- NOTE: We might want this to error on `Nothing`s so we know that something has gone wrong
                    --       (but I'll change that while debugging, maybe it'll just work... hahaha)
                    provenConcreteParentTypes :: [CompT Void]
                    provenConcreteParentTypes = mapMaybe decideConcreteCompT fullyConcreteParentTypes
                    -- This is the var "resolved" relative to the parent lambda's level. I am pretty sure it should always be a
                    -- `BoundAt Z ...`
                    var = BoundAt Z argPos
                    -- This is what we've been driving at: A list of every possible concretification of this rigid for each call site of the parent function
                    -- NOTE(to self): might want to throw errors on `Nothing` cases instead of using `mapMaybe`, at least for debugging
                    concretificationsForThisRigid :: [ValT Void]
                    concretificationsForThisRigid =
                        mapMaybe
                            ( \concrete ->
                                decideConcrete
                                    =<< instantiationHelper vacuous var concrete parentPolyFunTy
                            )
                            provenConcreteParentTypes
                 in
                    M.singleton rigid <$> concretificationsForThisRigid
            -- We already did the work in `concretifies`, we just return a singleton list of a singleton map w/ the instantiation
            Here concreteResult -> [M.singleton rigid concreteResult]

-- 'getInstantiations' but works on the types we actually need
instantiationHelper ::
    forall (a :: Type).
    (CompT a -> CompT AbstractTy) -> -- need to pass this in so we can use this on CompT Voids
    AbstractTy -> -- the tyvar
    CompT a -> -- The more concrete type. Might be CompT Void if we KNOW it's concrete
    CompT AbstractTy -> -- The more polymorphic type.
    Maybe (ValT AbstractTy)
instantiationHelper f var concrete poly = M.lookup var $ runReader (getInstantiations [var] poly' concrete') 0
  where
    concrete' = Vector.toList . compTArgSchema $ f concrete
    poly' = Vector.toList . compTArgSchema $ poly

-- Given a list of variables, one list of types representing the function type (minus the result, we don't care about it i think),
-- and a second list of types representing the arguments to which it is applied, determine all the instantiations
-- I know we hate lists but it seems really silly to do this w/ vectors...
getInstantiations :: [AbstractTy] -> [ValT AbstractTy] -> [ValT AbstractTy] -> Reader Int (Map AbstractTy (ValT AbstractTy))
getInstantiations [] _ _ = pure M.empty
getInstantiations _ [] _ = pure M.empty
getInstantiations _ _ [] = pure M.empty
getInstantiations (var : vars) fs@(fE : fEs) as@(aE : aEs) =
    instantiates var aE fE >>= \case
        Nothing -> (<>) <$> getInstantiations [var] fEs aEs <*> getInstantiations vars fs as
        Just t -> M.insert var t <$> getInstantiations vars fs as

instantiates ::
    AbstractTy ->
    ValT AbstractTy -> -- the "more concrete type", usually the actual argument from 'app'
    ValT AbstractTy -> -- the "more polymorphic type', usually from the fn definition
    Reader Int (Maybe (ValT AbstractTy))
instantiates var concrete abstract = case (concrete, abstract) of
    (x, Abstraction a) ->
        sameVar var a >>= \case
            True -> pure $ Just x
            False -> pure Nothing
    (ThunkT (CompN _ concreteFn), ThunkT (CompN _ abstractFn)) ->
        let concreteFn' = Vector.toList $ compTBodyToVec concreteFn
            abstractFn' = Vector.toList $ compTBodyToVec abstractFn
         in local (+ 1) $ go concreteFn' abstractFn'
    (Datatype tnC argsC, Datatype tnA argsA)
        | tnC == tnA -> go (Vector.toList argsC) (Vector.toList argsA)
    _ -> pure Nothing
  where
    -- second arg gets adjusted here, not first
    -- I THINK we need to do this?
    sameVar :: AbstractTy -> AbstractTy -> Reader Int Bool
    sameVar varA varB = do
        varB' <- resolveVar varB
        pure $ varA == varB'

    go :: [ValT AbstractTy] -> [ValT AbstractTy] -> Reader Int (Maybe (ValT AbstractTy))
    go [] _ = pure Nothing
    go _ [] = pure Nothing
    go (c : cs) (a : as) = (<|>) <$> instantiates var c a <*> go cs as

resolveVar :: AbstractTy -> Reader Int AbstractTy
resolveVar (BoundAt db ix) = do
    offset <- ask
    let db' = fromJust . preview asInt $ review asInt db - offset
    pure $ BoundAt db' ix

decideConcreteCompT :: CompT AbstractTy -> Maybe (CompT Void)
decideConcreteCompT (CompN cnt body) =
    fmap (compN cnt . vecToCompTBody) . traverse decideConcrete . compTBodyToVec $ body

decideConcrete :: ValT AbstractTy -> Maybe (ValT Void)
decideConcrete = \case
    Abstraction _ -> Nothing
    ThunkT (CompN cnt body) -> do
        body' <- traverse decideConcrete $ compTBodyToVec body
        pure . ThunkT . compN cnt $ vecToCompTBody body'
    BuiltinFlat biTy -> Just (BuiltinFlat biTy)
    Datatype tn args -> Datatype tn <$> traverse decideConcrete args

-- We need to collect all of the child ASGs for each lambda. We do this all in one pass, so the
-- second arg is still the top level id of the main ASG. The outer keys of the map are lambda node IDs and the
-- inner map is a representation of the ASG
getLambdaSubASG :: ASG -> Id -> Map LambdaId (Map Id ASGNode)
getLambdaSubASG asg i = case nodeAt i asg of
    AnError -> M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> case bRef of
            -- If the body is just an arg then I *think* there's nothing we can do here?
            AnArg{} -> M.empty
            AnId child ->
                let allChildNodes = getAllNodes asg child
                    here = M.singleton (LambdaId i) allChildNodes
                    smallerComponents = getLambdaSubASG asg child
                 in here <> smallerComponents
        Force fRef -> goRef fRef
        _ -> M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> M.empty
        -- We're going "top down" so we may not have encountered the lambda yet.
        -- This might lead to us processing the same lambda more than twice (which isn't great)
        -- but that shouldn't affect correctness and I can fix the performance later
        App fn args _ _ ->
            let fnAsg = getLambdaSubASG asg fn
                args' = vFoldMap goRef args
             in fnAsg <> args'
        Thunk child -> getLambdaSubASG asg child -- I think?
        Cata ty handlers arg -> M.unionsWith (<>) (goRef <$> handlers) <> goRef arg
        DataConstructor _tn _cn args -> vFoldMap goRef args
        Match scrut handlers -> goRef scrut <> vFoldMap goRef handlers
  where
    goRef :: Ref -> Map LambdaId (Map Id ASGNode)
    goRef = \case
        AnArg{} -> M.empty
        AnId ix -> getLambdaSubASG asg ix

getAllNodes :: ASG -> Id -> Map Id ASGNode
getAllNodes asg i = case thisNode of
    AnError -> here
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> here <> goRef bRef
        Force fRef -> here <> goRef fRef
        _ -> here
    AValNode _valT valNode -> case valNode of
        Lit _ -> here
        App fn args _ _ -> here <> getAllNodes asg fn <> Vector.foldMap goRef args
        Thunk child -> here <> getAllNodes asg child
        DataConstructor _tn _cn args -> here <> Vector.foldMap goRef args
        Match scrut handlers -> here <> goRef scrut <> Vector.foldMap goRef handlers
        Cata ty handlers arg -> here <> M.unions (goRef <$> handlers) <> goRef arg
  where
    thisNode = nodeAt i asg
    here = M.singleton i thisNode

    goRef = \case
        AnArg{} -> M.empty
        AnId ix -> getAllNodes asg ix

getCallSiteChainMap ::
    ASG ->
    Id ->
    Map LambdaId (Set AppId) ->
    Reader (Vector LambdaId) (Map AppId (Vector LambdaId))
getCallSiteChainMap asg i callsites = case nodeAt i asg of
    AnError -> pure M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> case M.lookup (LambdaId i) callsites of
            Nothing -> goRef bRef
            Just{} -> local (Vector.cons (LambdaId i)) $ goRef bRef
        Force fRef -> goRef fRef
        _ -> pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit{} -> pure M.empty
        App fn args _ _ -> case M.lookup (LambdaId fn) callsites of
            Nothing -> do
                fnPart <- getCallSiteChainMap asg fn callsites
                argsPart <- vFoldMap id <$> traverse goRef args
                pure $ fnPart <> argsPart
            Just{} -> do
                cxt <- ask
                M.insert (AppId i) cxt <$> do
                    fnPart <- getCallSiteChainMap asg fn callsites
                    argsPart <- vFoldMap id <$> traverse goRef args
                    pure $ fnPart <> argsPart
        Thunk child -> getCallSiteChainMap asg child callsites
        DataConstructor _ _ args -> vFoldMap id <$> traverse goRef args
        Match scrut handlers -> vFoldMap id <$> traverse goRef (scrut `Vector.cons` handlers)
        Cata ty handlers arg -> vFoldMap id <$> traverse goRef (Vector.fromList (arg : Vector.toList handlers))
  where
    goRef = \case
        AnArg{} -> pure M.empty
        AnId ix -> getCallSiteChainMap asg ix callsites

{- NOTE: I can probably rewrite this as a single traversal/fold after I know it works. Still kind of sick and
         doing it this way seemed likely to reduce the possibility for mistakes.
-}

-- The Set IS NOT AN ORDERED LIST OF HIERARCHICAL CALLSITES, it is instead an exhaustive set of possibile concretifications of the key lambda
-- in every "upwards" call site that might concretify a tyvar differently
getCallChain :: ASG -> Id -> Map LambdaId (Set LambdaId) -- it should be a NonEmpty but I just want to get the logic right for now
getCallChain asg i = foldl' go M.empty raw
  where
    -- Assumes that the top level is a function (it should be)
    raw :: Set (LambdaId, LambdaId)
    raw = runReader (getCallChain' asg i) (LambdaId i)

    go :: Map LambdaId (Set LambdaId) -> (LambdaId, LambdaId) -> Map LambdaId (Set LambdaId)
    go acc (caller, called) =
        M.alter
            ( \case
                Nothing -> Just $ S.singleton caller
                Just v -> Just $ S.insert caller v
            )
            called
            acc

getCallChain' :: ASG -> Id -> Reader LambdaId (Set (LambdaId, LambdaId)) -- (Container,Containee)
getCallChain' asg i = case nodeAt i asg of
    AnError -> pure S.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> do
            parent <- ask
            let here = (parent, LambdaId i)
            rest <- local (\_ -> LambdaId i) (goRef bRef)
            if i == topLevelId asg
                then pure rest
                else pure $ S.insert here rest
        Force fRef -> goRef fRef
        _ -> pure S.empty
    AValNode _valT valNode -> case valNode of
        Lit{} -> pure S.empty
        App fn args _ _ -> do
            fnPart <- getCallChain' asg fn
            argsPart <- Vector.foldMap id <$> traverse goRef args
            pure $ fnPart <> argsPart
        Thunk child -> getCallChain' asg child
        DataConstructor _tn _cn args -> Vector.foldMap id <$> traverse goRef args
        Match scrut handlers -> do
            scrutPart <- goRef scrut
            handlersPart <- Vector.foldMap id <$> traverse goRef handlers
            pure $ scrutPart <> handlersPart
        Cata ty handlers arg -> Vector.foldMap id <$> traverse goRef (Vector.fromList (arg : Vector.toList handlers))
  where
    goRef = \case
        AnArg{} -> pure S.empty
        AnId ix -> getCallChain' asg ix

chaseRigid ::
    LambdaId -> -- the starting point. if the DB is Z we will just return this
    DeBruijn ->
    Map LambdaId (Set LambdaId) ->
    LambdaId
chaseRigid lamStart Z _ = lamStart
chaseRigid lamStart db@(S x) callChains =
    let unmapped = M.toList callChains
     in case find (\v -> lamStart `S.member` snd v) unmapped of
            Just (next, _) -> chaseRigid next x callChains
            Nothing -> error "Ran out of chains indices in chaseRigid before we reached our goal"

tyInstDeps :: ASG -> Id -> Reader (Vector Id) (Map Id (Map Id (Vector Id)))
tyInstDeps asg i = case nodeAt i asg of
    AnError -> pure M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> local (Vector.cons i) $ goRef bodyRef
        Force fRef -> goRef fRef
        _ -> pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> pure M.empty
        App fn args _ _ -> do
            cxt <- ask
            -- Our result is a Map LambdaId (Map AppId (Vector Id)), so the 'fn' comes first (somewhat unintuitively given the traversal order)
            let here = M.singleton fn (M.singleton i cxt)
            fnPart <- tyInstDeps asg fn
            argsParts <- M.unionsWith goMerge <$> traverse goRef (Vector.toList args)
            pure $ M.unionsWith goMerge ([here, fnPart, argsParts] :: [(Map Id (Map Id (Vector Id)))])
        Thunk child -> tyInstDeps asg child
        Cata ty handlers arg -> M.unionsWith goMerge <$> traverse goRef (arg : Vector.toList handlers)
        DataConstructor _tn _cn args -> M.unionsWith goMerge <$> (traverse goRef . Vector.toList $ args)
        Match scrut handlers -> do
            scrut' <- goRef scrut
            handlers' <- M.unionsWith goMerge <$> (traverse goRef . Vector.toList $ handlers)
            pure $ M.unionWith goMerge scrut' handlers'
  where
    goRef :: Ref -> Reader (Vector Id) (Map Id (Map Id (Vector Id)))
    goRef = \case
        AnId i' -> tyInstDeps asg i'
        AnArg{} -> pure M.empty

    -- I am not 10000% sure that (<>) is what we want so I'm splitting this out to a helper so it's easier to fix if I'm wrong.
    -- This does seem right though. We don't expect overlapping keys here.
    -- We still need to `unionWith/unionsWith` because the map monoid won't combine the monoids of its elements if they're monoidal
    goMerge :: Map Id (Vector Id) -> Map Id (Vector Id) -> Map Id (Vector Id)
    goMerge = (<>)

-- The Set Id in the return type is the set of all call sites of the lambda that is that key of that map entry
-- I.e.
getCallSites :: Set Id -> ASG -> Id -> Map LambdaId (Set AppId)
getCallSites lambdas asg i = case nodeAt i asg of
    AnError -> M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> goRef bodyRef
        Force fRef -> goRef fRef
        _ -> M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> M.empty
        App fn args _ _ -> case S.member fn lambdas of
            False -> M.unionWith (<>) (getCallSites lambdas asg fn) (vFoldMap goRef args)
            True ->
                let here = M.singleton (LambdaId fn) (S.singleton $ AppId i)
                    fromFn = getCallSites lambdas asg fn
                    fromArgs = M.unionsWith (<>) . map goRef . Vector.toList $ args
                 in M.unionsWith (<>) ([here, fromFn, fromArgs] :: [(Map LambdaId (Set AppId))])
        Thunk child -> getCallSites lambdas asg child
        Cata ty handlers arg -> M.unionsWith (<>) (goRef <$> (arg : Vector.toList handlers))
        DataConstructor _tn _cn args -> M.unionsWith (<>) (goRef <$> args)
        Match scrut handlers -> M.unionWith (<>) (goRef scrut) (M.unionsWith (<>) (goRef <$> handlers))
  where
    goRef :: Ref -> Map LambdaId (Set AppId)
    goRef = \case
        AnId child -> getCallSites lambdas asg child
        AnArg _ -> M.empty

getTypeFixerChains' :: ASG -> Id -> Map TyFixerId (Set (Vector LambdaId))
getTypeFixerChains' asg i = fst $ execRWS (getTypeFixerChains asg i) mempty mempty

getTypeFixerChains :: ASG -> Id -> RWS (Vector LambdaId) () (Map TyFixerId (Set (Vector LambdaId))) ()
getTypeFixerChains asg i = case nodeAt i asg of
    AnError -> pure ()
    ACompNode compT compNode -> case compNode of
        Lam bodyRef -> local (Vector.cons (LambdaId i)) $ goRef bodyRef
        Force fRef -> goRef fRef
        _aBuiltin -> pure ()
    AValNode valT valNode -> case valNode of
        Lit _ -> pure ()
        Thunk thunkId -> getTypeFixerChains asg thunkId
        App fn args _ _ -> do
            logTyFixer AnAppId i
            getTypeFixerChains asg fn
            traverse_ goRef args
        Match scrut handlers -> do
            logTyFixer AMatchId i
            goRef scrut
            traverse_ goRef handlers
        Cata ty handlers arg -> do
            logTyFixer ACataId i
            traverse_ goRef handlers
            goRef arg
        DataConstructor _tn _cn args -> do
            logTyFixer AConstrId i
            traverse_ goRef args
  where
    goRef = \case
        AnId child -> getTypeFixerChains asg child
        AnArg _ -> pure ()

    logTyFixer :: (Id -> TyFixerId) -> Id -> RWS (Vector LambdaId) () (Map TyFixerId (Set (Vector LambdaId))) ()
    logTyFixer tyFixerKind tfId = do
        currentStack <- ask
        modify
            ( M.alter
                ( \case
                    Nothing -> Just $ S.singleton currentStack
                    Just knownPaths ->
                        if currentStack `S.member` knownPaths
                            then Just knownPaths
                            else Just $ S.insert currentStack knownPaths
                )
                (tyFixerKind tfId)
            )

allLambdas :: ASG -> Id -> Set Id
allLambdas asg i = case nodeAt i asg of
    AnError -> mempty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> S.insert i $ goRef bodyRef
        Force fRef -> goRef fRef
        _aBuiltin -> mempty
    AValNode _valT valNode -> case valNode of
        Lit _ -> mempty
        App fn args _ _ ->
            let fnPart = allLambdas asg fn
                argsPart = Vector.foldMap goRef args
             in fnPart <> argsPart
        Thunk child -> allLambdas asg child
        Cata ty handlers arg -> foldMap goRef ((arg : Vector.toList handlers) :: [Ref])
        DataConstructor _tn _cn args -> Vector.foldMap goRef args
        Match scrut handlers -> goRef scrut <> Vector.foldMap goRef handlers
  where
    goRef :: Ref -> Set Id
    goRef = \case
        AnId child -> allLambdas asg child
        AnArg _ -> mempty

-- helpers

-- Vector.foldMap uses the wrong monoid instance for `Map` so we need to always use this instead.
vFoldMap :: forall (a :: Type) (k :: Type) (v :: Type). (Ord k, Monoid v) => (a -> Map k v) -> Vector a -> Map k v
vFoldMap f = Vector.foldl' (\acc x -> M.unionWith (<>) acc (f x)) mempty

-- this is really fucking stupid but I don't have the time to do something better
compTBodyToVec :: forall a. CompTBody a -> Vector (ValT a)
compTBodyToVec (ArgsAndResult args res) = Vector.snoc args res

vecToCompTBody :: forall a. Vector (ValT a) -> CompTBody a
vecToCompTBody vec = case Vector.unsnoc vec of
    Just (args, res)
        | Vector.null args -> ReturnT res -- might not need this?
        | otherwise -> ArgsAndResult args res
    Nothing -> error "empty CompT"

compN :: Count "tyvar" -> CompTBody a -> CompT a
compN = CompN

compTBody :: CompT a -> CompTBody a
compTBody (CompN _ body) = body

compTArgSchema :: CompT a -> Vector (ValT a)
compTArgSchema t = case compTBody t of
    ArgsAndResult args _ -> args

substCompT ::
    forall (a :: Type).
    (ValT a -> ValT AbstractTy) ->
    Map AbstractTy (ValT a) ->
    CompT AbstractTy ->
    CompT AbstractTy
substCompT f dict (CompN cnt (compTBodyToVec -> bodyVec)) = CompN cnt (vecToCompTBody subbed) -- NOTE: COUNT WILL BE WRONG (I don't think it matters)
  where
    subbed = (\vt -> runReader (substitute f dict vt) 0) <$> bodyVec

-- the extra function arg lets this work with either AbstractTy or Void (which might be useful for us)
substitute ::
    forall (a :: Type).
    (ValT a -> ValT AbstractTy) ->
    Map AbstractTy (ValT a) ->
    ValT AbstractTy ->
    Reader Int (ValT AbstractTy)
substitute f dict = \case
    Abstraction a ->
        resolveVar a >>= \a' -> case M.lookup a' dict of
            Nothing -> pure $ Abstraction a
            Just t -> pure (f t)
    ThunkT (CompN cnt concreteFn) -> do
        let bodyAsVec = compTBodyToVec concreteFn
        subbedBody <- local (+ 1) $ traverse (substitute f dict) bodyAsVec
        pure . ThunkT . CompN cnt $ vecToCompTBody subbedBody
    Datatype tn args -> Datatype tn <$> traverse (substitute f dict) args
    other -> pure other

-- "unsafe" way to retrieve the original (i.e. possibly polymorphic) lambda type
lambdaTy :: ASG -> LambdaId -> CompT AbstractTy
lambdaTy asg (LambdaId l) = case nodeAt l asg of
    ACompNode compT _ -> compT
    _other -> error "Lambda id points at non-comp-node"

-- Checks whether a "was rigid" (identified by the Index) is instantiated at a given call site of the lambda
-- which binds it, and if so, sorts the resulting type that instantiates it into concrete or abstract.
concretifies ::
    ASG ->
    Index "tyvar" -> -- The arg index of the rigid. We know the DeBruijn must be Z
    AppId -> -- AppId of *a* call site of a "parent" lambda that binds the rigid we're examining
    -- We either get:
    --   1. Nothing (which indicates an internal error or something weird with a phantom type variable
    --      (REVIEW: Do we sufficiently 'check' for phantom tyvars before this? The requirements here
    --               may differ from our previous ones. A phantom tyvar is fine if it's never *used*
    --               anywhere, but things could get really broken if we don't forbid their use
    --               ***in explicit type applications that would result in them being a ridid***.
    --      )
    --   2. An rigid type variable, which means we have more work to do.
    --   3. A concrete type, which is what we want.
    Wedge (ValT Void) (ValT AbstractTy)
concretifies asg argPos (AppId pcsId) = case nodeAt pcsId asg of
    AValNode _ (App fn _args _instArgs monoFunTy) ->
        let polyFunTy = lambdaTy asg (LambdaId fn)
            var = BoundAt Z argPos
         in case instantiationHelper id var monoFunTy polyFunTy of
                Nothing -> Nowhere
                Just ty -> case decideConcrete ty of
                    Nothing -> There ty
                    Just ty' -> Here ty'
    _ -> error "App node does not point at an App ValNode!!!"

-- There has to be a term for what this does (can't remember it), but the general idea is given by the example:
-- `combine [["a","b"],["c"],["d","e"]]` ~ `["acd","ace","bcd","bce"]`
combine :: forall (a :: Type). (Monoid a) => [[a]] -> [a]
combine [] = []
combine (xs : xss) = go xs xss
  where
    go :: [a] -> [[a]] -> [a]
    go as [] = as
    go as (ys : yss) =
        let as' = (<>) <$> as <*> ys
         in go as' yss

countToTyVars :: Count "tyvar" -> Vector (ValT AbstractTy)
countToTyVars cnt
    | cntI == 0 = mempty
    | otherwise = mkTV <$> Vector.fromList [0 .. (cntI - 1)]
  where
    cntI :: Int
    cntI = review intCount cnt

    mkTV :: Int -> ValT AbstractTy
    mkTV = Abstraction . BoundAt Z . fromJust . preview intIndex

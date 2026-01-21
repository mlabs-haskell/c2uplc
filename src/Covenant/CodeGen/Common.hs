{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Covenant.CodeGen.Common where

import Covenant.ASG (
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
 )
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.Data (DatatypeInfo)
import Covenant.Test (Arg (UnsafeMkArg), Id (UnsafeMkId))
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT,
    CompT (CompN),
    CompTBody (ArgsAndResult),
    Constructor,
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (
        EnumData,
        NewtypeData,
        ProductListData
    ),
    TyName,
 )

-- N.B. *WE* have two different things called `ConstrData`
import Covenant.Type qualified as Ty

import Control.Monad.Error.Class (MonadError, throwError)
import Control.Monad.Reader.Class (MonadReader (local), ask, asks)
import Control.Monad.State.Class (MonadState (get), gets, modify, put)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.RWS (RWS, evalRWS)

import Data.Foldable (foldl', traverse_)

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Data.Text (Text)
import Data.Text qualified as T

import Optics.Core (review, view)

import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (intIndex)
import Covenant.MockPlutus (
    IsBuiltin,
    PlutusTerm,
    SomeBuiltin (SomeBuiltin1, SomeBuiltin2, SomeBuiltin3, SomeBuiltin6),
    bData,
    constrData,
    iData,
    listData,
    mapData,
    pApp,
    pBuiltin,
    pCase,
    pConstr,
    pDelay,
    pError,
    pForce,
    pLam,
    pLet,
    pVar,
    plutus_ConstrData,
    prettyPTerm,
 )

import Covenant.ArgDict ()

import Control.Monad.Except (runExceptT)
import Control.Monad.State (State, execState, runState)
import Covenant.ExtendedASG (ExtendedASG, ExtendedId (..), extendedNodes, forgetExtendedId, unExtendedASG)
import Covenant.JSON (CompilationUnit)
import Covenant.Transform (transformASG)
import Covenant.Transform.Common (PolyRepHandler, TyFixerFnData (TyFixerFnData))
import Covenant.Transform.Pipeline.Common (PipelineData, TransformState)
import Covenant.Transform.TyUtils (LambdaId (LambdaId), idToName)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Maybe (isJust)
import Data.Row.Records (HasType, KnownSymbol, Label, Rec, (.+), (.==), type (.+), type (.==))
import Data.Row.Records qualified as R
import Data.Set (Set)
import Data.Set qualified as S
import Data.Traversable (forM)
import Debug.Trace
import Debug.Trace (traceM)
import GHC.TypeLits (Symbol)
import PlutusCore (Name (Name))
import PlutusCore.MkPlc (mkConstant)
import Prettyprinter
import UntypedPlutusCore (Unique (Unique))

{- Since we're switching to top-down compilation, this has to work a little differently.

   We need some kind of reader context which allows us to:
     1. Resolve `arg`s to concrete names that are properly scoped.
     2. Determine whether we can `let` bind terms at a given point
     3. "Know where we are", since we need that *at least* for resolving args (we have to know the
        Id of the lambda they point at to make our naming scheme work).

   We should be able to handle this with a three-field context:
     - One field tracks the names corresponding to previously let-bound Ids
     - The other is just a `Vector LambdaId` that is used for DeBruijn resolution.
     - We'll also want the ASG in scope at all times, else we can't traverse top-down
-}
newtype CodeGenContext
    = CodeGenContext
    { getContext ::
        Rec
            ( "termScope" .== Map Id Name
                .+ "argScope" .== Map LambdaId (Vector Name)
                .+ "lamScope" .== Vector LambdaId
                .+ "asg" .== Map Id ASGNode
            )
    }

data CodeGenError
    = NoASG
    | TermNotInASG Id
    | TermNotInContext Id
    | NoDatatype TyName
    | ConstructorNotInDatatype TyName ConstructorName
    | InvalidOpaqueEncoding Text
    | ArgResolutionFail ArgResolutionFailReason
    deriving stock (Show, Eq)

data ArgResolutionFailReason
    = {- | We got @Nothing@ when we tried to look up the context corresponding to the
      @Id@ of the parent node where the arg was found.
      -}
      ParentIdLookupFailed Id
    | {- | The @Id@ of the parent node of the arg we are examining should index a @Vector Id@ but instead
      indexes a @Vector Name@.
      -}
      ParentIdPointsAtNames Id
    | -- | The @DeBruijn@ index of the arg points to an out of bounds lambda.
      DBIndexOutOfBounds DeBruijn
    | {- | The @Id@ of the lambda corresponding to the @DeBruijn@ index does not correspond to anything in our
      argument resolution dictionary.
      -}
      NoBindingContext Id
    | {- | The @Id@ of the Lambda that the DeBruijn points at corresponds to an entry in our
      argument resolution diciontary, but that entry is a @Vector Id@ and not the @Vector Name@
      that we need
      -}
      LamIdPointsAtContext Id
    deriving stock (Show, Eq)

newtype CodeGenM a = CodeGenM (ExceptT CodeGenError (RWS CodeGenContext () Int) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader CodeGenContext
        , MonadState Int
        , MonadError CodeGenError
        )
        via (ExceptT CodeGenError (RWS CodeGenContext () Int))

runCodeGenM :: forall a. Map Id ASGNode -> Map Id Name -> CodeGenM a -> Either CodeGenError a
runCodeGenM m termScope (CodeGenM act) = fst $ evalRWS (runExceptT act) cxt 0
  where
    cxt =
        CodeGenContext $
            #termScope .== termScope
                .+ #argScope .== mempty
                .+ #lamScope .== mempty
                .+ #asg .== m

getNode :: Id -> CodeGenM (Maybe ASGNode)
getNode i = do
    r <- asks getContext
    pure $ M.lookup i (r R..! #asg)

getArgScope :: CodeGenM (Map LambdaId (Vector Name))
getArgScope = do
    CodeGenContext r <- ask
    pure $ r R..! #argScope

getLamScope :: CodeGenM (Vector LambdaId)
getLamScope = do
    CodeGenContext r <- ask
    pure $ r R..! #lamScope

getTermScope :: CodeGenM (Map Id Name)
getTermScope = do
    CodeGenContext r <- ask
    pure $ r R..! #termScope

lookupVar :: Id -> CodeGenM (Maybe Name)
lookupVar i = do
    CodeGenContext r <- ask
    pure $ M.lookup i (r R..! #termScope)

resolveArg :: Arg -> CodeGenM Name
resolveArg aaa@(UnsafeMkArg argDb argPos _) = do
    argScope <- getArgScope
    lamScope <- getLamScope
    let db = review asInt argDb
        pos = review intIndex argPos
    case lamScope Vector.!? db of
        Nothing -> throwError $ ArgResolutionFail (DBIndexOutOfBounds argDb)
        Just parentLamId@(LambdaId plid) -> case M.lookup parentLamId argScope of
            Nothing -> throwError $ ArgResolutionFail (ParentIdLookupFailed plid)
            Just names -> case names Vector.!? pos of
                Nothing ->
                    error $
                        "\n\nFailed to resolve arg: "
                            <> show aaa
                            <> "\n Parent Lam Id: "
                            <> show plid
                            <> "\n db: "
                            <> show db
                            <> "\n pos: "
                            <> show pos
                            <> "\n lamScope: "
                            <> show lamScope
                            <> "\n argScope: "
                            <> show argScope
                Just argNm -> pure argNm

withBoundArgVars :: forall (a :: Type). LambdaId -> Vector Name -> CodeGenM a -> CodeGenM a
withBoundArgVars lid args = local go
  where
    go :: CodeGenContext -> CodeGenContext
    go (CodeGenContext r) = CodeGenContext $ rModify (M.insert lid args) #argScope r

freshUnique :: CodeGenM Unique
freshUnique = do
    old <- get
    let new = old + 1
    put new
    pure (Unique new)

crossLam :: CompT AbstractTy -> LambdaId -> CodeGenM PlutusTerm -> CodeGenM PlutusTerm
crossLam compT lid@(LambdaId i) act = do
    vars <- mkLamArgNames i compT
    let f = foldl' (\g argN -> g . pLam argN) id vars
    f <$> local (go vars) act
  where
    go :: Vector Name -> CodeGenContext -> CodeGenContext
    go vars (CodeGenContext r) =
        CodeGenContext
            . rModify (Vector.cons lid) #lamScope
            . rModify (M.insert lid vars) #argScope
            $ r

rModify ::
    forall (l :: Symbol) (t :: Type) (r :: R.Row Type).
    (KnownSymbol l, HasType l t r) =>
    (t -> t) ->
    Label l ->
    Rec r ->
    Rec r
rModify f l r = R.update l new r
  where
    new = f (r R..! l)

runTopDownCompile ::
    Rec PipelineData ->
    ExtendedASG ->
    Either CodeGenError PlutusTerm
runTopDownCompile plData eAsg = do
    let emptyPrepSt = #onlySrcNodes .== mempty .+ #initTermScope .== mempty .+ #bind .== mempty
        prepRec = execState (prepare plData eAsg) emptyPrepSt
        nodes = prepRec R..! #onlySrcNodes
        topId = fst $ M.findMax nodes
        termScope = prepRec R..! #initTermScope

        doBinds = foldr (\(nm, term) acc -> pLet nm term . acc) id (prepRec R..! #bind)
    doBinds <$> runCodeGenM nodes termScope (compileTopDown topId)

prettyMap :: (Show k, Show v) => Map k v -> String
prettyMap = M.foldrWithKey (\k v acc -> show k <> " := " <> show v <> "\n" <> acc) "\n"

-- this is stupid
-- FIXME: I need to ensure that the poly rep handlers get let bound *before* the synthetic
--        type fixer functions, or they'll be out of scope if we need to embed or project
--        constructors paramaterized by constant Integers or ByteStrings
prepare ::
    Rec PipelineData ->
    ExtendedASG ->
    State
        ( Rec
            ( "onlySrcNodes" .== Map Id ASGNode
                .+ "initTermScope" .== Map Id Name
                .+ "bind" .== [(Name, PlutusTerm)]
            )
        )
        ()
prepare plData eAsg = do
    modify $ R.update #onlySrcNodes (M.mapKeys forgetExtendedId srcNodes)
    traverse_ (go . forgetExtendedId) (M.keys specialNodes)
    modify $ rModify reverse #bind
  where
    (specialNodes, srcNodes) = M.partitionWithKey (\k _ -> isSynthNode k) eNodes
    eNodes = extendedNodes eAsg
    isSynthNode = \case
        IdentityFn _ -> True
        EphemeralError _ -> True
        Projection _ -> True
        Embedding _ -> True
        TyFixerFn _ -> True
        _ -> False

    tyFixers = plData R..! #tyFixers
    stubs = plData R..! #handlerStubs

    go i = case M.lookup i tyFixers of
        Just (TyFixerFnData _ _ _ thisTermCompiled _ nm _) -> do
            let UnsafeMkId iInner = i
                fnNm = Name nm (Unique (fromIntegral iInner))
            modify $ rModify (M.insert i fnNm) #initTermScope
            modify $ rModify ((fnNm, thisTermCompiled) :) #bind
        Nothing -> case M.lookup i stubs of
            Just stub -> do
                let iName = idToName i
                modify $ rModify (M.insert i iName) #initTermScope
                modify $ rModify ((iName, stub) :) #bind
            Nothing -> pure ()

nodeOrVar :: Id -> CodeGenM (Either Name ASGNode)
nodeOrVar i =
    lookupVar i >>= \case
        Just aVar -> pure $ Left aVar
        Nothing ->
            getNode i >>= \case
                Just aNode -> pure $ Right aNode
                Nothing -> error $ "No node or synthetic var info for: " <> show i

compileTopDown :: Id -> CodeGenM PlutusTerm
compileTopDown nodeId =
    nodeOrVar nodeId >>= \case
        Left nm -> pure $ pVar nm
        Right aNode -> case aNode of
            ACompNode compTy compNodeInfo -> case compNodeInfo of
                Builtin1 bi1 -> pure $ pBuiltin bi1
                Builtin2 bi2 -> pure $ pBuiltin bi2
                Builtin3 bi3 -> pure $ pBuiltin bi3
                Builtin6 bi6 -> pure $ pBuiltin bi6
                Force r -> pForce <$> compileRef r
                Lam r -> crossLam compTy (LambdaId nodeId) $ do
                    toBind <- letBinds (LambdaId nodeId) r
                    withLocalBinds toBind $ compileRef r
            AValNode valTy valNodeInfo -> case valNodeInfo of
                Lit aConstant -> litToTerm aConstant
                App fnId argRefs _ _ -> do
                    fn <- compileTopDown fnId
                    args <- traverse compileRef argRefs
                    pure $ foldl' pApp fn args
                Thunk childId -> pDelay <$> compileTopDown childId
                other -> error $ "value nodes should all be lits apps or thunks but got: " <> show other
  where
    compileRef :: Ref -> CodeGenM PlutusTerm
    compileRef r = case r of
        AnId i -> compileTopDown i
        AnArg arg -> pVar <$> resolveArg arg

    withLocalBinds :: Map Id ASGNode -> CodeGenM PlutusTerm -> CodeGenM PlutusTerm
    withLocalBinds toBind = letMany (M.keys toBind)
      where
        letMany :: [Id] -> CodeGenM PlutusTerm -> CodeGenM PlutusTerm
        letMany [] act = act
        letMany (i : rest) act = do
            let nm = idToName i
            t <- compileTopDown i
            local (doBind i nm) $
                letMany rest (pLet nm t <$> act)
          where
            doBind :: Id -> Name -> CodeGenContext -> CodeGenContext
            doBind thisId thisName (CodeGenContext r) =
                CodeGenContext $ rModify (M.insert thisId thisName) #termScope r

litToTerm :: AConstant -> CodeGenM PlutusTerm
litToTerm = \case
    AUnit -> pure $ mkConstant () ()
    ABoolean b -> pure $ mkConstant () b
    AnInteger i -> pure $ mkConstant () i
    AByteString bs -> pure $ mkConstant () bs
    AString txt -> pure $ mkConstant () txt

-- Uses the context to determine permissible let bindings
-- then descends into child nodes with a modified reader context where those are bound.
-- Kind of a hyper-specialized "local" that does some bookkeeping.
letBinds ::
    LambdaId ->
    Ref -> -- The BODY REF OF THE LAMBDA WE ARE DESCENDING INTO
    CodeGenM (Map Id ASGNode)
letBinds lambdaId@(LambdaId lamId) = getBindableSubTerms 0

mkLamArgNames :: Id -> CompT AbstractTy -> CodeGenM (Vector Name)
mkLamArgNames (UnsafeMkId idW) (CompN _ (ArgsAndResult argsRep _)) = flip Vector.imapM argsRep $ \pos _ -> do
    u <- freshUnique
    let txtPart = "arg_" <> T.pack (show idW) <> "_" <> T.pack (show pos)
    pure $ Name txtPart u

{- This is going to be *brutally* inefficient but I can always fix that later.

   We have to do something like:
     - For Args return an empty map
     - For Ids, check whether the *entire term* can be let bound.
         - If it can, return it as a singleton.
         - If it can't, recurse into the children and repeat this check.

-}
getBindableSubTerms :: Int -> Ref -> CodeGenM (Map Id ASGNode)
getBindableSubTerms dbOffset = \case
    -- We can't do anything if the lambda body is an arg, and even if we could, let binding it would just make the
    -- script larger for no reason (tho it'd probably evaluate away)
    AnArg _ -> pure M.empty
    AnId i ->
        alreadyCompiled i >>= \case
            True -> pure M.empty
            False -> go dbOffset i
  where
    withNode :: forall m. m -> Id -> (ASGNode -> CodeGenM m) -> CodeGenM m
    withNode def i f =
        nodeOrVar i >>= \case
            Left _ -> pure def
            Right node -> f node

    go :: Int -> Id -> CodeGenM (Map Id ASGNode)
    go dbOff nodeId = do
        withNode mempty nodeId $ \thisNode -> do
            safeToBind dbOff thisNode >>= \case
                True -> pure $ M.singleton nodeId thisNode
                False -> case thisNode of
                    ACompNode _ compNodeInfo -> case compNodeInfo of
                        Force r -> goRef dbOff r
                        Lam r -> goRef (dbOff + 1) r
                        _ -> pure M.empty
                    AValNode _ valNodeInfo -> case valNodeInfo of
                        Lit{} -> pure $ M.singleton nodeId thisNode
                        App fnId args _ _ -> do
                            fnBinds <- go dbOff fnId
                            argBinds <- M.unions <$> traverse (goRef dbOff) args
                            pure $ fnBinds <> argBinds
                        Thunk childId -> go dbOff childId
                        _ -> pure M.empty
      where
        goRef :: Int -> Ref -> CodeGenM (Map Id ASGNode)
        goRef dbDist r = case r of
            AnArg{} -> pure M.empty
            AnId childId -> go dbDist childId

    alreadyCompiled :: Id -> CodeGenM Bool
    alreadyCompiled = fmap isJust . lookupVar

    safeToBind :: Int -> ASGNode -> CodeGenM Bool
    safeToBind dbOff = \case
        ACompNode _ compNodeInfo -> case compNodeInfo of
            Force r -> safeToBindRef dbOff r
            Lam r ->
                -- FIXME
                -- we really want to check that it's EITHER "locally scoped"
                -- OR that all occurrences of any vars point to a higher level than the current point
                safeToBindRef (dbOff + 1) r
            _ -> pure True
        AValNode _ valNodeInfo -> case valNodeInfo of
            Lit _ -> pure True
            App fnId args _ _ -> do
                okFn <- withNode True fnId $ safeToBind dbOff
                okArgs <- and <$> traverse (safeToBindRef dbOff) args
                pure $ okFn && okArgs
            Thunk childId -> withNode True childId $ safeToBind dbOff
            _ -> pure False -- can't exist
    safeToBindRef :: Int -> Ref -> CodeGenM Bool
    safeToBindRef dbDist = \case
        AnArg (UnsafeMkArg argDb _ _) -> do
            {-
            If we see a (S Z) and our distance is, say, 5, we get:
               1 - 5 = -4 (which means we can't let bind)
            If we see a (S (S (S (S Z)))) and our distance is, say, 3, we get
               4 - 3 = 1 (which means we can let bind)
            I THINK?! REVIEW
            -}
            pure $ (review asInt argDb - dbDist) >= 0
        AnId i ->
            alreadyCompiled i >>= \case
                True -> pure True
                False -> withNode True i $ safeToBind dbDist

-- first part of tuple satisfies the monadic predicate, second part doesn't
partitionM :: forall (m :: Type -> Type) a. (Monad m) => (a -> m Bool) -> Vector a -> m (Vector a, Vector a)
partitionM p =
    Vector.foldM
        ( \acc x ->
            p x >>= \case
                True -> pure $ first (Vector.cons x) acc
                False -> pure $ second (Vector.cons x) acc
        )
        (Vector.empty, Vector.empty)

data LiftStatus
    = -- We can let- bind this thing atomically using our normal top-down compilation process
      AtomicLiftable
    | -- We have to compile the whole thing without any internal lifting/let-binding, but
      -- if we do that, we're OK to let bind
      InlineLiftable
    | -- We cannot lift.
      NoLift
    | -- We can lift without breaking things but doing so would not help script size
      OptionalLift
    deriving stock (Show, Eq, Ord)

instance Semigroup LiftStatus where
    NoLift <> _ = NoLift
    _ <> NoLift = NoLift
    AtomicLiftable <> InlineLiftable = InlineLiftable
    InlineLiftable <> AtomicLiftable = InlineLiftable
    AtomicLiftable <> AtomicLiftable = AtomicLiftable
    InlineLiftable <> InlineLiftable = InlineLiftable
    OptionalLift <> x = x
    x <> OptionalLift = x

instance Monoid LiftStatus where
    mempty = OptionalLift

-- first arg is the thing we're looking for, second arg is the starting point
countOccurs ::
    Id ->
    Id ->
    CodeGenM Int
countOccurs toCount start =
    nodeOrVar start >>= \case
        Left _ -> pure 0
        Right aNode -> case aNode of
            ACompNode _ compNodeInfo -> case compNodeInfo of
                Force r -> countRef r
                Lam r -> countRef r
                _ -> pure 0
            AValNode _ valNodeInfo -> case valNodeInfo of
                App fn args _ _ -> (+) <$> countId fn <*> (sum <$> traverse countRef args)
                Thunk i -> countId i
                _ -> pure 0
  where
    countId i
        | i == toCount = pure 1
        | otherwise = pure 0

    countRef = \case
        AnId i -> countId i
        AnArg _ -> pure 0

-- gets every arg out of a term recursively and resolves the DB to an Int relative to the given starting point
collectAndResolveArgs :: Int -> Id -> CodeGenM (Set Int)
collectAndResolveArgs dbOff start =
    nodeOrVar start >>= \case
        Left _ -> pure S.empty
        Right aNode -> case aNode of
            ACompNode _ compInfo -> case compInfo of
                Force r -> goRef dbOff r
                Lam r -> goRef (dbOff + 1) r
                _other -> pure S.empty
            AValNode _ valInfo -> case valInfo of
                App fn args _ _ -> do
                    fnRes <- collectAndResolveArgs dbOff fn
                    argsRes <- S.unions <$> traverse (goRef dbOff) args
                    pure $ fnRes <> argsRes
                Thunk i -> collectAndResolveArgs dbOff i
                _ -> pure S.empty
  where
    goRef offset = \case
        AnArg (UnsafeMkArg db _ _) -> pure . S.singleton $ (review asInt db - offset)
        AnId i -> collectAndResolveArgs dbOff i

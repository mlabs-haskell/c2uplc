{-# LANGUAGE RankNTypes #-}

module Covenant.CodeGen.Common
  ( CodeGenError (..),
    runTopDownCompile,
  )
where

-- N.B. *WE* have two different things called `ConstrData`

import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader.Class (MonadReader (local), ask, asks)
import Control.Monad.State (State, execState)
import Control.Monad.State.Class (MonadState (get), modify, put)
import Covenant.ASG
  ( ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Lit, Thunk),
  )
import Covenant.ArgDict (pCompT)
import Covenant.CodeGen.Stubs (StubError, mkNil, resolveStub, stubId)
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.ExtendedASG
  ( ExtendedASG,
    ExtendedId
      ( Embedding,
        EphemeralError,
        IdentityFn,
        Projection,
        TyFixerFn
      ),
    MonadASG (getASG),
    eTopLevelSrcNode,
    extendedNodes,
    forgetExtendedId,
  )
import Covenant.Index (intIndex)
import Covenant.Plutus
  ( pApp,
    pBuiltin,
    pDelay,
    pError,
    pForce,
    pLam,
    pLet,
    pVar,
    (#),
  )
import Covenant.Prim
  ( OneArgFunc (BData, IData, ListData, MapData),
    TwoArgFunc (ConstrData, MkCons),
  )
import Covenant.Transform.Common
  ( BuiltinFnData
      ( ByteString_Cata,
        Data_B,
        Data_Constr,
        Data_I,
        Data_List,
        Data_Map,
        Data_Match,
        Integer_Nat_Cata,
        Integer_Neg_Cata,
        List_Cata,
        List_Cons,
        List_Match,
        List_Nil,
        Map_Map,
        Map_Match,
        Pair_Match,
        Pair_Pair
      ),
    TyFixerFnData (BuiltinTyFixer, TyFixerFnData),
    pFreshLam2,
  )
import Covenant.Transform.Pipeline.Common (CodeGenData)
import Covenant.Transform.Pipeline.Monad
  ( ASTRef (ASTRef, appNodeId, underApps, underLams),
    CodeGen,
    PassM,
    RepPolyHandlers (RepPolyHandlers),
    runPass,
  )
import Covenant.Transform.TyUtils (AppId (AppId), LambdaId (LambdaId), idToName)
import Covenant.Type
  ( AbstractTy,
    CompT (CompN),
    CompTBody (ArgsAndResult),
    ConstructorName,
    TyName,
    ValT,
  )
import Covenant.Unsafe (Arg (UnsafeMkArg), Id (UnsafeMkId))
import Data.Foldable (foldl', traverse_)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (isJust)
import Data.Row.Records (HasType, KnownSymbol, Label, Rec, (.+), (.==), type (.+), type (.==))
import Data.Row.Records qualified as R
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.TypeLits (Symbol)
import Optics.Core (review, view)
import PlutusCore (Name (Name))
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore (DefaultFun, DefaultUni, Term, Unique (Unique))

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
  { _getContext ::
      Rec
        ( "termScope" .== Map Id (Term Name DefaultUni DefaultFun ())
            .+ "argScope" .== Map LambdaId (Vector Name)
            .+ "lamScope" .== Vector LambdaId
            -- We ONLY need an appscope for resolving Nil -_-
            .+ "appScope" .== Vector AppId
            .+ "asg" .== Map Id ASGNode
            .+ "tyFixers" .== Map Id TyFixerFnData
            .+ "repPolyHandlers" .== RepPolyHandlers
        )
  }

getContext ::
  CodeGenContext ->
  Rec
    ( "termScope" .== Map Id (Term Name DefaultUni DefaultFun ())
        .+ "argScope" .== Map LambdaId (Vector Name)
        .+ "lamScope" .== Vector LambdaId
        -- We ONLY need an appscope for resolving Nil -_-
        .+ "appScope" .== Vector AppId
        .+ "asg" .== Map Id ASGNode
        .+ "tyFixers" .== Map Id TyFixerFnData
        .+ "repPolyHandlers" .== RepPolyHandlers
    )
getContext (CodeGenContext x) = x

data CodeGenError
  = NoASG
  | TermNotInASG Id
  | TermNotInContext Id
  | NoDatatype TyName
  | ConstructorNotInDatatype TyName ConstructorName
  | InvalidOpaqueEncoding Text
  | ArgResolutionFail ArgResolutionFailReason
  | WrapStubError StubError
  | InvalidNilTy (ValT AbstractTy)
  | UnexpectedError
  deriving stock (Show, Eq)

data ArgResolutionFailReason
  = -- | We got @Nothing@ when we tried to look up the context corresponding to the
    --       @Id@ of the parent node where the arg was found.
    ParentIdLookupFailed Id
  | -- | The @Id@ of the parent node of the arg we are examining should index a @Vector Id@ but instead
    --       indexes a @Vector Name@.
    ParentIdPointsAtNames Id
  | -- | The @DeBruijn@ index of the arg points to an out of bounds lambda.
    DBIndexOutOfBounds DeBruijn
  | -- | The @Id@ of the lambda corresponding to the @DeBruijn@ index does not correspond to anything in our
    --       argument resolution dictionary.
    NoBindingContext Id
  | -- | The @Id@ of the Lambda that the DeBruijn points at corresponds to an entry in our
    --       argument resolution diciontary, but that entry is a @Vector Id@ and not the @Vector Name@
    --       that we need
    LamIdPointsAtContext Id
  deriving stock (Show, Eq)

-- TODO rewrite all the sigs to use constraints, no time now
type CodeGenM a = PassM CodeGenError CodeGenContext Int a

runCodeGenM ::
  forall a.
  RepPolyHandlers ->
  Map Id TyFixerFnData ->
  Map Id ASGNode ->
  Map Id (Term Name DefaultUni DefaultFun ()) ->
  CodeGenM a ->
  CodeGen (Either CodeGenError a)
runCodeGenM repPoly fixers m termScope act =
  runPass cxt 0 act >>= \case
    Left err -> pure $ Left err
    Right (a, _) -> pure $ Right a
  where
    cxt :: CodeGenContext
    cxt =
      CodeGenContext $
        #termScope .== termScope
          .+ #argScope .== mempty
          .+ #lamScope .== mempty
          .+ #appScope .== mempty
          .+ #asg .== m
          .+ #tyFixers .== fixers
          .+ #repPolyHandlers .== repPoly

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

getAppScope :: CodeGenM (Vector AppId)
getAppScope = do
  CodeGenContext r <- ask
  pure $ r R..! #appScope

getTyFixers :: CodeGenM (Map Id TyFixerFnData)
getTyFixers = do
  CodeGenContext r <- ask
  pure $ r R..! #tyFixers

checkNilFixer :: Id -> CodeGenM Bool
checkNilFixer i = do
  CodeGenContext r <- ask
  let RepPolyHandlers _ _ nilFixers = r R..! #repPolyHandlers
      nilFixerIds = S.fromList . map (\(ASTRef _ _ rId) -> rId) . S.toList $ nilFixers
  -- withLocation i $ \astRef -> pure $ astRef `S.member` nilFixers
  pure $ i `S.member` nilFixerIds

lookupVar :: Id -> CodeGenM (Maybe (Term Name DefaultUni DefaultFun ()))
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

freshUnique :: CodeGenM Unique
freshUnique = do
  old <- get
  let new = old + 1
  put new
  pure (Unique new)

crossLam ::
  CompT AbstractTy ->
  LambdaId ->
  CodeGenM (Term Name DefaultUni DefaultFun ()) ->
  CodeGenM (Term Name DefaultUni DefaultFun ())
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

-- TODO: Better name, this one is just a wrapper over 'local' (we need this to check ASTRefs in the
--       `canLet` stuff). This is all so we don't try to lift sub-ASGs that contain "disposable"
--       Nil type fixers
crossLamX :: forall a. LambdaId -> CodeGenM a -> CodeGenM a
crossLamX lid = local go
  where
    go (CodeGenContext r) = CodeGenContext $ rModify (Vector.cons lid) #lamScope r

crossApp :: AppId -> CodeGenM r -> CodeGenM r
crossApp appId = local (\(CodeGenContext r) -> CodeGenContext $ rModify (Vector.cons appId) #appScope r)

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
  Rec CodeGenData ->
  CodeGen (Either CodeGenError (Term Name DefaultUni DefaultFun ()))
runTopDownCompile plData = do
  eAsg <- getASG
  topId <- eTopLevelSrcNode
  let emptyPrepSt = #onlySrcNodes .== mempty .+ #initTermScope .== mempty .+ #bind .== mempty
  -- due to being boxed in by having ignored opaques + severe time constraints,
  -- we have to do this dumb hack to be able to match on them.
  matchDataId <- stubId "matchData"
  matchDataFn <- resolveStub "matchData"
  let prepRec = execState (prepare plData eAsg matchDataId matchDataFn) emptyPrepSt
  let nodes = prepRec R..! #onlySrcNodes
      -- topId = fst $ M.findMax nodes
      termScope = prepRec R..! #initTermScope
      repHandlers = plData R..! #repPolyHandlers
      doBinds = foldr (\(nm, term) acc -> pLet nm term . acc) id (prepRec R..! #bind)
  fmap doBinds <$> runCodeGenM repHandlers (plData R..! #tyFixers) nodes termScope (compileTopDown topId)

-- this is stupid
-- FIXME: I need to ensure that the poly rep handlers get let bound *before* the synthetic
--        type fixer functions, or they'll be out of scope if we need to embed or project
--        constructors paramaterized by constant Integers or ByteStrings
prepare ::
  Rec CodeGenData ->
  ExtendedASG ->
  Id ->
  Term Name DefaultUni DefaultFun () ->
  State
    ( Rec
        ( "onlySrcNodes" .== Map Id ASGNode
            .+ "initTermScope" .== Map Id (Term Name DefaultUni DefaultFun ())
            .+ "bind" .== [(Name, Term Name DefaultUni DefaultFun ())]
        )
    )
    ()
prepare plData eAsg matchDataId matchDataFn = do
  modify $ R.update #onlySrcNodes (M.mapKeys forgetExtendedId srcNodes)
  traverse_ (go . forgetExtendedId) (M.keys specialNodes)
  modify $ rModify (M.insert matchDataId matchDataFn) #initTermScope
  modify $ rModify ((idToName matchDataId, matchDataFn) :) #bind
  modify $ rModify reverse #bind
  where
    (specialNodes, srcNodes) = M.partitionWithKey (\k _ -> isSynthNode k) eNodes
    eNodes = extendedNodes eAsg
    isSynthNode = \case
      IdentityFn _ -> True
      EphemeralError _ -> False
      Projection _ -> True
      Embedding _ -> True
      TyFixerFn _ -> True
      _ -> False
    tyFixers = plData R..! #tyFixers
    RepPolyHandlers byId _ _ = plData R..! #repPolyHandlers
    go i = case M.lookup i tyFixers of
      Just (TyFixerFnData _ _ _ thisTermCompiled _ nm _) -> do
        let UnsafeMkId iInner = i
            fnNm = Name nm (Unique (fromIntegral iInner))
        modify $ rModify (M.insert i (pVar fnNm)) #initTermScope
        modify $ rModify ((fnNm, thisTermCompiled) :) #bind
      _ -> case M.lookup i byId of
        Just (stub, _, _) -> do
          modify $ rModify (M.insert i stub) #initTermScope
        -- we shouldn't need to bind any stubs here, the monad should take
        -- care of that for us. Not sure if we even need them in the term scope?
        Nothing -> pure ()

nodeOrVar :: Id -> CodeGenM (Either (Term Name DefaultUni DefaultFun ()) ASGNode)
nodeOrVar i =
  lookupVar i
    >>= \case
      Just aVar -> pure $ Left aVar
      Nothing ->
        getNode i >>= \case
          Just aNode -> pure $ Right aNode
          Nothing -> do
            tyFixers <- getTyFixers
            case M.lookup i tyFixers of
              Nothing -> do
                -- `id` is *kind of* a projection / embedding handler but we can't actually
                -- put it in the RepPolyHandlers thing because it doesn't have a "base type"
                -- so we have to catch it here
                idenId <- stubId "id"
                if i == idenId
                  then Left <$> resolveStub "id"
                  else error $ "No node or synthetic var info for: " <> show i
              Just tyFixer ->
                error $
                  "Somehow something tried to resolve Id "
                    <> show i
                    <> " which belongs to a type fixer of type: "
                    <> pCompT (view #fnTy tyFixer)

compileTopDown :: Id -> CodeGenM (Term Name DefaultUni DefaultFun ())
compileTopDown nodeId =
  nodeOrVar nodeId
    >>= \case
      Left nm -> pure nm
      Right aNode -> case aNode of
        AnError -> pure pError
        ACompNode compTy compNodeInfo -> case compNodeInfo of
          Builtin1 bi1 -> pure $ pBuiltin bi1
          Builtin2 bi2 -> pure $ pBuiltin bi2
          Builtin3 bi3 -> pure $ pBuiltin bi3
          Builtin6 bi6 -> pure $ pBuiltin bi6
          Force r -> pForce <$> compileRef r
          Lam r -> crossLam compTy (LambdaId nodeId) $ do
            toBind <- letBinds (LambdaId nodeId) r
            withLocalBinds toBind $ compileRef r
        AValNode _ valNodeInfo -> case valNodeInfo of
          Lit aConstant -> litToTerm aConstant
          App fnId argRefs _ fnTy -> do
            tyFixers <- getTyFixers
            -- special handling for Nil -_-
            isNilFixer <- checkNilFixer nodeId
            if isNilFixer
              then do
                let CompN _ (ArgsAndResult _ listTy) = fnTy
                mkNil mempty listTy >>= \case
                  Nothing -> throwError $ InvalidNilTy listTy
                  Just myNil -> pure myNil
              else case M.lookup fnId tyFixers of
                Just (BuiltinTyFixer _ biTyFixer) -> do
                  biFixer <- compileBIFixer biTyFixer
                  args <- traverse compileRef argRefs
                  if biNeedsDelay biTyFixer
                    then do
                      pure . pDelay $ foldl' pApp biFixer args
                    else do
                      pure $ foldl' pApp biFixer args
                _other -> do
                  fn <- compileTopDown fnId
                  args <- traverse compileRef argRefs
                  pure $ foldl' pApp fn args
          Thunk childId -> pDelay <$> compileTopDown childId
          other -> error $ "value nodes should all be lits apps or thunks but got: " <> show other
  where
    compileRef :: Ref -> CodeGenM (Term Name DefaultUni DefaultFun ())
    compileRef r = case r of
      AnId i -> do
        -- we have to check here for "nil-fixer-ness", I think?
        isNilFixer <- checkNilFixer i
        if isNilFixer
          then
            nodeOrVar i >>= \case
              Right (AValNode _ (App _ _ _ fnTy)) -> do
                let CompN _ (ArgsAndResult _ listTy) = fnTy
                mkNil mempty listTy >>= \case
                  Nothing -> throwError $ InvalidNilTy listTy
                  Just myNil -> pure myNil
              _ -> error "non-app node marked as nil fixer"
          else do
            compileTopDown i
      AnArg arg -> pVar <$> resolveArg arg

    -- we can't do Nil w/ just this information so we catch it above
    compileBIFixer :: BuiltinFnData -> CodeGenM (Term Name DefaultUni DefaultFun ())
    compileBIFixer = \case
      List_Cons -> pure $ pBuiltin MkCons
      List_Nil -> error "Unapplied Empty List Constructor"
      Data_I -> pure $ pBuiltin IData
      Data_B -> pure $ pBuiltin BData
      Data_List -> pure $ pBuiltin ListData
      Data_Map -> pure $ pBuiltin MapData
      Data_Constr -> pure $ pBuiltin ConstrData
      Pair_Pair -> resolveStub "Pair"
      Map_Map -> resolveStub "id"
      Integer_Nat_Cata -> resolveStub "cataNat"
      Integer_Neg_Cata -> resolveStub "cataNeg"
      List_Cata -> resolveStub "cataList"
      ByteString_Cata -> resolveStub "cataByteString"
      List_Match -> resolveStub "matchList"
      Pair_Match -> resolveStub "matchPair"
      Map_Match -> pFreshLam2 $ \xs f -> pure $ pForce f # xs
      Data_Match -> resolveStub "matchData"

    withLocalBinds ::
      Map Id ASGNode ->
      CodeGenM (Term Name DefaultUni DefaultFun ()) ->
      CodeGenM (Term Name DefaultUni DefaultFun ())
    withLocalBinds toBind = letMany (M.keys toBind)
      where
        letMany ::
          [Id] ->
          CodeGenM (Term Name DefaultUni DefaultFun ()) ->
          CodeGenM (Term Name DefaultUni DefaultFun ())
        letMany [] act = act
        letMany (i : rest) act = do
          let nm = idToName i
          t <- compileTopDown i
          local (doBind i nm) $
            letMany rest (pLet nm t <$> act)
          where
            doBind :: Id -> Name -> CodeGenContext -> CodeGenContext
            doBind thisId thisName (CodeGenContext r) =
              CodeGenContext $ rModify (M.insert thisId (pVar thisName)) #termScope r

{- -Used to tell us whether we need a `Delay`.

    Builtins that substitute in for Covenant-level ADT constructors
    do not magically delay the result of their own application the way that
    intro forms for user-defined ADTs do. (See the intro form generation machinery in
    Covenant.Transform.Intro for what I mean by that)

    This means that we end up with something like `Force (MkCons 1 [])`, which gives us this *incredibly*
    useful error message during evaluation:

      Eval Exception: An error has occurred:
        Attempted to instantiate a non-polymorphic term.
          Caused by: [1]
          Logs: []

    So we need to know which builtin type fixers "count as constructors". Note that here
    (as is the case basically everywher else), `Nil` is handled specially in that we "catch"
    occurrences of `Nil` at the node which *determines the type of the empty list*, which will never be
    a an application node with a `Nil` constructors.

    TODO: We should actually just handle nil specially in the Covenant repo and provide a special
          helper function for it so that we don't have to do this. This would all be a lot easier and less
          fragile if we didn't have to deduce that something is a `Nil` node. As things stand now I am not sure
          whether "rigid chains" totally break the current implementation, and I am not sure how to fix that
          given the current limitation.
-}
biNeedsDelay :: BuiltinFnData -> Bool
biNeedsDelay = \case
  -- Cons needs it
  List_Cons -> True
  -- We should never encounter a List_Nil during codegen, if we do something failed and the compiler has a
  -- very serious bug. Because we "catch" the App that fixes Nil's type, it ends up "forced" already (we just generate the empty list we
  -- need directly)
  List_Nil -> error "If we've called biNeedsDelay on List_Nil then things are already hopelessly broken. Report this to compiler authors."
  -- All constructors f Data need it
  Data_I -> True
  Data_B -> True
  Data_List -> True
  Data_Map -> True
  Data_Constr -> True
  -- Pair does not because it's stub handles this (in a similar way to a the ctor fn for a user ADT)
  Pair_Pair -> False
  -- Map does need it (I think?) because the `Map` constructor just compiles to `id`
  -- (i.e. it's kind of a "newtype" w/r/t intro-form-ed-ness)
  Map_Map -> True
  -- No match functions or catamorphisms need it
  Integer_Nat_Cata -> False
  Integer_Neg_Cata -> False
  List_Cata -> False
  ByteString_Cata -> False
  List_Match -> False
  Pair_Match -> False
  Map_Match -> False
  Data_Match -> False

litToTerm :: AConstant -> CodeGenM (Term Name DefaultUni DefaultFun ())
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
letBinds (LambdaId _) = getBindableSubTerms 0

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
      alreadyCompiled i >>= \case
        True -> pure def
        False ->
          nodeOrVar i >>= \case
            Left _ -> pure def
            Right node -> f node

    go :: Int -> Id -> CodeGenM (Map Id ASGNode)
    go dbOff nodeId = do
      withNode mempty nodeId $ \thisNode -> do
        safeToBind nodeId dbOff thisNode >>= \case
          True -> pure $ M.singleton nodeId thisNode
          False -> case thisNode of
            AnError -> pure $ M.singleton nodeId thisNode
            ACompNode _ compNodeInfo -> case compNodeInfo of
              Force r -> goRef dbOff r
              Lam r -> crossLamX (LambdaId nodeId) $ goRef (dbOff + 1) r
              _ -> pure M.empty
            AValNode _ valNodeInfo -> case valNodeInfo of
              Lit{} -> pure $ M.singleton nodeId thisNode
              App fnId args _ _ -> do
                fnBinds <- crossApp (AppId fnId) $ go dbOff fnId
                argBinds <- M.unions <$> traverse (goRef dbOff) args
                pure $ fnBinds <> argBinds
              Thunk childId -> go dbOff childId
              _ -> pure M.empty
      where
        goRef :: Int -> Ref -> CodeGenM (Map Id ASGNode)
        goRef dbDist r = case r of
          AnArg{} -> pure M.empty
          AnId childId ->
            alreadyCompiled childId >>= \case
              True -> pure mempty
              False -> go dbDist childId

    alreadyCompiled :: Id -> CodeGenM Bool
    alreadyCompiled i = do
      inCxt <- isJust <$> lookupVar i
      isStub <- isJust <$> (getTyFixers >>= \m -> pure $ M.lookup i m)
      RepPolyHandlers _ _ nilFixers <- asks (\(CodeGenContext r) -> r R..! #repPolyHandlers)
      isNilFixer <- withLocation i $ \astRef -> pure $ astRef `S.member` nilFixers
      pure (inCxt || isStub || isNilFixer)

    safeToBind :: Id -> Int -> ASGNode -> CodeGenM Bool
    safeToBind nodeId dbOff = \case
      AnError -> pure True
      ACompNode _ compNodeInfo -> case compNodeInfo of
        Force r -> safeToBindRef dbOff r
        Lam r ->
          -- FIXME
          -- we really want to check that it's EITHER "locally scoped"
          -- OR that all occurrences of any vars point to a higher level than the current point
          crossLamX (LambdaId nodeId) $ safeToBindRef (dbOff + 1) r
        _ -> pure True
      AValNode _ valNodeInfo -> case valNodeInfo of
        Lit _ -> pure True
        App fnId args _ _ -> do
          okFn <- crossApp (AppId fnId) $ withNode True fnId $ safeToBind fnId dbOff
          okArgs <- and <$> traverse (safeToBindRef dbOff) args
          pure $ okFn && okArgs
        Thunk childId -> withNode True childId $ safeToBind childId dbOff
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
          False -> withNode True i $ safeToBind i dbDist

withLocation :: forall r. Id -> (ASTRef -> CodeGenM r) -> CodeGenM r
withLocation i f = do
  lamScope <- fmap (\(LambdaId x) -> x) <$> getLamScope
  appScope <- fmap (\(AppId x) -> x) <$> getAppScope
  let ref = ASTRef{underLams = lamScope, underApps = appScope, appNodeId = i}
  f ref

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

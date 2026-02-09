{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.CodeGen.Stubs
  ( StubM,
    HandlerType (..),
    HasStubError (..),
    MonadStub (..),
    StubError (..),
    compileStubM,
    defStubs,
    compileStub',
    pInt,
    stubId,
    trySelectHandler,
    resolveStub,
    mkNil,
  )
where

import Algebra.Graph.AdjacencyMap (fromAdjacencySets)
import Algebra.Graph.AdjacencyMap.Algorithm (Cycle, reachable, topSort)
import Control.Monad.Except
  ( ExceptT (ExceptT),
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.RWS.Strict (RWST (RWST))
import Control.Monad.State.Strict
  ( MonadState (get, put),
    MonadTrans (lift),
    StateT (runStateT),
    modify',
  )
import Covenant.ASG (ASGNode (AnError))
import Covenant.ArgDict (pValT)
import Covenant.Data (DatatypeInfo)
import Covenant.ExtendedASG
  ( ExtendedId (EphemeralError),
    MonadASG (getASG, putASG),
    eInsert,
    runWithEmptyASG,
  )
import Covenant.Plutus
  ( caseConstrEnum,
    pBuiltin,
    pCase,
    pCons,
    pDelay,
    pError,
    pForce,
    pFst,
    pIf,
    pLet,
    pNilData,
    pSnd,
    pVar,
    (#),
    (#!),
    (#+),
    (#-),
    (#<),
    (#<=),
    (#==),
  )
import Covenant.Prim
  ( OneArgFunc
      ( BData,
        BLS12_381_G1_compress,
        BLS12_381_G1_uncompress,
        BLS12_381_G2_compress,
        BLS12_381_G2_uncompress,
        DecodeUtf8,
        EncodeUtf8,
        HeadList,
        IData,
        ListData,
        MapData,
        UnBData,
        UnConstrData,
        UnIData,
        UnListData,
        UnMapData
      ),
    SixArgFunc (ChooseData),
    TwoArgFunc (ConstrData, MkPairData),
  )
import Covenant.Test (Id (UnsafeMkId))
import Covenant.Transform.Common
  ( freshNamePrefix,
    pCaseList,
    pFreshLam,
    pFreshLam',
    pFreshLam2,
    pFreshLam2',
    pFreshLam3,
    pFreshLam3',
    pLetM,
    pLetM',
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    TyName,
    ValT (BuiltinFlat, Datatype),
  )
import Covenant.Universe
  ( ListProof (MkListProof),
    UniProof (MkUniProof),
    analyzeListTy,
    unsafeReflect,
  )
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (isJust, isNothing)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as Vector
import PlutusCore.Data (Data (Constr))
import PlutusCore.Default
  ( DefaultUni
      ( DefaultUniApply,
        DefaultUniData,
        DefaultUniProtoList,
        DefaultUniProtoPair
      ),
    Esc,
  )
import PlutusCore.MkPlc (mkConstant, mkConstantOf)
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))
import UntypedPlutusCore (DefaultFun, Term)

{- This module contains PLC fragments which are needed for code generation but cannot be written directly in
   Covenant.

   Due to the Unique requirement for PLC names, we have to produce these functions in a Monad that has access to
   a uniqueness counter. (We cannot start a 0 because we ingest an ASG that starts at 0 and has an arbitrary number of
   Ids, which are the source of the Unique for non-compiler-generated code).

   NOTE: I tried to write these in a sane way but they probably aren't maximally optimized.

   NOTE: Things prefixed with '_' are intended to be declarations in the monad that are part of the
         "runtime".
-}

--   Default "scope" for stubs
--   ***************************
--
--   NOTE: Since the whole purpose of this monad is to automate tracking dependencies amongst
--         PLC stubs, you don't have to worry about putting too many declarations into the context.
--         The "runner" for the monad only generates things that are either accessible in the
--         "top level scope" or dependencies of such things.

defStubs :: forall m. (MonadStub m) => m ()
defStubs = do
  _error
  -- identity fn
  _id
  -- Fix
  _fix
  -- Integer "Library"
  _recNat
  _recNatN
  _recNeg
  -- List "Library"
  _elimList
  _recList
  _pmap
  -- Logic. Here in case I need it (won't get compiled if I don't)
  _not
  _and
  _or
  -- Projections and Embeddings
  do
    -- Integer
    _projInt
    _embedInt
    -- ByteString
    _projByteString
    _embedByteString
    -- Bool
    _projBool
    _embedBool
    -- List (the embedding is universal, but NOTE the args needed)
    _embedList
    -- Map
    _projMap
    _embedMap
    -- String
    _projString
    _embedString
    -- Unit
    _projUnit
    _embedUnit
    -- BLS stuff (possibly superfluous)
    _proj_BLS12_381_G1
    _embed_BLS12_381_G1
    _proj_BLS12_381_G2
    _embed_BLS12_381_G2
  -- Catamorphism drivers
  _cataNat
  _cataNeg
  _cataByteString
  _cataList
  -- Match drivers
  _matchList
  _matchData
  _matchPair
  -- Intro forms
  _mkPair

--   Hard-coded Catamorphisms
--   ***************************

{- r -> (r -> r) -> Integer -> r -}
_cataNat :: forall m. (MonadStub m) => m ()
_cataNat = declare "cataNat" body
  where
    body :: m (Term Name DefaultUni DefaultFun ())
    body = pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
      recNat <- resolveStub "recNat"
      let nIsNegative = n #< pInt 0
      pure $
        pIf
          nIsNegative
          pError
          (recNat # whenZ # whenS # n)

{- r -> (r -> r) -> Integer -> r -}
_cataNeg :: forall m. (MonadStub m) => m ()
_cataNeg = declare "cataNeg" body
  where
    body :: m (Term Name DefaultUni DefaultFun ())
    body = pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
      pNot <- resolveStub "not"
      recNeg <- resolveStub "recNeg"
      let nIsPositive = pNot # (n #<= pInt 0)
      pure $
        pIf
          nIsPositive
          pError
          (recNeg # whenZ # whenS # n)

-- TODO need to test this
_cataByteString :: forall m. (MonadStub m) => m ()
_cataByteString = declare "cataByteString" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body
  where
    go :: m (Term Name DefaultUni DefaultFun ())
    go = pFreshLam3' "self" "whenEmpty" "whenNotEmpty" $ \self whenEmpty whenNonEmpty ->
      pFreshLam3' "originalBS" "len" "ix" $ \originalBS len ix -> do
        pure $
          pIf
            (ix #== len)
            whenEmpty
            ( whenNonEmpty
                # (originalBS #! ix)
                # (self # whenEmpty # whenNonEmpty # originalBS # len # (ix #+ pInt 1))
            )

--
_cataList :: forall m. (MonadStub m) => m ()
_cataList = declare "cataList" $ do
  fix <- resolveStub "fix"
  _ <- resolveStub "elimList"
  body <- pFreshLam' "self" $ \self ->
    pFreshLam3' "xs" "whenNil" "whenCons" $ \xs whenNil whenCons -> do
      whenCons' <- pFreshLam2' "y" "ys" $ \y ys -> pure $ whenCons # (self # ys # whenNil # whenCons) # y
      pure $ pCase xs [whenCons', whenNil]
  -- to force the handler thunk though TODO we should really just de-thunk in the ASG
  pFreshLam3 $ \xs whenNil whenCons -> pure $ (fix # body) # xs # whenNil # pForce whenCons

--   Hard-coded Intro (Constructor) Functions
--   **************************

-- cons is just the MkCons builtin which we can inline

-- nil is really really annoying. we have to know the fully concretified type b/c reasons

-- | This produces the correct empty list term directly and doesn't declare anything.
--  After pre-evaluation this will just reduce to the constant anyway. A 'Nothing' means
--  we cannot construct a builtin list of elements of that type.
mkNil ::
  forall m.
  (MonadStub m) =>
  Map TyName (DatatypeInfo AbstractTy) ->
  ValT AbstractTy ->
  m (Maybe (Term Name DefaultUni DefaultFun ()))
mkNil dtDict valT
  | listOfPairs valT = do
      let selectNilNm = selectNilName pairData
      mkSelectNil pairData
      selectNil <- resolveStub selectNilNm
      pure . Just $ selectNil # pInt 0
  | otherwise = case analyzeListTy dtDict valT of
      Nothing -> pure Nothing
      Just (depth, MkUniProof uni) -> do
        let selectNilNm = selectNilName uni
        mkSelectNil uni
        selectNil <- resolveStub selectNilNm
        pure . Just $ selectNil # pInt depth
  where
    listOfPairs (Datatype "List" args) = case args Vector.! 0 of
      Datatype "Pair" _ -> True
      _ -> False
    listOfPairs _ = False

-- :: a -> b -> (a -> Data) -> (b -> Data) -> Pair a b
_mkPair :: forall m. (MonadStub m) => m ()
_mkPair = declare "Pair" $
  pFreshLam2' "a" "b" $ \a b ->
    pFreshLam2' "embedA" "embedB" $ \embedA embedB ->
      pure . pDelay $
        pBuiltin MkPairData
          # (embedA # a)
          # (embedB # b)

-- Data uses builtin functions (which we can just inline cuz smaller than vars probably) for intro forms.

-- Map's intro form is just an identity function (it's a newtype on the intro side)

--   Hard-coded Eliminator (Match) Functions
--   **************************

-- this is just elimList with the arg order swapped to conform with the ctor order of our List decl
-- List a -> r -> <a -> r> -> r
_matchList :: forall m. (MonadStub m) => m ()
_matchList = declare "matchList" $ pFreshLam3' "xs" "goNil" "goCons" $ \xs goNil goCons -> do
  elim <- resolveStub "elimList"
  pure $ elim # pForce goCons # goNil # xs

_matchData :: forall m. (MonadStub m) => m ()
_matchData = declare "matchData" $
  pFreshLam3' "dat" "goCtor" "goMap" $ \dat goCtor goMap ->
    pFreshLam3' "goList" "goI" "goB" $ \goList goI goB -> do
      goCtor' <- asCtor goCtor dat
      pure $
        pBuiltin ChooseData
          # dat
          # goCtor'
          # (pForce goMap # (pBuiltin UnMapData # dat))
          # (pForce goList # (pBuiltin UnListData # dat))
          # (pForce goI # (pBuiltin UnIData # dat))
          # (pForce goB # (pBuiltin UnBData # dat))
  where
    asCtor ::
      Term Name DefaultUni DefaultFun () ->
      Term Name DefaultUni DefaultFun () ->
      m (Term Name DefaultUni DefaultFun ())
    asCtor goCtor scrut = do
      pLetM' "ctorIx_ctorBody" (pBuiltin UnConstrData # scrut) $ \scrutAsIntDataPair -> do
        let ctorIx = pFst scrutAsIntDataPair
            ctorArgs = pSnd scrutAsIntDataPair
        pure $ pForce goCtor # ctorIx # ctorArgs

_matchPair :: forall m. (MonadStub m) => m ()
_matchPair = declare "matchPair" $
  pFreshLam' "aPair" $ \aPair ->
    pFreshLam3' "f" "projA" "projB" $ \f projA projB -> do
      let a = pFst aPair
          b = pSnd aPair
      pure $ pForce f # (projA # a) # (projB # b)

--   Stub Monad
--   ************************
--
--   We need this for keeping track of dependencies between stubs. We want to make sure we
--   do not duplicate generated code, and also we need to ensure that we `let` bind things in the
--   correct order in the emitted PLC. Keeping track of the order manually has gotten unbearable, and
--   makes changes incredibly error-prone. This should solve that problem.

data StubContext
  = StubContext
  { _bindings :: Map Text (Name, Term Name DefaultUni DefaultFun (), Id), -- not everything actually needs an Id
    _deps :: Map Text (Set Text), -- an adjacency list, basically
    _depsAcc :: Set Text
  }

data StubError
  = NoBinding Text
  | MissingDeps Text (Set Text)
  | DepCycle (Cycle Text)
  | WitnessFail (ValT AbstractTy)
  | ImpossibleNilTy (ValT AbstractTy)
  deriving stock (Show, Eq)

newtype StubM m a = StubM (ExceptT StubError (StateT StubContext m) a)
  deriving
    ( Functor,
      Applicative,
      Monad
      -- I am intentionally not defining a MonadState instance so it doesn't "clash"
      -- with other instances. This will live at the bottom of a transformer stack with
      -- RWS on top. (I suspect a MonadState instance would lead to annoying fundeps inference problems)
    )
    via (ExceptT StubError (StateT StubContext m))

instance (MonadASG m) => MonadASG (StubM m) where
  getASG = StubM . lift . lift $ getASG
  putASG asg = StubM . lift . lift $ putASG asg

-- Stupid hack needed to support multiple levels of errors. Not very elegant but works...
-- Isomorphic to Either but I want something that is semantically clearer
class (Monad m) => HasStubError m where
  throwStubErr :: forall a. StubError -> m a

instance (Monad m, HasStubError m) => HasStubError (ExceptT e m) where
  throwStubErr = lift . throwStubErr

instance (Monad m, HasStubError m, Monoid w) => HasStubError (RWST r w s m) where
  throwStubErr = lift . throwStubErr

instance (Monad m) => HasStubError (StubM m) where
  throwStubErr = StubM . throwError

-- This is effectively a type class for things that contain a StubM somewhere in the stack
-- It's inelegant but it's the only thing I can think of on short notice
-- In theory any valid instance of this has to satisfy a kind of convoluted set of laws
-- that i am not going to bother trying to explicate here
class (MonadASG m, HasStubError m) => MonadStub m where
  -- Must log the name in to the present context
  stubData :: Text -> m (Name, Term Name DefaultUni DefaultFun (), Id)

  -- Do we have a stub associated with the name provided?
  stubExists :: Text -> m Bool

  -- Don't use this directly! Use 'declare'
  _bindStub :: Text -> Term Name DefaultUni DefaultFun () -> m ()

  -- This is "treat this action as a top level declaration", i.e.,
  -- run it with an empty "current scope" (the depsAcc field in StubContext)
  asTopLevel :: forall a. m a -> m a

instance (MonadASG m) => MonadStub (StubM m) where
  stubData :: Text -> StubM m (Name, Term Name DefaultUni DefaultFun (), Id)
  stubData nm = do
    StubContext bs _ _ <- StubM get
    case M.lookup nm bs of
      Just res -> do
        StubM $ modify' $ \(StubContext _bs _ds acc) -> StubContext _bs _ds (S.insert nm acc)
        pure res
      Nothing -> throwStubErr $ NoBinding nm

  stubExists :: (Monad m) => Text -> StubM m Bool
  stubExists nm = do
    StubContext bs _ _ <- StubM get
    pure $ M.member nm bs

  -- Don't use this directly!
  _bindStub :: Text -> Term Name DefaultUni DefaultFun () -> StubM m ()
  _bindStub nm stub = do
    StubContext bs ds acc <- StubM get
    let resolvedDeps = map (\x -> (x, M.lookup x ds)) (S.toList acc)
        depsInScope = all (isJust . snd) resolvedDeps
    if depsInScope
      then do
        plutusName@(Name _ (Unique w)) <- freshNamePrefix nm
        let thisId = UnsafeMkId (fromIntegral w)
            ds' = M.insert nm acc ds
            bs' = M.insert nm (plutusName, stub, thisId) bs
        StubM $ put $ StubContext bs' ds' mempty
      else do
        let notInScope = fst <$> filter (isNothing . snd) resolvedDeps
        throwStubErr $ MissingDeps nm (S.fromList notInScope)

  asTopLevel :: forall a. StubM m a -> StubM m a
  asTopLevel act = do
    StubContext _ _ acc <- StubM get
    StubM $ modify' $ \(StubContext a b _) -> StubContext a b mempty
    res <- act
    StubM $ modify' $ \(StubContext a b _) -> StubContext a b acc
    pure res

instance (Monoid w, MonadStub m) => MonadStub (RWST r w s m) where
  stubData = lift . stubData
  stubExists = lift . stubExists
  asTopLevel (RWST comp) = RWST $ \r s -> do
    asTopLevel (comp r s)
  _bindStub nm term = lift $ _bindStub nm term

instance (MonadStub m) => MonadStub (ExceptT e m) where
  stubData = lift . stubData
  stubExists = lift . stubExists
  asTopLevel (ExceptT comp) = ExceptT $ asTopLevel comp
  _bindStub nm term = lift $ _bindStub nm term

declare ::
  forall m.
  (MonadStub m) =>
  Text ->
  m (Term Name DefaultUni DefaultFun ()) ->
  m ()
declare nm mkStub =
  stubExists nm >>= \case
    True -> pure ()
    -- I dont think this actually needs to be an error?
    False -> asTopLevel $ do
      stub <- mkStub
      _bindStub nm stub

-- | This gets a variable reference to the stub, it does not
--  return the body of the stub. Compilation of the bodies is handled "automagically"
--  by compileStubM
resolveStub :: (MonadStub m) => Text -> m (Term Name DefaultUni DefaultFun ())
resolveStub nmTxt = do
  (pName, _, _) <- stubData nmTxt
  pure $ pVar pName

-- sometimes we just need the Id (e.g. for constructing asg nodes)
stubId :: (MonadStub m) => Text -> m Id
stubId nm = stubData nm >>= \case (_, _, i) -> pure i

runStubM :: forall m a. (MonadASG m) => StubM m () -> StubM m a -> m (Either StubError (StubContext, a))
runStubM (StubM scope) (StubM act') = do
  (\(e, cxt) -> case e of Left e' -> Left e'; Right res -> Right (cxt, res))
    <$> runStateT (runExceptT act) (StubContext mempty mempty mempty)
  where
    act = scope >> act'

-- this let-binds all of the dependencies after performing dependency analysis. ugh
compileStubM ::
  forall m.
  (MonadASG m) =>
  StubM m () ->
  StubM m (Term Name DefaultUni DefaultFun ()) ->
  m (Either StubError (Term Name DefaultUni DefaultFun ()))
compileStubM scope act =
  runStubM scope act >>= \case
    Left e -> pure (Left e)
    Right (StubContext binds depCs topDeps, inner) -> do
      -- TODO: cycle check?
      let asGraph = fromAdjacencySets $ M.toList depCs
          -- every transitive dependency reachable from the final set of dependencies. ugh
          reachableFromTop = S.fromList $ concatMap (reachable asGraph) (S.toList topDeps)
          onlyTrueDeps =
            fromAdjacencySets
              . M.toList
              . M.filterWithKey (\k _ -> k `S.member` reachableFromTop)
              $ depCs
      case topSort onlyTrueDeps of
        Left ohNoACycle -> pure (Left $ DepCycle ohNoACycle)
        Right (reverse -> depsInOrder) -> pure $ foldr (letBindEm binds) (Right inner) depsInOrder
  where
    letBindEm ::
      forall a.
      Map Text (Name, Term Name DefaultUni DefaultFun (), a) ->
      Text ->
      Either StubError (Term Name DefaultUni DefaultFun ()) ->
      Either StubError (Term Name DefaultUni DefaultFun ())
    letBindEm dict txtNm acc = case M.lookup txtNm dict of
      Nothing -> Left $ NoBinding txtNm
      Just (pNm, body, _) -> pLet pNm body <$> acc

-- for testing
compileStub' ::
  (forall m. (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())) ->
  Either StubError (Term Name DefaultUni DefaultFun ())
compileStub' act = runWithEmptyASG compiled
  where
    compiled :: forall m. (MonadASG m) => m (Either StubError (Term Name DefaultUni DefaultFun ()))
    compiled = compileStubM defStubs act

data HandlerType = Proj | Embed
  deriving stock (Show, Eq, Ord)

-- Utility function for retrieving embeddings / projections. Will declare list projections if they do not exist
trySelectHandler ::
  forall m.
  (MonadStub m) =>
  Map TyName (DatatypeInfo AbstractTy) ->
  HandlerType ->
  ValT AbstractTy ->
  m (Maybe (Term Name DefaultUni DefaultFun ()))
trySelectHandler dtDict htype valT = case valT of
  BuiltinFlat bi -> case htype of
    Proj -> case bi of
      IntegerT -> Just <$> resolveStub "projInt"
      ByteStringT -> Just <$> resolveStub "projByteString"
      BoolT -> Just <$> resolveStub "projBool"
      StringT -> Just <$> resolveStub "projString"
      UnitT -> Just <$> resolveStub "projUnit"
      BLS12_381_G1_ElementT -> Just <$> resolveStub "proj_BLS12_381_G1"
      BLS12_381_G2_ElementT -> Just <$> resolveStub "proj_BLS12_381_G2"
      _ -> pure Nothing
    Embed -> case bi of
      IntegerT -> Just <$> resolveStub "embedInt"
      ByteStringT -> Just <$> resolveStub "embedByteString"
      BoolT -> Just <$> resolveStub "embedBool"
      StringT -> Just <$> resolveStub "embedString"
      UnitT -> Just <$> resolveStub "embedUnit"
      BLS12_381_G1_ElementT -> Just <$> resolveStub "embed_BLS12_381_G1"
      BLS12_381_G2_ElementT -> Just <$> resolveStub "embed_BLS12_381_G2"
      _ -> pure Nothing
  Datatype "Pair" _args -> case htype of
    Proj -> Just <$> resolveStub "projPair"
    Embed -> Just <$> resolveStub "embedPair"
  Datatype "Map" _args -> case htype of
    Proj -> Just <$> resolveStub "projMap"
    Embed -> Just <$> resolveStub "embedMap"
  listTy@(Datatype "List" _) -> case analyzeListTy dtDict listTy of
    Nothing -> pure Nothing
    Just (depth, MkUniProof uni) -> case htype of
      Embed -> do
        let innerTy = unsafeReflect uni
        trySelectHandler dtDict htype innerTy >>= \case
          Nothing -> pure Nothing -- probably should be an error
          Just embedInner -> do
            embedList <- resolveStub "embedList"
            pure . Just $ embedList # pInt depth # embedInner
      Proj -> do
        let innerTy = unsafeReflect uni
        trySelectHandler dtDict htype innerTy >>= \case
          Nothing -> pure Nothing -- again, probably should be an error! TODO this
          Just projInner -> do
            projListWithType dtDict listTy projInner
            Just <$> resolveStub (projListKey uni)
  _ -> pure Nothing

{-
   ***************************
   List Projection & Embedding
   ***************************
-}

{- This is morally similar to something we can only express properly with dependent types, i.e.,
   you can think of this as a "type-erased" version of (ROUGHLY):

   data KnownDepthList n a where
     DepthZ :: List a  -> KnownDepthList Z a
     DepthS :: [KnownDepthList n a] -> KnownDepthList (S n) a

   embedList :: forall (n :: Natural). n -> (a -> Data) -> KnownDepthList n a -> Data

   and the implementation is like:
   embedList depth emb lst  =
      let go n | n <= 0 = \x -> emb  x
               | otherwise = \xs -> map (go (n - 1)) xs
      in ListData $ map (go depth) lst

   (We can't type this function in haskell or PLC or covenant b/c the type of 'go'
    depends on the value of `n`. We could type it in, like, Agda or something)
-}

_embedList ::
  forall (m :: Type -> Type).
  (MonadStub m) =>
  m ()
_embedList = declare "embedList" fun
  where
    listify x = pBuiltin ListData # x
    -- morally: Integer -> ((a -> b) -> List a -> List b) -> ... (can't express this without dep types see above)
    mkGo :: m (Term Name DefaultUni DefaultFun ())
    mkGo =
      pFreshLam3' "go_Depth" "go_embEl" "go_mapF" $ \depth embEl mapF -> do
        recNat <- resolveStub "recNat"
        goS <- pFreshLam2' "f" "xs" $ \f xs -> pure $ listify (mapF # f # xs)
        pure $ recNat # embEl # goS # depth
    fun :: m (Term Name DefaultUni DefaultFun ())
    fun = pFreshLam3' "fun_Depth" "fun_embEl" "fun_xs" $ \depth innerF xs -> do
      map' <- resolveStub "map"
      pLetM (map' # pNilData) $ \mapF -> do
        go <- mkGo
        let goF = go # depth # innerF # mapF
            resList = mapF # goF # xs
        pure $ pBuiltin ListData # resList

{- The dual of embedList.

Morally, this is like:

forall (n :: Natural). n -> (Data -> a) -> List Data -> KnownDepthList n a

(which obviously can't be a total function, but for our purposes that doesn't matter)

implementation should be like:

projList nDepth projEl lst =
  let go n | n <= 0 = \x -> proj x
           | otherwise = \xs -> map (go ( n - 1 ) (unListData xs)
  in map (go nDepth) lst

Don't use this directly. Use projListWithType
-}

-- (Data -> a) -> Integer -> Data -> [a]
projList ::
  forall (m :: Type -> Type) (a :: Type).
  (MonadStub m) =>
  DefaultUni (Esc a) -> m (Term Name DefaultUni DefaultFun ())
projList wit = body
  where
    body :: m (Term Name DefaultUni DefaultFun ())
    body = pFreshLam2' "projEl" "depth" $ \projEl depth -> do
      mkNil' <- resolveStub (selectNilName wit)
      go <- mkGo mkNil'
      pure $ go # depth # projEl
    unList :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
    unList t = pBuiltin UnListData # t
    -- Integer -> (Data -> a) -> Data -> [a]
    mkGo :: Term Name DefaultUni DefaultFun () -> m (Term Name DefaultUni DefaultFun ())
    mkGo nil = pFreshLam2' "depth" "projEl" $ \depth projEl -> do
      recNat <- resolveStub "recNatN"
      mapF <- resolveStub "map"
      goS <- pFreshLam3' "n" "f" "ys" $ \n f ys -> do
        pure $ (mapF # (nil # n)) # f # unList ys
      goZ <- do
        let map0 = mapF # (nil # mkConstant @Integer () 0)
        pFreshLam' "goZ_xs" $ \xs -> pure $ map0 # projEl # unList xs
      pure (recNat # goZ # goS # depth)

{- The version we'll actually use.  -}
projListWithType ::
  forall (m :: Type -> Type).
  (MonadStub m) =>
  Map TyName (DatatypeInfo AbstractTy) ->
  ValT AbstractTy ->
  Term Name DefaultUni DefaultFun () ->
  m ()
projListWithType dtDict valT projEl = case analyzeListTy dtDict valT of
  Nothing -> error $ "Cannot create list projection for " <> pValT valT
  Just (depth, MkUniProof wit) -> do
    let projFName = projListKey wit
    mkSelectNil wit
    declare projFName $ do
      projF <- projList wit
      pure $ projF # projEl # mkConstant () depth

projListKey :: forall (a :: Type). DefaultUni (Esc a) -> Text
projListKey w = "projList[" <> T.pack (show w) <> "]"

--   Map Projection / Embedding
--   ***************************
--
--   NOTE: Ugh pair can't stay data encoded at all times

pairData :: DefaultUni (Esc (Data, Data))
pairData = DefaultUniProtoPair `DefaultUniApply` DefaultUniData `DefaultUniApply` DefaultUniData

_projMap :: forall m. (MonadStub m) => m ()
_projMap = declare "projMap" $ pFreshLam' "mapCtorOfData" $ \mapCtorOfData -> do
  pure (pBuiltin UnMapData # mapCtorOfData)

_embedMap :: forall m. (MonadStub m) => m ()
_embedMap = declare "embedMap" $ pFreshLam' "listOfData" $ \listOfPairData ->
  pure $ pBuiltin MapData # listOfPairData

--   Pair Projection / Embedding
--   ***************************
--
--   NOTE: The "offchain" representation of Pair is (Data,Data) ALWAYS. Its AsData form is `Ctor 0 [a,b]``

_projPair :: forall m. (MonadStub m) => m ()
_projPair = declare "projPair" $ pFreshLam' "dataPair" $ \dataPair -> do
  let innerDataList = pSnd (pBuiltin UnConstrData # dataPair)
  pCaseList innerDataList $ \a rest -> do
    let b = pBuiltin HeadList # rest
    pure $ pBuiltin MkPairData # a # b

_embedPair :: forall m. (MonadStub m) => m ()
_embedPair = declare "embedPair" $ pFreshLam' "aPair" $ \dataPair -> do
  pure $ pBuiltin ConstrData # pInt 0 # pCons (pFst dataPair) (pCons (pSnd dataPair) pNilData)

--   Bool Projection / Embedding
--   ***************************

_projBool :: (MonadStub m) => m ()
_projBool = declare "projBool" $ pFreshLam' "b" $ \b ->
  pure $ caseConstrEnum b [mkConstant () True, mkConstant () False]

_embedBool :: (MonadStub m) => m ()
_embedBool = declare "embedBool" $ pFreshLam' "b" $ \b ->
  pure $ pIf b troo fawlse
  where
    troo = mkConstant () $ Constr 0 []
    fawlse = mkConstant () $ Constr 1 []

--   Int Projection / Embedding
--   ***************************

_projInt :: (MonadStub m) => m ()
_projInt = declare "projInt" $ pure (pBuiltin UnIData)

_embedInt :: (MonadStub m) => m ()
_embedInt = declare "embedInt" $ pure (pBuiltin IData)

--   Bytestring Projection / Embedding
--   *********************************

_projByteString :: (MonadStub m) => m ()
_projByteString = declare "projByteString" $ pure (pBuiltin UnBData)

_embedByteString :: (MonadStub m) => m ()
_embedByteString = declare "embedByteString" $ pure (pBuiltin BData)

--   String Projection / Embedding
--   ****************************

_projString :: (MonadStub m) => m ()
_projString = declare "projString" $ pFreshLam' "utf8_data" $ \utf8_data ->
  pure $ pBuiltin DecodeUtf8 # (pBuiltin UnBData # utf8_data)

_embedString :: (MonadStub m) => m ()
_embedString = declare "embedString" $ pFreshLam' "aString" $ \aString ->
  pure $ pBuiltin BData # (pBuiltin EncodeUtf8 # aString)

--   Unit Projection / Embedding
--   ****************************

_projUnit :: (MonadStub m) => m ()
_projUnit = declare "projUnit" $ pFreshLam' "unitData" $ \_ ->
  pure $ mkConstant () ()

_embedUnit :: (MonadStub m) => m ()
_embedUnit = declare "embedUnit" $ pFreshLam' "aUnit" $ \_ ->
  pure $ mkConstant () (Constr 0 [])

--   BLS Primitive Projection / Embedding
--   ****************************
--
--   NOTE: These are probably superfluous since they don't exist in ledger types... but
--         I guess in theory someone might want to put them on the chain? Maybe?

_proj_BLS12_381_G1 :: (MonadStub m) => m ()
_proj_BLS12_381_G1 = declare "proj_BLS12_381_G1" $ pFreshLam' "blsG1Data" $ \blsG1Data ->
  pure $ pBuiltin BLS12_381_G1_uncompress # (pBuiltin UnBData # blsG1Data)

_embed_BLS12_381_G1 :: (MonadStub m) => m ()
_embed_BLS12_381_G1 = declare "embed_BLS12_381_G1" $ pFreshLam' "blsG1" $ \blsG1 ->
  pure $ pBuiltin BData # (pBuiltin BLS12_381_G1_compress # blsG1)

_proj_BLS12_381_G2 :: (MonadStub m) => m ()
_proj_BLS12_381_G2 = declare "proj_BLS12_381_G2" $ pFreshLam' "blsG2Data" $ \blsG2Data ->
  pure $ pBuiltin BLS12_381_G2_uncompress # (pBuiltin UnBData # blsG2Data)

_embed_BLS12_381_G2 :: (MonadStub m) => m ()
_embed_BLS12_381_G2 = declare "embed_BLS12_381_G2" $ pFreshLam' "blsG2" $ \blsG2 ->
  pure $ pBuiltin BData # (pBuiltin BLS12_381_G2_compress # blsG2)

-- Ml_Result - Has no data encoding NOTE: Need to error here

--   Misc things we need in scope
--   *********************************

_id :: (MonadStub m) => m ()
_id = declare "id" $ pFreshLam $ \x -> pure x

-- we don't use an an error node at the plc in case we accidentally forget to remove this.
-- the error node at the covenant level is necessary
_error :: (MonadStub m) => m ()
_error = do
  declare "error" $ pure (mkConstant () ())
  (_, _, i) <- stubData "error"
  eInsert (EphemeralError i) AnError

-- We aren't putting the unique error here because it needs to be removed anyway and nothing
-- at the PLC level depends upon it (it's a trick for mocking functions in the ASG)

{-  ***********
    Combinators
    ***********

   NOTE: This should be fairly CPU-efficient but is fairly script-size-inefficient. Eventually we should probably
         implement a script-size-efficient version (pretty sure we can?) and have a compiler option to choose between
         the two.

         We can't use Y because UPLC is strict and it won't ever terminate so we use Z.
-}

-- "PLC level" version
_fix :: (MonadStub m) => m ()
_fix = declare "fix" $ do
  pFreshLam' "f" $ \f -> do
    g <- pFreshLam' "x" $ \x -> do
      (f #) <$> pFreshLam' "v" (\v -> pure $ x # x # v)
    pure $ g # g

{-
    ***************
    Basic Integer API
    ***************
-}

{- r -> (r -> r) ->  Integer -> r -}
_recNat :: (MonadStub m) => m ()
_recNat = declare "recNat" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
      let isZero = n #<= pInt 0
      pure $ pIf isZero whenZ (whenS # (self # whenZ # whenS # (n #- pInt 1)))

--  r -> (r -> Integer -> r) ->  Integer -> r
_recNatN :: (MonadStub m) => m ()
_recNatN = declare "recNatN" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
      let isZero = n #== pInt 0
          whenS' = whenS # n
      pure $ pIf isZero whenZ (whenS' # (self # whenZ # whenS # (n #- pInt 1)))

_recNeg :: (MonadStub m) => m ()
_recNeg = declare "recNeg" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
      let isZero = n #== pInt 0
      pure $
        pIf
          isZero
          whenZ
          (whenS # (self # whenZ # whenS # (n #+ pInt 1)))

{-
    ***************
    Basic list API
    ***************

    NOTE: More-or-less borrowed from Plutarch (modulo the empty list thing, see note to `map`)
-}

{-  elimList :: forall a. (a -> List a -> r) -> r -> List a -> r -}
_elimList :: (MonadStub m) => m ()
_elimList = declare "elimList" $
  pFreshLam3' "goCons" "goNil" "ws" $ \goCons goNil xs ->
    pure $ pCase xs [goCons, goNil]

{-
   recList ::
     ((List a -> r) -> a -> List a -> r)
     (List a -> r) -> r
     List a ->
     r
-}
_recList ::
  (MonadStub m) =>
  m ()
_recList = declare "recList" $ do
  elim <- resolveStub "elimList"
  fix <- resolveStub "fix"
  pFreshLam2' "goCons_recList" "goNil_recList" $ \goCons goNil -> do
    f <- pFreshLam' "recList_self" $ \self -> pure $ elim # (goCons # self) # (goNil # self)
    pure $ fix # f

{-
   The Term Name DefaultUni DefaultFun () argument is a *correctly typed UPLC empty list constant*.

   This is almost incomprehensibly stupid, but we need to pass that around as an arguments.
   PLC is immutable (obviously) so `map` constructs a new list and it is impossible to do that
   if we do not know the type of the empty list we need. There is no way to pass that *type* in
   Untyped PLC so we pass the empty list itself.
-}
_pmap ::
  (MonadStub m) =>
  -- type-specific nil
  m ()
_pmap = declare "map" $ pFreshLam2' "map_nil" "map_f" $ \nil f -> do
  goCons <- pFreshLam3' "self" "v" "vs" $ \self x xs -> pure $ pCons (f # x) (self # xs)
  goNil <- pFreshLam' "_" $ \_ -> pure nil
  recList <- resolveStub "recList"
  pure $ recList # goCons # goNil

{-
  This is a bit weird. This constructs an empty list value of the correct "depth"
  (where 0 means [a], 1 means [[a]], etc). We need something like this for list projections.

  This only goes "up to" 10 (but we can always add more cases if we need them).

  Empty lists of different types are not compatible in UPLC, and there is no UPLC way to pass
  a type as an argument. Moreover, writing a list projection requires us to get ahold of
  the empty list of the correct type several times, so we can't just pass in a single correctly
  typed empty list (we *can* do that for embeddings because the result is always `Data`)

  Morally, given the above sketched dependent types, this has a PLC level "type" like:

  selectNil :: forall (n :: Natural).

  NOTE: This checks to see if we've already generated a declaration of the correct type.
-}
mkSelectNil ::
  forall (m :: Type -> Type) (a :: Type).
  (MonadStub m) =>
  DefaultUni (Esc a) ->
  m ()
mkSelectNil uni = declare declNm $ pFreshLam' "selectNil_depth" $ \depth ->
  pure $
    pCase
      depth
      [ mkList 0,
        mkList 1,
        mkList 2,
        mkList 3,
        mkList 4,
        mkList 5,
        mkList 6,
        mkList 7,
        mkList 8,
        mkList 9,
        mkList 10
      ]
  where
    declNm = selectNilName uni

    mkList :: Int -> Term Name DefaultUni DefaultFun ()
    mkList n = case mkWitness n of
      MkListProof wit -> mkConstantOf () wit []

    mkWitness :: Int -> ListProof
    mkWitness n
      | n <= 0 = MkListProof $ DefaultUniApply DefaultUniProtoList uni
      | otherwise = case mkWitness (n - 1) of
          MkListProof t -> MkListProof $ DefaultUniApply DefaultUniProtoList t

selectNilName :: forall (a :: Type). DefaultUni (Esc a) -> Text
selectNilName w = "selectNil[" <> T.pack (show w) <> "]"

{-
    *************
    Logic
    *************
  NOTE: Uses case on bools for efficiency.
-}

_not :: forall m. (MonadStub m) => m ()
_not = declare "not" $ pFreshLam $ \b ->
  pure $ pIf b (mkConstant () False) (mkConstant () True)

_and :: forall m. (MonadStub m) => m ()
_and = declare "and" $ pFreshLam2 $ \b1 b2 ->
  pure $ pIf b1 b2 (mkConstant () False)

_or :: forall m. (MonadStub m) => m ()
_or = declare "or" $ pFreshLam2 $ \b1 b2 ->
  pure $ pIf b1 (mkConstant () True) b2

{-
    *************
    Small helpers
    *************
-}

pInt :: Integer -> Term Name DefaultUni DefaultFun ()
pInt = mkConstant ()

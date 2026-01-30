{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.CodeGen.Stubs where

import Data.Map (Map)
import Data.Map qualified as M

import Covenant.ASG (
    ASGNode (ACompNode, AnError),
    Ref (AnArg),
 )
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    TyName,
    ValT (BuiltinFlat, Datatype),
    tyvar,
 )

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (ix0)
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (LamInternal), Id (UnsafeMkId), list, unsafeMkDatatypeInfos)
import Data.Kind (Type)

import Covenant.ExtendedASG
import Covenant.Transform.Common
import Data.Row.Records (Rec, (.+), (.==))

import Algebra.Graph.AdjacencyMap
import Algebra.Graph.AdjacencyMap.Algorithm
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State.Strict (MonadState (get, put), MonadTrans (lift), StateT (runStateT), modify')
import Covenant.ArgDict
import Covenant.Data (DatatypeInfo)
import Covenant.MockPlutus
import Covenant.Prim (OneArgFunc (IData, ListData, UnIData, UnListData, BData, UnBData))
import Covenant.Universe
import Data.Foldable (foldrM, traverse_)
import Data.Maybe (isJust, isNothing)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Debug.Trace (traceM)
import PlutusCore.Data (Data (Constr, I, List))
import PlutusCore.Default (DefaultUni (..), Esc)
import PlutusCore.MkPlc (mkConstant, mkConstantOf)
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))


{- This module contains PLC fragments which are needed for code generation but cannot be written directly in
   Covenant.

   Due to the Unique requirement for PLC names, we have to produce these functions in a Monad that has access to
   a uniqueness counter. (We cannot start a 0 because we ingest an ASG that starts at 0 and has an arbitrary number of
   Ids, which are the source of the Unique for non-compiler-generated code).

   NOTE: I tried to write these in a sane way but they probably aren't maximally optimized.

   NOTE: Things prefixed with '_' are intended to be declarations in the monad that are part of the
         "runtime".
-}

{- ***************************
   Default "scope" for stubs
   ***************************

   NOTE: Since the whole purpose of this monad is to automate tracking dependencies amongst
         PLC stubs, you don't have to worry about putting too many declarations into the context.
         The "runner" for the monad only generates things that are either accessible in the
         "top level scope" or dependencies of such things.
-}


defStubs :: forall m. (MonadASG m) => StubM m ()
defStubs = do
    _fix
    _recNat
    _recNatN
    _recNeg
    _elimList
    _recList
    _pmap
    _projBool
    _embedBool
    _projInt
    _embedInt
    _projByteString
    _embedByteString
    _id
    embedList
    _not
    _and
    _or
    _cataNat
    _cataNeg
    _cataByteString 

{- ***************************
   Hard-coded Catamorphisms
   ***************************
-}

{- r -> (r -> r) -> Integer -> r -}
_cataNat :: forall m. MonadASG m => StubM m ()
_cataNat = declare "cataNat" body
  where
    body :: StubM m PlutusTerm
    body = pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        recNat <- resolveStub "recNat"
        let nIsNegative = n #< i 0
        pure $ pIf nIsNegative
                   pError
                   (recNat # whenZ # whenS # n)

{- r -> (r -> r) -> Integer -> r -}
_cataNeg :: forall m. MonadASG m => StubM m ()
_cataNeg = declare "cataNeg" body
  where
    body :: StubM m PlutusTerm
    body = pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        pNot <- resolveStub "not"
        recNeg <- resolveStub "recNeg"
        let nIsPositive = pNot # (n #<= i 0)
        pure $ pIf nIsPositive
                   pError
                   (recNeg # whenZ # whenS # n)

-- TODO need to test this
_cataByteString :: forall m. MonadASG m => StubM m ()
_cataByteString = declare "cataByteString" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body 
  where
    go :: StubM m PlutusTerm
    go = pFreshLam3' "self" "whenEmpty" "whenNotEmpty" $ \self whenEmpty whenNonEmpty ->
      pFreshLam3' "originalBS" "len" "ix" $ \originalBS len ix -> do
        pure $ pIf (ix #== len)
                   whenEmpty
                   (whenNonEmpty
                     # (originalBS #! ix)
                     # (self # whenEmpty # whenNonEmpty # originalBS # len # (ix #- i 1)))

--
_cataList :: forall m. MonadASG m => StubM m ()
_cataList = declare "cataList" $ do
  fix <- resolveStub "fix"
  body <- go
  pure $ fix # body
 where
   go :: StubM m PlutusTerm
   go = _

{- *************************
   Stub Monad
   ************************

   We need this for keeping track of dependencies between stubs. We want to make sure we
   do not duplicate generated code, and also we need to ensure that we `let` bind things in the
   correct order in the emitted PLC. Keeping track of the order manually has gotten unbearable, and
   makes changes incredibly error-prone. This should solve that problem.
-}

data StubContext
    = StubContext
    { bindings :: Map Text (Name, PlutusTerm, Id) -- not everything actually needs an Id 
    , deps :: Map Text (Set Text) -- an adjacency list, basically
    , depsAcc :: Set Text
    }

data StubError
    = NoBinding Text
    | MissingDeps Text (Set Text)
    | DepCycle (Cycle Text)
    | WitnessFail (ValT AbstractTy)
    deriving stock (Show)

newtype StubM m a = StubM (ExceptT StubError (StateT StubContext m) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState StubContext
        , MonadError StubError
        )
        via (ExceptT StubError (StateT StubContext m))

instance (MonadASG m) => MonadASG (StubM m) where
    getASG = StubM . lift . lift $ getASG

    putASG asg = StubM . lift . lift $ putASG asg

runStubM :: forall m a. (MonadASG m) => StubM m a -> m (Either StubError (StubContext, a))
runStubM (StubM act) =
    (\(e, cxt) -> case e of Left e -> Left e; Right res -> Right (cxt, res))
        <$> runStateT (runExceptT act) (StubContext mempty mempty mempty)

-- this let-binds all of the dependencies after performing dependency analysis. ugh
compileStubM :: forall m. (MonadASG m) => StubM m PlutusTerm -> m (Either StubError PlutusTerm)
compileStubM act =
    runStubM act >>= \case
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
            traceM $ "\ndeps: " <> show depCs
            traceM $ "\ntopDeps: " <> show topDeps
            traceM $ "\nreachableFromTop: " <> show reachableFromTop
            traceM $ "\nonlyTrueDeps: " <> show (adjacencyList onlyTrueDeps)
            case topSort onlyTrueDeps of
                Left ohNoACycle -> pure (Left $ DepCycle ohNoACycle)
                Right (reverse -> depsInOrder) -> pure $ foldr (letBindEm binds) (Right inner) depsInOrder
  where
    letBindEm :: forall a.
        Map Text (Name, PlutusTerm, a) ->
        Text ->
        Either StubError PlutusTerm ->
        Either StubError PlutusTerm
    letBindEm dict txtNm acc = case M.lookup txtNm dict of
        Nothing -> Left $ NoBinding txtNm
        Just (pNm, body,_) -> pLet pNm body <$> acc

-- for testing
compileStub' :: (forall m. (MonadASG m) => StubM m PlutusTerm) -> Either StubError PlutusTerm
compileStub' act = runWithEmptyASG compiled
  where
    compiled :: forall m. (MonadASG m) => m (Either StubError PlutusTerm)
    compiled = compileStubM act

resolveStub :: (Monad m) => Text -> StubM m PlutusTerm
resolveStub txt = do
    StubContext bs _ _ <- get
    case M.lookup txt bs of
        Just (res, _,_) -> do
            modify' $ \(StubContext _bs _ds acc) -> StubContext _bs _ds (S.insert txt acc)
            pure (pVar res)
        Nothing -> throwError $ NoBinding txt

resolveStub' :: Monad m => Text -> StubM m (Name,PlutusTerm,Id)
resolveStub' nm = do
    StubContext bs _ _ <- get
    case M.lookup nm bs of
        Just res -> do
            modify' $ \(StubContext _bs _ds acc) -> StubContext _bs _ds (S.insert nm acc)
            pure res 
        Nothing -> throwError $ NoBinding nm

stubExists :: (Monad m) => Text -> StubM m Bool
stubExists nm = do
    StubContext bs ds _ <- get
    pure $ M.member nm bs

-- clears the dependency accumulator before and after it runs, you can't nest calls to declare,
-- this is only a tool for sorting out top-level dependencies amongst stubs
declare :: forall m. (MonadASG m) => Text -> StubM m PlutusTerm -> StubM m ()
declare nm mkStub =
    stubExists nm >>= \case
        True -> pure ()
            -- I dont think this actually needs to be an error?
            -- initAcc
        False -> withNoDeps $ do
          stub <- mkStub
          bindStub stub
  where
    withNoDeps :: StubM m a -> StubM m a
    withNoDeps act = do
      StubContext _ _ acc <- get
      modify' $ \(StubContext a b _) -> StubContext a b mempty
      res <- act
      modify' $ \(StubContext a b _) -> StubContext a b acc
      pure res

    bindStub :: PlutusTerm -> StubM m ()
    bindStub stub = do
        StubContext bs ds acc <- get
        let resolvedDeps = map (\x -> (x, M.lookup x ds)) (S.toList acc)
            depsInScope = all (isJust . snd) resolvedDeps
        if depsInScope
            then do
                plutusName@(Name _ (Unique w)) <- freshNamePrefix nm
                let thisId = UnsafeMkId (fromIntegral w)
                    ds' = M.insert nm acc ds
                    bs' = M.insert nm (plutusName, stub, thisId) bs
                put $ StubContext bs' ds' mempty
            else do
                let notInScope = fst <$> filter (isNothing . snd) resolvedDeps
                throwError $ MissingDeps nm (S.fromList notInScope)

data HandlerType = Projection | Embedding
  deriving stock (Show, Eq, Ord)

-- Utility function for retrieving embeddings / projections. Will declare list projections if they do not exist
selectHandler :: forall m. MonadASG m
              => HandlerType
              -> ValT AbstractTy
              -> StubM m (Name,PlutusTerm,Id)
selectHandler htype valT = case valT of
  BuiltinFlat IntegerT -> resolveStub' "projInt"

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

embedList ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    StubM m ()
embedList = declare "embedList" fun
  where
    listify x = pBuiltin ListData # x
    -- morally: Integer -> ((a -> b) -> List a -> List b) -> ... (can't express this without dep types see above)
    mkGo :: StubM m PlutusTerm
    mkGo =
        pFreshLam3' "go_Depth" "go_embEl" "go_mapF" $ \depth embEl mapF -> do
            recNat <- resolveStub "recNat"
            goS <- pFreshLam2' "f" "xs" $ \f xs -> pure $ listify (mapF # f # xs)
            pure $ recNat # embEl # goS # depth

    fun :: StubM m PlutusTerm
    fun = pFreshLam3' "fun_Depth" "fun_embEl" "fun_xs" $ \depth innerF xs -> do
        map <- resolveStub "map"
        pLetM (map # pNilData) $ \mapF -> do
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
    (MonadASG m) =>
    DefaultUni (Esc a) -> StubM m PlutusTerm
projList wit = body
  where
    body = pFreshLam2' "projEl" "depth"  $ \projEl  depth  -> do
        mkNil <- resolveStub (selectNilName wit)
        go <- mkGo mkNil
        pure $ go # depth # projEl 

    declNm = projListKey wit

    unList :: PlutusTerm -> PlutusTerm
    unList t = pBuiltin UnListData # t

    -- Integer -> (Data -> a) -> Data -> [a]
    mkGo :: PlutusTerm -> StubM m PlutusTerm
    mkGo nil = pFreshLam2' "depth" "projEl"  $ \depth projEl -> do
        recNat <- resolveStub "recNatN"
        mapF <- resolveStub "map"
        goS <- pFreshLam3' "n" "f" "ys" $ \n f ys -> do
            pure $  (mapF # (nil # n)) # f # unList ys
        goZ <- do
            let map0 = mapF # (nil # mkConstant @Integer () 0)
            pFreshLam' "goZ_xs" $ \xs -> pure $ map0 # projEl # unList xs
        pure $ (recNat # goZ # goS # depth)

{- The version we'll actually use.  -}
projListWithType ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    Map TyName (DatatypeInfo AbstractTy) ->
    ValT AbstractTy ->
    PlutusTerm ->
    StubM m ()
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

-- The idea is that we'll do one pass where we generate them all and then in a later pass we use this to look
-- up things we expect to be generated.
getListProj' :: forall m (a :: Type). (MonadASG m) => DefaultUni (Esc a) -> StubM m PlutusTerm
getListProj' w = resolveStub (projListKey w)

-- | TAKES THE BASE/INNERMOST TYPE, NOT THE FULL LIST TYPE
getListProj :: forall m. (MonadASG m) => Map TyName (DatatypeInfo AbstractTy) -> ValT AbstractTy -> StubM m PlutusTerm
getListProj dict valT = case decideUniType dict valT of
    Nothing -> throwError $ WitnessFail valT
    Just (MkUniProof w) -> getListProj' w

{- ***************************
   Bool Projection / Embedding
   ***************************
-}

_projBool :: (MonadASG m) => StubM m ()
_projBool = declare "projBool" $ pFreshLam' "b" $ \b ->
    pure $ caseConstrEnum b [mkConstant () True, mkConstant () False]

_embedBool :: (MonadASG m) => StubM m ()
_embedBool = declare "embedBool" $ pFreshLam' "b" $ \b ->
    pure $ pIf b troo fawlse
  where
    troo = mkConstant () $ Constr 0 []
    fawlse = mkConstant () $ Constr 1 []

{- ***************************
   Int Projection / Embedding
   ***************************
-}

_projInt :: (MonadASG m) => StubM m ()
_projInt = declare "projInt" $ pure (pBuiltin UnIData)

_embedInt :: MonadASG m => StubM m ()
_embedInt = declare "embedInt" $ pure (pBuiltin IData)


{- *********************************
   Bytestring Projection / Embedding
   *********************************
-}

_projByteString :: MonadASG m => StubM m ()
_projByteString = declare "projByteString" $ pure (pBuiltin UnBData)

_embedByteString :: MonadASG m => StubM m ()
_embedByteString = declare "embedByteString" $ pure (pBuiltin BData)

{- *********************************
   Misc things we need in scope
   *********************************
-}

_id :: MonadASG m => StubM m ()
_id = declare "id" $ pFreshLam $ \x -> pure x

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
_fix :: (MonadASG m) => StubM m ()
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
_recNat :: (MonadASG m) => StubM m ()
_recNat = declare "recNat" $ do
    fix <- resolveStub "fix"
    body <- go
    pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        let isZero = n #<= i 0
        pure $ pIf isZero whenZ (whenS # (self # whenZ # whenS # (n #- i 1)))

--  r -> (r -> Integer -> r) ->  Integer -> r
_recNatN :: (MonadASG m) => StubM m ()
_recNatN = declare "recNatN" $ do
    fix <- resolveStub "fix"
    body <- go
    pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        let isZero = n #== i 0
            whenS' = whenS # n
        pure $ pIf isZero whenZ (whenS' # (self # whenZ # whenS # (n #- i 1)))

_recNeg :: (MonadASG m) => StubM m ()
_recNeg = declare "recNeg" $ do
    fix <- resolveStub "fix"
    body <- go
    pure $ fix # body
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        let isZero = n #== i 0
        pure $
            pIf
                isZero
                whenZ
                (whenS # (self # whenZ # whenS # (n #+ i 1)))

{-
    ***************
    Basic list API
    ***************

    NOTE: More-or-less borrowed from Plutarch (modulo the empty list thing, see note to `map`)
-}

{-  elimList :: forall a. (a -> List a -> r) -> r -> List a -> r -}
_elimList :: (MonadASG m) => StubM m ()
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
    (MonadASG m) =>
    StubM m ()
_recList = declare "recList" $ do
    elim <- resolveStub "elimList"
    fix <- resolveStub "fix"
    pFreshLam2' "goCons_recList" "goNil_recList" $ \goCons goNil -> do
        f <- pFreshLam' "recList_self" $ \self -> pure $ elim # (goCons # self) # (goNil # self)
        pure $ fix # f

{-
   The PlutusTerm argument is a *correctly typed UPLC empty list constant*.

   This is almost incomprehensibly stupid, but we need to pass that around as an arguments.
   PLC is immutable (obviously) so `map` constructs a new list and it is impossible to do that
   if we do not know the type of the empty list we need. There is no way to pass that *type* in
   Untyped PLC so we pass the empty list itself.
-}
_pmap ::
    (MonadASG m) =>
    -- type-specific nil
    StubM m ()
_pmap = declare "map" $ pFreshLam2' "map_nil" "map_f" $ \nil f  -> do
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
    (MonadASG m) =>
    DefaultUni (Esc a) ->
    StubM m ()
mkSelectNil uni = declare declNm $ pFreshLam' "selectNil_depth" $ \depth ->
    pure $
        pCase
            depth
            [ mkList 0
            , mkList 1
            , mkList 2
            , mkList 3
            , mkList 4
            , mkList 5
            , mkList 6
            , mkList 7
            , mkList 8
            , mkList 9
            , mkList 10
            ]
  where
    declNm = selectNilName uni

    mkList :: Int -> PlutusTerm
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

_not :: forall m. MonadASG m =>  StubM m ()
_not = declare "not" $ pFreshLam $ \b ->
  pure $ pIf b (mkConstant () False) (mkConstant () True)

_and :: forall m. (MonadASG m) => StubM m ()
_and = declare "and" $ pFreshLam2 $ \b1 b2 ->
  pure $ pIf b1 b2 (mkConstant () False)

_or :: forall m. (MonadASG m) => StubM m ()
_or = declare "or" $ pFreshLam2 $ \b1 b2 ->
  pure $ pIf b1 (mkConstant () True) b2



{-
    *************
    Small helpers
    *************
-}

i :: Integer -> PlutusTerm
i = mkConstant ()


{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.FirstPass where

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
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (LamInternal), list, unsafeMkDatatypeInfos)
import Data.Kind (Type)

import Covenant.ExtendedASG
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Data.Row.Records (Rec, (.+), (.==))

import Covenant.ArgDict
import Covenant.Data (DatatypeInfo)
import Covenant.MockPlutus
import Covenant.Prim (OneArgFunc (IData, ListData, UnIData, UnListData))
import Covenant.Universe
import Debug.Trace (traceM)
import PlutusCore.Data (Data (I, List))
import PlutusCore.Default (DefaultUni (DefaultUniApply, DefaultUniProtoList), Esc)
import PlutusCore.MkPlc (mkConstant, mkConstantOf)

-- From here on out the top level node CANNOT BE ASSUMED TO BE THE HIGHEST NODE NUMERICALLY.
-- This is annoying but there really isn't a sensible way around it.
--
-- We also have to remember to "catch" the IDs for these functions during codegen
-- since they won't have a body, so we're going to have to keep the map around for a while too.
firstPass :: forall (m :: Type -> Type). (MonadASG m) => m (Rec FirstPassMeta)
firstPass = do
    uniqueErrorId <- ephemeralErrorId
    identityId <- mkIdentityFn
    eInsert uniqueErrorId AnError
    polyRepHandlers <- M.unions <$> traverse (mkRepHandler uniqueErrorId) ([IntegerT, ByteStringT] :: [BuiltinFlatT])
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

-- Converts an (arbitrarily nested) builtin list containing
-- The type of this is "morally":
--   Integer -> (a -> Data) -> List a -> Data
-- The integer is the depth of the list (where 0 represents a list without any inner lists)
-- and the function is the embedder for the innermost non-List type.

{- embList self depth emb list =
     let go n = if n <= 0
                then \x -> emb # x
                else \x -> map # (go # (n - 1)) # xs
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
    m PlutusTerm
embedList = fun
  where
    listify x = pBuiltin ListData # x
    -- morally: Integer -> ((a -> b) -> List a -> List b) -> ... (can't express this without dep types see above)
    mkGo :: m PlutusTerm
    mkGo =
        pFreshLam' "go_Depth" $ \depth ->
            pFreshLam' "go_EmbEl" $ \embEl ->
                pFreshLam' "go_MapF" $ \mapF -> do
                    recNat <- recNat'
                    goS <- pFreshLam2' "f" "xs" $ \f xs -> pure $ listify (mapF # f # xs)
                    pure $ recNat # embEl # goS # depth

    fun :: m PlutusTerm
    fun = pFreshLam' "fun_Depth" $ \depth ->
        pFreshLam' "fun_EmbEl" $ \innerF ->
            pFreshLam' "fun_xs" $ \xs -> do
                mapL <- mapV2 pNilData
                pLetM mapL $ \mapF -> do
                    go <- mkGo
                    let goF = go # depth # innerF # mapF
                    let resList = mapF # goF # xs
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
-}
projList ::
    forall (m :: Type -> Type) (a :: Type).
    (MonadASG m) =>
    DefaultUni (Esc a) -> m PlutusTerm
projList wit = pFreshLam3' "projEl" "xs" "depth" $ \projEl xs depth -> do
    tNil <- selectNil wit
    pLetM' "mkNil" tNil $ \mkNil -> do
        go <- mkGo mkNil
        pLetM' "go" go $ \go' -> do
            let goF = go' # depth # projEl
            pure $ goF # xs
  where
    unList :: PlutusTerm -> PlutusTerm
    unList t = pBuiltin UnListData # t

    mkGo :: PlutusTerm -> m PlutusTerm
    mkGo nil = pFreshLam2' "depth" "projEl" $ \depth projEl -> do
        recNat <- recNatN
        goS <- pFreshLam3' "n" "f" "xs" $ \n f xs -> do
            mapF <- mapV2 (nil # n)
            pure $ mapF # f # unList xs
        goZ <- do
            mapF <- mapV2 (nil # mkConstant @Integer () 0)
            pFreshLam' "goZ_xs" $ \xs -> pure $ mapF # projEl # unList xs -- pFreshLam' "xs" $ \xs -> pure $ mapF # projEl # xs
        pure $ recNat # goZ # goS # depth

onlyList :: Map TyName (DatatypeInfo AbstractTy)
onlyList = unsafeMkDatatypeInfos [list]

projListWithType ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    Map TyName (DatatypeInfo AbstractTy) ->
    ValT AbstractTy ->
    PlutusTerm ->
    m PlutusTerm
projListWithType dtDict valT projEl = case analyzeListTy dtDict valT of
    Nothing -> error $ "Cannot create list projection for " <> pValT valT
    Just (depth, MkUniProof wit) -> do
        traceM $ "depth: " <> show depth
        traceM $ "wit: " <> show wit
        projF <- projList wit
        pFreshLam' "xs" $ \xs -> pure $ projF # projEl # xs # mkConstant () depth

listTy :: ValT AbstractTy -> ValT AbstractTy
listTy t = Datatype "List" [t]

testListTy0 = listTy $ BuiltinFlat IntegerT

testListTy1 = listTy testListTy0

testListTy2 = listTy testListTy1

testList0 :: PlutusTerm
testList0 = mkConstant @Data () (List (I <$> [1, 2, 3, 4, 5]))

testList1 :: PlutusTerm
testList1 = mkConstant @Data () (List (map List (map I <$> [[1], [2, 3], [4]])))

testList2 :: PlutusTerm
testList2 = mkConstant @Data () (List [List [List [I 1], List [I 2, I 3]], List [List [I 4]]])

projInt :: forall m. (MonadASG m) => m PlutusTerm
projInt = pFreshLam' "x" $ \x -> pure $ pBuiltin UnIData # x

testProjList :: ValT AbstractTy -> PlutusTerm -> PlutusTerm
testProjList listType listTerm = runWithEmptyASG $ do
    projIntF <- projInt
    projListF <- projListWithType onlyList listType projIntF
    pure $ projListF # listTerm

test1 = testProjList testListTy1 testList1

{-
  This is a bit weird. This constructs an empty list value of the correct "depth"
  (where 0 means [a], 1 means [[a]], etc). We need something like this for list projections.

  This only goes "up to" 10 (but we can always add more cases if we need them)
-}
selectNil ::
    forall (m :: Type -> Type) (a :: Type).
    (MonadASG m) =>
    DefaultUni (Esc a) -> m PlutusTerm
selectNil uni = pFreshLam' "selectNil_depth" $ \depth ->
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
    mkList :: Int -> PlutusTerm
    mkList n = case mkWitness n of
        MkListProof wit -> mkConstantOf () wit []

    mkWitness :: Int -> ListProof
    mkWitness n
        | n <= 0 = MkListProof $ DefaultUniApply DefaultUniProtoList uni
        | otherwise = case mkWitness (n - 1) of
            MkListProof t -> MkListProof $ DefaultUniApply DefaultUniProtoList t

-- r -> (r -> r) ->  Integer -> r
recNat' :: (MonadASG m) => m PlutusTerm
recNat' = mkZ =<< go
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        let isZero = n #<= i 0
        pure $ pIf isZero whenZ (whenS # (self # whenZ # whenS # (n #- i 1)))

--  r -> (r -> Integer -> r) ->  Integer -> r
recNatN :: (MonadASG m) => m PlutusTerm
recNatN = mkZ =<< go
  where
    go = pFreshLam' "self" $ \self -> pFreshLam3' "whenZ" "whenS" "n" $ \whenZ whenS n -> do
        let isZero = n #<= i 0
            whenS' = whenS # n
        pure $ pIf isZero whenZ (whenS' # (self # whenZ # whenS # (n #- i 1)))

testPIf = pIf (mkConstant () True) (i 1) (i 0)

-- ([] :: [b]) -> (a -> b) -> List a -> List b
-- I.e. it takes an empty list of the "right type"
mapList ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    PlutusTerm ->
    m PlutusTerm
mapList typedNil = do
    mapF <- pFix =<< mapFun
    pure $ mapF # typedNil
  where
    mapFun :: m PlutusTerm
    mapFun =
        pFreshLam' "map_Self" $ \self ->
            pFreshLam' "map_Nil" $ \nil ->
                pFreshLam' "map_f" $ \f ->
                    pFreshLam' "map_xs" $ \xs -> do
                        doCons <- pFreshLam $ \self' ->
                            pFreshLam2 $ \y ys -> do
                                let y' = f # y
                                    ys' = self' # nil # f # ys
                                pure $ pCons y' ys'
                        pure $ pCase xs [doCons # self, nil]

i :: Integer -> PlutusTerm
i = mkConstant ()

depth1Ints :: PlutusTerm
depth1Ints = mkConstant @[[Integer]] () [[1, 2, 3], [4], [5, 6]]

depth0Ints :: PlutusTerm
depth0Ints = mkConstant @[Integer] () [1, 2, 3, 4]

-- FOR TESTING / INSPECTION ONLY
embedListTest :: PlutusTerm
embedListTest = runWithEmptyASG $ do
    emb <- embedList
    iDat <- pFreshLam $ \x -> pure $ pBuiltin IData # x
    pure $ emb # i 0 # iDat # depth0Ints

mapTest :: PlutusTerm
mapTest = runWithEmptyASG $ do
    _mapInts <- mapV2 (mkConstant @[Integer] () [])
    _subOne <- pFreshLam' "sub_x" $ \x -> pure $ x #- i 1
    pLetM' "map" _mapInts $ \mapInts ->
        pLetM' "minus_one" _subOne $ \subOne ->
            pure $ mapInts # subOne # depth1Ints

mapV2 ::
    (MonadASG m) =>
    -- type-specific nil
    PlutusTerm ->
    -- Returns: (a -> b) -> List a -> List b
    m PlutusTerm
mapV2 nil = pFreshLam' "map_f" $ \f -> do
    _goCons <- pFreshLam3' "self" "x" "xs" $ \self x xs -> pure $ pCons (f # x) (self # xs)
    _goNil <- pFreshLam' "_" $ \_ -> pure nil
    _recList <- recList
    pLetM' "recList" _recList $ \goRecList ->
        pLetM' "goCons" _goCons $ \goCons ->
            pLetM' "goNil" _goNil $ \goNil -> do
                pure $ goRecList # goCons # goNil

recListTest :: PlutusTerm
recListTest = runWithEmptyASG $ do
    -- ([Int] -> Int) -> Int -> [Int] -> Int
    fCons <- pFreshLam3' "self" "x" "xs" $ \_ x _ -> pure x
    fNil <- pFreshLam' "_xs" $ \_ -> pure (i 0)
    recList' <- recList
    pure $ recList' # fCons # fNil # depth1Ints

-- ((List a -> r) -> a -> List a -> r)
-- (List a -> r) -> r
-- List a -> r
recList ::
    (MonadASG m) =>
    m PlutusTerm
recList = do
    pFreshLam' "goCons_recList" $ \goCons ->
        pFreshLam' "goNi_recList" $ \goNil -> do
            _elim <- elimList
            -- _fix <- testFix
            pLetM' "elimList" _elim $ \elim -> do
                -- pLetM' "fix" _fix $ \fix -> do
                _f <- pFreshLam' "self" $ \self -> pure $ elim # (goCons # self) # (goNil # self)
                pLetM' "reclist_go" _f $ \f ->
                    mkZ f

-- (a -> List a -> r) -> r -> List a -> r
elimList :: (MonadASG m) => m PlutusTerm
elimList = pFreshLam3' "goCons" "goNil" "xs" $ \goCons goNil xs -> pure $ pCase xs [goCons, goNil]

elimListTest :: PlutusTerm
elimListTest = runWithEmptyASG $ do
    elim <- elimList
    fCons <- pFreshLam2' "x" "xs" $ \x _xs -> pure x
    pure $ elim # fCons # i 0 # depth1Ints

mkZ' :: (MonadASG m) => m PlutusTerm
mkZ' = pFreshLam' "f" $ \f -> do
    g <- pFreshLam' "x" $ \x -> do
        (f #) <$> pFreshLam' "v" (\v -> pure $ x # x # v)
    pure $ g # g

mkZ :: (MonadASG m) => PlutusTerm -> m PlutusTerm
mkZ f = do
    g <- pFreshLam' "x" $ \x -> do
        (f #) <$> pFreshLam' "v" (\v -> pure $ x # x # v)
    pure $ g # g

testFix :: (MonadASG m) => m PlutusTerm
testFix = pFreshLam' "f" $ \f -> do
    x <- pFreshLam' "x" $ \r -> pure $ f # (r # r)
    pure $ x # x

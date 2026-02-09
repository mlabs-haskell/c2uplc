{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
-- TODO: Once the tests are wired up properly, should be removed
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Covenant.CodeGen (evalTerm)
import Covenant.CodeGen.Stubs
  ( StubM,
    compileStub',
    defStubs,
    pInt,
    resolveStub,
  )
import Covenant.Data (DatatypeInfo)
import Covenant.ExtendedASG (MonadASG)
import Covenant.Plutus
  ( pBuiltin,
    prettyPTerm,
    (#),
    (#-),
  )
import Covenant.Prim (OneArgFunc (IData, UnIData))
import Covenant.Test (list, unsafeMkDatatypeInfos)
import Covenant.Transform.Common
  ( pFreshLam,
    pFreshLam',
    pFreshLam2',
    pFreshLam3',
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (IntegerT),
    TyName,
    ValT (BuiltinFlat, Datatype),
  )
import Data.Map (Map)
import PlutusCore.Data (Data (I, List))
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term)

main :: IO ()
main = error "TODO SETUP STUB TESTS (everything was checked in a repl so OK for right now)"

{-
  *************
  Testing Stuff
  *************

  Eventually need to move to a test suite, but for now these are just some simple cases
  and utilities for quick GHCI validation.
-}

onlyList :: Map TyName (DatatypeInfo AbstractTy)
onlyList = unsafeMkDatatypeInfos [list]

listTy :: ValT AbstractTy -> ValT AbstractTy
listTy t = Datatype "List" [t]

testListTy0 :: ValT AbstractTy
testListTy0 = listTy $ BuiltinFlat IntegerT

testListTy1 :: ValT AbstractTy
testListTy1 = listTy testListTy0

testListTy2 :: ValT AbstractTy
testListTy2 = listTy testListTy1

testList0 :: Term Name DefaultUni DefaultFun ()
testList0 = mkConstant @Data () (List (I <$> [1, 2, 3, 4, 5]))

testList1 :: Term Name DefaultUni DefaultFun ()
testList1 = mkConstant @Data () (List (map List (map I <$> [[1], [2, 3], [4]])))

testList2 :: Term Name DefaultUni DefaultFun ()
testList2 = mkConstant @Data () (List [List [List [I 1], List [I 2, I 3]], List [List [I 4]]])

projInt :: forall m. (MonadASG m) => m (Term Name DefaultUni DefaultFun ())
projInt = pFreshLam' "x" $ \x -> pure $ pBuiltin UnIData # x

elimListTest :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
elimListTest = do
  elim <- resolveStub "elimList"
  fCons <- pFreshLam2' "x" "xs" $ \x _xs -> pure x
  pure $ elim # fCons # pInt 0 # depth0Ints

{-
testProjList :: (MonadASG m) => ValT AbstractTy -> Term Name DefaultUni DefaultFun () -> StubM m Term Name DefaultUni DefaultFun ()
testProjList listType listTerm = do
    projIntF <- projInt
    projListWithType onlyList listType projIntF
    projListF <- getListProj onlyList (BuiltinFlat IntegerT)
    pure $ projListF # listTerm
-}
depth1Ints :: Term Name DefaultUni DefaultFun ()
depth1Ints = mkConstant @[[Integer]] () [[1, 2, 3], [4], [5, 6]]

depth0Ints :: Term Name DefaultUni DefaultFun ()
depth0Ints = mkConstant @[Integer] () [1, 2, 3, 4]

-- FOR TESTING / INSPECTION ONLY
embedListTest :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
embedListTest = do
  emb <- resolveStub "embedList"
  iDat <- pFreshLam $ \x -> pure $ pBuiltin IData # x
  pure $ emb # pInt 0 # iDat # depth0Ints

mapTest :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
mapTest = do
  mkMap <- resolveStub "map"
  let pmap = mkMap # mkConstant @[Integer] () []
  subOne <- pFreshLam' "sub_x" $ \x -> pure $ x #- pInt 1
  pure $ pmap # subOne # depth0Ints

recListTest :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
recListTest = do
  -- ([Int] -> Int) -> Int -> [Int] -> Int
  fCons <- pFreshLam3' "self" "x" "xs" $ \_ x _ -> pure x
  fNil <- pFreshLam' "_xs" $ \_ -> pure (pInt 0)
  recList' <- resolveStub "recList"
  pure $ recList' # fCons # fNil # depth1Ints

testEmbTrue :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
testEmbTrue = do
  emb <- resolveStub "embedBool"
  pure $ emb # mkConstant () True

-- Round trips
testProjTrue :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
testProjTrue = do
  emb <- resolveStub "embedBool"
  let embedded = emb # mkConstant () True
  proj <- resolveStub "projBool"
  pure $ proj # embedded

testEmbFalse :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
testEmbFalse = do
  emb <- resolveStub "embedBool"
  pure $ emb # mkConstant () False

-- Round trips
testProjFalse :: (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
testProjFalse = do
  emb <- resolveStub "embedBool"
  let embedded = emb # mkConstant () False
  proj <- resolveStub "projBool"
  pure $ proj # embedded

runTest ::
  (forall m. (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())) ->
  IO ()
runTest stub' = case compileStub' stub of
  Left stubErr -> print stubErr
  Right hm -> do
    putStrLn "Stub compilation success. Pretty unevaluated term:"
    putStrLn ""
    print $ prettyPTerm hm
    putStrLn ""
    putStrLn "Trying evaluation..."
    case evalTerm hm of
      Left evalErr -> putStrLn evalErr
      Right res -> do
        putStrLn "Success! Evaluation result: "
        print (prettyPTerm res)
  where
    stub :: forall m. (MonadASG m) => StubM m (Term Name DefaultUni DefaultFun ())
    stub = defStubs >> stub'

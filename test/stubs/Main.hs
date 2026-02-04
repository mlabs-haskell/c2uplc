{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

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
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (LamInternal), Id, list, unsafeMkDatatypeInfos)
import Data.Kind (Type)

import Covenant.ExtendedASG
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Data.Row.Records (Rec, (.+), (.==))

import Algebra.Graph.AdjacencyMap
import Algebra.Graph.AdjacencyMap.Algorithm
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State.Strict (MonadState (get, put), MonadTrans (lift), StateT (runStateT), modify')
import Covenant.ArgDict
import Covenant.CodeGen (evalTerm)
import Covenant.CodeGen.Stubs
import Covenant.Data (DatatypeInfo)
import Covenant.MockPlutus
import Covenant.Prim (OneArgFunc (IData, ListData, UnIData, UnListData))
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

elimListTest :: (MonadASG m) => StubM m PlutusTerm
elimListTest = do
    elim <- resolveStub "elimList"
    fCons <- pFreshLam2' "x" "xs" $ \x _xs -> pure x
    pure $ elim # fCons # i 0 # depth0Ints

testProjList :: (MonadASG m) => ValT AbstractTy -> PlutusTerm -> StubM m PlutusTerm
testProjList listType listTerm = do
    projIntF <- projInt
    projListWithType onlyList listType projIntF
    projListF <- getListProj onlyList (BuiltinFlat IntegerT)
    pure $ projListF # listTerm

depth1Ints :: PlutusTerm
depth1Ints = mkConstant @[[Integer]] () [[1, 2, 3], [4], [5, 6]]

depth0Ints :: PlutusTerm
depth0Ints = mkConstant @[Integer] () [1, 2, 3, 4]

-- FOR TESTING / INSPECTION ONLY
embedListTest :: (MonadASG m) => StubM m PlutusTerm
embedListTest = do
    emb <- resolveStub "embedList"
    iDat <- pFreshLam $ \x -> pure $ pBuiltin IData # x
    pure $ emb # i 0 # iDat # depth0Ints

mapTest :: (MonadASG m) => StubM m PlutusTerm
mapTest = do
    mkMap <- resolveStub "map"
    let pmap = mkMap # mkConstant @[Integer] () []
    subOne <- pFreshLam' "sub_x" $ \x -> pure $ x #- i 1
    pure $ pmap # subOne # depth0Ints

recListTest :: (MonadASG m) => StubM m PlutusTerm
recListTest = do
    -- ([Int] -> Int) -> Int -> [Int] -> Int
    fCons <- pFreshLam3' "self" "x" "xs" $ \_ x _ -> pure x
    fNil <- pFreshLam' "_xs" $ \_ -> pure (i 0)
    recList' <- resolveStub "recList"
    pure $ recList' # fCons # fNil # depth1Ints

testEmbTrue :: (MonadASG m) => StubM m PlutusTerm
testEmbTrue = do
    emb <- resolveStub "embedBool"
    pure $ emb # mkConstant () True

-- Round trips
testProjTrue :: (MonadASG m) => StubM m PlutusTerm
testProjTrue = do
    emb <- resolveStub "embedBool"
    let embedded = emb # mkConstant () True
    proj <- resolveStub "projBool"
    pure $ proj # embedded

testEmbFalse :: (MonadASG m) => StubM m PlutusTerm
testEmbFalse = do
    emb <- resolveStub "embedBool"
    pure $ emb # mkConstant () False

-- Round trips
testProjFalse :: (MonadASG m) => StubM m PlutusTerm
testProjFalse = do
    emb <- resolveStub "embedBool"
    let embedded = emb # mkConstant () False
    proj <- resolveStub "projBool"
    pure $ proj # embedded

runTest :: (forall m. (MonadASG m) => StubM m PlutusTerm) -> IO ()
runTest stub' = case compileStub' stub of
    Left stubErr -> putStrLn (show stubErr)
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
    stub :: forall m. (MonadASG m) => StubM m PlutusTerm
    stub = defStubs >> stub'

{-# LANGUAGE OverloadedLists #-}

module Main where

import Covenant.ASG
import Covenant.CodeGen
import Covenant.Data
import Covenant.JSON
import Covenant.Type

import Covenant.Constant
import Covenant.Prim
import Prettyprinter
import UntypedPlutusCore ()

import Control.Monad (void)
import Covenant.MockPlutus (PlutusTerm)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Vector (Vector)
import Data.Vector qualified as V
import Debug.Trace

import Optics.Core (view)
import Prettyprinter

import Covenant.DeBruijn (DeBruijn (..))
import Covenant.Index
import Covenant.MockPlutus (prettyPTerm)
import Covenant.Test (unsafeMkDatatypeInfos)
import Data.Either (isRight)
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main =
    defaultMain $
        testGroup
            "compilation"
            [ testCase "simpleCaseCompilesWithoutErrors" simpleCase
            ]
  where
    simpleCase = assertBool "addTwoNumbers didn't compile" . isRight $ testCompile mempty addTwoNumbers

data CompilerError
    = ASGConstructionFail CovenantError
    | CodeGenFail CodeGenError
    deriving stock (Show)

testCompile ::
    forall a.
    Vector (DataDeclaration AbstractTy) ->
    ASGBuilder a ->
    Either String PlutusTerm
testCompile dtDict builder = case mkASG dtDict builder of
    Left asgErr -> Left $ show (ASGConstructionFail asgErr)
    Right cu -> case compile cu of
        Left cgErr -> Left $ show (CodeGenFail cgErr)
        Right resTerm -> do
            traceM $ "\n" <> show (prettyPTerm resTerm) <> "\n"
            case evalTerm resTerm of
                Left errMsg -> Left errMsg
                Right evaluated -> do
                    traceM $ "\nevaluated:\n" <> show (prettyPTerm evaluated)
                    pure evaluated

maybeT :: DataEncoding -> DataDeclaration AbstractTy
maybeT =
    DataDeclaration
        "Maybe"
        count1
        [ Constructor "Nothing" []
        , Constructor "Just" [tyvar Z ix0]
        ]

maybeSOP :: DataDeclaration AbstractTy
maybeSOP = maybeT SOP

maybeData :: DataDeclaration AbstractTy
maybeData = maybeT (PlutusData Covenant.Type.ConstrData)

abcT :: DataDeclaration AbstractTy
abcT =
    DataDeclaration
        "ABC"
        count0
        [ Constructor "A" []
        , Constructor "B" []
        , Constructor "C" []
        ]
        (PlutusData EnumData)

myListT :: DataEncoding -> DataDeclaration AbstractTy
myListT =
    DataDeclaration
        "MyList"
        count1
        [ Constructor "MyNil" []
        , Constructor "MyCons" [tyvar Z ix0, Datatype "MyList" [tyvar Z ix0]]
        ]

myListSOP :: DataDeclaration AbstractTy
myListSOP = myListT SOP

myListData :: DataDeclaration AbstractTy
myListData = myListT (PlutusData Covenant.Type.ConstrData)

productT :: DataEncoding -> DataDeclaration AbstractTy
productT =
    DataDeclaration
        "Product"
        count1
        [Constructor "Product" [BuiltinFlat IntegerT, tyvar Z ix0]]

productData :: DataDeclaration AbstractTy
productData = productT (PlutusData ProductListData)

productSOP :: DataDeclaration AbstractTy
productSOP = productT SOP

myNewtype :: DataDeclaration AbstractTy
myNewtype =
    DataDeclaration
        "Newtype"
        count1
        [Constructor "Newtype" [tyvar Z ix0]]
        (PlutusData NewtypeData)

testLam :: ValT AbstractTy -> ASGBuilder Ref -> ASGBuilder Id
testLam retT = lam (Comp0 $ ReturnT retT)

mkASG ::
    forall a.
    Vector (DataDeclaration AbstractTy) ->
    ASGBuilder a ->
    Either CovenantError CompilationUnit
mkASG dtDict builder = case runASGBuilder (unsafeMkDatatypeInfos $ V.toList dtDict) builder of
    Left err' -> Left err'
    Right (ASG asg) -> do
        pure $ CompilationUnit dtDict asg (Version 0 0)

addTwoNumbers :: ASGBuilder Id
addTwoNumbers = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
    one <- AnId <$> lit (AnInteger 1)
    two <- AnId <$> lit (AnInteger 2)
    plus <- builtin2 AddInteger
    AnId <$> app' plus [one, two]

mkJust :: ASGBuilder Id
mkJust = lam (Comp0 $ ReturnT (Datatype "Maybe" [BuiltinFlat IntegerT])) $ do
    zero <- AnId <$> lit (AnInteger 0)
    two <- AnId <$> lit (AnInteger 2)
    AnId <$> ctor' "Maybe" "Just" [two]

matchOnMaybeInt :: ASGBuilder Id
matchOnMaybeInt = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
    zero <- AnId <$> lit (AnInteger 0)
    two <- AnId <$> lit (AnInteger 2)
    just2 <- AnId <$> ctor' "Maybe" "Just" [two]
    plus <- builtin2 AddInteger
    justHandler <- lazyLam (Comp0 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)) $ do
        justWhat <- arg Z ix0
        AnId <$> app' plus [AnArg justWhat, AnArg justWhat]
    AnId <$> match just2 [zero, AnId justHandler]

introEnum :: ASGBuilder Id
introEnum = lam (Comp0 $ ReturnT (Datatype "ABC" [])) $ AnId <$> ctor' "ABC" "A" []

elimEnum :: ASGBuilder Id
elimEnum = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
    myABC <- AnId <$> ctor' "ABC" "A" []
    one <- AnId <$> lit (AnInteger 2)
    two <- AnId <$> lit (AnInteger 3)
    three <- AnId <$> lit (AnInteger 4)
    AnId <$> match myABC [one, two, three]

introProduct :: ASGBuilder Id
introProduct = lam (Comp0 $ ReturnT (Datatype "Product" [BuiltinFlat BoolT])) $ do
    one <- AnId <$> lit (AnInteger 1)
    fawlse <- AnId <$> lit (ABoolean False)
    AnId <$> ctor' "Product" "Product" [one, fawlse]

introNewtype :: ASGBuilder Id
introNewtype = testLam (Datatype "Newtype" [BuiltinFlat IntegerT]) $ do
    one <- AnId <$> lit (AnInteger 1)
    AnId <$> ctor' "Newtype" "Newtype" [one]

elimNewtype :: ASGBuilder Id
elimNewtype = testLam (BuiltinFlat IntegerT) $ do
    one <- AnId <$> lit (AnInteger 1)
    myNT <- AnId <$> ctor' "Newtype" "Newtype" [one]
    idF <- lazyLam (Comp1 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)) $ AnArg <$> arg Z ix0
    AnId <$> match myNT [AnId idF]

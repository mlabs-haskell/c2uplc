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

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
import Data.Vector qualified as V
import Debug.Trace

import Optics.Core (view)
import Prettyprinter

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
    simpleCase = assertBool "addTwoNumbers didn't compile" . isRight $ testCompile M.empty addTwoNumbers

data CompilerError
    = ASGConstructionFail CovenantError
    | CodeGenFail CodeGenError
    deriving stock (Show)

testCompile ::
    forall a.
    Map TyName (DatatypeInfo AbstractTy) ->
    ASGBuilder a ->
    Either CompilerError PlutusTerm
testCompile dtDict builder = case mkASG dtDict builder of
    Left asgErr -> Left (ASGConstructionFail asgErr)
    Right cu -> case compile cu of
        Left cgErr -> Left (CodeGenFail cgErr)
        Right resTerm -> do
            traceM $ "\n" <> show (pretty resTerm) <> "\n"
            pure resTerm

mkASG ::
    forall a.
    Map TyName (DatatypeInfo AbstractTy) ->
    ASGBuilder a ->
    Either CovenantError CompilationUnit
mkASG dtDict builder = case runASGBuilder dtDict builder of
    Left err' -> Left err'
    Right (ASG asg) -> do
        pure $ CompilationUnit (extractDecls dtDict) asg (Version 0 0)
  where
    extractDecls :: Map TyName (DatatypeInfo AbstractTy) -> V.Vector (DataDeclaration AbstractTy)
    extractDecls = V.fromList . map (view #originalDecl) . M.elems

addTwoNumbers :: ASGBuilder Id
addTwoNumbers = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
    one <- AnId <$> lit (AnInteger 1)
    two <- AnId <$> lit (AnInteger 2)
    plus <- builtin2 AddInteger
    AnId <$> app' plus [one, two]

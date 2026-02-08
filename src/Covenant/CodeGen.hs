module Covenant.CodeGen (compile, compileIO, evalTerm, compilePretty, CodeGenError) where

-- N.B. *WE* have two different things called `ConstrData`

import Codec.Extras.SerialiseViaFlat (SerialiseViaFlat (SerialiseViaFlat))
import Codec.Serialise (writeFileSerialise)
import Control.Exception (throwIO)
import Covenant.CodeGen.Common
  ( CodeGenError (WrapStubError),
    runTopDownCompile,
  )
import Covenant.ExtendedASG (wrapASG)
import Covenant.JSON (CompilationUnit (CompilationUnit), deserializeCompilationUnit)
import Covenant.MockPlutus (PlutusTerm, prettyPTerm)
import Covenant.Test (unsafeMkDatatypeInfos)
import Covenant.Transform (transformASG)
import Covenant.Transform.Pipeline.Monad (Datatypes (Datatypes), runCodeGen)
import Data.Bifunctor (Bifunctor (first))
import Data.Kind (Type)
import Data.Text (Text)
import Data.Vector qualified as Vector
import PlutusCore (Name)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import Prettyprinter (Doc, pretty)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

compilePretty ::
  forall (ann :: Type).
  CompilationUnit -> Either CodeGenError (Doc ann)
compilePretty = fmap pretty . compile

{- Add optimization pass after UPLC generation

   See: https://github.com/Plutonomicon/plutarch-plutus/blob/treasury-milestone-3/Plutarch/Internal/Term.hs#L829-L853
-}
compile :: CompilationUnit -> Either CodeGenError PlutusTerm
compile (CompilationUnit datatypesRaw asg _version) = first WrapStubError $ runCodeGen (wrapASG asg) $ do
  cgData <- transformASG datatypes
  runTopDownCompile cgData >>= \case
    Left cgErr -> error $ "Compilation error during code generation: " <> show cgErr
    Right aTerm -> pure aTerm
  where
    datatypes :: Datatypes
    datatypes = Datatypes $ unsafeMkDatatypeInfos (Vector.toList datatypesRaw)

compileIO :: FilePath -> IO ()
compileIO path = do
  putStrLn $ "Attempting to compile compilation unit at: " <> path <> "..."
  cu <- deserializeCompilationUnit path
  putStrLn "Compilation unit successfully deserialized and validated."
  putStrLn "Attempting to generate UPLC code..."
  case compile cu of
    Left cgErr -> throwIO . userError $ "Code generation failed\nReason: " <> show cgErr
    Right aTerm -> do
      putStrLn "Code generation succeeded!"
      putStrLn "Raw Script:"
      print aTerm
      putStrLn ""
      putStrLn "Pretty Script:"
      print (prettyPTerm aTerm)
      putStrLn ""
      putStrLn "Attempting to pre-evaluate result (reduces script size / optimizes code / catches simple mistakes)..."
      case evalTerm aTerm of
        Left plcErr -> do
          putStrLn "Evaluation failed :-("
          putStrLn "  Reason:"
          putStrLn plcErr
        Right evalResult -> do
          putStrLn "Evaluation succeeded!"
          putStrLn "Raw evaluated script:"
          print evalResult
          putStrLn "Pretty evaluated script:"
          print (prettyPTerm evalResult)
          putStrLn "Writing output to: ./SCRIPT.plc"
          serializePlc "SCRIPT.plc" evalResult

serializePlc ::
  FilePath ->
  PlutusTerm ->
  IO ()
serializePlc path =
  writeFileSerialise path
    . SerialiseViaFlat
    . UPLC.UnrestrictedProgram
    . UPLC.Program () PLC.latestVersion

-----------------------------------

-- Returns a pretty error bundle (or at least, like, a string-ey error bundle)
-- or the evaluated term

evalTerm :: PlutusTerm -> Either String PlutusTerm
evalTerm t = case errOrRes of
  Left anErr -> Left $ "Failure!\n  Eval Exception: " <> show anErr <> "\n  Logs: " <> show log'
  Right res -> pure res
  where
    (errOrRes, log') = evalTerm' t

-- no budget, don't care yet
evalTerm' ::
  PlutusTerm ->
  ( Either
      (Cek.CekEvaluationException Name PLC.DefaultUni PLC.DefaultFun)
      PlutusTerm,
    [Text]
  )
evalTerm' t =
  case Cek.runCek defaultCekParametersForTesting Cek.counting Cek.logEmitter t of
    (errOrRes, _, logs) -> (errOrRes, logs)

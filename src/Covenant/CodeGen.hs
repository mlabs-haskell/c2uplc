module Covenant.CodeGen
  ( compile,
    evalTerm,
    compilePretty,
    CodeGenError,
  )
where

-- N.B. *WE* have two different things called `ConstrData`

import Covenant.CodeGen.Common
  ( CodeGenError (WrapStubError),
    runTopDownCompile,
  )
import Covenant.ExtendedASG (wrapASG)
import Covenant.JSON (CompilationUnit (CompilationUnit))
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
import UntypedPlutusCore (DefaultFun, DefaultUni, Term)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

compilePretty ::
  forall (ann :: Type).
  CompilationUnit -> Either CodeGenError (Doc ann)
compilePretty = fmap pretty . compile

{- Add optimization pass after UPLC generation

   See: https://github.com/Plutonomicon/plutarch-plutus/blob/treasury-milestone-3/Plutarch/Internal/Term.hs#L829-L853
-}
compile :: CompilationUnit -> Either CodeGenError (Term Name DefaultUni DefaultFun ())
compile (CompilationUnit datatypesRaw asg _version) = first WrapStubError $ runCodeGen (wrapASG asg) $ do
  cgData <- transformASG datatypes
  runTopDownCompile cgData >>= \case
    Left cgErr -> error $ "Compilation error during code generation: " <> show cgErr
    Right aTerm -> pure aTerm
  where
    datatypes :: Datatypes
    datatypes = Datatypes $ unsafeMkDatatypeInfos (Vector.toList datatypesRaw)

-----------------------------------

-- Returns a pretty error bundle (or at least, like, a string-ey error bundle)
-- or the evaluated term

evalTerm ::
  Term Name DefaultUni DefaultFun () ->
  Either String (Term Name DefaultUni DefaultFun ())
evalTerm t = case errOrRes of
  Left anErr -> Left $ "Failure!\n  Eval Exception: " <> show anErr <> "\n  Logs: " <> show log'
  Right res -> pure res
  where
    (errOrRes, log') = evalTerm' t

-- no budget, don't care yet
evalTerm' ::
  Term Name DefaultUni DefaultFun () ->
  ( Either
      (Cek.CekEvaluationException Name PLC.DefaultUni PLC.DefaultFun)
      (Term Name DefaultUni DefaultFun ()),
    [Text]
  )
evalTerm' t =
  case Cek.runCek defaultCekParametersForTesting Cek.counting Cek.logEmitter t of
    (errOrRes, _, logs) -> (errOrRes, logs)

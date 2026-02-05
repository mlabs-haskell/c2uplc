module Covenant.CodeGen (compile, compileIO, evalTerm, compilePretty, CodeGenError) where

import Covenant.ASG (
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
 )
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.Data (DatatypeInfo)
import Covenant.Test (Arg (UnsafeMkArg), Id (UnsafeMkId), unsafeMkDatatypeInfos)
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT,
    Constructor,
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (
        EnumData,
        NewtypeData,
        ProductListData
    ),
    TyName,
 )

-- N.B. *WE* have two different things called `ConstrData`
import Covenant.Type qualified as T

import Control.Monad.Error.Class (MonadError, throwError)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.RWS (RWS, evalRWS)

import Data.Foldable (foldl')

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Data.Text (Text)

import Optics.Core (review, view)

import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (intIndex)
import Covenant.MockPlutus (
    PlutusTerm,
    SomeBuiltin (SomeBuiltin1, SomeBuiltin2, SomeBuiltin3, SomeBuiltin6),
    bData,
    constrData,
    iData,
    listData,
    mapData,
    pApp,
    pBuiltin,
    pCase,
    pConstr,
    pDelay,
    pError,
    pForce,
    pLam,
    pVar,
    plutus_ConstrData,
    prettyPTerm,
 )

import Covenant.ArgDict ()
import Covenant.CodeGen.Common

import Codec.Serialise (writeFileSerialise)
import Control.Monad.Except (runExceptT)
import Covenant.ExtendedASG (extendedNodes, unExtendedASG, wrapASG)
import Covenant.JSON (CompilationUnit (CompilationUnit), deserializeCompilationUnit)
import Covenant.Transform (transformASG)
import Covenant.Transform.Common (TyFixerFnData (TyFixerFnData))
import Covenant.Transform.Pipeline.Common (CodeGenData, TransformState)
import Covenant.Transform.TyUtils (idToName)
import Data.Maybe (isJust)
import Data.Row.Records (Rec)
import Data.Row.Records qualified as R
import PlutusCore (Name (Name))
import PlutusCore.MkPlc (mkConstant)
import Prettyprinter
import UntypedPlutusCore (Unique (Unique))

-- evaluation stuff

import Codec.Extras.SerialiseViaFlat (SerialiseViaFlat (SerialiseViaFlat))
import Control.Exception (throwIO)
import Covenant.CodeGen.Stubs (StubError)
import Covenant.Transform.Pipeline.Monad (CodeGen, Datatypes (Datatypes), runCodeGen)
import Data.Bifunctor (Bifunctor (first))
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (
    ExBudget (ExBudget),
    ExRestrictingBudget (ExRestrictingBudget),
    minusExBudget,
 )
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (ExCPU), ExMemory (ExMemory))
import Prettyprinter
import UntypedPlutusCore (
    Program (Program),
    Term,
    Version (Version),
 )
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

compilePretty = fmap pretty . compile

{- Add optimization pass after UPLC generation

   See: https://github.com/Plutonomicon/plutarch-plutus/blob/treasury-milestone-3/Plutarch/Internal/Term.hs#L829-L853
-}
compile :: CompilationUnit -> Either CodeGenError PlutusTerm
compile cu@(CompilationUnit datatypesRaw asg _version) = first WrapStubError $ runCodeGen (wrapASG asg) $ do
    cgData <- transformASG datatypes
    runTopDownCompile cgData >>= \case
        Left cgErr -> error $ "Compilation error during code generation: " <> show cgErr
        Right aTerm -> pure aTerm
  where
    datatypes = Datatypes $ unsafeMkDatatypeInfos (Vector.toList datatypesRaw)

    prettyNodes acc [] = vcat $ reverse acc
    prettyNodes acc ((UnsafeMkId i, node) : rest) =
        let here = "let" <+> pretty i <+> "=" <+> viaShow node
         in prettyNodes (here : acc) rest

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

-- TODO: Need to rework this to ignore synthetic (compiler generated) nodes since we really really really
--       want to make sure they definitely get let bound
countOccurs :: Id -> [ASGNode] -> Int
countOccurs i = foldl' go 0
  where
    countId :: Id -> Int
    countId i' = if i == i' then 1 else 0

    countRef :: Ref -> Int
    countRef = \case
        AnId i' -> if i == i' then 1 else 0
        AnArg _ -> 0

    go :: Int -> ASGNode -> Int
    go n = \case
        ACompNode _compTy compNodeInfo -> case compNodeInfo of
            Force r -> n + countRef r
            Lam r -> n + countRef r
            _other -> n
        AValNode _valT valNodeInfo -> case valNodeInfo of
            Lit _aConstant -> n
            App fn args _ _ -> n + countId fn + sum (countRef <$> args)
            Thunk i' -> n + countId i'
            Cata ty handlers arg -> n + sum (countRef <$> arg `Vector.cons` handlers)
            DataConstructor _tn _cn fields -> n + sum (countRef <$> fields)
            Match scrut handlers -> n + countRef scrut + sum (countRef <$> handlers)
        AnError{} -> n

-----------------------------------

-- Returns a pretty error bundle (or at least, like, a string-ey error bundle)
-- or the evaluated term

evalTerm :: PlutusTerm -> Either String PlutusTerm
evalTerm t = case errOrRes of
    Left anErr -> Left $ "Failure!\n  Eval Exception: " <> show anErr <> "\n  Logs: " <> show log
    Right res -> pure res
  where
    (errOrRes, log) = evalTerm' t

-- no budget, don't care yet
evalTerm' ::
    PlutusTerm ->
    ( Either
        (Cek.CekEvaluationException Name PLC.DefaultUni PLC.DefaultFun)
        PlutusTerm
    , [Text]
    )
evalTerm' t =
    case Cek.runCek defaultCekParametersForTesting Cek.counting Cek.logEmitter t of
        (errOrRes, _, logs) -> (errOrRes, logs)

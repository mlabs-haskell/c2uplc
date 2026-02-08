module Main (main) where

import Covenant.CodeGen (compile, evalTerm)
import Covenant.JSON (deserializeCompilationUnit)
import Data.Set qualified as Set
import Options.Applicative
  ( ArgumentFields,
    InfoMod,
    Mod,
    ParserInfo,
    ReadM,
    argument,
    execParser,
    fullDesc,
    header,
    help,
    helper,
    info,
    metavar,
    progDesc,
    str,
    (<**>),
  )
import PlutusCore qualified as PLC
import PlutusCore.Annotation (SrcSpans (SrcSpans))
import PlutusLedgerApi.Envelope (writeCodeEnvelope)
import PlutusTx.Code (CompiledCodeIn (DeserializedCode))
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (addExtension, dropExtension, isValid, takeExtension)
import UntypedPlutusCore qualified as UPLC

main :: IO ()
main = do
  path <- execParser parserInfo
  putStrLn $ "Attempting to compile compilation unit at: " <> path
  cu <- deserializeCompilationUnit path
  putStrLn "Compilation unit validated"
  putStrLn "Generating UPLC"
  case compile cu of
    Left err -> do
      putStrLn "Code generation failed"
      putStrLn "Reason:"
      print err
      exitFailure
    Right t -> do
      putStrLn "Generated"
      putStrLn "Pre-evaluating"
      case evalTerm t of
        Left err -> do
          putStrLn "Pre-evaluation failed"
          putStrLn " Reason:"
          putStrLn err
          exitFailure
        Right evaluated -> do
          putStrLn "Pre-evaluation succeeded"
          let outputFilePath = addExtension (dropExtension path <> "-compiled") "json"
          putStrLn $ "Writing Plutus envelope to " <> outputFilePath
          withNamedDB <- case UPLC.deBruijnTerm evaluated of
            Left err -> do
              putStrLn "DeBruijn conversion of named terms failed"
              putStrLn "If you see this, it is definitely an internal error: please report it!"
              print err
              exitFailure
            Right result -> pure result
          let asProgram = UPLC.Program () PLC.latestVersion withNamedDB
          let compiled = DeserializedCode (fmap (const (SrcSpans Set.empty)) asProgram) Nothing mempty
          writeCodeEnvelope "Generated with c2uplc" compiled outputFilePath
          putStrLn "Output successful"
          exitSuccess

-- Helpers

parserInfo :: ParserInfo FilePath
parserInfo = info (argument parseFP mods <**> helper) infoMod
  where
    parseFP :: ReadM FilePath
    parseFP = do
      raw <- str
      if isValid raw
        then case takeExtension raw of
          ".json" -> pure raw
          _ -> fail "not a JSON file"
        else fail "not a valid file path"
    mods :: Mod ArgumentFields FilePath
    mods =
      help "Path to a JSON file containing a serialized Covenant IR"
        <> metavar "INPUT_FILE"
    infoMod :: InfoMod FilePath
    infoMod = fullDesc <> progDesc "Code generator for Covenant IR into UPLC" <> header "c2uplc"

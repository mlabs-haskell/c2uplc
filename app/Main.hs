module Main (main) where

import Covenant.CodeGen (compileIO)
import Options.Applicative (
    ArgumentFields,
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
import System.FilePath (isValid, takeExtension)

main :: IO ()
main = execParser parserInfo >>= compileIO

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

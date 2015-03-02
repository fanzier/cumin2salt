{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main where

import           FunLogic.Core.ModBuilder         (importUnqualified)
import qualified Language.CuMin.ModBuilder        as CM
import           Language.CuMin.Prelude           (preludeModule)
import           Language.CuminToSalt.Translation (cuminToSalt, filterPrelude)
import qualified Language.SaLT.Pretty             as SP
import           Options.Applicative
import qualified Text.PrettyPrint.ANSI.Leijen     as PP

data Options = Options
  { inputFile   :: String
  , outputFile  :: String
  , withPrelude :: Bool
  }

main :: IO ()
main = execParser opts >>= act
  where
  opts = info (helper <*> optionParser)
    $ fullDesc
    <> progDesc "Translate a CuMin program (INPUT) to an equivalent SaLT program."
    <> header "CuMin to SaLT translation"

optionParser :: Parser Options
optionParser = Options
  <$> argument str (metavar "INPUT" <> help "the CuMin input file")
  <*> strOption (short 'o' <> metavar "OUTPUT" <> value "Out.cumin" <> help "the SaLT output file")
  <*> switch (long "with-prelude" <> help "whether to include prelude functions in output")

act :: Options -> IO ()
act (Options { inputFile, outputFile, withPrelude }) =
  CM.buildModuleFromFile inputFile >>= \case
    Left msg -> print msg
    Right modul -> case importUnqualified modul preludeModule of
      Left conflicts -> putStrLn "Conflicts with names in Prelude: " >> print conflicts
      Right modulWithPrelude ->
        writeFile outputFile
          . flip PP.displayS ""
          . PP.renderPretty 0.7 80
          . PP.plain
          . SP.prettyModule
          . (if withPrelude then id else filterPrelude)
          . cuminToSalt
          $ modulWithPrelude

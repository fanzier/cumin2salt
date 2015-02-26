{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main where

import           FunLogic.Core.ModBuilder         (importUnqualified)
import qualified Language.CuMin.ModBuilder        as CM
import           Language.CuMin.Prelude           (preludeModule)
import           Language.CuminToSalt.Translation (cuminToSalt, filterPrelude)
import qualified Language.SaLT.Pretty             as SP
import           Options.Applicative

data Options = Options
  { inputFile :: String
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

act :: Options -> IO ()
act (Options { inputFile }) =
  CM.buildModuleFromFile inputFile >>= \case
    Left msg -> print msg
    Right modul -> case importUnqualified modul preludeModule of
      Left conflicts -> putStrLn "Conflicts with names in Prelude: " >> print conflicts
      Right modulWithPrelude ->
        SP.displayPretty 80
        . SP.prettyModule
        . cuminToSalt
        $ modulWithPrelude

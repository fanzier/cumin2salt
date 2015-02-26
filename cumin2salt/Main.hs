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
  <*> switch ( long "with-prelude" <> help "whether to include prelude functions in output")

act :: Options -> IO ()
act (Options { inputFile, withPrelude }) =
  CM.buildModuleFromFile inputFile >>= \case
    Left msg -> print msg
    Right modul -> case importUnqualified modul preludeModule of
      Left conflicts -> putStrLn "Conflicts with names in Prelude: " >> print conflicts
      Right modulWithPrelude ->
        SP.displayPretty 80
        . SP.prettyModule
        . (if withPrelude then id else filterPrelude)
        . cuminToSalt
        $ modulWithPrelude

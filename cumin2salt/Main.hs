{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main where

import           Data.Default.Class
import qualified Data.Map                         as M
import           FunLogic.Core.ModBuilder         (importUnqualified)
import qualified Language.CuMin.AST               as C
import qualified Language.CuMin.ModBuilder        as CM
import           Language.CuMin.Prelude           (preludeModule)
import qualified Language.CuMin.TypeChecker       as CT
import           Language.CuminToSalt
import qualified Language.SaLT.Pretty             as SP
import           Options.Applicative
import qualified Text.PrettyPrint.ANSI.Leijen     as PP

data Options = Options
  { inputFile   :: String
  , outputFile  :: String
  , doSimplify  :: Bool
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
  <*> strOption (short 'o' <> metavar "OUTPUT" <> value "Out.salt" <> help "the SaLT output file (default: Out.salt)")
  <*> switch (short 's' <> long "simplify" <> help "whether to simplify the output")
  <*> switch (long "with-prelude" <> help "whether to include prelude functions in output")

act :: Options -> IO ()
act (Options { inputFile, outputFile, doSimplify, withPrelude }) =
  checkFile inputFile >>= \case
    Nothing -> putStrLn $ "\nLoading `" ++ inputFile ++ "` failed."
    Just modulWithPrelude ->
      writeFile outputFile
      . flip PP.displayS ""
      . PP.renderPretty 0.7 80
      . PP.plain
      . SP.prettyModule
      . (if withPrelude then id else filterPrelude)
      . cuminToSalt doSimplify
      $ modulWithPrelude

checkFile :: FilePath -> IO (Maybe C.Module)
checkFile cuminFile =
  CM.buildModuleFromFile cuminFile >>= \case
    Left msg -> PP.putDoc (PP.pretty msg) >> return Nothing
    Right modul -> case importUnqualified modul preludeModule of
      Left (adtConflicts, functionConflicts) -> do
        putStrLn "Some names in the module conflict with prelude names:"
        mapM_ (putStrLn . fst) (M.toList adtConflicts)
        mapM_ (putStrLn . fst) (M.toList functionConflicts)
        return Nothing
      Right modulWithPrelude -> case CT.evalTC (CT.checkModule modulWithPrelude) def def of
        Left msg -> PP.putDoc (PP.pretty msg) >> return Nothing
        Right () -> return $ Just modulWithPrelude

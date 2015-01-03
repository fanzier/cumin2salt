{-# LANGUAGE LambdaCase #-}
module Main where

import           FunLogic.Core.ModBuilder         (importUnqualified)
import qualified Language.CuMin.ModBuilder        as CM
import           Language.CuMin.Prelude           (preludeModule)
import           Language.CuminToSalt.Translation (cuminToSalt)
import qualified Language.SaLT.Pretty             as SP
import           System.Environment               (getArgs)

main :: IO ()
main = do
  [cuminFile] <- getArgs
  CM.buildModuleFromFile cuminFile >>= \case
    Left msg -> print msg
    Right modul -> case importUnqualified modul preludeModule of
      Left conflicts -> putStrLn "Conflicts with names in Prelude: " >> print conflicts
      Right modulWithPrelude -> SP.displayPretty 80 . SP.prettyModule . cuminToSalt $ modulWithPrelude

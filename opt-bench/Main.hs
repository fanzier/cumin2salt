{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE QuasiQuotes #-}
module Main where

import           Control.Applicative
import           Control.DeepSeq                       (NFData (..))
import qualified Control.Monad.Logic                   as Logic
import           Criterion.Main
import           Data.Default.Class
import qualified Data.Map                              as M
import           Data.Maybe                            (mapMaybe)
import           Data.Traversable
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin                        as Cumin
import           Language.CuminToSalt
import qualified Language.SaLT                         as Salt
import qualified Language.SaLT.Semantics.Denotational  as SD
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

-- | Stores the result of an evaluation.
-- CuMin and SalT values are converted to this type for comparison.
data Result = Constructor Cumin.DataConName [Result] | Literal Integer
  deriving (Show, Eq)

-- | Allows to evaluate the computation results completely.
instance NFData Result where
  rnf (Constructor _ rs) = rnf rs
  rnf (Literal i) = rnf i

-- | Monad with depth-first-search characteristics.
type DFSMonad = Search.UnFair Logic.Logic
-- | Monad with breadth-first-search characteristics.
type BFSMonad = Logic.Logic

main :: IO ()
main = do
  Just cuminModul <- checkFile "cumin/Benchmark.cumin"
  let noOptMod = cuminToSalt False cuminModul
  let optMod = cuminToSalt True cuminModul
  defaultMain $ map (benchPerformance noOptMod optMod)
    [ ("AddPeano", [Salt.saltExp|benchAdd<::>|])
    , ("SubPeano", [Salt.saltExp|benchSub<::>|])
    , ("DivPeano", [Salt.saltExp|benchDiv<::>|])
    , ("FibNat", [Salt.saltExp|benchFib<::>|])
    , ("Last", [Salt.saltExp|benchLast<::>|])
    , ("PermSort", [Salt.saltExp|benchSort<::>|])
    ]
  where
  benchPerformance noOptMod optMod (descr, exp) = bgroup descr
    [ bench "NoOpt" $ nf (saltEvaluateFirst noOptMod) exp
    , bench "Opt" $ nf (saltEvaluateFirst optMod) exp
    ]

-- | Evaluates the SaLT expression and returns the first result.
-- Only the first result without any bottoms is returned.
-- Evaluation uses breadth-first search without pruning.
saltEvaluateFirst :: Salt.Module -> Salt.Exp -> Result
saltEvaluateFirst modul e = head $ mapMaybe saltToResult $ Search.observeAll $ ensureSet (SD.runEval (SD.eval e) modul SD.StepInfinity id :: SD.Value BFSMonad)
  where
  ensureSet (SD.VSet vs _) = vs
  ensureSet _ = error "result not a set"

-- | Converts a SaLT Value to a Result if it contains no bottoms or partial function applications.
saltToResult :: SD.Value n -> Maybe Result
saltToResult = \case
  SD.VCon c vs _ -> Constructor c <$> traverse saltToResult vs
  SD.VNat i -> Just $ Literal i
  _ -> Nothing

checkFile :: FilePath -> IO (Maybe Cumin.Module)
checkFile cuminFile =
  Cumin.buildModuleFromFile cuminFile >>= \case
      Left msg -> print msg >> return Nothing
      Right modul ->
        case Cumin.importUnqualified modul Cumin.preludeModule of
          Left (adtConflicts, functionConflicts) -> do
            putStrLn "Some names in the module conflict with prelude names:"
            mapM_ (putStrLn . fst) (M.toList adtConflicts)
            mapM_ (putStrLn . fst) (M.toList functionConflicts)
            return Nothing
          Right modulWithPrelude -> case Cumin.evalTC (Cumin.checkModule modulWithPrelude) def def of
            Left msg -> PP.putDoc (PP.pretty msg) >> return Nothing
            Right () -> return $ Just modulWithPrelude

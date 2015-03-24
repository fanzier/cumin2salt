{-# LANGUAGE LambdaCase  #-}
module Main where

import           Control.Applicative
import qualified Control.Monad.Logic                   as Logic
import           Data.Default.Class
import           Data.Function
import qualified Data.Map                              as M
import           Data.Maybe                            (mapMaybe)
import           Data.Traversable
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin                        as Cumin
import qualified Language.CuMin.Semantics.Denotational as CD
import           Language.CuminToSalt
import qualified Language.SaLT                         as Salt
import qualified Language.SaLT.Semantics.Denotational  as SD
import           Test.Hspec
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

-- | Stores the result of an evaluation.
-- CuMin and SalT values are converted to this type for comparison.
data Result = Constructor Cumin.DataConName [Result] | Literal Integer
  deriving (Show, Eq)

-- | Monad with depth-first-search characteristics.
type DFSMonad = Search.UnFair Logic.Logic
-- | Monad with breadth-first-search characteristics.
type BFSMonad = Logic.Logic

main :: IO ()
main = hspec spec

-- | Specifies that the translated CuMin functions give the same results as the original ones.
-- This is checked with and without optimizations enabled.
spec :: Spec
spec =
  describe "CuMin/SaLT equivalence tests" $ do
    Just cuminModul <- runIO $ checkFile "cumin/TestCases.cumin"
    let saltModul1 = cuminToSalt True cuminModul
    let saltModul2 = cuminToSalt False cuminModul
    mapM_ (testEquiv cuminModul) [("unoptimized code", saltModul1), ("optimized code", saltModul2)]
  where
  testEquiv cuminModul (descr, saltModul) = describe descr $
    mapM_ shouldBeEquivalent
      [ ("mapTest", shouldBe)
      , ("andTest", shouldBe)
      , ("failedTest", shouldBe)

      , ("testDoubleCoin", shouldBe)
      , ("testCoinPlusCoin", shouldBe)
      , ("testMaybeDouble1", shouldBe)
      , ("testMaybeDouble2", shouldBe)

      , ("testSub", shouldBe `on` head)
      , ("testTimes", shouldBe `on` head)
      , ("testDiv", shouldBe `on` head)

      , ("testLast", shouldBe `on` head)
      , ("testSort", shouldBe `on` head)

      , ("minusTest", shouldBe `on` head)
      , ("timesTest", shouldBe `on` head)

      , ("caseTest1", shouldBe)
      , ("caseTest2", shouldBe)
      , ("caseTest3", shouldBe)
      , ("letTest", shouldBe)
      ]
    where
    -- | Checks whether a given function gives equivalent results with respect to a given condition.
    shouldBeEquivalent :: (String, [Result] -> [Result] -> Expectation) -> Spec
    shouldBeEquivalent (function, condition) = it function $ condition
      (cuminEvaluate cuminModul (Cumin.EFun function []))
      (saltEvaluate saltModul (Salt.EFun function []))

-- | Evaluate a CuMin expression in the context of a module to a list of results.
cuminEvaluate :: Cumin.Module -> Cumin.Exp -> [Result]
cuminEvaluate modul e = mapMaybe cuminToResult $ Search.observeAll (CD.runEval (CD.eval e) modul CD.StepInfinity id :: BFSMonad (CD.Value BFSMonad))

-- | Evaluate a SaLT expression in the context of a module to a list of results.
saltEvaluate :: Salt.Module -> Salt.Exp -> [Result]
saltEvaluate modul e = mapMaybe saltToResult $ Search.observeAll $ ensureSet (SD.runEval (SD.eval e) modul SD.StepInfinity id :: SD.Value BFSMonad)
  where
  ensureSet (SD.VSet vs _) = vs
  ensureSet _ = error "result not a set"

-- | Converts a CuMin Value to a Result if it contains no bottoms or partial function applications.
cuminToResult :: CD.Value n -> Maybe Result
cuminToResult = \case
  CD.VCon c vs _ -> Constructor c <$> traverse cuminToResult vs
  CD.VNat i -> Just $ Literal i
  _ -> Nothing

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

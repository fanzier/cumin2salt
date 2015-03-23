{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE QuasiQuotes #-}
module Main where

import           Control.Applicative
import qualified Control.Monad.Logic                   as Logic
import           Data.Default.Class
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
  testEquiv cuminModul (descr, saltModul) = describe descr $ do
    it "mapTest" $ shouldEvaluateToSame (cuminModul, [Cumin.cuminExp|mapTest<::>|]) (saltModul, [Salt.saltExp|mapTest<::>|])
    it "andTest" $ shouldEvaluateToSame (cuminModul, [Cumin.cuminExp|andTest<::>|]) (saltModul, [Salt.saltExp|andTest<::>|])
    it "failedTest" $ shouldEvaluateToSame (cuminModul, [Cumin.cuminExp|failedTest<::>|]) (saltModul, [Salt.saltExp|failedTest<::>|])

shouldEvaluateToSame :: (Cumin.Module, Cumin.Exp) -> (Salt.Module, Salt.Exp) -> Expectation
shouldEvaluateToSame (cm, ce) (sm, se) = cuminEvaluate cm ce `shouldBe` saltEvaluate sm se

cuminEvaluate :: Cumin.Module -> Cumin.Exp -> [Result]
cuminEvaluate modul e = mapMaybe cuminToResult $ Search.observeAll (CD.runEval (CD.eval e) modul CD.StepInfinity id :: BFSMonad (CD.Value BFSMonad))

saltEvaluate :: Salt.Module -> Salt.Exp -> [Result]
saltEvaluate modul e = mapMaybe saltToResult $ Search.observeAll $ ensureSet (SD.runEval (SD.eval e) modul SD.StepInfinity id :: SD.Value BFSMonad)
  where
  ensureSet (SD.VSet vs _) = vs
  ensureSet _ = error "result not a set"

cuminToResult :: CD.Value n -> Maybe Result
cuminToResult = \case
  CD.VCon c vs _ -> Constructor c <$> traverse cuminToResult vs
  CD.VNat i -> Just $ Literal i
  _ -> Nothing

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

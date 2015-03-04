module Language.CuminToSalt where

import           Control.Lens
import qualified Data.Map                           as M
import           FunLogic.Core.AST                  as F
import qualified Language.CuMin.AST                 as C
import           Language.CuMin.Prelude             (preludeModule)
import           Language.CuminToSalt.Analysis
import           Language.CuminToSalt.Optimizations (simplifyModule)
import           Language.CuminToSalt.Renamer
import           Language.CuminToSalt.Translation
import qualified Language.SaLT.AST                  as S

cuminToSalt :: Bool -> C.Module -> S.Module
cuminToSalt simplify
  = evalRenamer
  . internalToSaltModule
  . (if simplify then simplifyModule else id)
  . cModToSMod
  . cuminModuleToInternal

filterPrelude :: S.Module -> S.Module
filterPrelude
  = (modBinds %~ (`M.difference` preludeBinds))
  . (modADTs %~ (`M.difference` preludeADTs))
  where
  preludeBinds = preludeModule^.modBinds
  preludeADTs = preludeModule^.modADTs

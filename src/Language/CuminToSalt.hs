module Language.CuminToSalt where

import           Control.Lens
import qualified Data.Map                           as M
import           FunLogic.Core.AST                  as F
import qualified Language.CuMin.AST                 as C
import           Language.CuMin.Prelude             (preludeModule)
import           Language.CuminToSalt.Optimizations (simplifyModule)
import           Language.CuminToSalt.Renamer
import           Language.CuminToSalt.Translation
import qualified Language.SaLT.AST                  as S

-- | Transform a CuMin module to an equivalent SaLT module.
-- The boolean argument specifies whether the translated code is simplified.
cuminToSalt :: Bool -> C.Module -> S.Module
cuminToSalt simplify
  = evalRenamer
  . internalToSaltModule
  . (if simplify then simplifyModule else id)
  . cModToSMod
  . cuminModuleToInternal

-- | Filter the prelude functions from a SaLT module.
-- Useful since there already is a special prelude for SaLT code that arises from CuMin code.
filterPrelude :: S.Module -> S.Module
filterPrelude
  = (modBinds %~ (`M.difference` preludeBinds))
  . (modADTs %~ (`M.difference` preludeADTs))
  where
  preludeBinds = preludeModule^.modBinds
  preludeADTs = preludeModule^.modADTs

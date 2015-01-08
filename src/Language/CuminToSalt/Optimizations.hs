{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.CuminToSalt.Optimizations where

import           Bound
import           Control.Applicative
import           Control.Lens
import qualified Data.Map                         as M
import           FunLogic.Core.AST                as F
import           Language.CuminToSalt.TypeChecker
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util

simplifyExp :: forall v. Show v => VarEnv v -> SExp v -> SExp v
simplifyExp varEnv e = case transformSubExpressions simplifyExp varEnv e of
  -- First monad law. This one is used all the time.
  SESetBind (SESet x) _ y -> simplifyExp varEnv $ instantiate (const x) y
  -- Second monad law. This almost never fires. Included for completeness
  -- and silly cases like "let y = x in y" which is translated to
  -- "x >>= \y -> { y }" and transformed to "x" as desired.
  SESetBind x _ (Scope (SESet (SEVar (B ())))) -> x
  -- Third monad law. Associating everything to the right enables the first
  -- monad law to optimize more aggressively.
  SESetBind (SESetBind m x f) y g ->
    SESetBind m x (toScope $ SESetBind (fromScope f) y (F <$> g))
  -- Beta reduction. Useful for constructor lambdas.
  SEApp (SELam _ _ x) y -> simplifyExp varEnv $ instantiate (const y) x
  -- Leave everything else untouched.
  ex -> ex

simplifyBinding :: VarEnv VarName -> SBinding VarName -> SBinding VarName
simplifyBinding varEnv = sBindExp %~ simplifyExp varEnv

simplifyModule :: SModule VarName -> SModule VarName
simplifyModule m = m & sModBinds %~ fmap (simplifyBinding initialVarEnv)
  where
  initialVarEnv :: VarEnv VarName
  initialVarEnv = VarEnv
    { _localVar = \v -> error $ "No free variable expected but found: " ++ show v
    , _globalTypes = fmap (view sBindType) $ m^.sModBinds
    , _constructorTypes = M.fromList $ M.toList (m^.sModADTs)
        >>= \(_, a) -> a^.adtConstr
        >>= \c@(ConDecl cName _) -> return (cName, (a, c))
    }

-- * Transform subexpressions

transformSubExpressions
  :: Show v
  => (forall w. Show w => VarEnv w -> SExp w -> SExp w)
  -> VarEnv v -> SExp v -> SExp v
transformSubExpressions t varEnv = \case
  SELam v ty x -> SELam v ty $
    walkScope t (const $ VarInfo v ty) varEnv x
  SESetBind x v y -> let TSet ty = tyCheckSExp varEnv x in
    SESetBind (t varEnv x) v
    (walkScope t (const $ VarInfo v ty) varEnv y)
  SEApp x y -> SEApp (t varEnv x) (t varEnv y)
  SEPrim oper es -> SEPrim oper (map (t varEnv) es)
  SECase x alts -> let ty = tyCheckSExp varEnv x in
    SECase (t varEnv x) $
      map (transformAlt t ty varEnv) alts
  SESet s -> SESet (t varEnv s)
  e -> e

transformAlt
  :: Show v
  => (forall w. Show w => VarEnv w -> SExp w -> SExp w)
  -> Type -> VarEnv v -> Alt SExp v -> Alt SExp v
transformAlt t ty varEnv = enterAlt ty varEnv
  (\b@(VarInfo v _) s -> AVarPat v $ walkScope t (const b) varEnv s)
  (\c bs s ->  let vs = map _vName bs in
   AConPat c vs $ walkScope t (bs !!) varEnv s
  )

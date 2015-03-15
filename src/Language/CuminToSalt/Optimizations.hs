{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.CuminToSalt.Optimizations where

import           Bound
import           Bound.Scope
import           Control.Applicative
import           Control.Lens
import           FunLogic.Core.AST                as F
import           Language.CuminToSalt.TypeChecker
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util

simplifyExp :: forall v. Show v => VarEnv v -> SExp v -> SExp v
simplifyExp varEnv e = case transformSubExpressions simplifyExp varEnv e of
  -- First monad law. This one is used all the time.
  SESetBind (SESet x) f -> simplifyExp varEnv $ SEApp f x
  -- Second monad law. This almost never fires. Included for completeness
  -- and silly cases like "let y = x in y" which is translated to
  -- "x >>= \y -> { y }" and transformed to "x" as desired.
  SESetBind x (SELam _ _ (Scope (SESet (SEVar (B ()))))) -> x
  -- Third monad law. Associating everything to the right enables the first
  -- monad law to optimize more aggressively.
  SESetBind (SESetBind m f) g ->
    let TSet ty = tyCheckSExp varEnv m
    in SESetBind m $ simplifyExp varEnv $
      SELam "arg" ty $ toScope $ SESetBind (SEApp (F <$> f) (return (B ()))) (F <$> g)
  -- Beta reduction. Useful for constructor lambdas.
  SEApp (SELam _ _ x) y | safeToReduce x -> simplifyExp varEnv $ instantiate (const y) x
  -- Eta reduction. Useful for unnecessarily lamdbas by third monad law.
  SELam _ _ (Scope (SEApp f (SEVar (B ())))) | Just f' <- fromConstantScope f -> simplifyExp varEnv f'
  -- Leave everything else untouched.
  ex -> ex
  where
  -- Beta reduction is safe if the bound variable occurs at most once.
  safeToReduce x = length (bindings x) <= 1
  fromConstantScope :: SExp (Var () (SExp v)) -> Maybe (SExp v)
  fromConstantScope t = (>>= id) <$> traverse k t
    where
    k (B _) = Nothing
    k (F a) = Just a

simplifyBinding :: VarEnv Void -> SBinding -> SBinding
simplifyBinding varEnv = sBindExp %~ simplifyExp varEnv

simplifyModule :: SModule -> SModule
simplifyModule m = m & modBinds %~ fmap (simplifyBinding initialVarEnv)
  where
  initialVarEnv :: VarEnv Void
  initialVarEnv = makeInitialVarEnv
    (fmap (view sBindType) $ m^.modBinds)
    (m^.modADTs)

-- * Transform subexpressions

transformSubExpressions
  :: Show v
  => (forall w. Show w => VarEnv w -> SExp w -> SExp w)
  -> VarEnv v -> SExp v -> SExp v
transformSubExpressions t varEnv = \case
  SELam v ty x -> SELam v ty $
    transformScope t (const $ VarInfo v ty) varEnv x
  SESetBind x y -> SESetBind (t varEnv x) (t varEnv y)
  SEApp x y -> SEApp (t varEnv x) (t varEnv y)
  SEPrim oper es -> SEPrim oper (map (t varEnv) es)
  SECase x alts -> let ty = tyCheckSExp varEnv x in
    SECase (t varEnv x) $
      map (transformAlt t ty varEnv) alts
  SESet s -> SESet (t varEnv s)
  e -> e

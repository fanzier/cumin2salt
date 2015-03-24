{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Language.CuminToSalt.TypeChecker where

import           Data.Maybe                 (fromJust)
import           Debug.Trace.LocationTH
import           FunLogic.Core.AST
import qualified Language.CuMin.AST         as C
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util

-- | Type checks a CuMin expression.
tyCheckCExp :: VarEnv v -> CExp v -> Type
tyCheckCExp varEnv = \case
  CEVar v -> _vType $ _localVar varEnv v
  CELet v x s -> reduceScope tyCheckCExp (const $ VarInfo v $ tyCheckCExp varEnv x) varEnv s
  CELetFree v ty s -> reduceScope tyCheckCExp (const $ VarInfo v ty) varEnv s
  CEFailed ty -> ty
  CEFun v tys -> $check . fromJust . instantiateTyDecl tys $ lookupGlobal varEnv v
  CEApp x _ -> let TFun _ ty =  tyCheckCExp varEnv x in ty
  CELit _ -> TNat
  CEPrim oper _ -> case oper of
    C.PrimEq -> TCon "Bool" []
    C.PrimAdd -> TNat
  CECon c tys -> $check . fromJust . instantiateTyDecl tys . conDeclToTyDecl $ lookupConstructor varEnv c
  CECase e alts -> let ty = tyCheckCExp varEnv e in reduceAlt tyCheckCExp ty varEnv (head alts)

-- | Type checks a SaLT expression. Throws an error if it fails.
-- This function is also used as a consistency check during translation.
tyCheckSExp :: VarEnv v -> SExp v -> Type
tyCheckSExp varEnv = \case
  SEVar v -> _vType $ _localVar varEnv v
  SEFun v tys -> $check . fromJust . instantiateTyDecl tys $ lookupGlobal varEnv v
  SELam v ty x -> TFun ty $ reduceScope tyCheckSExp (const $ VarInfo v ty) varEnv x
  SESetBind x y ->
    let TSet xTy = tyCheckSExp varEnv x
        yTy = tyCheckSExp varEnv y
    in case yTy of
      TFun argTy resTy | argTy == xTy -> resTy
      _ -> $failure $ show yTy ++ " doesn't match " ++ show xTy
  SEApp y x ->
    let xTy = tyCheckSExp varEnv x
        yTy = tyCheckSExp varEnv y
    in case yTy of
      TFun argTy resTy | argTy == xTy -> resTy
      _ -> $failure $ show yTy ++ " doesn't match " ++ show xTy
  SELit _ -> TNat
  SEPrim oper es ->
    let tys = map (tyCheckSExp varEnv) es
    in if any (/= head tys) tys then $failure $ show oper ++ show tys else
    case oper of
      C.PrimEq -> TCon "Bool" []
      C.PrimAdd -> TNat
  SECon c tys -> $check . fromJust . instantiateTyDecl tys . conDeclToTyDecl $ lookupConstructor varEnv c
  SESet x -> TSet $ tyCheckSExp varEnv x
  SECase e alts -> let ty = tyCheckSExp varEnv e in reduceAlt tyCheckSExp ty varEnv (head alts)
  SEFailed ty -> ty
  SEUnknown ty -> TSet ty

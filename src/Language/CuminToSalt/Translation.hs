{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Language.CuminToSalt.Translation where

import           Bound
import           Control.Applicative
import           Control.Lens
import           Data.Foldable                      (traverse_)
import           Data.List                          (elemIndex)
import qualified Data.Map                           as M
import           Data.Maybe
import qualified Data.Set                           as Set
import           Debug.Trace.LocationTH
import           FunLogic.Core.AST                  as F
import qualified Language.CuMin.AST                 as C
import           Language.CuminToSalt.Optimizations (simplifyModule)
import           Language.CuMin.Prelude             (preludeModule)
import           Language.CuminToSalt.Renamer
import           Language.CuminToSalt.TypeChecker
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util
import qualified Language.SaLT.AST                  as S
import qualified Language.SaLT.Pretty               as SP

-- * CuMin -> Internal CuMin Representation

cuminExpToInternal :: Set.Set VarName -> C.Exp -> CExp VarName
cuminExpToInternal localVars = \case
  C.EVar v -> if v `Set.member` localVars then CEVar v else CEFun v []
  C.ELet v x y -> CELet v (cuminExpToInternal localVars x) (abstract1 v (cuminExpToInternal (Set.insert v localVars) y))
  C.ELetFree v ty e -> CELetFree v ty (abstract1 v (cuminExpToInternal (Set.insert v localVars) e))
  C.EFailed ty -> CEFailed ty
  C.EFun v tys -> CEFun v tys
  C.EApp x y -> CEApp (cuminExpToInternal localVars x) (cuminExpToInternal localVars y)
  C.ELit l -> CELit l
  C.EPrim oper xs -> CEPrim oper (map (cuminExpToInternal localVars) xs)
  C.ECon c tys -> CECon c tys
  C.ECase e alts -> CECase (cuminExpToInternal localVars e) (map (cuminAltToInternal localVars) alts)

cuminAltToInternal :: Set.Set VarName -> C.Alt -> Alt CExp VarName
cuminAltToInternal localVars (C.Alt p e) = case p of
  PVar v -> AVarPat v (abstract1 v (cuminExpToInternal (Set.insert v localVars) e))
  PCon c vs -> AConPat c vs (abstract (`elemIndex` vs) (cuminExpToInternal (Set.fromList vs `Set.union` localVars) e))

cuminBindingToInternal :: C.Binding -> CBinding
cuminBindingToInternal b = CBinding
  { _cBindName = b^.C.bindingName
  , _cBindType = b^.C.bindingType
  , _cBindArgs = b^.C.bindingArgs
  , _cBindExp = checkedBoundExp
  , _cBindSrc = b^.C.bindingSrc
  }
  where
  checkedBoundExp = fromMaybe failureFreeVars (closed boundExp)
  failureFreeVars = $failure $ "Bug: Binding unexpectedly contains free variables: " ++ show boundExp
  boundExp = abstract (`elemIndex` bindArgs) $ cuminExpToInternal (Set.fromList bindArgs) $ b^.C.bindingExpr
  bindArgs = b^.C.bindingArgs

cuminModuleToInternal :: C.Module -> CModule
cuminModuleToInternal = fmap cuminBindingToInternal

-- * Internal CuMin Representation -> Internal SaLT Representation

cExpToSExp :: Show v => VarEnv v -> CExp v -> SExp v
cExpToSExp varEnv = \case
  CEVar v -> SESet (SEVar v)
  CELet v x s ->
    let
      x' = cExpToSExp varEnv x
      TSet ty = tyCheckSExp varEnv x'
      s' = transformScope cExpToSExp (const $ VarInfo v ty) varEnv s
    in SESetBind x' v s'
  CELetFree v ty s ->
    let s' = transformScope cExpToSExp (const $ VarInfo v ty) varEnv s
    in SESetBind (SEUnknown ty) v s'
  CEFailed ty -> SESet (SEFailed ty)
  CEFun v tys -> SEFun v tys
  CEApp x y ->
    let
      x' = cExpToSExp varEnv x
      y' = cExpToSExp varEnv y
    in SESetBind x' "fun" (toScope $ SESetBind (F <$> y') "arg" (toScope $ SEApp (return (F (B ()))) (return (B ()))))
  CELit lit -> SESet (SELit lit)
  CEPrim oper es ->
    let
      es' = map (cExpToSExp varEnv) es
    in makePrimExp es' oper
  CECon c tys -> makeConstructorLambda c tys
  CECase e alts ->
    let
      e' = cExpToSExp varEnv e
      TSet ty = tyCheckSExp varEnv e'
      alts' = map (transformAlt cExpToSExp ty varEnv) alts
    in SESetBind e' "scrutinee" (Scope $ SECase (return (B ())) (map (fmap (F . return)) alts'))
  where
  makeConstructorLambda :: Show v => VarName -> [Type] -> SExp v
  makeConstructorLambda c tyInsts =
    let
      conDecl = lookupConstructor varEnv c
      tyDecl = conDeclToTyDecl conDecl
      ty = cTypeToSType . $check . fromJust $ instantiateTyDecl tyInsts tyDecl
      (tys, _) = extractSetArgs ty
      scope :: SExp w -> [Type] -> SExp w
      scope e [] = SESet e
      scope e (t:ts) = SESet . SELam "conArg" t $ Scope (scope (SEApp (F . return <$> e) (return (B ()))) ts)
    in scope (SECon c tyInsts) tys
  makePrimExp :: Show v => [SExp v] -> C.PrimOp -> SExp v
  makePrimExp exps oper = go [] exps
    where
    go :: Show v => [SExp v] -> [SExp v] -> SExp v
    go fs = \case
      [] -> SESet $ SEPrim oper (reverse fs)
      x:xs -> SESetBind x "primOpArg" (toScope $ go (return (B ()) : map (fmap F) fs) (map (fmap F) xs))

cBindToSBind :: VarEnv Void -> CBinding -> SBinding
cBindToSBind varEnv b = SBinding
  { _sBindName = b^.cBindName
  , _sBindType = TyDecl q c (TSet tySalt)
  , _sBindExp = makeLambda
      (zip3 [0..] (b^.cBindArgs) indexedTys)
      varEnv
      (b^.cBindExp)
  , _sBindSrc = b^.cBindSrc
  }
  where
  TyDecl q c tyCumin = b^.cBindType
  tySalt = cTypeToSType tyCumin
  (indexedTys, _) = extractSetArgs tySalt
  makeLambda :: Show v => [(Int, VarName, Type)] -> VarEnv v -> Scope Int CExp v -> SExp v
  makeLambda [] vars s = cExpToSExp vars ($check $ fromJust $ extractFromConstantScope s)
  makeLambda ((i, v, ty):tys) vars s
    = SESet . SELam v ty $
      transformScope
        (makeLambda tys)
        (const $ VarInfo v ty)
        vars
        (abstractInScope (\j -> if i == j then Just () else Nothing) s)

cModToSMod :: CModule -> SModule
cModToSMod m = translateADTs $ cBindToSBind initialVarEnv <$> m
  where
  initialVarEnv :: VarEnv Void
  initialVarEnv = makeInitialVarEnv
    (fmap (transformTyDecl . view cBindType) $ m^.modBinds)
    (m^.modADTs)
  transformTyDecl (TyDecl q c ty) = TyDecl q c (cTypeToSType ty)
  translateADTs = modADTs %~ fmap cAdtToSAdt

cAdtToSAdt :: ADT -> ADT
cAdtToSAdt = adtConstr.each %~ translateConDecl
  where
  translateConDecl (ConDecl c tys) = ConDecl c (map cTypeToSType tys)

-- * Internal SaLT Representation -> SaLT

internalToSalt :: VarEnv v -> SExp v -> Renamer S.Exp
internalToSalt varEnv = \case
  SEVar v -> return . S.EVar $ _vName $ _localVar varEnv v
  SEFun v tys -> return $ S.EFun v tys
  SELam v ty x -> withLocal v $ do
      Just j <- resolve v
      let w = makeVar v j
      S.ELam w ty <$> reduceScope internalToSalt (const $ VarInfo w ty) varEnv x
  SESetBind x v y -> S.EPrim S.PrimBind <$> do
    x' <- internalToSalt varEnv x
    let TSet ty = tyCheckSExp varEnv x
    y' <- internalToSalt varEnv (SELam v ($checkTrace (show (tyCheckSExp varEnv x) ++ "\n\n" ++ show (SP.prettyExp x')) ty) y)
    return [x', y']
  SEApp x y -> S.EApp <$> internalToSalt varEnv x <*> internalToSalt varEnv y
  SELit l -> return $ S.ELit l
  SEPrim oper es -> S.EPrim (cuminToSaltOp oper) <$> traverse (internalToSalt varEnv) es
  SECon n tys -> return $ S.ECon n tys
  SESet x -> S.ESet <$> internalToSalt varEnv x
  SECase x alts -> do
    x' <- internalToSalt varEnv x
    let ty = tyCheckSExp varEnv x
    y' <- traverse (altToSalt varEnv ty) alts
    return $ S.ECase x' y'
  SEFailed ty -> return $ S.EFailed ty
  SEUnknown ty -> return $ S.EUnknown ty

altToSalt :: VarEnv v -> Type -> Alt SExp v -> Renamer S.Alt
altToSalt varEnv ty =
  enterAlt ty varEnv
    -- Variable pattern:
    (\(VarInfo v vTy) x -> withLocal v $ do
      Just w <- resolveName v
      e <- reduceScope internalToSalt (const $ VarInfo w vTy) varEnv x
      return $ S.Alt (PVar w) e
    )
    -- Constructor pattern:
    (\c bs x ->
      let vs = map _vName bs
          tys = map _vType bs
      in withLocals vs $ do
        ws <- traverse ($check . fmap fromJust . resolveName) vs
        e <- reduceScope internalToSalt (\i -> VarInfo (ws !! i) (tys !! i)) varEnv x
        return $ S.Alt (PCon c ws) e
    )

internalToSaltBinding :: VarEnv Void -> SBinding -> Renamer S.Binding
internalToSaltBinding varEnv b = fillBinding <$> internalToSalt varEnv (b^.sBindExp)
  where
  fillBinding e = S.Binding
    { S._bindingName = b^.sBindName
    , S._bindingExpr = e
    , S._bindingType = b^.sBindType
    , S._bindingSrc = b^.sBindSrc
    }

internalToSaltModule :: SModule -> Renamer S.Module
internalToSaltModule m = do
  traverse_ addGlobal (M.keys $ m^.modBinds)
  traverse (internalToSaltBinding initialVarEnv) m
  where
  initialVarEnv :: VarEnv Void
  initialVarEnv = makeInitialVarEnv
    (fmap (view sBindType) $ m^.modBinds)
    (m^.modADTs)

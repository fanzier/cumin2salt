{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Language.CuminToSalt.Translation where

import           Bound
import           Control.Applicative
import           Control.Arrow (second)
import           Control.Lens
import           Data.List                          (elemIndex)
import           Data.Maybe
import qualified Data.Set                           as Set
import           Debug.Trace.LocationTH
import           FunLogic.Core.AST                  as F
import qualified Language.CuMin.AST                 as C
import           Language.CuminToSalt.Renamer
import           Language.CuminToSalt.TypeChecker
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util
import qualified Language.SaLT.AST                  as S

-- * CuMin -> Internal CuMin Representation

-- | Convert a CuMin expression to the internal nameless representation.
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

-- | Translate a CuMin case alternative to the internal representation.
cuminAltToInternal :: Set.Set VarName -> C.Alt -> Alt CExp VarName
cuminAltToInternal localVars (C.Alt p e) = case p of
  PVar v -> AVarPat v (abstract1 v (cuminExpToInternal (Set.insert v localVars) e))
  PCon c vs -> AConPat c vs (abstract (`elemIndex` vs) (cuminExpToInternal (Set.fromList vs `Set.union` localVars) e))

-- | Translate a CuMin function definition to the internal representation.
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

-- | Translate a CuMin module to the internal representation.
cuminModuleToInternal :: C.Module -> CModule
cuminModuleToInternal = fmap cuminBindingToInternal

-- * Internal CuMin Representation -> Internal SaLT Representation
-- This is were the actual translation takes place.

-- | Translate a CuMin expression to SaLT, in the internal representation.
cExpToSExp :: Show v => VarEnv v -> CExp v -> SExp v
cExpToSExp varEnv = \case
  CEVar v -> SESet (SEVar v)
  CELet v x s ->
    let
      x' = cExpToSExp varEnv x
      TSet ty = tyCheckSExp varEnv x'
      s' = transformScope cExpToSExp (const $ VarInfo v ty) varEnv s
    in SESetBind x' (SELam v ty s')
  CELetFree v ty s ->
    let s' = transformScope cExpToSExp (const $ VarInfo v ty) varEnv s
    in SESetBind (SEUnknown ty) (SELam v ty s')
  CEFailed ty -> SESet (SEFailed ty)
  CEFun v tys -> SEFun v tys
  CEApp x y ->
    let
      x' = cExpToSExp varEnv x
      TSet xTy = $check $ tyCheckSExp varEnv x'
      y' = cExpToSExp varEnv y
      TSet yTy = $check $ tyCheckSExp varEnv y'
    in SESetBind x' $ SELam "fun" xTy $ toScope $ SESetBind (F <$> y') $ SELam "arg" yTy $ toScope $ SEApp (return . F $ B ()) (return $ B ())
  CELit lit -> SESet (SELit lit)
  CEPrim oper es ->
    let
      es' = map (cExpToSExp varEnv) es
      typedEs = map (\e -> ($check $ let TSet ty = tyCheckSExp varEnv e in ty, e)) es'
    in makePrimExp typedEs oper
  CECon c tys -> makeConstructorLambda c tys
  CECase e alts ->
    let
      e' = cExpToSExp varEnv e
      TSet ty = tyCheckSExp varEnv e'
      alts' = map (transformAlt cExpToSExp ty varEnv) alts
    in SESetBind e' $ SELam "scrutinee" ty $ Scope $ SECase (return (B ())) (map (fmap (F . return)) alts')
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
  makePrimExp :: Show v => [(Type, SExp v)] -> C.PrimOp -> SExp v
  makePrimExp exps oper = go [] exps
    where
    go :: Show v => [SExp v] -> [(Type, SExp v)] -> SExp v
    go fs = \case
      [] -> SESet $ SEPrim oper (reverse fs)
      (ty,x):xs -> SESetBind x $ SELam "primOpArg" ty $ toScope $ go (return (B ()) : map (fmap F) fs) (map (second (fmap F)) xs)

-- | Translate a CuMin binding to SaLT, in the internal representation.
cBindToSBind :: VarEnv Void -> CBinding -> SBinding
cBindToSBind varEnv b = SBinding
  { _sBindName = b^.cBindName
  , _sBindType = tyDecl
  , _sBindExp = makeLambda
      (zip3 [0..] (b^.cBindArgs) indexedTys)
      varEnv
      (b^.cBindExp)
  , _sBindSrc = b^.cBindSrc
  }
  where
  tyDecl@(TyDecl _ _ (TSet tySalt)) = translateTyDecl (b^.cBindType)
  (indexedTys, _) = extractSetArgs tySalt
  -- | Create the set and lambda wrappers for a translated SaLT function: { \x -> { \y -> { ... } } }
  makeLambda :: Show v => [(Int, VarName, Type)] -> VarEnv v -> Scope Int CExp v -> SExp v
  makeLambda [] vars s = cExpToSExp vars ($checkTrace (show s) $ fromJust $ extractFromConstantScope s)
  makeLambda ((i, v, ty):tys) vars s
    = SESet . SELam v ty $
      transformScope
        (makeLambda tys)
        (const $ VarInfo v ty)
        vars
        (abstractInScope (\j -> if i == j then Just () else Nothing) s)

-- | Translate a CuMin module to SaLT, in the internal representation.
cModToSMod :: CModule -> SModule
cModToSMod m = translateADTs $ cBindToSBind initialVarEnv <$> m
  where
  initialVarEnv :: VarEnv Void
  initialVarEnv = makeInitialVarEnv
    (fmap (translateTyDecl . view cBindType) $ m^.modBinds)
    (m^.modADTs)

-- | Translate a CuMin type declaration to the corresponding declaration in SaLT.
translateTyDecl :: TyDecl -> TyDecl
translateTyDecl (TyDecl q c ty) = TyDecl q c (TSet (cTypeToSType ty))

-- | Translate a CuMin type to the corresponding SaLT type required by the translation.
cTypeToSType :: Type -> Type
cTypeToSType = \case
  TVar a -> TVar a
  TFun s t -> TFun (cTypeToSType s) (TSet $ cTypeToSType t)
  TCon c tys -> TCon c (map cTypeToSType tys)

-- Translate an ADT from CuMin to SaLT.
translateADTs :: CoreModule b -> CoreModule b
translateADTs = modADTs %~ fmap cAdtToSAdt
  where
  cAdtToSAdt :: ADT -> ADT
  cAdtToSAdt = adtConstr.each %~ translateConDecl
    where
    translateConDecl (ConDecl c tys) = ConDecl c (map cTypeToSType tys)

-- * Internal SaLT Representation -> SaLT
-- The translation from the internal nameless representation to SaLT
-- uses the renamer to generate fresh names.

-- | Translate the internal nameless SaLT expression to the actual SaLT expression type.
-- This renames variables, making the names unique.
internalToSalt :: VarEnv v -> SExp v -> Renamer S.Exp
internalToSalt varEnv = \case
  SEVar v -> return . S.EVar $ _vName $ _localVar varEnv v
  SEFun v tys -> return $ S.EFun v tys
  SELam v ty x -> withLocal v $ do
      Just j <- resolve v
      let w = makeVar v j
      S.ELam w ty <$> reduceScope internalToSalt (const $ VarInfo w ty) varEnv x
  SESetBind x y -> S.EPrim S.PrimBind <$> do
    x' <- internalToSalt varEnv x
    y' <- internalToSalt varEnv y
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

-- | The same renaming for case alternatives.
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

-- | Translate the internal SaLT representation of top-level definitions to the regular one.
internalToSaltBinding :: VarEnv Void -> SBinding -> Renamer S.Binding
internalToSaltBinding varEnv b = fillBinding <$> internalToSalt varEnv (b^.sBindExp)
  where
  fillBinding e = S.Binding
    { S._bindingName = b^.sBindName
    , S._bindingExpr = e
    , S._bindingType = b^.sBindType
    , S._bindingSrc = b^.sBindSrc
    }

-- | Translate the internal representation of SaLT modules to the regular one.
internalToSaltModule :: SModule -> Renamer S.Module
internalToSaltModule m = traverse (internalToSaltBinding initialVarEnv) m
  where
  initialVarEnv :: VarEnv Void
  initialVarEnv = makeInitialVarEnv
    (fmap (view sBindType) $ m^.modBinds)
    (m^.modADTs)

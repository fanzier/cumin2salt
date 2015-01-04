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
import           Data.Foldable                    (traverse_)
import           Data.List                        (elemIndex)
import qualified Data.Map                         as M
import           Data.Maybe                       (fromJust)
import           Debug.Trace.LocationTH
import           FunLogic.Core.AST                as F
import qualified Language.CuMin.AST               as C
import           Language.CuminToSalt.Renamer
import           Language.CuminToSalt.TypeChecker
import           Language.CuminToSalt.Types
import           Language.CuminToSalt.Util
import qualified Language.SaLT.AST                as S
import qualified Language.SaLT.Pretty             as SP

cuminToSalt :: C.Module -> S.Module
cuminToSalt
  = evalRenamer
  . internalToSaltModule
  . cModToSMod
  . cuminModuleToInternal

-- * CuMin -> Internal CuMin Representation

cuminExpToInternal :: C.Exp -> CExp VarName
cuminExpToInternal = \case
  C.EVar v -> CEVar v
  C.ELet v x y -> CELet v (cuminExpToInternal x) (abstract1 v (cuminExpToInternal y))
  C.ELetFree v ty e -> CELetFree v ty (abstract1 v (cuminExpToInternal e))
  C.EFailed ty -> CEFailed ty
  C.EFun v tys -> CEFun v tys
  C.EApp x y -> CEApp (cuminExpToInternal x) (cuminExpToInternal y)
  C.ELit l -> CELit l
  C.EPrim oper xs -> CEPrim oper (map cuminExpToInternal xs)
  C.ECon c tys -> CECon c tys
  C.ECase e alts -> CECase (cuminExpToInternal e) (map cuminAltToInternal alts)

cuminAltToInternal :: C.Alt -> Alt CExp VarName
cuminAltToInternal (C.Alt p e) = case p of
  PVar v -> AVarPat v (abstract1 v (cuminExpToInternal e))
  PCon c vs -> AConPat c vs (abstract (`elemIndex` vs) (cuminExpToInternal e))

cuminBindingToInternal :: C.Binding -> CBinding VarName
cuminBindingToInternal b = CBinding
  { _cBindName = b^.C.bindingName
  , _cBindType = b^.C.bindingType
  , _cBindArgs = b^.C.bindingArgs
  , _cBindExpr = boundExp
  }
  where
  boundExp = assert' isClosed $
    abstract (`elemIndex` (b^.C.bindingArgs)) $ cuminExpToInternal $ b^.C.bindingExpr

cuminModuleToInternal :: C.Module -> CModule VarName
cuminModuleToInternal m = CModule
  { _cModADTs = m^.modADTs
  , _cModBinds = cuminBindingToInternal <$> m^.modBinds
  , _cModName = m^.modName
  }

-- * Internal CuMin Representation -> Internal SaLT Representation

cExpToSExp :: Show v => VarEnv v -> CExp v -> SExp v
cExpToSExp varEnv = \case
  CEVar v -> SESet (SEVar v)
  CELet v x s ->
    let
      x' = cExpToSExp varEnv x
      TSet ty = tyCheckSExp varEnv x'
      s' = walkScope cExpToSExp (const $ VarInfo v ty) varEnv s
    in SESetBind x' v s'
  CELetFree v ty s ->
    let s' = walkScope cExpToSExp (const $ VarInfo v ty) varEnv s
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
      alts' = map (cAltToSAlt ty varEnv cExpToSExp) alts
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
    go fs es = case es of
      [] -> SESet $ SEPrim oper (reverse fs)
      x:xs -> SESetBind x "primOpArg" (toScope $ go (return (B ()) : map (fmap F) fs) (map (fmap F) xs))

cAltToSAlt
  :: (Monad f, Monad g, Show v)
  => Type
  -> VarEnv v
  -> (forall w. Show w => VarEnv w -> f w -> g w)
  -> Alt f v
  -> Alt g v
cAltToSAlt ty varEnv te =
  enterAlt ty varEnv
    (\b@(VarInfo v _) x ->
      AVarPat v $ walkScope te (const b) varEnv x
    )
    (\c bs x -> let vs = map _vName bs in
      AConPat c vs $ walkScope te (bs !!) varEnv x
    )

cBindToSBind :: VarEnv VarName -> CBinding VarName -> SBinding VarName
cBindToSBind varEnv b = SBinding
  { _sBindName = b^.cBindName
  , _sBindType = TyDecl q c (TSet tySalt)
  , _sBindExp = makeLambda
      (zip3 [0..] (b^.cBindArgs) indexedTys)
      varEnv
      (b^.cBindExpr)
  }
  where
  TyDecl q c tyCumin = b^.cBindType
  tySalt = cTypeToSType tyCumin
  (indexedTys, _) = extractSetArgs tySalt
  makeLambda :: Show v => [(Int, VarName, Type)] -> VarEnv v -> Scope Int CExp v -> SExp v
  makeLambda [] vars s = cExpToSExp vars ($check $ fromJust $ extractFromConstantScope s)
  makeLambda ((i, v, ty):tys) vars s
    = SESet . SELam v ty $
      walkScope
        (makeLambda tys)
        (const $ VarInfo v ty)
        vars
        (abstractInScope (\j -> if i == j then Just () else Nothing) s)

cModToSMod :: CModule VarName -> SModule VarName
cModToSMod m = SModule
  { _sModName = m^.cModName
  , _sModADTs = m^.cModADTs
  , _sModBinds = cBindToSBind initialVarEnv <$> m^.cModBinds
  }
  where
  initialVarEnv :: VarEnv VarName
  initialVarEnv = VarEnv
    { _localVar = \v ->  error $ "No free variable expected but found: " ++ show v
    , _globalTypes = fmap (transformTyDecl . view cBindType) $ m^.cModBinds
    , _constructorTypes = M.fromList $ M.toList (m^.cModADTs)
        >>= \(_, a) -> a^.adtConstr
        >>= \c@(ConDecl cName _) -> return (cName, (a, c))
    }
  transformTyDecl (TyDecl q c ty) = TyDecl q c (cTypeToSType ty)

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

internalToSaltBinding :: VarEnv VarName -> SBinding VarName -> Renamer S.Binding
internalToSaltBinding varEnv b = fillBinding <$> internalToSalt varEnv (b^.sBindExp)
  where
  fillBinding e = S.Binding
    { S._bindingName = b^.sBindName
    , S._bindingExpr = e
    , S._bindingType = b^.sBindType
    , S._bindingSrc = undefined
    }

internalToSaltModule :: SModule VarName -> Renamer S.Module
internalToSaltModule m = do
  traverse_ addGlobal (M.keys $ m^.sModBinds)
  fillModule <$> traverse (internalToSaltBinding initialVarEnv) (m^.sModBinds)
  where
  fillModule bs = CoreModule
    { S._modADTs = m^.sModADTs
    , S._modBinds = bs
    , S._modName = m^.sModName
    }
  initialVarEnv :: VarEnv VarName
  initialVarEnv = VarEnv
    { _localVar = \v -> error $ "No free variable expected but found: " ++ show v
    , _globalTypes = fmap (view sBindType) $ m^.sModBinds
    , _constructorTypes = M.fromList $ M.toList (m^.sModADTs)
        >>= \(_, a) -> a^.adtConstr
        >>= \c@(ConDecl cName _) -> return (cName, (a, c))
    }

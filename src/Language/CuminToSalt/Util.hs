{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Language.CuminToSalt.Util where

import           Bound
import           Control.Applicative
import           Control.Lens
import           Control.Monad
import qualified Data.Map                   as M
import           Data.Maybe                 (fromJust)
import           Debug.Trace.LocationTH
import           FunLogic.Core.AST
import qualified FunLogic.Core.Pretty       as FP
import qualified Language.CuMin.AST         as C
import           Language.CuminToSalt.Types
import qualified Language.SaLT.AST          as S

-- * Handling variable environments

combineVarEnvs :: (b -> VarInfo) -> VarEnv v -> VarEnv (Var b v)
combineVarEnvs b (VarEnv v g c) = VarEnv k g c
  where
  k (B b') = b b'
  k (F v') = v v'

lookupConstructor :: VarEnv v -> VarName -> (ADT, ConDecl)
lookupConstructor varEnv v = varEnv^.constructorTypes.at v.to ($checkTrace ("con not found: " ++ v) . fromJust)

lookupGlobal :: VarEnv v -> VarName -> TyDecl
lookupGlobal varEnv v = $checkTrace v . fromJust $ ty1 `mplus` (conDeclToTyDecl <$> conDecl)
  where
  ty1 = varEnv^.globalTypes.at v
  conDecl = varEnv^.constructorTypes.at v

-- * Handling types

instantiateTyDecl :: [Type] -> TyDecl -> Maybe Type
instantiateTyDecl tyArgs (TyDecl tyVars _ ty) = do
  let
    subst = M.fromList $ zip tyVars tyArgs
    replaceVar (TVar v) = M.lookup v subst
    replaceVar x = return x
  transformM replaceVar ty

instantiateConDecl :: [String] -> [Type] -> ConDecl -> Maybe [Type]
instantiateConDecl tyVars tyArgs (ConDecl _ tys) = do
  let
    subst = M.fromList $ zip tyVars tyArgs
    replaceVar (TVar v) = M.lookup v subst
    replaceVar x = return x
  mapM (transformM replaceVar) tys

extractSetArgs :: Type -> ([Type], Type)
extractSetArgs (TFun a (TSet b)) = over _1 (a:) $ extractSetArgs b
extractSetArgs ty = ([], ty)

conDeclToTyDecl :: (ADT, ConDecl) -> TyDecl
conDeclToTyDecl (adt, ConDecl _ tys) = TyDecl (adt^.adtTyArgs) [] $ go tys
  where
  go = foldr TFun $ TCon (adt^.adtName) (map TVar (adt^.adtTyArgs))

cTypeToSType :: Type -> Type
cTypeToSType = \case
  TVar a -> TVar a
  TFun s t -> TFun (cTypeToSType s) (TSet $ cTypeToSType t)
  TCon c tys -> TCon c (map cTypeToSType tys)

-- * Scope functions

abstractInScope :: (Functor f, Monad f) => (b -> Maybe bb) -> Scope b f v -> Scope bb (Scope b f) v
abstractInScope f = toScope . Scope . fmap k . fromScope
  where
  k (B b) = case f b of
    Just bb -> F . return $ B bb
    Nothing -> B b
  k (F v) = F . return $ F v

extractFromConstantScope :: (Monad f, Traversable f, Show b) => Scope b f v -> Maybe (f v)
extractFromConstantScope s = traverse k $ fromScope s
  where
  k (B b) = $failure (show b)
  k (F v) = Just v

reduceScope
  :: (Monad f)
  => (forall w. VarEnv w -> f w -> t) -- the function on expressions
  -> (b -> VarInfo) -- what to do with bound variables
  -> VarEnv v -- what to do with free variables
  -> Scope b f v -- the scope to be reduced
  -> t
reduceScope t b vars s = t (combineVarEnvs b vars) (fromScope s)

walkScope
  :: forall b v f g. (Monad f, Monad g, Show v, Show b)
  => (forall w. Show w => VarEnv w -> f w -> g w) -- the function on expressions
  -> (b -> VarInfo) -- what to do with bound variables
  -> VarEnv v -- what to do with free variables
  -> Scope b f v -- the scope to be walked along
  -> Scope b g v
walkScope t b vars s = toScope $ t (combineVarEnvs b vars) (fromScope s)

-- * Miscellaneous

cuminToSaltOp :: C.PrimOp -> S.PrimOp
cuminToSaltOp = \case
  C.PrimAdd -> S.PrimAdd
  C.PrimEq -> S.PrimEq

enterAlt
  :: Type
  -> VarEnv v
  -> (VarInfo -> Scope () f v -> a)
  -> (VarName -> [VarInfo] -> Scope Int f v -> a)
  -> Alt f v
  -> a
enterAlt ty varEnv varPat conPat = \case
  AVarPat v s -> varPat (VarInfo v ty) s
  AConPat c conArgs s -> case ty of
   TVar _ -> error $
     "Expected constructor type " ++ c ++ " but got expression of type " ++ show (FP.prettyType ty)
   TCon _ tyArgs ->
     let (adt, conDecl) = lookupConstructor varEnv c
         types = $checkTrace (show (FP.prettyType ty) ++ show adt ++ show conDecl) $ fromJust $ instantiateConDecl (adt^.adtTyArgs) tyArgs conDecl
     in conPat c (zipWith VarInfo conArgs types) s

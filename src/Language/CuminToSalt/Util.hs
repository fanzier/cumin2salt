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

-- | Given information about new bound variables and an old variable environment,
-- create a new environment where the old variables are "lifted" one level up
-- and the new variables are now directly bound.
combineVarEnvs :: (b -> VarInfo) -> VarEnv v -> VarEnv (Var b v)
combineVarEnvs b (VarEnv v g c) = VarEnv k g c
  where
  k (B b') = b b'
  k (F v') = v v'

-- | Look up the ADT and declaration of a constructor in an environment.
lookupConstructor :: VarEnv v -> VarName -> (ADT, ConDecl)
lookupConstructor varEnv v = varEnv^.constructorTypes.at v.to ($checkTrace ("con not found: " ++ v) . fromJust)

-- | Look up a global function's type declaration in an environment.
lookupGlobal :: VarEnv v -> VarName -> TyDecl
lookupGlobal varEnv v = $checkTrace v . fromJust $ ty1 `mplus` (conDeclToTyDecl <$> conDecl)
  where
  ty1 = varEnv^.globalTypes.at v
  conDecl = varEnv^.constructorTypes.at v

-- | Given a program's function and ADT definitions, it creates an environment with no local variables.
-- This is the starting point when beginning to traverse the AST of an expression.
makeInitialVarEnv :: Show v => M.Map VarName TyDecl -> M.Map VarName ADT -> VarEnv v
makeInitialVarEnv globals adts = VarEnv
  { _localVar = \v ->  error $ "No free variable expected but found: " ++ show v
  , _globalTypes = globals
  , _constructorTypes = M.fromList $ M.toList adts
      >>= \(_, a) -> a^.adtConstr
      >>= \c@(ConDecl cName _) -> return (cName, (a, c))
  }

-- * Handling types

-- | Instantiates a type declaration.
instantiateTyDecl :: [Type] -> TyDecl -> Maybe Type
instantiateTyDecl tyArgs (TyDecl tyVars _ ty) = do
  let
    subst = M.fromList $ zip tyVars tyArgs
    replaceVar (TVar v) = M.lookup v subst
    replaceVar x = return x
  transformM replaceVar ty

-- | Instantiates the argument types of a constructor.
instantiateConDecl :: [String] -> [Type] -> ConDecl -> Maybe [Type]
instantiateConDecl tyVars tyArgs (ConDecl _ tys) = do
  let
    subst = M.fromList $ zip tyVars tyArgs
    replaceVar (TVar v) = M.lookup v subst
    replaceVar x = return x
  mapM (transformM replaceVar) tys

-- | In a function of the form   a -> { b -> { c -> { ... } } },
-- extract the argument types, i.e. a, b, c ...
extractSetArgs :: Type -> ([Type], Type)
extractSetArgs (TFun a (TSet b)) = over _1 (a:) $ extractSetArgs b
extractSetArgs ty = ([], ty)

-- | Construct the type declaration of a constructor, viewed as a function.
conDeclToTyDecl :: (ADT, ConDecl) -> TyDecl
conDeclToTyDecl (adt, ConDecl _ tys) = TyDecl (adt^.adtTyArgs) [] $ go tys
  where
  go = foldr TFun $ TCon (adt^.adtName) (map TVar (adt^.adtTyArgs))

-- * Scope functions
-- These functions help with handling Scopes from the bound library.
-- Due to their abstract nature, they are not easy to explain.

-- | Given a function that selects certain variables (by mapping them to Just) and a scope that binds variables,
-- construct an outer scope with all the other variables and an inner scope with the selected ones.
abstractInScope :: (Functor f, Monad f) => (b -> Maybe bb) -> Scope b f v -> Scope bb (Scope b f) v
abstractInScope f = toScope . Scope . fmap k . fromScope
  where
  k (B b) = case f b of
    Just bb -> F . return $ B bb
    Nothing -> B b
  k (F v) = F . return $ F v

-- | Transform a scope, where the bound variables are not used, to an expression.
extractFromConstantScope :: (Monad f, Traversable f, Show b) => Scope b f v -> Maybe (f v)
extractFromConstantScope s = traverse k $ fromScope s
  where
  k (B b) = $failure (show b)
  k (F v) = Just v

-- | Reduce a Scope given a function to reduce expressions without having to worry about combining the variable environments.
reduceScope
  :: (Monad f)
  => (forall w. VarEnv w -> f w -> t) -- ^ the function on expressions
  -> (b -> VarInfo) -- ^ information about bound variables
  -> VarEnv v -- ^ information about the free variables
  -> Scope b f v -- ^ the scope to be reduced
  -> t
reduceScope t b vars s = t (combineVarEnvs b vars) (fromScope s)

-- | Given a transformation of expressions, create a transformation of Scopes without worrying about combining the variable environments.
transformScope
  :: forall b v f g. (Monad f, Monad g, Show v, Show b)
  => (forall w. Show w => VarEnv w -> f w -> g w) -- ^ the transformation on expressions
  -> (b -> VarInfo) -- ^ information about bound variables
  -> VarEnv v -- ^ information about free variables
  -> Scope b f v -- ^ the scope to be transformed
  -> Scope b g v
transformScope t b vars s = toScope $ t (combineVarEnvs b vars) (fromScope s)

-- * Handling case alternatives

-- | A clean way to inspect a case alternative.
-- This way, the messy type handling only has to be done in this one place.
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

-- | Convenience function for transforming case alternatives.
transformAlt
  :: (Show v, Monad f, Monad g)
  => (forall w. Show w => VarEnv w -> f w -> g w)
  -> Type -> VarEnv v -> Alt f v -> Alt g v
transformAlt t ty varEnv = enterAlt ty varEnv
  (\b@(VarInfo v _) s -> AVarPat v $ transformScope t (const b) varEnv s)
  (\c bs s -> let vs = map _vName bs in
   AConPat c vs $ transformScope t (bs !!) varEnv s
  )

-- | Convenience function for reducing case alternatives.
reduceAlt
  :: (Monad f)
  => (forall w. VarEnv w -> f w -> t)
  -> Type -> VarEnv v -> Alt f v -> t
reduceAlt t ty varEnv = enterAlt ty varEnv
  (\b s -> reduceScope t (const b) varEnv s)
  (\_ bs s -> reduceScope t (bs !!) varEnv s)

-- * Miscellaneous

-- | Translate a primitive CuMin operation to a SaLT primitive.
cuminToSaltOp :: C.PrimOp -> S.PrimOp
cuminToSaltOp = \case
  C.PrimAdd -> S.PrimAdd
  C.PrimEq -> S.PrimEq

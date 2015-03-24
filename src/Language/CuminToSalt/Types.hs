{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
module Language.CuminToSalt.Types where

import           Bound
import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Map            as M
import           FunLogic.Core.AST   as F
import qualified Language.CuMin.AST  as C
import           Prelude.Extras

-- | Empty data type. Useful for proving that expressions do not contain free variables.
data Void

deriving instance Eq Void
deriving instance Show Void

-- * Internal CuMin representation (nameless)

type CModule = CoreModule CBinding

-- | A top level function binding.
data CBinding = CBinding
  { _cBindName :: VarName
  , _cBindArgs :: [VarName]
  , _cBindExp  :: Scope Int CExp Void
  , _cBindType :: TyDecl
  , _cBindSrc  :: SrcRef
  }
  deriving (Eq, Show)

instance IsBinding CBinding where
  type BindingExp CBinding = Scope Int CExp Void
  bindingName f bnd = (\x -> bnd {_cBindName = x}) <$> f (_cBindName bnd)
  bindingExpr f bnd = (\x -> bnd {_cBindExp = x}) <$> f (_cBindExp bnd)
  bindingType f bnd = (\x -> bnd {_cBindType = x}) <$> f (_cBindType bnd)
  bindingSrc  f bnd = (\x -> bnd {_cBindSrc  = x}) <$> f (_cBindSrc  bnd)

-- | Nameless representation of CuMin expressions using Scope.
-- It constructors correspond to the regular CuMin data type.
data CExp v
  = CEVar v
  | CELet VarName (CExp v) (Scope () CExp v) -- the bound variable name, the bound expression, and the expression it is used in
  | CELetFree VarName Type (Scope () CExp v) -- the bound logic variable, its type and the expression it is used in.
  | CEFailed Type
  | CEFun VarName [Type]
  | CEApp (CExp v) (CExp v)
  | CELit Lit
  | CEPrim C.PrimOp [CExp v]
  | CECon VarName [Type]
  | CECase (CExp v) [Alt CExp v]
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Eq1 CExp
instance Show1 CExp
instance Applicative CExp where
  pure = return
  (<*>) = ap

-- | Monad instance for capture-avoiding substitution.
instance Monad CExp where
  return = CEVar
  e >>= f = case e of
    CEVar v -> f v
    CELet v x y -> CELet v (x >>= f) (y >>>= f)
    CELetFree v ty x -> CELetFree v ty (x >>>= f)
    CEFailed ty -> CEFailed ty
    CEFun v tys -> CEFun v tys
    CEApp x y -> CEApp (x >>= f) (y >>= f)
    CELit l -> CELit l
    CEPrim oper es -> CEPrim oper (map (>>= f) es)
    CECon n tys -> CECon n tys
    CECase x alts -> CECase (x >>= f) (map (>>>= f) alts)

-- * Alternatives

-- Nameless representation of case alternatives.
data Alt f v
  = AVarPat VarName (Scope () f v) -- a catch-all variable pattern and the corresponding expression.
  | AConPat DataConName [VarName] (Scope Int f v) -- a constructor pattern with the bound variable names and the corresponding expression.
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq1 f, Monad f) => Eq1 (Alt f)

-- | Allow substitution on case alternatives.
instance Bound Alt where
  AVarPat v x >>>= f = AVarPat v (x >>>= f)
  AConPat c vs x >>>= f = AConPat c vs (x >>>= f)

-- * Internal SaLT representation (nameless)

type SModule = CoreModule SBinding

-- | A top level functon binding.
data SBinding = SBinding
  { _sBindName :: VarName
  , _sBindType :: TyDecl
  , _sBindExp  :: SExp Void
  , _sBindSrc  :: SrcRef
  }
  deriving (Eq, Show)

instance IsBinding SBinding where
  type BindingExp SBinding = SExp Void
  bindingName f bnd = (\x -> bnd {_sBindName = x}) <$> f (_sBindName bnd)
  bindingExpr f bnd = (\x -> bnd {_sBindExp = x}) <$> f (_sBindExp bnd)
  bindingType f bnd = (\x -> bnd {_sBindType = x}) <$> f (_sBindType bnd)
  bindingSrc  f bnd = (\x -> bnd {_sBindSrc  = x}) <$> f (_sBindSrc  bnd)

-- | Nameless representation of SaLT expressions using Scope.
-- The constructors correspond to the regular SaLT expression type.
data SExp v
  = SEVar v
  | SEFun VarName [Type]
  | SELam VarName Type (Scope () SExp v) -- the bound variable name, its type and the expression it is used in.
  | SESetBind (SExp v) (SExp v) -- union of the sets represented by the second expression, indexed by the first one.
  | SEApp (SExp v) (SExp v)
  | SELit Lit
  | SEPrim C.PrimOp [SExp v]
  | SECon VarName [Type]
  | SESet (SExp v)
  | SECase (SExp v) [Alt SExp v]
  | SEFailed Type
  | SEUnknown Type
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Eq1 SExp
instance Show1 SExp
instance Applicative SExp where
  pure = return
  (<*>) = ap

-- | Monad instance for capture-avoiding substitution.
instance Monad SExp where
  return = SEVar
  e >>= f = case e of
    SEVar v -> f v
    SEFun v tys -> SEFun v tys
    SELam v ty x -> SELam v ty (x >>>= f)
    SESetBind x y -> SESetBind (x >>= f) (y >>= f)
    SEApp x y -> SEApp (x >>= f) (y >>= f)
    SELit l -> SELit l
    SEPrim oper es -> SEPrim oper (map (>>= f) es)
    SECon n tys -> SECon n tys
    SESet x -> SESet (x >>= f)
    SECase x alts -> SECase (x >>= f) (map (>>>= f) alts)
    SEFailed ty -> SEFailed ty
    SEUnknown ty -> SEUnknown ty


-- * Typing Environment

-- | A variable environment has information about free variables in scope,
-- and about the global definitions of a program:
-- the top-level function types and the types of ADT constructors.
data VarEnv v = VarEnv
  { _localVar         :: v -> VarInfo
  , _globalTypes      :: M.Map VarName TyDecl
  , _constructorTypes :: M.Map VarName (ADT, ConDecl)
  }

-- | Information about a variable: its name and type.
data VarInfo = VarInfo
  { _vName :: VarName
  , _vType :: Type
  } deriving (Show)

-- Lens stuff
makeLenses ''CBinding
makeLenses ''SBinding
makeLenses ''VarEnv
makeLenses ''VarInfo

-- Patterns
pattern TSet t = TCon "Set" [t]

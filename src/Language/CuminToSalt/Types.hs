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

data Void

deriving instance Eq Void
deriving instance Show Void

type CModule = CoreModule CBinding

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

-- Scoped CuMin Expression
data CExp v
  = CEVar v
  | CELet VarName (CExp v) (Scope () CExp v)
  | CELetFree VarName Type (Scope () CExp v)
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

-- Scoped Alternative
data Alt f v
  = AVarPat VarName (Scope () f v)
  | AConPat VarName [VarName] (Scope Int f v)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq1 f, Monad f) => Eq1 (Alt f)

instance Bound Alt where
  AVarPat v x >>>= f = AVarPat v (x >>>= f)
  AConPat c vs x >>>= f = AConPat c vs (x >>>= f)

type SModule = CoreModule SBinding

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

-- Scoped SaLT Expression
data SExp v
  = SEVar v
  | SEFun VarName [Type]
  | SELam VarName Type (Scope () SExp v)
  | SESetBind (SExp v) (SExp v)
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

data VarEnv v = VarEnv
  { _localVar         :: v -> VarInfo
  , _globalTypes      :: M.Map VarName TyDecl
  , _constructorTypes :: M.Map VarName (ADT, ConDecl)
  }

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

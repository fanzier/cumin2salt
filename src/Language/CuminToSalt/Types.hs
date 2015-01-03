{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
module Language.CuminToSalt.Types where

import           Bound
import           Control.Applicative
import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Map            as M
import           FunLogic.Core.AST   as F
import qualified Language.CuMin.AST  as C
import           Prelude.Extras

data Ident = Ident { varName :: VarName, varId :: Int }
  deriving (Show, Eq)

assert' :: (a -> Bool) -> a -> a
assert' f a = assert (f a) a

data CModule v = CModule
  { _cModName  :: VarName
  , _cModADTs  :: M.Map VarName ADT
  , _cModBinds :: M.Map VarName (CBinding v)
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

data CBinding v = CBinding
  { _cBindName :: v
  , _cBindArgs :: [v]
  , _cBindExpr :: Scope Int CExp v
  , _cBindType :: TyDecl
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

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

data SModule v = SModule
  { _sModName  :: VarName
  , _sModADTs  :: M.Map VarName ADT
  , _sModBinds :: M.Map VarName (SBinding v)
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

data SBinding v = SBinding
  { _sBindName :: v
  , _sBindType :: TyDecl
  , _sBindExp  :: SExp v
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- Scoped SaLT Expression
data SExp v
  = SEVar v
  | SEFun VarName [Type]
  | SELam VarName Type (Scope () SExp v)
  | SESetBind (SExp v) VarName (Scope () SExp v)
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
    SESetBind x v y -> SESetBind (x >>= f) v (y >>>= f)
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
makeLenses ''CModule
makeLenses ''CBinding
makeLenses ''SModule
makeLenses ''SBinding
makeLenses ''VarEnv
makeLenses ''VarInfo

-- Patterns
pattern TSet t = TCon "Set" [t]

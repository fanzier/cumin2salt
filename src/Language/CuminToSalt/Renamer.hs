module Language.CuminToSalt.Renamer where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Trans.State.Strict
import qualified Data.Map as M

data RState v = RState
  { counter :: Int
  , locals :: M.Map v Int
  , globals :: M.Map v Int
  }

newtype RenamerT v m a = RenamerT { runRenamerT :: StateT (RState v) m a }

instance Functor m => Functor (RenamerT v m) where
  fmap f = RenamerT . fmap f . runRenamerT

instance (Applicative m, Functor m, Monad m) => Applicative (RenamerT v m) where
  pure = RenamerT . pure
  f <*> m = RenamerT $ runRenamerT f <*> runRenamerT m

instance (Applicative m, Functor m, Monad m) => Monad (RenamerT v m) where
  return = RenamerT . return
  m >>= f = RenamerT $ runRenamerT m >>= (runRenamerT . f)

evalRenamerT :: Monad m => RenamerT v m a -> m a
evalRenamerT = flip evalStateT (RState 0 M.empty M.empty) . runRenamerT

evalRenamer :: Renamer a -> a
evalRenamer = runIdentity . evalRenamerT

withLocal :: (Monad m, Ord v) => v -> RenamerT v m a -> RenamerT v m a
withLocal v m = RenamerT $ do
  RState _ l' _ <- get
  (i, g', a) <- withStateT (\(RState c l g) -> RState (c + 1) (M.insert v c l) g) $ do
    a <- runRenamerT m
    RState i _ g <- get
    return (i, g, a)
  put (RState i l' g')
  return a

withLocals :: (Monad m, Ord v) => [v] -> RenamerT v m a -> RenamerT v m a
withLocals vs m = foldr withLocal m vs

addGlobal :: (Monad m, Ord v) => v -> RenamerT v m ()
addGlobal v = RenamerT $ modify (\(RState c l g) -> RState (c + 1) l (M.insert v c g))

resolve :: (Monad m, Ord v, Show v) => v -> RenamerT v m (Maybe Int)
resolve v = RenamerT $ gets (\(RState _ l g) -> M.lookup v l `mplus` M.lookup v g)

resolveName :: (Functor m, Monad m) => String -> RenamerT String m (Maybe String)
resolveName v = fmap (makeVar v) <$> resolve v

makeVar :: String -> Int -> String
makeVar v i = v ++ show i

fresh :: Monad m => RenamerT v m Int
fresh = RenamerT $ do
  RState i l g <- get
  put $ RState (i + 1) l g
  return i

freshLocal :: (Functor m, Monad m) => String -> RenamerT v m String
freshLocal v = makeVar v <$> fresh

data AST v = Bind v (Exp v) (AST v) | E deriving Show
data Exp v = Use v (Exp v) | Par (Exp v) (Exp v) | Local v (Exp v) | U deriving Show

type Renamer = RenamerT String Identity

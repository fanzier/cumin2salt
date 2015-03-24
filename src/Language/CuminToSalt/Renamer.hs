module Language.CuminToSalt.Renamer where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Trans.State.Strict
import qualified Data.Map as M

-- * The renamer makes sure that variable names do not clash
-- by appending a unique number (ID) to them.
-- During renaming, we do not have to worry about global functions
-- since they are marked by "<::>" in the output,
-- so they cannot be confused with local variables.

-- | The state of the renamer.
-- The unique counter is for generation of fresh variables.
-- locals maps variable names to their unique ID.
data RState v = RState
  { counter :: Int
  , locals :: M.Map v Int
  }

newtype RenamerT v m a = RenamerT { runRenamerT :: StateT (RState v) m a }

type Renamer = RenamerT String Identity

instance Functor m => Functor (RenamerT v m) where
  fmap f = RenamerT . fmap f . runRenamerT

instance (Applicative m, Functor m, Monad m) => Applicative (RenamerT v m) where
  pure = RenamerT . pure
  f <*> m = RenamerT $ runRenamerT f <*> runRenamerT m

instance (Applicative m, Functor m, Monad m) => Monad (RenamerT v m) where
  return = RenamerT . return
  m >>= f = RenamerT $ runRenamerT m >>= (runRenamerT . f)

evalRenamerT :: Monad m => RenamerT v m a -> m a
evalRenamerT = flip evalStateT (RState 0 M.empty) . runRenamerT

evalRenamer :: Renamer a -> a
evalRenamer = runIdentity . evalRenamerT

-- | Execute an action with one more local variable in the context.
withLocal :: (Monad m, Ord v) => v -> RenamerT v m a -> RenamerT v m a
withLocal v m = RenamerT $ do
  RState _ l' <- get
  (i, a) <- withStateT (\(RState c l) -> RState (c + 1) (M.insert v c l)) $ do
    a <- runRenamerT m
    RState i _ <- get
    return (i, a)
  put (RState i l')
  return a

-- | Execute an action with more local variables in the context.
withLocals :: (Monad m, Ord v) => [v] -> RenamerT v m a -> RenamerT v m a
withLocals vs m = foldr withLocal m vs

-- | Retrieve the ID of variable name.
resolve :: (Monad m, Ord v, Show v) => v -> RenamerT v m (Maybe Int)
resolve v = RenamerT $ gets (\(RState _ l) -> M.lookup v l)

-- | Retrieve the unique name of a variable name.
resolveName :: (Functor m, Monad m) => String -> RenamerT String m (Maybe String)
resolveName v = fmap (makeVar v) <$> resolve v

-- | Construct a unique name by appending the ID to the variable name.
-- An underscore is inserted to prevent digits from running together.
-- Otherwise, a variable "x2" should not be renamed to "x23",
-- which may already be the renamed variant of a variable "x".
makeVar :: String -> Int -> String
makeVar v i = v ++ "_" ++ show i

-- | Generate a fresh ID by increasing the counter.
fresh :: Monad m => RenamerT v m Int
fresh = RenamerT $ do
  RState i l <- get
  put $ RState (i + 1) l
  return i

-- | Generate a fresh local variable.
freshLocal :: (Functor m, Monad m) => String -> RenamerT v m String
freshLocal v = makeVar v <$> fresh

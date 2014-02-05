{-# LANGUAGE Rank2Types, FunctionalDependencies, MultiParamTypeClasses #-}
module ReaderReflection (
    ReaderT, runReaderT, readerT, ask, lift,
    ) where

import Data.Proxy
import Data.Reflection
import Control.Monad.IO.Class
import Control.Monad.Trans.Class


newtype Tag r s m a = T { unT :: m a }

instance Monad m => Monad (Tag r s m) where
    return a = T (return a)
    m >>= k  = T (unT m >>= unT . k)

newtype ReaderT r m a = R { run :: forall s. Reifies s r => Tag r s m a }

instance Monad m => Monad (ReaderT r m) where
    (>>=)  = bindR
    return = returnR

instance MonadIO m => MonadIO (ReaderT r m) where liftIO = liftIOR
instance MonadTrans (ReaderT r)             where lift   = liftR

runReaderT :: ReaderT r m a -> (r -> m a)
runReaderT (R m) r = reify r (\p -> unT (asProxyOf m p))

asProxyOf :: Tag r s m a -> Proxy s -> Tag r s m a
asProxyOf v _ = v

readerT :: Monad m => (r -> m a) -> ReaderT r m a
readerT f = ask >>= lift . f

bindR :: Monad m => ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
bindR m k = R (run m >>= \a -> run (k a))

returnR :: Monad m => a -> ReaderT r m a
returnR a = R (return a)

ask :: Monad m => ReaderT r m r
ask = R (tag Proxy)
    where
    tag :: forall s r a m. (Monad m, Reifies s r) => Proxy s -> Tag r s m r
    tag p = T (return (reflect p))

liftIOR :: MonadIO m => IO a -> ReaderT r m a
liftIOR m = R (T $ liftIO m)

liftR :: m a -> ReaderT r m a
liftR m = R (T m)


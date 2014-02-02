{-----------------------------------------------------------------------------
    Reader monad transformer
------------------------------------------------------------------------------}
module Reader (
    ReaderT, runReaderT, readerT, ask, lift,
    ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class

newtype ReaderT r m a = R { runReaderT :: r -> m a }

instance Monad m => Monad (ReaderT r m) where
    (>>=)  = bindR
    return = returnR

instance MonadIO m => MonadIO (ReaderT r m) where
    liftIO = liftIOR

instance MonadTrans (ReaderT r) where
    lift m = R $ \r -> m

readerT :: (r -> m a) -> ReaderT r m a
readerT = R

bindR :: Monad m => ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
bindR m k = R $ \r -> runReaderT m r >>= \a -> runReaderT (k a) r
    
returnR :: Monad m => a -> ReaderT r m a
returnR a = R $ \r -> return a

ask :: Monad m => ReaderT r m r
ask = R $ \r -> return r

liftIOR :: MonadIO m => IO a -> ReaderT r m a
liftIOR m = R $ \r -> liftIO m

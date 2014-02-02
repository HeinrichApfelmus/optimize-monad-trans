{-----------------------------------------------------------------------------
    Reader monad transformer
------------------------------------------------------------------------------}
{-# LANGUAGE ImplicitParams, Rank2Types #-}
module ReaderImplicit (
    ReaderT, runReaderT, readerT, ask, lift,
    ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class

newtype ReaderT r m a = R { run :: (?ask :: r) => m a }

instance Monad m => Monad (ReaderT r m) where
    (>>=)  = bindR
    return = returnR

instance MonadIO m => MonadIO (ReaderT r m) where liftIO = liftIOR
instance MonadTrans (ReaderT r)             where lift   = liftR

runReaderT :: ReaderT r m a -> (r -> m a)
runReaderT (R m) r = let ?ask = r in m

readerT :: Monad m => (r -> m a) -> ReaderT r m a
readerT f = R (f ?ask)

bindR :: Monad m => ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
bindR m k = R (run m >>= \a -> run (k a))
    
returnR :: Monad m => a -> ReaderT r m a
returnR a = R (return a)

ask :: Monad m => ReaderT r m r
ask = R (return ?ask)

liftIOR :: MonadIO m => IO a -> ReaderT r m a
liftIOR m = R (liftIO m)

liftR :: m a -> ReaderT r m a
liftR m = R m

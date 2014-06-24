{-----------------------------------------------------------------------------
Reader monad transformer
------------------------------------------------------------------------------}
module Reader (
    ReaderT, runReaderT, ask, lift,
    ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.IORef

newtype ReaderT r m a = R { runReaderT :: r -> m a }

instance Monad m => Monad (ReaderT r m) where
    (>>=) = bindR
    return = returnR

instance MonadIO m => MonadIO (ReaderT r m) where
    liftIO = liftIOR

instance MonadTrans (ReaderT r) where
    lift m = R (\_ -> m)

bindR :: Monad m => ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
bindR m k = R (\r -> runReaderT m r >>= \a -> runReaderT (k a) r)

returnR :: Monad m => a -> ReaderT r m a
returnR a = R (\_ -> return a)

ask :: Monad m => ReaderT r m r
ask = R return

liftIOR :: MonadIO m => IO a -> ReaderT r m a
liftIOR m = R (\_ -> liftIO m)

type Value = IORef Int

{-
ask1 :: ReaderT Value (ReaderT Value IO) Value
ask1 = ask

ask2 :: ReaderT Value (ReaderT Value IO) Value
ask2 = lift ask

runEval1 :: ReaderT Value (ReaderT Value IO) a -> IO Int
runEval1 m = do
    ref <- newIORef 0
    runReaderT (runReaderT m ref) ref
    readIORef ref
-}

ask1 :: ReaderT (Value, Value) IO Value
ask1 = liftM fst ask

ask2 :: ReaderT (Value, Value) IO Value
ask2 = liftM snd ask

runEval2 :: ReaderT (Value, Value) IO void -> IO Int
runEval2 m = do
    ref <- newIORef 0
    runReaderT m (ref, ref)
    readIORef ref

{-# LANGUAGE CPP #-}
module Eval1 where

import Data.IORef

#ifdef IMPLICIT
import ReaderImplicit
#else
#ifdef REFLECTION
import ReaderReflection
#else
import Reader
#endif
#endif

type Value = IORef Int
type Eval  = ReaderT Value (ReaderT Value IO)

ask1 :: Eval Value
ask1 = ask

ask2 :: Eval Value
ask2 = lift ask

runEval :: Eval void -> IO Int
runEval m = do
    ref <- newIORef 0
    runReaderT (runReaderT m ref) ref
    readIORef ref

bindEval
  :: Eval a
  -> (a -> Eval b)
  -> Eval b
bindEval m k = readerT $ \x -> readerT $ \y -> do
    a <- runReaderT (runReaderT m x) y
    runReaderT (runReaderT (k a) x) y
{-# INLINE bindEval #-}
{-# RULES "rewrite >>= for Eval" (>>=) = bindEval #-}

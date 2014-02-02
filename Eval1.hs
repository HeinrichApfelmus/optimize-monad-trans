{-# LANGUAGE CPP #-}
module Eval1 where

import Data.IORef

#ifdef IMPLICIT
import ReaderImplicit
#else
import Reader
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
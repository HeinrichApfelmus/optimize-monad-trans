module Eval2 where

import Control.Monad
import Data.IORef
import Reader

type Value = IORef Int
type Eval  = ReaderT (Value,Value) IO

ask1 :: Eval Value
ask1 = liftM fst ask

ask2 :: Eval Value
ask2 = liftM snd ask

runEval :: Eval void -> IO Int
runEval m = do
    ref <- newIORef 0
    runReaderT m (ref,ref)
    readIORef ref
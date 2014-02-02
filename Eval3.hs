module Eval3 where

import Control.Monad.IO.Class
import Data.IORef

type    Value  = IORef Int
newtype Eval a = E { run :: Value -> Value -> IO a }

instance Monad Eval where
    return a = E $ \_ _ -> return a
    m >>= k  = E $ \x y -> run m x y >>= \a -> run (k a) x y
--    m >>= k  = E $ \x -> let b = run m x in \y -> b y >>= \a -> run (k a) x y

{-
Key difference: (>>=)

Evaluating one parameter first and then the second in Eval1
might have more sharing than the Eval3 variant.
This is similar to the  state hack  in GHC's IO.
Unfortunately, there doesn't seem to be a way to undo the sharing?!

-}


instance MonadIO Eval where
    liftIO m = E $ \_ _ -> m

ask1 :: Eval Value
ask1 = E $ \x _ -> return x

ask2 :: Eval Value
ask2 = E $ \_ y -> return y

runEval :: Eval void -> IO Int
runEval m = do
    ref <- newIORef 0
    run m ref ref
    readIORef ref
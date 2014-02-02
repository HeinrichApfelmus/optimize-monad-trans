{-----------------------------------------------------------------------------
    Optimizination of Monad Transformers

    This module is an experiment in optimizing monad transformer stacks.
------------------------------------------------------------------------------}
{-# LANGUAGE CPP #-}
module OptimizeMonadTrans (
    Children, example, main
    ) where

import Control.Monad.IO.Class
import Data.IORef

#ifdef VARIANT
import VARIANT
#endif

main = print =<< runEval example

{-----------------------------------------------------------------------------
    Example problem:
    
    A monadic traversal, for instance the traversal of a tree.
    The goal is to have the source code be inlined to a point
    where `go` becomes a tight inner loop.
------------------------------------------------------------------------------}
type Children m a = a -> m [a]

{-# INLINE traverseTree #-}
traverseTree :: Monad m => Children m a -> a -> m ()
traverseTree children x = go [x]
    where
    go []     = return ()
    go (x:xs) = do
        ys <- children x
        go (ys ++ xs)

{-----------------------------------------------------------------------------
    Concrete tree type
------------------------------------------------------------------------------}
data Tree
    = Branch (Eval Int) [Tree]
    | Leaf

evaluate :: Tree -> Eval [Tree]
evaluate (Branch action children) = do
    a   <- action
    ref <- ask1
    liftIO $ do
        b <- readIORef ref
        writeIORef ref $! a + b
    return children
evaluate Leaf = do
    ref <- ask2
    liftIO $ do
        b <- readIORef ref
        writeIORef ref $! b + 1
    return []

{-# NOINLINE example #-}
    -- We want to concentrate on optimizing this function.
example :: Eval ()
example = traverseTree evaluate tree

{-# NOINLINE tree #-}
    -- We don't want GHC to inline the tree,
    -- because in real applications, the tree is created dynamically.
tree :: Tree
tree = Branch (return 1) [Branch (return 2) [Leaf,Leaf], Leaf]

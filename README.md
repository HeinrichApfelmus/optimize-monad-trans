This is a toy problem to investigate how the [Glasgow Haskell Compiler][ghc] can optimize a [monad transformer stack][transformers].

  [transformers]: http://hackage.haskell.org/package/transformers
  [ghc]: http://www.haskell.org/ghc/docs/latest/html/users_guide/index.html

[Discussion on reddit](http://www.reddit.com/r/haskell/comments/1wgk8r/frp_release_of_reactivebanana_version_08/cf2faou).

Overview
--------

Consider the generic problem of traversing some data structure using a monad. Think [`Data.Traversable`][traversable]. The traversal is usually coded as a recursive loop, like this

    go :: Structure -> Monad A 
    go x = ... go x' ...

The `Monad` is usually a function type, for instance a state monad

    type Monad a = S -> (a, S)

The `go` function looks like a recursive definition of a closure / function, but that's not what we want. Instead, what we want is that the state monad is inlined into the definition of `go`, so that it becomes a tight inner loop. In other words, we are not interested in the result `Monad A` as a first class value, we just want to use the monad to organize our traversal.

  [traversable]: http://hackage.haskell.org/package/base-4.6.0.1/docs/Data-Traversable.html


Example & Analysis
------------------

The module [`OptimizeMonadTrans`](OptimizeMonadTrans.hs) implements a traversal

    traverseTree :: Monad m => (a -> m [a]) -> a -> m ()

which is then applied to a tree

    evaluate :: Tree -> Eval [Tree]

The monad `Eval` is a simple `ReaderT` monad transformer on top of `IO`. The reader monad should be the simplest case to optimize for the compiler. The goal is to have `ghc -O` inline the monad to the point that the traversal becomes a tight inner loop.

Different implementations for the `Eval` monad can yield different results:

* The module [`Eval1`](Eval1.hs) implementes a two-level `ReaderT` transformer. The resulting core [`OptimizeMonadTrans.core1.hs`](results/OptimizeMonadTrans.core1.hs) is not good, it allocates closures. It looks roughly like this:

        traverseExample :: [Tree] -> Eval1.Value -> ReaderT Eval1.Value IO ()
        traverseExample = \tree valueOuter ->
            case tree of _ {
                []     -> return';
                (x:xs) -> 
                    let m_Xim :: ReaderT Eval1.Value IO [Tree]
                        m_Xim = case x of _ {
                                OptimizeMonadTrans.Branch action children -> ... 
                            }
                    in
                        \(valueInner :: Eval1.value)
                         (s :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                            case m_Xim valueInner s of _
                                { ... traverseExample ... };
            }

        
        return' :: Eval1.Value -> GHC.Prim.State# GHC.Prim.RealWorld
                -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
        return' = \_ s -> (# s, () #)

    The program performs a case analysis on the list of trees after binding the outer reader value to `valueOuter`, but then it allocates an action `m_Xim` for the inner reader and builds a closure that essentially just calls `m_Xim`. 

* The module [`Eval2`](Eval2.hs) uses a single level `ReaderT`. The resulting core [`OptimizeMonadTrans.core2.hs`](results/OptimizeMonadTrans.core2.hs) is very good, the traversal is inlined into a tight inner loop. It looks roughly like this:

        traverseExample :: [Tree] -> (Eval2.Value,Eval2.Value)
            -> GHC.Prim.State# GHC.Prim.RealWorld
            -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
        traverseExample = \tree value s ->
            case tree of _ {
              []     -> (# s, () #);
              (x:xs) -> case x of _ {
                  OptimizeMonadTrans.Branch action_aAv children_aAw -> ... ;
                  ...
              }
        
    After taking both the reader value and GHC's internal state token for the IO monad as arguments, the program continues a case analysis on the list of trees. No other closures are build and no monadic action is shared with a `let` binding.

The first variant `Eval1` is more modular, as it uses a stack of monad transformers, while the second variant `Eval2` yields much faster code. Is it possible to add INLINE or other compiler annotations to have the first variant behave like the second?

Unfortunately, the answer is **"no"**. The variant `Eval3` reveals why. Defining a reader monad with two arguments,
    
    newtype Eval a = E { run :: Value -> Value -> IO a }

the stack of monad transformers from variant `Eval1` is equivalent to the monad bind

    m >>= k  = E $ \x -> let b = run m x in \y -> b y >>= \a -> run (k a) x y

while the single argument from variant `Eval2` is equivalent to

    m >>= k  = E $ \x y -> run m x y >>= \a -> run (k a) x y

The difference is slight but important: in the first variant, the computation `run m x` i shared over several values for `y`, while in the second variant, the computation `run m x` is recomputed for every invocation with a value `y`. Since this computation could have been very expensive, rightfully GHC refuses to inline the first variant.

Note that the same reasoning could be applied to the state token for the `IO` monad. Why doesn't GHC build closures for that? The answer is that the compiler treats the `State#` type constructor as a special case and doesn't refrain from recomputing `IO` actions. This is GHC's infamous [state hack][].

  [state hack]: https://ghc.haskell.org/trac/ghc/ticket/1168


Building
--------

A [`Makefile`](Makefile) helps with compiling. The commands

    $ make core1
    $ make core2
    $ make core3
    $ make core3s

will compile the main module using the different variants and output the corresponding GHC core to the [`results`](results/) folder.

There are two more exotic variants as well. Building with

    $ make coreImplicit

will use GHCs `ImplicitParameters` extension to implement the reader monad transformer, while

    $ make coreRefl

uses [type class reflection][reflection] to implement the monad transformer, both in the hope of circumventing the issue with sharing by moving the reader arguments into the type system. However, as the core demonstrates, neither implementation succeeds.

  [reflection]: http://hackage.haskell.org/package/reflection

Resources
---------

GHC documentation

* [How to read GHC Core](http://www.haskell.org/ghc/docs/7.6.3/html/users_guide/options-debugging.html#idp39365504). Reading core may take a little time to get used to, but it's actually less painful than it looks at first glance. The main clutter is actually type signatures, which can be ignored for the most part.
* [INLINE and INLINEABLE pragmas](http://www.haskell.org/ghc/docs/7.6.3/html/users_guide/pragmas.html#inline-noinline-pragma). Note that INLINE inlines the original right-hand side, not an optimized one.
* [SPECIALIZE pragma](http://www.haskell.org/ghc/docs/7.6.3/html/users_guide/pragmas.html#specialize-pragma). Specializes polymorphic types. This doesn't seem to be a problem in our case, though.
* [RULES pragma](http://www.haskell.org/ghc/docs/7.6.3/html/users_guide/rewrite-rules.html). Rewrite rules, the big gun. Not sure whether they apply in this situation, though, because everything should be solveable by inlining. However, the [CONLIKE pragma](http://www.haskell.org/ghc/docs/7.6.3/html/users_guide/rewrite-rules.html#conlike) seems interesting for reducing `let` statements, though it only applies to rules.

General information on improving running times of Haskell programs

* Stackoverflow — [Tools for analyzing performance of a Haskell program][tools]
* Haskellwiki — [Performance tips for Monads][wiki]. Seems somewhat uninformed. (Jan 2014)

  [wiki]: http://www.haskell.org/haskellwiki/Performance/Monads
  [tools]: http://stackoverflow.com/questions/3276240/tools-for-analyzing-performance-of-a-haskell-program

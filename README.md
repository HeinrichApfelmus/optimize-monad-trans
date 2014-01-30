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


Specific example
----------------

The module [`OptimizeMonadTrans`](OptimizeMonadTrans.hs) implements a traversal

    traverseTree :: Monad m => (a -> m [a]) -> a -> m ()

which is then applied to a tree

    evaluate :: Tree -> Eval [Tree]

The goal is to have `ghc -O` inline the monad `Eval` to the point that the traversal becomes a tight inner loop.

Different implementations for the `Eval` monad can yield different results:

* The module [`Eval1`](Eval1.hs) implementes a two-level `ReaderT` transformer. The resulting core [`OptimizeMonadTrans.core1.hs`](OptimizeMonadTrans.core1.hs) is not good, it allocates closures.

* The module [`Eval2`](Eval2.hs) uses a single level `ReaderT`. The resulting core [`OptimizeMonadTrans.core2.hs`](OptimizeMonadTrans.core2.hs) is very good, the traversal is inlined into a tight inner loop.

The module [`Reader`](Reader.hs) implements the reader transformer. The goal is to add various INLINE pragmas to its implementation, so that `Eval1` will be inlined just as well as `Eval2` is. But how??

A [`Makefile`](Makefile) helps with compiling. The commands

    $ make core1
    $ make core2

will compile the main module using `Eval1` or `Eval2` respectively and output the corresponding GHC core.

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

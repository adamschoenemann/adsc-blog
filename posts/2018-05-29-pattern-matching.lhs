---
title: Pattern matching ADTs
---
This post is about implementing coverage checking of pattern matches using Haskell.
It does not involve any super-advanced type-level trickery, so as long you\'re 
somewhat comfortable with monad transformers you should be fine.

Introduction
------------
Pattern matching coverage on generalized algebraic data types is a complicated problem, and 
has seen many attempts at a solution in recent years. In contrast, pattern matching 
on ordinary ADTs is often simply mentioned as a trivial matter and delegated to 
a footnoote. When I recently had to implement a coverage checking algorithm in a 
Haskell-like language *without* GADTs, I found that there was a dearth of 
information (which was not paywalled) on how to go about such a problem. 
Specifically, I needed to disallow not only non-exhaustive matches but also
redundant matches.
Eventually, I devised a solution that is a small modification of a well-known algorithm.
I don\'t expect that there is anything academically novel about my modification,
but I do wish that I hadn\'t spent so much time searching in vain for a ready-made solution.
This blog post is my attempt at rectifying this state of affairs for those that 
come after me!

When dealing with pattern matching clauses, we can typically encounter two kinds
of problems:

- The clauses are non-exhaustive; for example
  ``` haskell
  case xs of
    [] -> ...
  ```
  In this example, we have clearly not dealt with the case where `xs` is a cons
  constructed list. If we accept such a match we can introduce divergence
  into our language very easily.
- There are one or more redundant clauses; for example
  ``` haskell
  case xs of
    [] -> ...
    x : xs' -> ...
    xs' -> ...
  ```
  In this example, the last branch is essentially dead code, as it will never
  be reached.

The only information I could find on the internet on coverage checking was Conor McBride\'s
[great StackOverflow answer][1] which explains the core idea [behind Lennart Augustsson\'s 
technique for compiling pattern matches][3]. I also found a kindred spirit in 
Tim Humphries who had encountered the same lack of information and devised
[an algorithm using tries][2].

The problem was that I could not get McBride\'s explanation to account for
*redundant pattern matches*. McBride explains how to use the algorithm to flag
*overlapping patterns*, but this is too strong a requirement. For example,
``` haskell
case xs of
  [] -> ...
  xs' -> ...
```
would be flagged as an issue, since `xs'` strictly overlaps with `[]`. But this
is rarely what we want since we often use catch-all patterns for convenience.

While I only took a cursory look at Tim Humphries\' implementation, 
it did not appear to make any attempt at checking anything beyond exhaustivity,
so I could not steal his code shamelessly either.

After pouring over McBride\'s explanation for many hours, I eventually discovered
how to modify it to suit my needs by introducing just a tiny bit of extra state.

The language
------------
With that out of the way, let us start modeling our problem in Haskell.

Since this is a literate Haskell file, we\'ll kick things off with some obligatory
language extensions and imports.

\begin{code}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

import Control.Monad.Except (ExceptT, runExceptT, MonadError, throwError)
import Control.Monad.State (StateT, runStateT, MonadState, get, modify)
import Control.Monad.Reader (Reader, runReader, MonadReader, asks, local)
import Data.Foldable (foldlM)
import Control.Monad (replicateM)
import Data.Maybe (catMaybes)
\end{code}

None of these extensions or imports should worry you right now.

We need to define the language of types and patterns we\'ll be working on. Lets keep
it simple.

\begin{code}
data Type 
  = TConstr String
  deriving (Eq, Show)

data Pattern ident
  = PBind ident
  | PMatch String [Pattern ident]
  deriving (Eq, Show)
\end{code}

Types are just an open set of nullary type constructors. So for example `Unit` or `Boolean`
or `IntList`. Our language does not have polymorphism, but the algorithm will work
fine with a bit of extra machinery for polymorphic types as well ([demonstration][Coverage.hs]).

Patterns are only slightly more complicated. A pattern can *bind* a value or it can *match*
(destructure) a value. As an example, the clauses in
```haskell
case xs of
  Cons x xs' -> ...
  xs' -> ...
```
would be encoded as
```haskell
[ PMatch "Cons" [PBind "x", PBind "xs'"]
, PBind "xs"
]
```
We\'ll refrain from use infix pattern-operators like `(:)` and instead use their
\"ordinary\" prefix-form names (e.g. `Cons` for `(:)`) just to simplify our implementation and presentation.

You\'ll notice that `Pattern` is parameterized over `ident`. We use this to 
distinguish patterns with user-given names and fresh machine-generated 
names.

An initial algorithm
-------------
Disclaimer: just to be absolutely clear, this algorithm is mostly due to
[Augustsson][3] and just a small extension of the outline provided by [Conor
McBride\'s StackOverflow answer][1]. I don\'t pretend to have invented anything
novel.

Here is a sketch of how the algorithm works.

\newcommand{\head}[0]{\mathsf{head}}
\newcommand{\tail}[0]{\mathsf{tail}}
\newcommand{\coveredBy}[0]{\mathsf{coveredBy}}

The expression $q\, \coveredBy\, ρ$ checks if an \"ideal pattern\" $q$ is covered by a list 
of actual patterns $ρ$. The ideal pattern starts off being a simple name-binding pattern,
and is further refined when needed through the algorithm.

- If $ρ$ is the empty list, then we cannot cover $q$ and the match is not exhaustive.
- If there is a substitution of variables $υ$ in $q$ 
  such that $υ\, q$ ($υ$ applied to $q$) equals $\head(ρ)$ then:
  - If the substitution $υ$ is an *injective renaming
    of variables*, then we know that $q$ is fully covered by $\head(ρ)$.
    Such a substitution only maps variables to variables.
  - Otherwise, then there is a mapping in $υ$ that maps a variable $x_1$ to a constructor.
    For each constructor $c_i$ of $x_1$\'s type, apply the substitution
    $\left[x_1 ↦ c_i\right]$
    to $q$ giving $q'$, and solve $q'\, \coveredBy\, ρ$.
- If no such substitution exists, then $q$ cannot be covered by $\head(ρ)$ and so we
  recurse with $q\, \coveredBy\, \tail(ρ)$.

An example
==========
The algorithm above will not detect redundant patterns, but before we extend it to do so, let us
see an example:
``` haskell
case xs of 
  Nil -> ...
  Cons x' xs' -> ...
```
This gives the problem `xs coveredBy [Nil, Cons x' xs']`

We start comparing `xs` to `Nil`. There is a valid substitution $υ$, namely 
`[xs ↦ Nil]`. 
Since `Nil` is not a variable, $υ$ is not injective, so we have to \"split\"
on `xs` with each list constructor, giving us problems:

```
Nil coveredBy [Nil, Cons x' xs']
Cons a´ b´ coveredBy [Nil, Cons x' xs']
```
Here, `a´` and `b´` are fresh names, so we postfix them with a tick for clarity.

The first sub-problem
has a solution of the empty substitution (which is injective) so we can discharge that.
The second sub-problem will first try to find a substitution to unify `Cons a´ b´` and
`Nil`, but no such substitution exists, so we\'ll discard `Nil` and move on to the next
pattern.

```
Cons a´ b´ coveredBy [Cons x' xs']
```

There is an obvious injective substitution, namely `[a´ ↦ x', b´ ↦ xs']`, and the algorithm
terminates with success.

Redundant patterns
------------------
In McBride\'s answer, he shows how to detect any *overlapping* patterns. Whenever we discharge
a case through an injective substitution, we can check that there are no other covering 
patterns in our list. To use his example:
``` haskell
case xs of
  Nil -> ...
  ys -> ...
```
```
xs coveredBy [Nil, ys]
  Nil coveredBy [Nil, ys] <-- overlap with ys
  Cons a´ b´ coveredBy [Nil, ys]
```

But this is not what we really want, since we want to permit catch-all patterns. My solution
was to simply keep track of how many times a clause was used to discharge an ideal pattern,
and then check that every clause was used at least once after the algorithm terminated. 
Using this scheme, the example above would be permitted, whereas

``` haskell
case xs of 
  Nil -> ...
  Cons x' xs' -> ...
  ys -> ... 
```

would be flagged, since the last clause is redundant.

Now that we\'ve extended the original algorithm a bit and we have a better understanding
of the problem, we can try to write a more detailed algorithm in pseudo-Haskell before
proceeding to the implementation.

``` Haskell
checkCoverage :: IdealPattern -> List of Clauses -> Success or Failure
checkCoverage q ρ =
  if q `coveredBy` ρ
    then if any ρᵢ was not used return Failure (ρᵢ is redundant)
    else Success
  
coveredBy :: IdealPattern -> List of Clauses -> Success or Failure
q `coveredBy` ρ =
  if ρ is the empty list
    then Failure (q is not covered!)
  else 
    let υ = a substitution such that υ q = (head ρ)   or  nothing
    if υ is nothing
      then q `coveredBy` (tail ρ)
    else 
      if υ is injective 
        then increment the usages of (head ρ) with 1
        else 
          let x = the variable in q that must map to some constructor
          let τ = typeOf x
          for each c in (constructorsOf τ)
            let q' = q with x substituted for c
            q' `coveredBy` ρ
```

Implementation
--------------
We\'ll start by formalizing some of the concepts used in the pseudo-code algorithm.

\begin{code}
type Name = String
type ClausePattern = Pattern Name
type FreshName = Integer
type IdealPattern = Pattern FreshName
\end{code}

These type synonyms will just make our code a bit more readable.
We\'ll also need to fetch the constructors for a type at some point, so let\'s define those:

\begin{code}
data Constructor = Constructor Name [Type]
\end{code}

For example, the constructors of `IntList` are `Constructor "Nil" []` and 
`Constructor "Cons" [TConstr "Int", TConstr "IntList"]`.

The pseudo-code mentions substitutions, so lets define what a substitution 
actually is.

\begin{code}
newtype Subst ident = Subst { unSubst :: [(FreshName, Pattern ident)] }
  deriving (Eq, Show, Monoid)
\end{code}

We\'ll just use a newtype wrapper around an associative list. A more efficient implementation
would of course be a `Map`, but for now let\'s keep things simple. Note that the domain
of the substitution will alwas be `FreshName` since we never touch the patterns
that the user has defined.

Using structural recursion over `Pattern` we can apply a substitution
to a pattern, giving us a new pattern.

\begin{code}
apply :: Subst FreshName -> Pattern FreshName -> Pattern FreshName
apply (Subst assocs) = go where
  go (PBind i) 
    | Just pat' <- lookup i assocs = pat'
    | otherwise                    = PBind i
  go (PMatch nm subpats) =
    PMatch nm (map go subpats)
\end{code}

We\'ll also need to know if a substitution is injective. We\'ll use a new data type
to represent this.

\begin{code}
data IsInjectiveResult
  = Injective
  | NotInjective FreshName
  deriving (Show, Eq)
\end{code}

A substitution is either injective, or not-injective due to a binding. This data type is
isomorphic to `Maybe` but `Maybe`\'s established semantics do not fit very well to this
problem, we we\'ll use our own data type.

We can easily establish whether a substitution is injective by recursing over the list
it wraps.

\begin{code}
isInjective :: Subst ident -> IsInjectiveResult
isInjective (Subst xs) = go xs where
  go [] = Injective
  go ((b, p) : xs') =
    case p of
    PBind _    -> go xs'
    PMatch _ _ -> NotInjective b
\end{code}

If we look at the pseudo-Haskell algorithm, we can identify some helper functions that
we will most definitely need. We can also see that the computation must be able to
fail in a few different ways. Seems like we\'ll need a monad! 
We can create a type class that allows us to abstract over the exact representation of
our computation, which will force us to stay at the domain-level when we\'re writing
the implementation.

\begin{code}
class Monad m => Coverage m where
  -- get the type of a name-binding
  getType :: FreshName -> m Type
  -- get the constructors of a type
  getConstructors :: Type -> m [Constructor]
  -- extend the computation with bindings of names to types
  withTypes :: [(FreshName, Type)] -> m a -> m a
  -- get a fresh name
  freshName :: m FreshName
  -- fail a coverage check
  coverageError :: CoverageError -> m a
\end{code}

A coverage-check can fail for the reasons specified in the pseudo-Haskell, but we could
also encounter some more \"low-level\" errors, like malformed patterns, empty types or 
a failing lookup of types or constructors.

\begin{code}
data CoverageError
  = RedundantClauses [ClausePattern]
  | CannotCover IdealPattern
  | MalformedPattern ClausePattern
  | EmptyType Type
  | NoTypeFound FreshName
  | NoConstructorsFound Type
  deriving (Show, Eq)
\end{code}

Since we\'re associating a number (usages) with each input clause, we\'ll create a
datatype to maintain this association.

\begin{code}
data Clause = Clause { usages :: Integer, pattern :: ClausePattern }

useClause :: Clause -> Clause
useClause br = br { usages = usages br + 1 }
\end{code}

Looking at the specification, we could make do with a boolean field since we only
keep track of the used/not-used state of clauses. I\'ll stick with the `Integer`
field though, as it could potentially be useful information, for debugging 
purposes if nothing else.

With the main plumbing out of the way, we can jump right into the implementation of
the `coveredBy` function, which checks that the patterns are exhaustive and updates
the clauses with their number of usages.

coveredBy
=========

\begin{code}
-- the explicit forall is so we can refer back to `m` in the signature of the
-- where-binding
coveredBy :: forall m. (Coverage m) => IdealPattern -> [Clause] -> m [Clause]
coveredBy ideal [] = coverageError (CannotCover ideal)
coveredBy ideal (clause : clauses) = 
  ideal `hasSubst` pattern clause >>= \case
    Nothing -> 
      (clause :) <$> coveredBy ideal clauses

    Just subst ->
      case isInjective subst of
        Injective -> 
          pure (useClause clause : clauses)

        NotInjective binding -> do
          typ <- getType binding
          constructors <- getConstructors typ
          foldlM (coveredByRefined binding) (clause : clauses) constructors

  where
    coveredByRefined :: FreshName -> [Clause] -> Constructor -> m [Clause]
    coveredByRefined fname clauses' constructor = do
      (refineTo, refinedTypes) <- constructorToPattern constructor
      let refined = apply (Subst [(fname, refineTo)]) ideal
      withTypes refinedTypes (refined `coveredBy` clauses')
\end{code}

We update the usages of the clauses by returning them from the function. Even if we do
not use a clause, we will still need to return it, so it won\'t \"disappear\"
from the set of clauses for the next sub-problem. The main divergence from the 
pseudo-Haskell is the `coveredByRefined` helper function, which is iterated over the
constructors of the type of the binding that we\'re splitting on. It uses the
`constructorToPattern` function to convert a constructor of a type to a pattern.

constructorToPattern
====================
\begin{code}
constructorToPattern :: Coverage m => Constructor -> m (IdealPattern, [(FreshName, Type)])
constructorToPattern (Constructor nm args) = do
  let arglen = length args
  freshNames <- replicateM arglen freshName
  let typeAssocs = zip freshNames args
  pure (PMatch nm (map PBind freshNames), typeAssocs)
\end{code}

Here we both generate fresh names to stand in for the arguments of the constructor, but
we also return a list associating the names to their appropriate types.

hasSubst
========
We also need to know if an ideal pattern can transformed into a covering pattern through
a substitution, which we can define as

\begin{code}
hasSubst :: Coverage m => IdealPattern -> ClausePattern -> m (Maybe (Subst Name))
hasSubst (PBind x) pat = pure . pure $ Subst [(x, pat)]
hasSubst (PMatch nm1 pats1) (PMatch nm2 pats2)
  | nm1 /= nm2 = 
      pure Nothing
  | length pats1 /= length pats2 = 
      coverageError (MalformedPattern (PMatch nm2 pats2))
  | null pats1 = pure (Just mempty)
  | otherwise = 
      mconcat <$> (sequence (zipWith hasSubst pats1 pats2))
hasSubst (PMatch _ _) (PBind _) = pure (Just mempty)
\end{code}

- $x\, \mathsf{hasSubst}\, p$ is always the substitution $[x ↦ p]$.  
- $(c\, p_1 \dots p_n)\; \mathsf{hasSubst}\; (c\, p'_1 \dots p'_n)$ is just the
   concatenation of the substitutions of the sub-patterns.  
- The last case is somewhat interesting as it says that
  $(c\, p_1 \dots p_n)\; \mathsf{hasSubst}\; x$ is just the empty substitution.
  This is contrary to Augustsson\'s method, where this is not true. Instead, the clauses
  are refined along with the ideal pattern, so such a case does not occur. I could not find
  a good reason to do this though, so I chose to bake in this notion of generality instead.

checkCoverage
=============
We can now put the icing on the cake and define the function that actually
aplies the coverage checking algorithm!

\begin{code}
checkCoverage :: Coverage m => IdealPattern -> [ClausePattern] -> m ()
checkCoverage ideal userpats = do
  checkedClausees <- ideal `coveredBy` (map asClause userpats) 
  case unusedPatterns checkedClausees of
    [] -> pure ()
    unreached -> coverageError $ RedundantClauses unreached
  where 
    asClause pat = Clause { usages = 0, pattern = pat }

    unusedPatterns clauses = 
      let onlyUnused = \cl -> if usages cl < 1 then Just (pattern cl) else Nothing
      in  catMaybes (map onlyUnused clauses)
\end{code}

It is very like the pseudo-Haskell specification, but with a bit more book-keeping to
set up and tear down the state we need.

Testing our code
-----------------
Now, we can start working out how to actually run and test our algorithm. We have to start
by picking a concrete datatype to implement our `Coverage` type class.

\begin{code}
newtype CoverageM r = CoverageM 
  { unCoverageM :: 
      ExceptT 
        CoverageError 
        (StateT CoverageState (Reader CoverageRead)) r 
  }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError CoverageError
           , MonadState CoverageState
           , MonadReader CoverageRead
           )

data CoverageRead = CoverageRead 
  { crTypes :: [(FreshName, Type)]
  , crConstructors :: [(Type, [Constructor])]
  }

type CoverageState = Integer
\end{code}

We use the `GeneralizedNewtypeDeriving` language extension along with monad transformers to
derive a bunch of nifty functionality for us! If you\'re not familiar with monad transformers,
this might look a bit arcane, but it really is just boilerplate. To keep things simple, we
again use associative lists where `Map` might be more appropriate.

We can now make our `CoverageM` monad an instance of our `Coverage` type class, and
then define a way to run a computation in our monad.

\begin{code}
instance Coverage CoverageM where
  getType uid = 
    asks crTypes
    >>= maybe (coverageError $ NoTypeFound uid) pure . lookup uid

  getConstructors typ = 
    asks crConstructors
    >>= maybe (coverageError $ NoConstructorsFound typ) noEmptyTypes . lookup typ
    where
      noEmptyTypes [] = coverageError (EmptyType typ)
      noEmptyTypes cs = pure cs
  
  withTypes types = local (\r -> r { crTypes = types ++ crTypes r })
  
  freshName = get >>= (\i -> modify (+1) >> pure i)
  
  coverageError = throwError

runCoverageM
  :: CoverageState
  -> CoverageRead
  -> CoverageM a
  -> (Either CoverageError a, CoverageState)
runCoverageM st rd (CoverageM x) = 
  runReader (runStateT (runExceptT x) st) rd
\end{code}

Finally, we can test our algorithm on some example inputs. Normally, I would use a testing
framework like [Tasty][4], but for this blog post let us just do some quick and dirty
testing.

\begin{code}
test :: IO ()
test = do
  let tunit = TConstr "Unit"
  specify "simple tests" $ do
    let rd = CoverageRead [0 |-> tunit] [tunit |-> [Constructor "MkUnit" []]]

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "MkUnit" []])
      `shouldBe` (Right (), 0)

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "Just" []])
      `shouldBe` (Left (CannotCover (PMatch "MkUnit" [])), 0)

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "MkUnit" [], PBind "x"])
      `shouldBe` (Left (RedundantClauses [PBind "x"]), 0)

  specify "slightly more advanced" $ do
    let rd = CoverageRead 
          [ 0 |-> TConstr "UnitList" ] 
          [ TConstr "UnitList" |-> 
            [ Constructor "Nil" []
            , Constructor "Cons" [tunit, tunit]
            ]
          , tunit |-> [Constructor "MkUnit" []]
          ]

    specify "shallow match works" $ do
      let branches = [PMatch "Cons" [PBind "x", PBind "xs"], PMatch "Nil" []]
      runCoverageM 0 rd (checkCoverage (PBind 0) branches) `shouldBe` (Right (), 2)

    specify "deep matching on head works" $ do
      let branches = [PMatch "Cons" [PMatch "MkUnit" [], PBind "xs"], PMatch "Nil" []]
      runCoverageM 0 rd (checkCoverage (PBind 0) branches) `shouldBe` (Right (), 2)

    specify "deep matching on head works" $ do
      let branches = [PMatch "Cons" [PMatch "MkUnit" [], PBind "xs"], PMatch "Nil" []]
      runCoverageM 0 rd (checkCoverage (PBind 0) branches) `shouldBe` (Right (), 2)

  putStrLn "All tests succeeded"
  pure ()
  where
    specify :: String -> IO () -> IO ()
    specify = flip const
    (!x) `shouldBe` (!y)
      | x == y = pure ()
      | otherwise = error $ "Expected " ++ show x ++ " to equal " ++ show y
    (|->) x y = (x,y)
\end{code}

These tests are hardly exhaustive, but they will do for our purposes. Since this algorithm
is quite simple yet has real-world uses, it\'d be a fun exercise to write some property-based
tests for it, or even to prove some simple properties about it. Off the top of my head, I
can think of

- If `q` is successfully covered by `ρ`, then duplicating any pattern `ρᵢ` in `ρ` will
  cause a redundant-pattern error with `ρᵢ`.
- If `q` is not covered by `ρ`, we can fix it by inserting a catch-all pattern
  into the end of `ρ`.
- If `q` is covered by `ρ`, then ``q `coveredBy` (PBind "x" : ρ)`` will cause a 
  redundant-pattern error with `ρ`.

Furthermore, a space/time complexity analysis of the algorithm should also be an 
interesting (yet surmountable) task. Haskell\'s lazy semantics are quite useful,
but always provide for extra challenge when attempting to reason about the
runtime characteristics of your code.
  
That\'s it for now, thanks for reading!


[1]: https://stackoverflow.com/questions/7883023/algorithm-for-type-checking-ml-like-pattern-matching
[2]: https://teh.id.au/posts/2017/03/10/simple-exhaustivity/index.html
[3]: https://dl.acm.org/citation.cfm?id=5303
[4]: https://hackage.haskell.org/package/tasty

[Coverage.hs]: https://github.com/adamschoenemann/clofrp/blob/master/library/CloFRP/Check/Coverage.hs
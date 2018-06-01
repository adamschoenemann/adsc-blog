---
title: Pattern matching ADTs
---
This post is about implementing coverage checking of pattern matches in Haskell.
It does not involve any super-advanced type-level trickery, so if you're comfortable
reading just-above-basic Haskell you should be fine.

Introduction
------------
Pattern matching coverage on generalized algebraic datatypes is a complicated problem, and 
has seen many attempts at a solution in recent years. Pattern matching 
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
    (x : xs') -> ...
    xs' -> ...
  ```
  In this example, the last branch is essentially dead code, as it will never
  be reached.

The only information I could find on the internet on coverage checking was Conor McBride\'s
[great StackOverflow answer][1] which explains the core idea behind Lennart Augustsson\'s 
technique for compiling pattern matches. I also found a kindred spirit in 
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

While I only took a cursory look at Tim Humphries' implementation, 
it did not appear to make any attempt at checking anything beyond exhaustivity,
so I could not steal his code shamelessly either.

After pouring over McBride's explanation for many hours, I eventually discovered
how to modify it to suit my needs by introducing just a tiny bit of extra state.

The algorithm
-------------
Disclaimer: just be absolutely clear, this algorithm is mostly due to
[Augustsson][3] and just a small extension of the outline provided by [Conor
McBride\'s StackOverflow answer][1]. I don\'t pretend to have invented anything
novel.

With that out of the way, let us start directly modeling our problem in Haskell.

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





here is a sketch of how the algorithm works.

The problem is to check if an *ideal pattern* $q$ is covered by a set of
pattern-matching clauses $ρ$. If there is a substitution of variables $υ$ in $q$ 
such that $υ q$ ($υ$ applied to $q$) equals $ρ_1$ then we can say that $ρ_1$
is an *instance* of $q$. If, furthermore, the substitution $υ$ is an *injective renaming
of variables*, then we know that 



Implementation
--------------

To kick things off, the obligatory language extensions and some imports


\begin{code}
-- import Debug.Trace

trace _ x = x
traceM _ = pure ()

\end{code}
First, we must define a simple language to work with

\begin{code}
type Name = String
data Type 
  = TConstr Name
  | TUnit 
  | TInt
  deriving (Eq, Show)

data Pattern ident
  = PBind ident
  | PMatch Name [Pattern ident]
  deriving (Eq, Show)

type UserPattern = Pattern Name
type UniqueIdent = Integer
type IdealPattern = Pattern UniqueIdent

data CoverageError
  = RedundantBranches [UserPattern]
  | CannotCover IdealPattern
  | MalformedPattern UserPattern
  | EmptyType Type
  | NoTypeFound UniqueIdent
  | NoConstructorsFound Type
  deriving (Show, Eq)

data Constructor = Constructor Name [Type]

class (Monad m, MonadState CoverageState m, MonadError CoverageError m) 
  => Coverage m where
      getType :: UniqueIdent -> m Type
      getConstructors :: Type -> m [Constructor]
      withTypes :: [(UniqueIdent, Type)] -> m a -> m a

data CoverageRead = CoverageRead 
  { crTypes :: [(UniqueIdent, Type)]
  , crConstructors :: [(Type, [Constructor])]
  }

type CoverageState = Integer

newtype CoverageM r = CoverageM 
  { unCoverageM 
      :: ExceptT 
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

runCoverageM
  :: CoverageState
  -> CoverageRead
  -> CoverageM a
  -> (Either CoverageError a, CoverageState)
runCoverageM st rd (CoverageM x) = 
  runReader (runStateT (runExceptT x) st) rd
  
instance Coverage CoverageM where
  getType uid = 
    asks crTypes
    >>= maybe (throwError $ NoTypeFound uid) pure . lookup uid

  getConstructors typ = 
    asks crConstructors
    >>= maybe (throwError $ NoConstructorsFound typ) pure . lookup typ
  
  withTypes types = local (\r -> r { crTypes = types ++ crTypes r })


constructorToPattern :: MonadState UniqueIdent m => Constructor -> m (IdealPattern, [(UniqueIdent, Type)])
constructorToPattern (Constructor nm args) = do
  let arglen = length args
  newIdents <- replicateM arglen newIdent
  let typeAssocs = zip newIdents args
  pure (PMatch nm (map PBind newIdents), typeAssocs)
  where
    newIdent = get >>= (\i -> modify (+1) >> pure i)

data Branch = Branch { usages :: Integer, pattern :: UserPattern }

useBranch :: Branch -> Branch
useBranch br = br { usages = usages br + 1 }

newtype Subst ident = Subst { unSubst :: [(UniqueIdent, Pattern ident)] }
  deriving (Eq, Show, Monoid)

apply :: Subst UniqueIdent -> Pattern UniqueIdent -> Pattern UniqueIdent
apply (Subst assocs) = go where
  go pat@(PBind i) 
    | Just pat' <- lookup i assocs = pat'
    | otherwise = pat
  go (PMatch nm subpats) =
    PMatch nm (map go subpats)

hasSubst :: MonadError CoverageError m => IdealPattern -> UserPattern -> m (Maybe (Subst Name))
hasSubst (PBind x1) pat = pure . pure $ Subst [(x1, pat)]
hasSubst (PMatch nm1 pats1) pat@(PMatch nm2 pats2)
  | nm1 /= nm2 = 
      pure Nothing
  | length pats1 /= length pats2 = 
      throwError (MalformedPattern pat)
  | null pats1 = pure (Just mempty)
  | otherwise = 
      mconcat <$> (sequence $ (zipWith hasSubst pats1 pats2))
hasSubst (PMatch _ _) _pat = pure (Just mempty)

data IsInjectiveResult
  = Injective
  | NotInjective UniqueIdent
  deriving (Show, Eq)

isInjective :: Subst ident -> IsInjectiveResult
isInjective (Subst []) = Injective
isInjective (Subst ((b,p):xs)) =
  case p of
    PBind _ -> isInjective (Subst xs)
    PMatch _ _ -> NotInjective b

checkCoverage 
  :: Coverage m
  => IdealPattern -> [UserPattern] -> m ()
checkCoverage ideal userpats = do
  checkedBranches <- (ideal `coveredBy` (map asBranch userpats)) 
  let unreached = unusedPatterns checkedBranches
  if length unreached > 0
    then throwError $ RedundantBranches unreached
    else pure ()
  where 
    asBranch pat = Branch { usages = 0, pattern = pat }

    unusedPatterns clauses = 
      let onlyUnused = \br -> if usages br < 1 then Just (pattern br) else Nothing
      in  catMaybes (map onlyUnused clauses)

coveredBy 
  :: forall m. (Coverage m)
  => IdealPattern -> [Branch] -> m [Branch]
coveredBy ideal [] = throwError (CannotCover ideal)
coveredBy ideal (branch : branches) = 
  hasSubst ideal (pattern branch) >>= \case
    Nothing -> do
      traceM (show ideal ++ " not covered by " ++ show (pattern branch))
      (branch :) <$> coveredBy ideal branches

    Just subst ->
      case isInjective subst of
        Injective -> do
          traceM (show ideal ++ " covered by " ++ show (pattern branch)) 
          pure (useBranch branch : branches)

        NotInjective ident -> do
          traceM $ "not injective: " ++ show subst
          typ <- getType ident
          splitOn ident typ (branch : branches)

  where
    splitOn :: UniqueIdent -> Type -> [Branch] -> m [Branch]
    splitOn ident typ branches' = 
      getConstructors typ >>= \case
        [] -> 
          throwError (EmptyType typ)

        constructors -> 
          foldlM (coveredByRefined ident) branches' constructors
    
    coveredByRefined ident branches' constructor = do
      (refineTo, refinedTypes) <- constructorToPattern constructor
      let refined = apply (Subst [(ident, refineTo)]) ideal
      trace ("refined: " ++ show ident ++ " to " ++ show refined) 
        $ withTypes refinedTypes
        $ coveredBy refined branches'


  
test :: IO ()
test = do
  specify "simple tests" $ do
    let rd = CoverageRead [0 |-> TUnit] [TUnit |-> [Constructor "MkUnit" []]]

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "MkUnit" []])
      `shouldBe` (Right (), 0)

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "Just" []])
      `shouldBe` (Left (CannotCover (PMatch "MkUnit" [])), 0)

    runCoverageM 0 rd (checkCoverage (PBind 0) [PMatch "MkUnit" [], PBind "x"])
      `shouldBe` (Left (RedundantBranches [PBind "x"]), 0)

  specify "slightly more advanced" $ do
    let rd = CoverageRead 
          [ 0 |-> TConstr "UnitList" ] 
          [ TConstr "UnitList" |-> 
            [ Constructor "Nil" []
            , Constructor "Cons" [TUnit, TUnit]
            ]
          , TUnit |-> [Constructor "MkUnit" []]
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

[1]: https://stackoverflow.com/questions/7883023/algorithm-for-type-checking-ml-like-pattern-matching
[2]: https://teh.id.au/posts/2017/03/10/simple-exhaustivity/index.html
[3]: https://dl.acm.org/citation.cfm?id=5303
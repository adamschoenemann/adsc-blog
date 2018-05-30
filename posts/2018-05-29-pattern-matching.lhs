---
title: Pattern matching ADTs
---
Pattern matching on generalized algebraic datatypes is a complicated problem, and 
has seen many attempts at a solution in recent years. Pattern matching 
on ordinary ADTs is often simply mentioned as a trivial matter and delegated to 
a footnoote. When I recently had to implement a coverage checking algorithm in a 
Haskell-like language *without* GADTs, I found that there was a dearth of 
information (which was not paywalled) on how to go about such a problem. 
This blog post is my attempt at rectifying this state of affairs for those that 
come after me!

To kick things off, the obligatory language extensions and some imports

\begin{code}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Monad.Except (ExceptT, runExceptT, MonadError, throwError)

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
  = RedundantBranch UserPattern
  | CannotCover IdealPattern
  deriving (Show, Eq)

class (Monad m, MonadError CoverageError m) => Coverage ident m where
  getType :: ident -> m Type
  getConstructors :: Type -> m [Pattern ident]

data Branch = Branch { usages :: Integer, pattern :: UserPattern }

newtype Subst = Subst { unSubst :: [(UniqueIdent, UserPattern)] }

checkCoverage 
  :: (MonadError CoverageError m)
  => IdealPattern -> [UserPattern] -> m ()
checkCoverage ideal userpats = (ideal `coveredBy` (map asBranch userpats)) >> pure () where
  asBranch pat = Branch { usages = 0, pattern = pat }

coveredBy 
  :: (MonadError CoverageError m)
  => IdealPattern -> [Branch] -> m [Branch]
coveredBy ideal [] = throwError (CannotCover ideal)
coveredBy ideal (branch:branches) = undefined

  



\end{code}

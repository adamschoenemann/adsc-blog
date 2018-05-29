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

First, we must define a simple language to work with

\begin{code}
newtype Ident = { unIdent :: String }
data Expr  
  = Var Ident -- ^ x
  | Lam Ident Type Expr -- λ(x: A). e 
  | App Expr Expr -- e1 e2
\end{code}

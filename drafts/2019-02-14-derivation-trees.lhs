---
title: Derivation trees
---

\begin{code}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Data.Map (Map)
import qualified Data.Map as M
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Applicative (Alternative(..))
import           Data.Text (Text)
import           Data.Tree
import qualified Data.Text as T
import           Lens.Micro.Platform

infixr 2 :->

data Ty = Ty :-> Ty | TyInt deriving (Eq, Show)

type Name = Text

infixl 9 :@:

data Exp
  = Var Name
  | Abs (Name, Ty) Exp
  | Exp :@: Exp
  | Const Integer
  deriving (Eq, Show)


infixr 2 -:>
(-:>) :: (Name, Ty) -> Exp -> Exp
(x, t) -:> e = Abs (x, t) e

infer :: Exp -> Maybe Ty
infer = go mempty where
  go ctx = \case
    Var x -> M.lookup x ctx
    e1 :@: e2 -> do
      t1 :-> t1' <- go ctx e1
      t2 <- go ctx e2
      guard (t1 == t2)
      pure t1'
    Abs (x, t1) e -> do
      t2 <- go (M.insert x t1 ctx) e
      pure (t1 :-> t2)
    Const _i -> pure TyInt


class HasDerivationState s a b | s -> a, s -> b where
  derivationState :: Lens' s (Tree (a, b))

instance HasDerivationState (Tree (a, b)) a b where
  derivationState = id

type MonadDerivation s m a b = (MonadFix m, MonadState s m, HasDerivationState s a b)

deriveFix :: MonadDerivation s m a b => ((a -> m b) -> a -> m b) -> a -> m b
deriveFix f = f (derive (deriveFix f))

derive :: MonadDerivation s m a b => (a -> m b) -> a -> m b
derive computation begin = mdo
  Node x f <- use derivationState
  r2 <- (derivationState .= Node (begin, r2) []) *> computation begin
  b <- use derivationState
  derivationState .= Node x (f ++ [b]) -- TODO: bad performance
  pure r2

type Ctx = Map Name Ty

infer' :: forall s m. (Alternative m, MonadDerivation s m (Ctx, Exp) Ty) => Exp -> m Ty
infer' expr = go (mempty, expr) where
  go :: (Ctx, Exp) -> m Ty
  go (ctx, exp) = case exp of
    Var x ->
     case M.lookup x ctx of
      Just t -> pure t
      Nothing -> fail $ "unknown type for " <> show x
    Abs (x, t1) e -> do
      t2 <- derive go (M.insert x t1 ctx, e)
      pure (t1 :-> t2)
    Const _i -> pure TyInt
    e1 :@: e2 -> do
      t1 :-> t1' <- derive go (ctx, e1)
      t2 <- derive go (ctx, e2)
      guard (t1 == t2)
      pure t1'


newtype CheckM a
  = CheckM { unCheckM :: ExceptT Name (State (Tree ((Ctx, Exp), Ty))) a }
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadState (Tree ((Ctx, Exp), Ty))
    , MonadFix
    , MonadError Name
    )

runCheckM :: Tree ((Ctx, Exp), Ty) -> CheckM a -> (Either Name a, Tree ((Ctx, Exp), Ty))
runCheckM initState checkM = runState (runExceptT (unCheckM checkM)) initState

runCheckMDerivation :: (Exp -> CheckM Ty) -> Exp -> (Either Name Ty, Tree ((Ctx, Exp), Ty))
runCheckMDerivation check init =
  let (r, final) = runCheckM (Node (init, final) []) (check init)
  in  (r, final)

main :: IO ()
main = do
  let (r, tree) = runCheckMDerivation infer' (Const 10)
  putStrLn (drawTree $ fmap show tree)
  print r

\end{code}

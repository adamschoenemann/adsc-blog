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
  deriving (Functor
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

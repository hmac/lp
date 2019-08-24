{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
module Expr
  ( Expr
  , BExpr
  , Context
  , module Expr.Synonym
  , safeTranslate
  , translate
  )
where


import           Data.List                      ( elemIndex
                                                , sort
                                                )
import           Expr.Synonym
import           Expr.Base                      ( Expr
                                                , BExpr
                                                )

-- Convert the frontend syntax into the backend syntax, replacing explicit
-- variable names with De Bruijn indices
translate :: Expr -> BExpr
translate expr = case safeTranslate mempty expr of
  Right e   -> e
  Left  err -> error err

type Context = [(String, Expr)]

-- This function takes a Context as an argument,
-- which is a map from variable names to expressions.
-- To make this usable in the world of BExpr (where all variables are de Bruijn
-- indices into an ordered list of variables) we take the variable names and
-- sort them, and take that as the starting list of variables, as if they were
-- bound in that order.
-- e.g. with a context [(a, ...), (b, ...), (f, ...), (e, ...)]
--           and expression \x. \y. x
--      we pretend to have \a. \b. \e. \f. \x. \y. x
--      which produces     \   \   \   \   \   \   1
-- TODO: recursion scheme
safeTranslate :: Context -> Expr -> Either String BExpr
safeTranslate context = go (sort (map fst context))
 where
  go :: [String] -> Expr -> Either String BExpr
  go ctx = \case
    Var x -> case elemIndex x ctx of
      Just i  -> pure $ Var i
      Nothing -> Left $ "Cannot find variable " ++ x
    Ann e t -> do
      e' <- go ctx e
      t' <- go ctx t
      pure $ Ann e' t'
    App a b -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ App a' b'
    Lam x e -> do
      e' <- go (x : ctx) e
      pure $ Lam () e'
    Pi x t e -> do
      t' <- go ctx t
      e' <- go (x : ctx) e
      pure $ Pi () t' e'
    Type  -> pure Type
    Nat   -> pure Nat
    Zero  -> pure Zero
    Suc e -> do
      e' <- go ctx e
      pure $ Suc e'
    Prod a b -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Prod a' b'
    Sum l r -> do
      l' <- go ctx l
      r' <- go ctx r
      pure $ Sum l' r'
    SumL l -> do
      l' <- go ctx l
      pure $ SumL l'
    SumR r -> do
      r' <- go ctx r
      pure $ SumR r'
    List t -> do
      t' <- go ctx t
      pure $ List t'
    LNil       -> pure LNil
    LCons x xs -> do
      x'  <- go ctx x
      xs' <- go ctx xs
      pure $ LCons x' xs'
    T           -> pure T
    Unit        -> pure Unit
    Void        -> pure Void
    Equal t a b -> do
      t' <- go ctx t
      a' <- go ctx a
      b' <- go ctx b
      pure $ Equal t' a' b'
    Refl a -> do
      a' <- go ctx a
      pure (Refl a')
    EqElim a m mr x y eq -> do
      a'  <- go ctx a
      m'  <- go ctx m
      mr' <- go ctx mr
      x'  <- go ctx x
      y'  <- go ctx y
      eq' <- go ctx eq
      pure $ EqElim a' m' mr' x' y' eq'
    W a b -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ W a' b'
    Sup a b -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Sup a' b'
    Absurd r -> do
      r' <- go ctx r
      pure $ Absurd r'
    Fin r -> do
      r' <- go ctx r
      pure $ Fin r'
    FZero r -> do
      r' <- go ctx r
      pure $ FZero r'
    FSuc r -> do
      r' <- go ctx r
      pure $ FSuc r'
    ProdElim -> pure ProdElim
    NatElim  -> pure NatElim
    ListElim -> pure ListElim
    FinElim  -> pure FinElim

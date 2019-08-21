{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
module Expr where

import           Prelude                 hiding ( pi )

import           Data.Functor.Foldable
import           Data.Eq.Deriving
import           Text.Show.Deriving
import           Data.List                      ( elemIndex
                                                , sort
                                                )

data ExprF b x r -- r: inductive type, b: binder type, x: variable type
  = Var x
  | Ann r r
  | App r r
  | Lam b r
  | Pi b r r
  | Type
  deriving (Show, Eq, Functor)

$(deriveEq1 ''ExprF)
$(deriveShow1 ''ExprF)

-- The frontend syntax
-- Explicit variable names represented as Strings
type FExprF = ExprF String String

-- The backend syntax
-- Variables represented with De Bruijn indices
type BExprF = ExprF () Int

type Expr = Fix FExprF
type BExpr = Fix BExprF

-- Convenience constructors
var :: String -> Expr
var s = Fix (Var s)

ann :: Expr -> Expr -> Expr
ann e t = Fix (Ann e t)

app :: Expr -> Expr -> Expr
app a b = Fix (App a b)

lam :: String -> Expr -> Expr
lam s e = Fix (Lam s e)

pi :: String -> Expr -> Expr -> Expr
pi s t e = Fix (Pi s t e)

type_ :: Expr
type_ = Fix Type

-- Convert the frontend syntax into the backend syntax, replacing explicit
-- variable names with De Bruijn indices
-- TODO: recursion scheme
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
safeTranslate :: Context -> Expr -> Either String BExpr
safeTranslate ctx = go (sort (map fst ctx))
 where
  go :: [String] -> Expr -> Either String BExpr
  go ctx = \case
    Fix (Var x) -> case elemIndex x ctx of
      Just i  -> pure $ Fix (Var i)
      Nothing -> Left $ "Cannot find variable " ++ x
    Fix (Ann e t) -> do
      e' <- go ctx e
      t' <- go ctx t
      pure $ Fix $ Ann e' t'
    Fix (App a b) -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ App a' b'
    Fix (Lam x e) -> do
      e' <- go (x : ctx) e
      pure $ Fix $ Lam () e'
    Fix (Pi x t e) -> do
      t' <- go ctx t
      e' <- go (x : ctx) e
      pure $ Fix $ Pi () t' e'
    Fix Type -> pure $ Fix Type


-- Utilities
mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f = map (\(x, y) -> (x, f y))

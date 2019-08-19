{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
module Expr where

import           Prelude                 hiding ( pi )

import           Data.Functor.Foldable
import           Data.Eq.Deriving
import           Text.Show.Deriving
import           Data.List                      ( elemIndex )

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
translate expr = go [] expr
 where
  go ctx = \case
    Fix (Var x) -> case elemIndex x ctx of
      Just i  -> Fix (Var i)
      Nothing -> error $ "Cannot find variable " ++ x
    Fix (Ann e t ) -> Fix $ Ann (go ctx e) (go ctx t)
    Fix (App a b ) -> Fix $ App (go ctx a) (go ctx b)
    Fix (Lam x e ) -> Fix $ Lam () (go (x : ctx) e)
    Fix (Pi x t e) -> Fix $ Pi () (go ctx t) (go (x : ctx) e)
    Fix Type       -> Fix Type

type Context = [(String, Expr)]

-- Utilities
mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f = map (\(x, y) -> (x, f y))

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Expr where

import Prelude hiding (pi)

import Data.Functor.Foldable
import Data.Eq.Deriving
import Text.Show.Deriving

data ExprF a = Var String
            | Ann a a
            | App a a
            | Lam String a -- TODO: rethink binders?
            | Pi String a a
            | Type
            deriving (Show, Eq, Functor)

$(deriveEq1 ''ExprF)
$(deriveShow1 ''ExprF)

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

type Expr = Fix ExprF

pretty :: Expr -> String
pretty expr = cata f expr
  where f :: ExprF String -> String
        f = \case
              Var v    -> v
              Ann e t  -> e <> " : " <> t
              App x y  -> x <> " " <> y
              Lam v e  -> "(λ" <> v <> ". " <> e <> ")"
              Pi x t e -> "∀ (" <> x <> " : " <> t <> "). " <> e
              Type     -> "Type"

pp :: Expr -> IO ()
pp = putStrLn . pretty

type Context = [(String, Expr)]

-- Utilities
mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f = map (\(x, y) -> (x, f y))

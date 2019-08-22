{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
module Expr where

import           Prelude                 hiding ( pi
                                                , sum
                                                )

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
  | Nat
  | Zero
  | Suc r
  | NatElim r r r r
  | Prod r r
  | ProdElim r r
  | Sum r r
  | SumL r
  | SumR r
  | SumElim r r r
  | List r
  | LNil
  | LCons r r
  | ListElim r r r r
  | T    -- T : Type
  | Unit -- Unit : T
  | Void
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

nat :: Expr
nat = Fix Nat

zero :: Expr
zero = Fix Zero

suc :: Expr -> Expr
suc = Fix . Suc

natElim :: Expr -> Expr -> Expr -> Expr -> Expr
natElim m mz ms k = Fix $ NatElim m mz ms k

prod :: Expr -> Expr -> Expr
prod a b = Fix $ Prod a b

prodElim :: Expr -> Expr -> Expr
prodElim f p = Fix $ ProdElim f p

sum :: Expr -> Expr -> Expr
sum l r = Fix $ Sum l r

suml :: Expr -> Expr
suml = Fix . SumL

sumr :: Expr -> Expr
sumr = Fix . SumR

sumElim :: Expr -> Expr -> Expr -> Expr
sumElim lf rf s = Fix $ SumElim lf rf s

list :: Expr -> Expr
list = Fix . List

lnil :: Expr
lnil = Fix LNil

lcons :: Expr -> Expr -> Expr
lcons x xs = Fix $ LCons x xs

listElim :: Expr -> Expr -> Expr -> Expr -> Expr
listElim m l s f = Fix $ ListElim m l s f

tt :: Expr
tt = Fix T

unit :: Expr
unit = Fix Unit

void :: Expr
void = Fix Void

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
    Fix Type    -> pure $ Fix Type
    Fix Nat     -> pure $ Fix Nat
    Fix Zero    -> pure $ Fix Zero
    Fix (Suc e) -> do
      e' <- go ctx e
      pure $ Fix $ Suc e'
    Fix (NatElim m mz ms k) -> do
      m'  <- go ctx m
      mz' <- go ctx mz
      ms' <- go ctx ms
      k'  <- go ctx k
      pure $ Fix $ NatElim m' mz' ms' k'
    Fix (Prod a b) -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ Prod a' b'
    Fix (ProdElim f p) -> do
      f' <- go ctx f
      p' <- go ctx p
      pure $ Fix $ ProdElim f' p'
    Fix (Sum l r) -> do
      l' <- go ctx l
      r' <- go ctx r
      pure $ Fix $ Sum l' r'
    Fix (SumL l) -> do
      l' <- go ctx l
      pure $ Fix $ SumL l'
    Fix (SumR r) -> do
      r' <- go ctx r
      pure $ Fix $ SumR r'
    Fix (SumElim lf rf s) -> do
      lf' <- go ctx lf
      rf' <- go ctx rf
      s'  <- go ctx s
      pure $ Fix $ SumElim lf' rf' s'
    Fix (List t) -> do
      t' <- go ctx t
      pure $ Fix $ List t'
    Fix LNil         -> pure $ Fix LNil
    Fix (LCons x xs) -> do
      x'  <- go ctx x
      xs' <- go ctx xs
      pure $ Fix $ LCons x' xs'
    Fix (ListElim m l s f) -> do
      m' <- go ctx m
      l' <- go ctx l
      s' <- go ctx s
      f' <- go ctx f
      pure $ Fix $ ListElim m' l' s' f'
    Fix T    -> pure $ Fix T
    Fix Unit -> pure $ Fix Unit
    Fix Void -> pure $ Fix Void

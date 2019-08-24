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
  | Prod r r
  | ProdElim
  | Sum r r
  | SumL r
  | SumR r
  | SumElim
  | List r
  | LNil
  | LCons r r
  | ListElim
  | T    -- T : Type
  | Unit -- Unit : T
  | Void
  | Equal r r r
  | Refl r
  | EqElim r r r r r r
  | W r r
  | Sup r r
  | Absurd r
  | Fin r
  | FZero r
  | FSuc r
  | FinElim
  | NatElim
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

natElim :: Expr
natElim = Fix NatElim

suc :: Expr -> Expr
suc = Fix . Suc

prod :: Expr -> Expr -> Expr
prod a b = Fix $ Prod a b

prodElim :: Expr
prodElim = Fix ProdElim

sum :: Expr -> Expr -> Expr
sum l r = Fix $ Sum l r

suml :: Expr -> Expr
suml = Fix . SumL

sumr :: Expr -> Expr
sumr = Fix . SumR

sumElim :: Expr
sumElim = Fix SumElim

list :: Expr -> Expr
list = Fix . List

lnil :: Expr
lnil = Fix LNil

lcons :: Expr -> Expr -> Expr
lcons x xs = Fix $ LCons x xs

listElim :: Expr
listElim = Fix ListElim

tt :: Expr
tt = Fix T

unit :: Expr
unit = Fix Unit

void :: Expr
void = Fix Void

equal :: Expr -> Expr -> Expr -> Expr
equal t a b = Fix $ Equal t a b

refl :: Expr -> Expr
refl a = Fix (Refl a)

eqElim :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
eqElim a m mr x y eq = Fix $ EqElim a m mr x y eq

w :: Expr -> Expr -> Expr
w a b = Fix $ W a b

sup :: Expr -> Expr -> Expr
sup a b = Fix $ Sup a b

absurd :: Expr -> Expr
absurd = Fix . Absurd

fin :: Expr -> Expr
fin = Fix . Fin

fzero :: Expr -> Expr
fzero = Fix . FZero

fsuc :: Expr -> Expr
fsuc = Fix . FSuc

finElim :: Expr
finElim = Fix FinElim

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
    Fix (Prod a b) -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ Prod a' b'
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
    Fix (List t) -> do
      t' <- go ctx t
      pure $ Fix $ List t'
    Fix LNil         -> pure $ Fix LNil
    Fix (LCons x xs) -> do
      x'  <- go ctx x
      xs' <- go ctx xs
      pure $ Fix $ LCons x' xs'
    Fix T             -> pure $ Fix T
    Fix Unit          -> pure $ Fix Unit
    Fix Void          -> pure $ Fix Void
    Fix (Equal t a b) -> do
      t' <- go ctx t
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ Equal t' a' b'
    Fix (Refl a) -> do
      a' <- go ctx a
      pure $ Fix (Refl a')
    Fix (EqElim a m mr x y eq) -> do
      a'  <- go ctx a
      m'  <- go ctx m
      mr' <- go ctx mr
      x'  <- go ctx x
      y'  <- go ctx y
      eq' <- go ctx eq
      pure $ Fix $ EqElim a' m' mr' x' y' eq'
    Fix (W a b) -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ W a' b'
    Fix (Sup a b) -> do
      a' <- go ctx a
      b' <- go ctx b
      pure $ Fix $ Sup a' b'
    Fix (Absurd r) -> do
      r' <- go ctx r
      pure $ Fix $ Absurd r'
    Fix (Fin r) -> do
      r' <- go ctx r
      pure $ Fix $ Fin r'
    Fix (FZero r) -> do
      r' <- go ctx r
      pure $ Fix $ FZero r'
    Fix (FSuc r) -> do
      r' <- go ctx r
      pure $ Fix $ FSuc r'
    Fix ProdElim -> pure $ Fix ProdElim
    Fix NatElim  -> pure $ Fix NatElim
    Fix ListElim -> pure $ Fix ListElim
    Fix FinElim  -> pure $ Fix FinElim

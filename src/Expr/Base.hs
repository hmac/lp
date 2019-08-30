{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
module Expr.Base where

import           Data.Eq.Deriving
import           Text.Show.Deriving
import           Data.Functor.Foldable

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
  | Rec r r r
  | Absurd r r
  | Fin r
  | FZero r
  | FSuc r
  | FinElim
  | NatElim
  | Boolean
  | BTrue
  | BFalse
  | BoolElim
  | BoolAxiom
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

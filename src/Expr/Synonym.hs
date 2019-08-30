{-# LANGUAGE PatternSynonyms #-}
module Expr.Synonym where

import qualified Expr.Base as E
import           Data.Functor.Foldable

-- These patterns allow us to use the usual constructor names from Expr and have
-- each one be implicitly wrapped in Fix. It makes working with Expr a lot
-- easier.

pattern Var x = Fix (E.Var x)
pattern Ann e t = Fix (E.Ann e t)
pattern App a b = Fix (E.App a b)
pattern Lam x e = Fix (E.Lam x e)
pattern Pi x t e = Fix (E.Pi x t e)
pattern Type = Fix E.Type
pattern Nat = Fix E.Nat
pattern Zero = Fix E.Zero
pattern Suc n = Fix (E.Suc n)
pattern Prod a b = Fix (E.Prod a b)
pattern ProdElim = Fix E.ProdElim
pattern Sum a b = Fix (E.Sum a b)
pattern SumL a = Fix (E.SumL a)
pattern SumR b = Fix (E.SumR b)
pattern SumElim = Fix E.SumElim
pattern List a = Fix (E.List a)
pattern LNil = Fix E.LNil
pattern LCons x xs = Fix (E.LCons x xs)
pattern ListElim = Fix E.ListElim
pattern T = Fix E.T
pattern Unit = Fix E.Unit
pattern Void = Fix E.Void
pattern Equal a x y = Fix (E.Equal a x y)
pattern Refl x = Fix (E.Refl x)
pattern EqElim a m mr x y eq = Fix (E.EqElim a m mr x y eq)
pattern W a b = Fix (E.W a b)
pattern Sup a b = Fix (E.Sup a b)
pattern Rec m a b = Fix (E.Rec m a b)
pattern Absurd t e = Fix (E.Absurd t e)
pattern Fin n = Fix (E.Fin n)
pattern FZero n = Fix (E.FZero n)
pattern FSuc n = Fix (E.FSuc n)
pattern FinElim = Fix E.FinElim
pattern NatElim = Fix E.NatElim
pattern Boolean = Fix E.Boolean
pattern BTrue = Fix E.BTrue
pattern BFalse = Fix E.BFalse
pattern BoolElim = Fix E.BoolElim
pattern BoolAxiom = Fix E.BoolAxiom

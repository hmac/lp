{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Expr.Pretty where

import           Data.Functor.Foldable
import           Expr
import           Pretty

instance Pretty (Fix (ExprF String String)) where
  pretty = cata f
   where
    f :: FExprF (Doc ann) -> Doc ann
    f = \case
      Var v             -> pretty v
      Ann e t           -> e <+> ":" <+> t
      App x y           -> x <+> y
      Lam v e           -> "(\\" <> pretty v <> "." <+> e <> ")"
      Pi x t e          -> "forall (" <> pretty x <+> ":" <+> t <> ")." <+> e
      Type              -> "Type"
      Nat               -> "Nat"
      Zero              -> "Zero"
      Suc n             -> "Suc" <+> n
      NatElim m mz ms k -> "natElim" <+> m <+> mz <+> ms <+> k
      Prod     a b      -> a <> "*" <> b
      ProdElim g p      -> "prodElim" <+> g <+> p

instance Pretty (Fix (ExprF () Int)) where
  pretty = cata f
   where
    f :: BExprF (Doc ann) -> Doc ann
    f = \case
      Var i             -> pretty i
      Ann e t           -> e <+> ":" <+> t
      App x y           -> x <+> y
      Lam _ e           -> "(\\." <+> e <> ")"
      Pi _ t e          -> "forall (_ :" <+> t <> "). " <> e
      Type              -> "Type"
      Nat               -> "Nat"
      Zero              -> "Zero"
      Suc n             -> "Suc" <+> n
      NatElim m mz ms k -> "natElim" <+> m <+> mz <+> ms <+> k
      Prod     a b      -> a <> "*" <> b
      ProdElim g p      -> "prodElim" <+> g <+> p

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Expr.Pretty where

import           Data.Functor.Foldable
import           Expr
import           Pretty

instance Pretty (Fix (ExprF String String)) where
  pretty expr = cata f expr
   where
    f :: FExprF (Doc ann) -> Doc ann
    f = \case
      Var v    -> pretty v
      Ann e t  -> e <> " : " <> t
      App x y  -> x <> " " <> y
      Lam v e  -> "(\\" <> pretty v <> ". " <> e <> ")"
      Pi x t e -> "forall (" <> pretty x <> " : " <> t <> "). " <> e
      Type     -> "Type"

instance Pretty (Fix (ExprF () Int)) where
  pretty expr = cata f expr
   where
    f :: BExprF (Doc ann) -> Doc ann
    f = \case
      Var i    -> pretty i
      Ann e t  -> e <> " : " <> t
      App x y  -> x <> " " <> y
      Lam _ e  -> "(\\. " <> e <> ")"
      Pi _ t e -> "forall (_ : " <> t <> "). " <> e
      Type     -> "Type"

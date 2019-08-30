{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Expr.Pretty where

import           Data.Functor.Foldable
import           Expr.Base
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal

type Document = Doc AnsiStyle

pp :: (Pretty x, Pretty b) => Fix (ExprF b x) -> String
pp = show . prettyExpr

-- Annotations
keyword :: Document -> Document
keyword = annotate (color Blue)

var :: Document -> Document
var = annotate (color Red)

binder :: Document -> Document
binder = annotate (color Green)

prim :: Document -> Document
prim = annotate (color Magenta)

prettyExpr :: (Pretty b, Pretty x) => Fix (ExprF b x) -> Document
prettyExpr = para f
 where
  f :: (Pretty b, Pretty x) => ExprF b x (Fix (ExprF b x), Document) -> Document
  f = \case
    Var v             -> var $ pretty v
    Ann (_, e) (_, t) -> parens $ e <+> ":" <+> t
    App (_, x) (ye, y) | singleton ye -> sep [x, y]
                       | otherwise    -> sep [x, parens y]
    Lam v (_, e) -> binder "λ" <> var (pretty v) <> "." <+> hang 2 e
    Pi x (_, t) (_, e) ->
      keyword "forall" <+> parens (pretty x <+> ":" <+> t) <> "." <+> hang 2 e
    Type       -> prim "Type"
    Nat        -> prim "Nat"
    Zero       -> "0"
    Suc (n, r) -> case natToInt (Fix (Suc n)) of
      Just i  -> pretty i    -- try to convert the expr directly to an integer
      Nothing -> "Suc" <+> r -- fall back to printing the AST if that fails
    NatElim -> "natElim"
    Prod (x, a) (y, b) | singleton x && singleton y -> a <> "*" <> b
                       | singleton x                -> a <> "*" <> parens b
                       | singleton y                -> parens a <> "*" <> b
                       | otherwise -> parens a <> "*" <> parens b
    ProdElim -> "prodElim"
    Sum (x, l) (y, r) | singleton x && singleton y -> l <> "|" <> r
                      | singleton x                -> l <> "|" <> parens r
                      | singleton y                -> parens l <> "|" <> r
                      | otherwise -> parens l <> "|" <> parens r
    SumL (_, l)          -> "Left" <+> l
    SumR (_, r)          -> "Right" <+> r
    SumElim              -> "sumElim"
    List (_, t)          -> prim "List" <+> t
    LNil                 -> "Nil"
    LCons (_, x) (_, xs) -> x <+> "::" <+> xs
    ListElim             -> "listElim"
    T                    -> prim "T"
    Unit                 -> "Unit"
    Void                 -> prim "Void"
    Equal _ (x, a) (y, b) | singleton x && singleton y -> a <+> "=" <+> b
                          | singleton x -> "Eq" <+> a <+> parens b
                          | singleton y -> "Eq" <+> parens a <+> b
                          | otherwise -> "Eq" <+> parens a <+> parens b
    Refl (_, a) -> "Refl" <+> a
    EqElim (_, a) (_, m) (_, mr) (_, x) (_, y) (_, eq) ->
      sep ["eqElim", a, m, mr, x, y, eq]
    W   (_, a) (_, b)        -> prim "W" <+> a <+> b
    Sup (_, a) (_, b)        -> "sup" <+> a <+> b
    Rec (_, m) (_, a) (_, b) -> "rec" <+> m <+> a <+> b
    Absurd (_, _t) (_, e)    -> "absurd" <+> e
    Fin   (Fix (App _ _), k) -> prim "Fin" <+> parens k
    Fin   (_            , k) -> prim "Fin" <+> k
    FZero _t                 -> "F0"
    FSuc  (n, r)             -> case finToInt (Fix (FSuc n)) of
      Just i  -> "F" <> pretty i
      Nothing -> "FSuc" <+> r
    FinElim   -> "finElim"
    Boolean   -> "Bool"
    BTrue     -> "True"
    BFalse    -> "False"
    BoolElim  -> "boolElim"
    BoolAxiom -> "boolAxiom"

natToInt :: Fix (ExprF b x) -> Maybe Int
natToInt (Fix Zero   ) = Just 0
natToInt (Fix (Suc n)) = (+ 1) <$> natToInt n
natToInt _             = Nothing

finToInt :: Fix (ExprF b x) -> Maybe Int
finToInt (Fix (FZero _t)) = Just 0
finToInt (Fix (FSuc  n )) = (+ 1) <$> finToInt n
finToInt _                = Nothing

singleton :: Fix (ExprF b x) -> Bool
singleton (Fix e) = case e of
  Var _   -> True
  Type    -> True
  T       -> True
  Unit    -> True
  Void    -> True
  LNil    -> True
  Nat     -> True
  Zero    -> True
  FZero _ -> True
  Boolean -> True
  BTrue   -> True
  BFalse  -> True
  _       -> False

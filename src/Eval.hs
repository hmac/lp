{-# LANGUAGE LambdaCase #-}
module Eval where

import Data.Functor.Foldable
import Expr

nfc :: Context -> Expr -> Expr
nfc ctx e = head (reduceList ctx e)

reduceList :: Context -> Expr -> [Expr]
reduceList ctx expr = go [expr]
  where go (e : es) = let e' = reduce ctx e
                       in if e' == e
                          then e : es
                          else go (e' : e : es)
        go _ = [expr]

reduce :: Context -> Expr -> Expr
reduce ctx expr = para alg expr
  where alg = \case
                Var x -> case lookup x ctx of
                           Just x' -> x'
                           Nothing -> Fix (Var x)
                App ((Fix (Lam v a)), _ar) (b, _br) -> substitute v a b
                e     -> Fix $ fmap snd e

substitute :: String -> Expr -> Expr -> Expr
substitute v a b = topDown' alg a
  where alg = \case
                Fix (Var v')   | v' == v -> Left b
                               | otherwise -> Left $ Fix (Var v')
                Fix (Lam v' e) | v' == v -> Left $ Fix (Lam v' e)
                               | otherwise -> Right $ Fix (Lam v' e) -- TODO
                e -> Right e

-- Recurse through a structure top-down, applying the given transformation
-- Right means carry on recursing
-- Left means stop
topDown' :: Functor a => (Fix a -> Either (Fix a) (Fix a)) -> Fix a -> Fix a
topDown' f a = case f a of
                Right b -> Fix (fmap (topDown' f) (unfix b))
                Left b -> b

-- Not used - here for reference
topDown :: Functor a => (Fix a -> Fix a) -> Fix a -> Fix a
topDown f = Fix . fmap (topDown f) . unfix . f


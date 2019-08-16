{-# LANGUAGE LambdaCase #-}
module Eval where

import           Data.Functor.Foldable
import           Expr                    hiding ( Context )
import           Data.Maybe                     ( fromMaybe )

type Context = [BExpr]

nfc' :: [(String, Expr)] -> Expr -> Expr
nfc' ctx ex = head (reduceList' ex)
 where
  reduceList' expr = go [expr]
  go (e : es) =
    let e' = reduce' e in if e' == e then e : es else go (e' : e : es)
  go x = x
  reduce' expr = para alg expr
  alg = \case
    Var x -> case lookup x ctx of
      Just x' -> x'
      Nothing -> Fix (Var x)
    App ((Fix (Lam v a)), _ar) (b, _br) -> substitute v a b
    e -> Fix $ fmap snd e

nfc :: Context -> BExpr -> BExpr
nfc ctx e = head (reduceList ctx e)

reduceList :: Context -> BExpr -> [BExpr]
reduceList ctx expr = go [expr]
 where
  go (e : es) =
    let e' = reduce ctx e in if e' == e then e : es else go (e' : e : es)
  go _ = [expr]

reduce :: Context -> BExpr -> BExpr
reduce ctx (Fix expr) = case expr of
  App (Fix l@(Lam _ _)) (Fix b) -> breduce (Fix l) (Fix b)
  App a                 b       -> Fix $ App (reduce ctx a) (reduce ctx b)
  Lam v                 e       -> Fix $ Lam v (reduce ctx e)
  Var i                         -> fromMaybe (Fix (Var i)) (safeIndex i ctx)
  Ann e t                       -> Fix $ Ann (reduce ctx e) (reduce ctx t)
  Pi x t e                      -> Fix $ Pi x (reduce ctx t) (reduce ctx e)
  Type                          -> Fix Type

-- TODO: this is so messy and complex - surely we can simplify it
breduce :: BExpr -> BExpr -> BExpr
breduce (Fix (Lam _ (Fix e))) (Fix b) =
  -- Substitute matching variables
  let e'  = sub b 0 e
  -- Decrement free variables
      e'' = decFree 0 e'
                                  -- Remove lambda
  in  Fix e''
 where
  sub b i (Var j) | i == j    = b
                  | otherwise = Var j
  sub b i (Lam v (Fix e)) = Lam v (Fix (sub b (i + 1) e))
  sub b i (Pi x (Fix t) (Fix e)) =
    Pi x (Fix (sub b i t)) (Fix (sub b (i + 1) e))
  sub b i Type                    = Type
  sub b i (Ann (Fix e ) (Fix t )) = Ann (Fix (sub b i e)) (Fix (sub b i t))
  sub b i (App (Fix e1) (Fix e2)) = App (Fix (sub b i e1)) (Fix (sub b i e2))

  decFree i (Var j) | j > i     = Var (j - 1)
                    | otherwise = Var j
  decFree i (Lam v (Fix e)) = Lam v (Fix (decFree (i + 1) e))
  decFree i (Pi x (Fix t) (Fix e)) =
    Pi x (Fix (decFree i t)) (Fix (decFree (i + 1) e))
  decFree i Type                  = Type
  decFree i (Ann (Fix e) (Fix t)) = Ann (Fix (decFree i e)) (Fix (decFree i t))
  decFree i (App (Fix a) (Fix b)) = App (Fix (decFree i a)) (Fix (decFree i b))

substitute :: String -> Expr -> Expr -> Expr
substitute v a b = topDown' alg a
 where
  alg = \case
    Fix (Var v') | v' == v   -> Left b
                 | otherwise -> Left $ Fix (Var v')
    Fix (Lam v' e) | v' == v   -> Left $ Fix (Lam v' e)
                   | otherwise -> Right $ Fix (Lam v' e) -- TODO
    e -> Right e

-- Recurse through a structure top-down, applying the given transformation
-- Right means carry on recursing
-- Left means stop
topDown' :: Functor a => (Fix a -> Either (Fix a) (Fix a)) -> Fix a -> Fix a
topDown' f a = case f a of
  Right b -> Fix (fmap (topDown' f) (unfix b))
  Left  b -> b

-- Not used - here for reference
topDown :: Functor a => (Fix a -> Fix a) -> Fix a -> Fix a
topDown f = Fix . fmap (topDown f) . unfix . f

-- TODO: move to utils
safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []       = Nothing
safeIndex 0 (x : _ ) = Just x
safeIndex i (x : xs) = safeIndex (i - 1) xs

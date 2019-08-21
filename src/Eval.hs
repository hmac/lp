{-# LANGUAGE LambdaCase #-}
module Eval
  ( evalExpr
  )
where

import           Data.Functor.Foldable
import           Expr                    hiding ( Context )
import           Data.Maybe                     ( fromMaybe )

evalExpr :: [(String, Expr)] -> Expr -> Expr
evalExpr ctx ex = head (reduceList' ex)
 where
  reduceList' expr = go [expr]
  go (e : es) =
    let e' = reduce' e in if e' == e then e : es else go (e' : e : es)
  go x = x
  reduce' = \case
    Fix (Var x                ) -> fromMaybe (Fix (Var x)) (lookup x ctx)
    Fix (Ann e               _) -> reduce' e
    Fix (App (Fix (Lam x e)) b) -> substitute x e b
    Fix (App a               b) -> Fix (App (reduce' a) (reduce' b))
    -- When eval'ing under a lambda, we add the lambda's binding to the
    -- environment with a value of (Var <binding>) to ensure that we don't
    -- substitute any identically-named outer bindings into the lambda.
    -- E.g. if we eval (\x. x) in a context of [x = e] we don't want to get
    --      (\x. e)
    Fix (Lam x e) ->
      let ctx' = (x, Fix (Var x)) : ctx in Fix (Lam x (evalExpr ctx' e))
    -- Same applies to Pi
    Fix (Pi x t e) ->
      let ctx' = (x, Fix (Var x)) : ctx
      in  Fix (Pi x (reduce' t) (evalExpr ctx' e))
    Fix Type                            -> Fix Type
    Fix Nat                             -> Fix Nat
    Fix Zero                            -> Fix Zero
    Fix (Suc n                        ) -> Fix $ Suc (reduce' n)

    Fix (NatElim _ mz _  (Fix Zero   )) -> mz
    Fix (NatElim m mz ms (Fix (Suc n))) -> app (app ms n) (natElim m mz ms n)
    Fix (NatElim m mz ms k            ) -> natElim m mz ms (reduce' k)

substitute :: String -> Expr -> Expr -> Expr
substitute v a b = topDown' alg a
 where
  alg = \case
    Fix (Var v') | v' == v   -> Left b
                 | otherwise -> Left $ Fix (Var v')
    Fix (Lam v' e) | v' == v   -> Left $ Fix (Lam v' e)
                   | otherwise -> Right $ Fix (Lam v' e) -- TODO
    Fix (Pi x t e) | x == v    -> Left $ Fix (Pi x t e)
                   | otherwise -> Right $ Fix (Pi x t e)
    e -> Right e

-- Recurse through a structure top-down, applying the given transformation
-- Right means carry on recursing
-- Left means stop
topDown' :: Functor a => (Fix a -> Either (Fix a) (Fix a)) -> Fix a -> Fix a
topDown' f a = case f a of
  Right b -> Fix (fmap (topDown' f) (unfix b))
  Left  b -> b

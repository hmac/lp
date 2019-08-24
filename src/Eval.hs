{-# LANGUAGE LambdaCase #-}
module Eval
  ( evalExpr
  )
where

import           Prelude                 hiding ( sum )
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
    Fix Type                               -> type_
    Fix Nat                                -> nat
    Fix Zero                               -> zero
    Fix (Suc n                           ) -> suc (reduce' n)

    Fix (NatElim _ mz _  (Fix Zero   )   ) -> mz
    Fix (NatElim m mz ms (Fix (Suc n))   ) -> app (app ms n) (natElim m mz ms n)
    Fix (NatElim m mz ms k               ) -> natElim m mz ms (reduce' k)

    Fix (Fin   r                         ) -> fin (reduce' r)
    Fix (FZero r                         ) -> fzero (reduce' r)
    Fix (FSuc  r                         ) -> fsuc (reduce' r)

    Fix (FinElim _ mz _ _ (Fix (FZero k))) -> app mz k
    Fix (FinElim m mz ms n (Fix (FSuc (Fix (FZero k))))) ->
      app (app (app ms k) (fzero k)) (finElim m mz ms n (fzero k))
    Fix (FinElim m mz ms n (Fix (FSuc (Fix (FSuc k))))) ->
      app (app (app ms k) (fsuc k)) (finElim m mz ms n (fsuc k))
    Fix (FinElim m mz ms n (Fix (FSuc k))) ->
      finElim m mz ms n (fsuc (reduce' k))
    Fix (FinElim m mz ms n k        ) -> finElim m mz ms n (reduce' k)

    Fix (Prod     a b               ) -> prod (reduce' a) (reduce' b)
    Fix (ProdElim f (Fix (Prod a b))) -> app (app f a) b
    Fix (ProdElim f p               ) -> prodElim f (reduce' p)

    Fix (Sum      l r               ) -> sum (reduce' l) (reduce' r)
    Fix (SumL l                     ) -> suml (reduce' l)
    Fix (SumR r                     ) -> sumr (reduce' r)
    Fix (SumElim f _ (Fix (SumL l)) ) -> app f l
    Fix (SumElim _ g (Fix (SumR r)) ) -> app g r
    Fix (SumElim f g s              ) -> sumElim f g (reduce' s)

    Fix (List t                     ) -> list (reduce' t)
    Fix LNil                          -> lnil
    Fix (LCons x xs               )   -> lcons (reduce' x) (reduce' xs)
    Fix (ListElim _ (Fix LNil) s _)   -> s
    Fix (ListElim m (Fix (LCons x xs)) s f) ->
      app (app (app f x) xs) (listElim m xs s f)
    Fix (ListElim m l s f)                 -> listElim m (reduce' l) s f

    Fix T                                  -> Fix T
    Fix Unit                               -> Fix Unit
    Fix Void                               -> Fix Void
    Fix (Absurd t                        ) -> absurd (reduce' t)
    Fix (Equal t a b) -> equal (reduce' t) (reduce' a) (reduce' b)
    Fix (Refl a                          ) -> refl (reduce' a)
    -- TODO: check that the below is correct
    Fix (EqElim _ _ mr _ _ (Fix (Refl z))) -> app mr z
    Fix (EqElim a m mr x y eq            ) -> eqElim a m mr x y (reduce' eq)

    Fix (W   a b                         ) -> w (reduce' a) (reduce' b)
    Fix (Sup a b                         ) -> sup (reduce' a) (reduce' b)

substitute :: String -> Expr -> Expr -> Expr
substitute v a b = topDown' alg a
 where
  alg = \case
    Fix (Var v') | v' == v   -> Left b
                 | otherwise -> Left $ Fix (Var v')
    Fix (Lam v' e) | v' == v   -> Left $ Fix (Lam v' e)
                   | otherwise -> Right $ Fix (Lam v' e) -- TODO: [remove this comment?]
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

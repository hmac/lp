{-# LANGUAGE LambdaCase #-}
module Eval
  ( evalExpr
  )
where

import           Prelude                 hiding ( sum )
import           Data.Functor.Foldable
import           Expr
import           Data.Maybe                     ( fromMaybe )

evalExpr :: Context -> Expr -> Expr
evalExpr ctx ex = head (reduceList' ex)
 where
  reduceList' expr = go [expr]
  go (e : es) =
    let e' = reduce' ctx e in if e' == e then e : es else go (e' : e : es)
  go x = x

-- TODO: rename to reduce
reduce' :: Context -> Expr -> Expr
reduce' ctx = go
 where
  go = \case
    Fix (Var x                ) -> fromMaybe (Fix (Var x)) (lookup x ctx)
    Fix (Ann e               _) -> e
    Fix (App (Fix (Lam x e)) b) -> substitute x e b
    Fix (App (Fix (App (Fix (App (Fix (App (Fix NatElim) m)) mz)) ms)) k) ->
      evalNatElim ctx m mz ms k
    Fix (App (Fix (App (Fix (App (Fix (App (Fix (App (Fix ProdElim) _a)) _b)) _c)) f)) p)
      -> evalProdElim ctx f p
    Fix (App (Fix (App (Fix (App (Fix (App (Fix (App (Fix (App (Fix SumElim) _a)) _b)) _c)) f)) g)) s)
      -> evalSumElim ctx f g s
    Fix (App (Fix (App (Fix (App (Fix (App (Fix (App (Fix ListElim) _a)) l)) m)) s)) f)
      -> evalListElim ctx l m s f
    Fix (App (Fix (App (Fix (App (Fix (App (Fix (App (Fix FinElim) m)) mz)) ms)) n)) f)
      -> evalFinElim ctx m mz ms n f
    Fix (App a b) -> Fix (App (go a) (go b))
    -- When eval'ing under a lambda, we add the lambda's binding to the
    -- environment with a value of (Var <binding>) to ensure that we don't
    -- substitute any identically-named outer bindings into the lambda.
    -- E.g. if we eval (\x. x) in a context of [x = e] we don't want to get
    --      (\x. e)
    Fix (Lam x e) ->
      let ctx' = (x, Fix (Var x)) : ctx in Fix (Lam x (evalExpr ctx' e))
    -- Same applies to Pi
    Fix (Pi x t e) ->
      let ctx' = (x, Fix (Var x)) : ctx in Fix (Pi x (go t) (evalExpr ctx' e))
    Fix Type                               -> type_
    Fix Nat                                -> nat
    Fix Zero                               -> zero
    Fix (Suc   n )                         -> suc (go n)

    Fix (Fin   r )                         -> fin (go r)
    Fix (FZero r )                         -> fzero (go r)
    Fix (FSuc  r )                         -> fsuc (go r)

    Fix (Prod a b)                         -> prod (go a) (go b)

    Fix (Sum  l r)                         -> sum (go l) (go r)
    Fix (SumL l  )                         -> suml (go l)
    Fix (SumR r  )                         -> sumr (go r)

    Fix (List t  )                         -> list (go t)
    Fix LNil                               -> lnil
    Fix (LCons x xs)                       -> lcons (go x) (go xs)

    Fix T                                  -> Fix T
    Fix Unit                               -> Fix Unit
    Fix Void                               -> Fix Void
    Fix (Absurd t                        ) -> absurd (go t)
    Fix (Equal t a b                     ) -> equal (go t) (go a) (go b)
    Fix (Refl a                          ) -> refl (go a)
    -- TODO: check that the below is correct
    Fix (EqElim _ _ mr _ _ (Fix (Refl z))) -> app mr z
    Fix (EqElim a m mr x y eq            ) -> eqElim a m mr x y (go eq)

    Fix (W   a b                         ) -> w (go a) (go b)
    Fix (Sup a b                         ) -> sup (go a) (go b)

evalNatElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr
evalNatElim _ _ mz _ (Fix Zero) = mz
evalNatElim ctx m mz ms (Fix (Suc n)) =
  app (app ms n) (evalNatElim ctx m mz ms n)
evalNatElim ctx m mz ms k = evalNatElim ctx m mz ms (reduce' ctx k)

evalProdElim :: Context -> Expr -> Expr -> Expr
evalProdElim _   f (Fix (Prod a b)) = app (app f a) b
evalProdElim ctx f p                = evalProdElim ctx f (reduce' ctx p)

evalSumElim :: Context -> Expr -> Expr -> Expr -> Expr
evalSumElim _   f _ (Fix (SumL l)) = app f l
evalSumElim _   _ g (Fix (SumR r)) = app g r
evalSumElim ctx f g s              = evalSumElim ctx f g (reduce' ctx s)

evalListElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr
evalListElim _ _ (Fix LNil) s _ = s
evalListElim ctx m (Fix (LCons x xs)) s f =
  app (app (app f x) xs) (evalListElim ctx m xs s f)
evalListElim ctx m l s f = evalListElim ctx m (reduce' ctx l) s f

evalFinElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
evalFinElim _ _ mz _ _ (Fix (FZero k)) = app mz k
evalFinElim ctx m mz ms n (Fix (FSuc (Fix (FZero k)))) =
  app (app (app ms k) (fzero k)) (evalFinElim ctx m mz ms n (fzero k))
evalFinElim ctx m mz ms n (Fix (FSuc (Fix (FSuc k)))) =
  app (app (app ms k) (fsuc k)) (evalFinElim ctx m mz ms n (fsuc k))
evalFinElim ctx m mz ms n (Fix (FSuc k)) =
  evalFinElim ctx m mz ms n (fsuc (reduce' ctx k))
evalFinElim ctx m mz ms n k = evalFinElim ctx m mz ms n (reduce' ctx k)

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

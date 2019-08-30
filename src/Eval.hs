{-# LANGUAGE LambdaCase #-}
module Eval
  ( evalExpr
  )
where

import           Data.Functor.Foldable
import           Expr
import           Expr.Pretty                    ( pp )
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
    Var x   -> fromMaybe (Var x) (lookup x ctx)
    Ann e _ -> e
    App (Lam x e) b -> substitute x e b

    -- Dispatch calls to eliminators to their respective eliminator function
    App (App (App (App NatElim m) mz) ms) k -> evalNatElim ctx m mz ms k
    App (App (App (App (App ProdElim a) b) c) f) p ->
      evalProdElim ctx a b c f p
    App (App (App (App (App (App SumElim a) b) c) f) g) s ->
      evalSumElim ctx a b c f g s
    App (App (App (App (App ListElim _a) l) m) s) f -> evalListElim ctx l m s f
    App (App (App (App (App FinElim m) mz) ms) n) f ->
      evalFinElim ctx m mz ms n f
    App (App (App (App BoolElim a) x) y) b -> evalBoolElim ctx a x y b

    App a       b              -> (App (go a) (go b))
    -- When eval'ing under a lambda, we add the lambda's binding to the
    -- environment with a value of (Var <binding>) to ensure that we don't
    -- substitute any identically-named outer bindings into the lambda.
    -- E.g. if we eval (\x. x) in a context of [x = e] we don't want to get
    --      (\x. e)
    Lam x e -> let ctx' = (x, Var x) : ctx in Lam x (evalExpr ctx' e)
    -- Same applies to Pi
    (Pi x t e) -> let ctx' = (x, Var x) : ctx in Pi x (go t) (evalExpr ctx' e)
    Type                       -> Type
    Nat                        -> Nat
    Zero                       -> Zero
    Suc   n                    -> Suc (go n)

    Fin   r                    -> Fin (go r)
    FZero r                    -> FZero (go r)
    FSuc  r                    -> FSuc (go r)

    Prod a b                   -> Prod (go a) (go b)

    Sum  l r                   -> Sum (go l) (go r)
    SumL l                     -> SumL (go l)
    SumR r                     -> SumR (go r)

    List t                     -> List (go t)
    LNil                       -> LNil
    LCons x xs                 -> LCons (go x) (go xs)

    T                          -> T
    Unit                       -> Unit
    Void                       -> Void
    Absurd t e                 -> Absurd (go t) (go e)
    Equal t a b                -> Equal (go t) (go a) (go b)
    Refl a                     -> Refl (go a)
    -- TODO: check that the below is correct
    EqElim _ _ mr _ _ (Refl z) -> App mr z
    EqElim a m mr x y eq       -> EqElim a m mr x y (go eq)

    W   a b                    -> W (go a) (go b)
    Sup a f                    -> Sup (go a) (go f)
    Rec m (Sup a f) r ->
      App (App (App r a) f) (Lam "x" (Rec m (App f (Var "x")) r))
    Rec m a r     -> Rec m (go a) r

    Boolean       -> Boolean
    BTrue         -> BTrue
    BFalse        -> BFalse
    BoolAxiom     -> BoolAxiom
    somethingElse -> error $ "Unexpected expression: " ++ pp somethingElse

evalNatElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr
evalNatElim _   _ mz _  Zero    = mz
evalNatElim ctx m mz ms (Suc n) = App (App ms n) (evalNatElim ctx m mz ms n)
evalNatElim ctx m mz ms k =
  App (App (App (App NatElim m) mz) ms) (reduce' ctx k)

evalProdElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
evalProdElim _ _ _ _ f (Prod x y) = App (App f x) y
evalProdElim ctx a b c f p =
  App (App (App (App (App ProdElim a) b) c) f) (reduce' ctx p)

evalSumElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
evalSumElim _ _ _ _ f _ (SumL l) = App f l
evalSumElim _ _ _ _ _ g (SumR r) = App g r
evalSumElim ctx a b c f g s =
  App (App (App (App (App (App SumElim a) b) c) f) g) (reduce' ctx s)
  -- evalSumElim ctx a b c f g (reduce' ctx s)

evalListElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr
evalListElim _ _ LNil s _ = s
evalListElim ctx m (LCons x xs) s f =
  App (App (App f x) xs) (evalListElim ctx m xs s f)
evalListElim ctx m l s f = evalListElim ctx m (reduce' ctx l) s f

evalFinElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
evalFinElim _ _ mz _ _ (FZero k) = App mz k
evalFinElim ctx m mz ms n (FSuc (FZero k)) =
  App (App (App ms k) (FZero k)) (evalFinElim ctx m mz ms n (FZero k))
evalFinElim ctx m mz ms n (FSuc (FSuc k)) =
  App (App (App ms k) (FSuc k)) (evalFinElim ctx m mz ms n (FSuc k))
evalFinElim ctx m mz ms n (FSuc k) =
  evalFinElim ctx m mz ms n (FSuc (reduce' ctx k))
evalFinElim ctx m mz ms n k = evalFinElim ctx m mz ms n (reduce' ctx k)

evalBoolElim :: Context -> Expr -> Expr -> Expr -> Expr -> Expr
evalBoolElim _ _ iftrue _       BTrue  = iftrue
evalBoolElim _ _ _      iffalse BFalse = iffalse
evalBoolElim ctx a iftrue iffalse b =
  App (App (App (App BoolElim a) iftrue) iffalse) (reduce' ctx b)

substitute :: String -> Expr -> Expr -> Expr
substitute v a b = topDown' alg a
 where
  alg = \case
    (Var v') | v' == v   -> Left b
             | otherwise -> Left $ Var v'
    (Lam v' e) | v' == v   -> Left $ Lam v' e
               | otherwise -> Right $ Lam v' e -- TODO: [remove this comment?]
    (Pi x t e) | x == v    -> Left $ Pi x t e
               | otherwise -> Right $ Pi x t e
    e -> Right e

-- Recurse through a structure top-down, applying the given transformation, and
-- allowing halting.
-- Right means carry on recursing
-- Left means stop
topDown' :: Functor a => (Fix a -> Either (Fix a) (Fix a)) -> Fix a -> Fix a
topDown' f a = case f a of
  Right b -> Fix (fmap (topDown' f) (unfix b))
  Left  b -> b

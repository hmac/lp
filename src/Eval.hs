{-# LANGUAGE LambdaCase #-}
module Eval where

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
    Fix Type -> Fix Type

type Context = [BExpr]

evalBExpr :: [BExpr] -> BExpr -> BExpr
evalBExpr = nfc

nfc :: Context -> BExpr -> BExpr
nfc ctx e = head (reduceList ctx e)

reduceList :: Context -> BExpr -> [BExpr]
reduceList ctx expr = go [expr]
 where
  go (e : es) =
    let e' = reduce ctx e in if e' == e then e : es else go (e' : e : es)
  go _ = [expr]

-- TODO: what about reducing applications of (Pi ...) x ?
reduce :: Context -> BExpr -> BExpr
reduce ctx (Fix expr) = case expr of
  App (Fix l@Lam{}  ) b -> breduce (Fix l) b
  App (Fix p@Pi{}   ) b -> breduce (Fix p) b
  App (Fix (Ann e _)) b -> reduce ctx (Fix (App e b))
  App a               b -> Fix $ App (reduce ctx a) (reduce ctx b)
  Lam v               e -> Fix $ Lam v (reduce ctx e)
  Var i                 -> fromMaybe (Fix (Var i)) (safeIndex i ctx)
  Ann e t               -> Fix $ Ann (reduce ctx e) (reduce ctx t)
  Pi x t e              -> Fix $ Pi x (reduce ctx t) (reduce ctx e)
  Type                  -> Fix Type

-- TODO: this is so messy and complex - surely we can simplify it
breduce :: BExpr -> BExpr -> BExpr
breduce (Fix (Lam _ (Fix e))) (Fix b) =
  -- Substitute matching variables
  let e'  = sub b 0 e
  -- Decrement free variables
      e'' = decFree e'
  in  Fix e''
breduce (Fix (Pi _ _ (Fix t))) (Fix b) =
  let t' = decFree (sub b 0 t) in Fix t'

sub :: ExprF () Int BExpr -> Int -> ExprF () Int BExpr -> ExprF () Int BExpr
sub b i (Var j) | i == j    = b
                | otherwise = Var j
sub b i (Lam v (Fix e)       )  = Lam v (Fix (sub b (i + 1) e))
sub b i (Pi x (Fix t) (Fix e))  = Pi x (Fix (sub b i t)) (Fix (sub b (i + 1) e))
sub _ _ Type                    = Type
sub b i (Ann (Fix e ) (Fix t )) = Ann (Fix (sub b i e)) (Fix (sub b i t))
sub b i (App (Fix e1) (Fix e2)) = App (Fix (sub b i e1)) (Fix (sub b i e2))

decFree :: ExprF () Int BExpr -> ExprF () Int BExpr
decFree = go 0
 where
  go i (Var j) | j > i     = Var (j - 1)
               | otherwise = Var j
  go i (Lam v (Fix e)       ) = Lam v (Fix (go (i + 1) e))
  go i (Pi x (Fix t) (Fix e)) = Pi x (Fix (go i t)) (Fix (go (i + 1) e))
  go _ Type                   = Type
  go i (Ann (Fix e) (Fix t))  = Ann (Fix (go i e)) (Fix (go i t))
  go i (App (Fix a) (Fix b))  = App (Fix (go i a)) (Fix (go i b))

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

-- Not used - here for reference
topDown :: Functor a => (Fix a -> Fix a) -> Fix a -> Fix a
topDown f = Fix . fmap (topDown f) . unfix . f

-- TODO: move to utils
safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []       = Nothing
safeIndex 0 (x : _ ) = Just x
safeIndex i (_ : xs) = safeIndex (i - 1) xs

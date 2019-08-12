module Tutorial.Eval where

import           Tutorial.Expr

type Env = [Value]

evalI :: TermI -> Env -> Value
evalI Star       _   = VStar
evalI (Pi  t t') env = VPi (evalC t env) (\x -> evalC t' (x : env))
evalI (Ann e _ ) env = evalC e env
evalI (Bound i ) env = env !! i
evalI (Free  n ) _   = vfree n
evalI (a :@: b ) env = vapp (evalI a env) (evalC b env)

evalC :: TermC -> Env -> Value
evalC (Inf e) env = evalI e env
evalC (Lam e) env = VLam (\x -> evalC e (x : env))

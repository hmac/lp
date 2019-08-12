module Tutorial.Infer where

import Tutorial.Expr
import Tutorial.Quote
import Tutorial.Eval

type Type = Value
type Context = [(Name, Type)]
type Result a = Either String a

throwError :: String -> Result a
throwError = Left

-- TODO: remove?
-- kindC :: Context -> Type -> Kind -> Result ()
-- kindC ctx (TFree x) Star
--   = case lookup x ctx of
--       Just (HasKind Star) -> return ()
--       _ -> throwError "unknown identifier"
-- kindC ctx (Fun k k') Star = do
--   kindC ctx k Star
--   kindC ctx k' Star

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i ctx (Ann e t) = do
  typeC i ctx t VStar
  let t' = evalC t []
  typeC i ctx e t'
  return t'
typeI i ctx Star = return VStar
typeI i ctx (Pi t e) = do
  typeC i ctx t VStar
  let t' = evalC t []
  typeC (i + 1) ((Local i, t') : ctx) (substC 0 (Free (Local i)) e) VStar
  return VStar
typeI i ctx (Free x) = case lookup x ctx of
                         Just t -> return t
                         Nothing -> throwError "unknown identifier"
typeI i ctx (e :@: e') = do
  te <- typeI i ctx e
  case te of
    VPi t t' -> do
      typeC i ctx e' t
      return (t' (evalC e' []))
    _ -> throwError "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i ctx (Inf e) t = do
  t' <- typeI i ctx e
  if quote0 t == quote0 t'
     then return ()
     else throwError "type mismatch"
typeC i ctx (Lam e) (VPi t t')
  = typeC (i + 1) ((Local i, t) : ctx) (substC 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeC i ctx _ _ = throwError "type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t)  = Ann (substC i r e) t
substI i r Star       = Star
substI i r (Pi t t')  = Pi (substC i r t) (substC (i + 1) r t')
substI i r (Bound j)  = if i == j then r else Bound j
substI i r (Free y)   = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)


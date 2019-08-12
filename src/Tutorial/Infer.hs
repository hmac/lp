module Tutorial.Infer where

import Tutorial.Expr

type Context = [(Name, Info)]
type Result a = Either String a

throwError :: String -> Result a
throwError = Left

kindC :: Context -> Type -> Kind -> Result ()
kindC ctx (TFree x) Star
  = case lookup x ctx of
      Just (HasKind Star) -> return ()
      _ -> throwError "unknown identifier"
kindC ctx (Fun k k') Star = do
  kindC ctx k Star
  kindC ctx k' Star

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i ctx (Ann e t) = do
  kindC ctx t Star
  typeC i ctx e t
  return t
typeI i ctx (Free x) = case lookup x ctx of
                         Just (HasType t) -> return t
                         Nothing -> throwError "unknown identifier"
typeI i ctx (e :@: e') = do
  te <- typeI i ctx e
  case te of
    Fun t t' -> do
      typeC i ctx e' t
      return t'
    _ -> throwError "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i ctx (Inf e) t = do
  t' <- typeI i ctx e
  if t == t' then return () else throwError "type mismatch"
typeC i ctx (Lam e) (Fun t t')
  = typeC (i + 1) ((Local i, HasType t) : ctx) (substC 0 (Free (Local i)) e) t'
typeC i ctx _ _ = throwError "type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) t
substI i r (Bound j) = if i == j then r else Bound j
substI i r (Free y) = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)


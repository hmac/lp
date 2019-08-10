module Infer where

import Data.Functor.Foldable
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift, MonadTrans)

import Expr
import Eval (nfc', substitute)

nfc :: Context -> Expr -> Expr
nfc = nfc'

type Env = (Context, Context) -- (types, values)
-- TODO: should we have a single environment containing both types and terms?

-- A helper to let us annotate errors with their source
infixr 5 <?>
(<?>) :: ReaderT Env (Except String) a -> String -> ReaderT Env (Except String) a
e <?> s = let f err = err <> " " <> s
           in mapReaderT (withExceptT f) e

label :: String -> ReaderT Env (Except String) a -> ReaderT Env (Except String) a
label = flip (<?>)

runInfer :: Env -> Expr -> Either String Expr
runInfer env expr = runExcept (runReaderT (infer expr) env)

-- TODO: use a custom error type instead of string, to include context
infer :: Expr -> ReaderT Env (Except String) Expr

-- ANN
infer (Fix (Ann e t)) = label "ANN" $ do
  check t (Fix Type)
  (_, vals) <- ask
  let t' = nfc vals t
  check e t'
  pure t'

-- TYPE
infer (Fix Type) = pure (Fix Type)

-- VAR
infer (Fix (Var v)) = label "VAR" $ do
  (types, _) <- ask
  case lookup v types of
    Just t -> pure t
    Nothing ->
      throw $ "could not determine type of variable " <> v <> "\n" <> show types

-- PI
infer (Fix (Pi x t e)) = label "PI" $ do
  _ <- check t (Fix Type)
  (types, vals) <- ask
  let t' = nfc vals t
  let env' = ((x, t') : types, vals)
  _ <- local (const env') $ check e (Fix Type)
  pure (Fix Type)

-- APP
infer (Fix (App e e')) = label "APP" $ do
  et <- infer e
  case et of
    Fix (Pi x t t') -> do
      _ <- check e' t
      let t'' = substitute x t' e'
      pure t''
    t -> throw $ "expected " <> pretty e <> " to be a Pi type, but was inferred to be " <> pretty t

-- Fallthrough
infer e = throw $ "could not infer type of " <> pretty e

check :: Expr -> Expr -> ReaderT Env (Except String) ()

-- LAM
-- We use explicit names for lambda-abstracted variables instead of de Bruijn indices.
-- Because of this, we need to insert into the context the type of the variable
-- in the Pi type *and* and the type of the variable in the lambda abstraction.
-- I'm not 100% sure this is valid, since they should really refer to the same
-- thing, but it seems to work for now.
check (Fix (Lam x e)) (Fix (Pi x' t t')) = label "LAM" $ do
  (types, vals) <- ask
  _ <- check (nfc vals t) (Fix Type)
  let env' = ((x', t) : (x, t) : types, vals)
  _ <- local (const env') $ check e t'
  pure ()

-- 𝚪 ⊢ e :↑ t
------------- (CHK)
-- 𝚪 ⊢ e :↓ t
check e t = label "CHK" $ do
  env <- ask
  let (types, vals) = env
  t' <- nfc vals <$> infer e
  let tn = nfc types t
  if isEqual env t' tn
    then pure ()
    else throw $ "could not infer that " <> pretty (nfc vals e) <>
                 " has type " <> pretty tn <>
                 " (inferred type " <> pretty t' <> " instead)" <>
                 "\n\n" <> show (mapSnd pretty vals) <>
                 "\n\n" <> show (mapSnd pretty types) <>
                 "\n\nisEqual env t' tn = " <> show (isEqual env t' tn) <>
                 "\n\n env: \n\n" <> show env <>
                 "\n\n t': \n\n" <> show t' <>
                 "\n\n tn: \n\n" <> show tn <>
                 "\n\n"

-- Determine if two expressions are equal, up to alpha conversion
-- Currently unsure how to express this via a recursion scheme
isEqual :: Env -> Expr -> Expr -> Bool
isEqual _env e1 e2 | e1 == e2 = True
isEqual env (Fix e1) (Fix e2) = eq e1 e2
  where (types, vals) = env
        ctx = types ++ vals
        eq (Var x) (Var y) = case (lookup x ctx, lookup y ctx) of
                               (Just x', Just y') -> isEqual env x' y'
                               _ -> False
        eq (Lam _ e) (Lam _ f) = isEqual env e f
        eq (App s t) (App u v) = isEqual env s u && isEqual env t v
        eq (Pi _ s t) (Pi _ u v) = isEqual env s u && isEqual env t v
        eq _ _ = False

-- Convenience function for throwing type errors
throw :: (Monad m, MonadTrans t) => e -> t (ExceptT e m) a
throw = lift . throwE

module Infer where

import           Data.Functor.Foldable
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class      ( lift
                                                , MonadTrans
                                                )

import           Expr                    hiding ( Context )
import           Expr.Pretty -- to import orphan Pretty instances for Expr
import           Eval                           ( nfc
                                                , reduce
                                                )
import           Pretty

import           System.IO.Unsafe               ( unsafePerformIO )

type Context = [BExpr]
type Env = (Context, Context) -- (types, values)
-- TODO: should we have a single environment containing both types and terms?

-- A helper to let us annotate errors with their source
infixr 5 <?>
(<?>)
  :: ReaderT Env (Except String) a -> String -> ReaderT Env (Except String) a
e <?> s = let f err = err <> " " <> s in mapReaderT (withExceptT f) e

label
  :: String -> ReaderT Env (Except String) a -> ReaderT Env (Except String) a
label = flip (<?>)

runInfer :: Env -> BExpr -> Either String BExpr
runInfer env expr = runExcept (runReaderT (infer expr) env)

-- TODO: use a custom error type instead of string, to include context
infer :: BExpr -> ReaderT Env (Except String) BExpr

-- ANN
infer (Fix (Ann e t)) = label "ANN" $ do
  check t (Fix Type)
  (types, _vals) <- ask
  let t' = nfc types t
  check e t'
  pure t'

-- TYPE
infer (Fix Type   ) = pure (Fix Type)

-- VAR
infer (Fix (Var v)) = label "VAR" $ do
  (types, _) <- ask
  case safeIndex v types of
    Just t -> pure t
    Nothing ->
      throw
        $  "could not determine type of variable "
        <> show v
        <> "\n"
        <> show types

-- PI
infer (Fix (Pi _ t e)) = label "PI" $ do
  check t (Fix Type)
  (types, vals) <- ask
  let t'   = nfc types t
  let env' = (t' : types, t' : vals)
  _ <- local (const env') $ check e (Fix Type)
  pure (Fix Type)

-- APP
infer (Fix (App e e')) = label "APP" $ do
  et <- infer e
  case et of
    Fix p@(Pi _ t _) -> do
      check e' t
      let tn = reduce [e'] $ Fix $ App (Fix p) e'
      pure tn
    t ->
      throw
        $  "expected "
        <> pp e
        <> " to be a Pi type, but was inferred to have type "
        <> pp t

-- Fallthrough
infer e = throw $ "could not infer type of " <> pp e

check :: BExpr -> BExpr -> ReaderT Env (Except String) ()

-- LAM
check (Fix (Lam _ e)) (Fix (Pi _ t t')) = label "LAM" $ do
  (types, vals) <- ask
  check (nfc vals t) (Fix Type)
  let tn   = t
  -- Assume (x : t) and add this to the environment when checking (e : t')
  let env' = (tn : types, vals)
  unsafePerformIO $ putStrLn ("env': " ++ show env') >> pure (pure ())
  unsafePerformIO $ putStrLn ("e: " ++ pp e) >> pure (pure ())
  unsafePerformIO $ putStrLn ("t': " ++ pp t') >> pure (pure ())
  _ <- local (const env') $ check e t'
  pure ()

-- 𝚪 ⊢ e :↑ t
------------- (CHK)
-- 𝚪 ⊢ e :↓ t
check e t = label "CHK" $ do
  env <- ask
  let (types, vals) = env
  t' <- nfc types <$> infer e
  let tn = nfc types t
  if t' == tn
    then pure ()
    else
      throw
      $  "could not infer that "
      <> pp (nfc vals e)
      <> " has type "
      <> pp tn
      <> " (inferred type "
      <> pp t'
      <> " instead)"
      <> " | vals: "
      <> show vals
      <> " | types: "
      <> show types
      <> " | env: "
      <> show env
      <> " | t': "
      <> show t'
      <> " | tn: "
      <> show tn

-- Convenience function for throwing type errors
throw :: (Monad m, MonadTrans t) => e -> t (ExceptT e m) a
throw = lift . throwE

safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []       = Nothing
safeIndex 0 (x : _ ) = Just x
safeIndex i (_ : xs) = safeIndex (i - 1) xs

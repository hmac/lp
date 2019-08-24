{-# LANGUAGE DerivingVia #-}
module Infer where

import qualified Data.Monoid                   as Monoid
                                                ( Sum(..) )
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class      ( lift
                                                , MonadTrans
                                                )

import           Expr                    hiding ( Context )
-- to import orphan Pretty instances for Expr
import           Expr.Pretty                    ( )
import           Eval                           ( evalExpr )
import           Pretty

import           System.IO.Unsafe               ( unsafePerformIO )

-- so we can still use mempty for Env
newtype Depth = Depth Int deriving (Semigroup, Monoid) via (Monoid.Sum Int)
                          deriving Show
                          deriving Num via Int

type Context = [(String, Expr)]
type Env = (Context, Context, Depth, Debug) -- (types, values, stack depth)

data Debug = DebugOn | DebugOff deriving Show

check_ :: Expr -> Expr -> ReaderT Env (Except String) ()
check_ e t = step (check e t)

infer_ :: Expr -> ReaderT Env (Except String) Expr
infer_ e = step (infer e)

step :: Monad m => ReaderT Env m a -> ReaderT Env m a
step f = do
  (types, vals, depth, debug) <- ask
  local (const (types, vals, depth + 1, debug)) f

trace :: Monad m => String -> ReaderT Env m ()
trace msg = do
  (_, _, Depth depth, debug) <- ask
  let prefix = replicate (depth * 2) '-'
      msg'   = prefix ++ msg
  case debug of
    DebugOn  -> unsafePerformIO $ putStrLn msg' >> pure (pure ())
    DebugOff -> pure ()

spy :: Monad m => ReaderT Env m Expr -> ReaderT Env m Expr
spy f = do
  x <- f
  trace $ "[" ++ pp x ++ "]"
  pure x

-- A helper to let us annotate errors with their source
label
  :: String -> ReaderT Env (Except String) a -> ReaderT Env (Except String) a
label = flip (<?>)
 where
  e <?> s =
    let f err = err <> " [" <> s <> "]" in mapReaderT (withExceptT f) e

runInfer :: (Context, Context) -> Expr -> Either String Expr
runInfer (types, vals) expr =
  runExcept (runReaderT (infer expr) (types, vals, 0, DebugOff))

runInferDebug :: (Context, Context) -> Expr -> Either String Expr
runInferDebug (types, vals) expr =
  runExcept (runReaderT (infer expr) (types, vals, 0, DebugOn))

-- for debugging
runCheck :: Env -> Expr -> Expr -> Either String ()
runCheck env expr t = runExcept (runReaderT (check expr t) env)

-- TODO: use a custom error type instead of string, to include context
infer :: Expr -> ReaderT Env (Except String) Expr

-- ANN
infer ((Ann e t)) = label "ANN" $ do
  trace "ANN"
  check_ t (Type)
  (_types, vals, _, _) <- ask
  let t' = evalExpr vals t
  trace $ "t: " ++ pp t'
  check_ e t'
  spy $ pure t'

-- TYPE
infer (Type   ) = pure (Type)

-- VAR
infer ((Var v)) = label "VAR" $ do
  trace $ "VAR (" ++ v ++ ")"
  (types, _, _, _) <- ask
  case lookup v types of
    Just t -> spy $ pure t
    Nothing ->
      throw
        $  "could not determine type of variable "
        <> show v
        <> "\n"
        <> show types

-- PI
infer ((Pi x t e)) = label "PI" $ do
  trace "PI"
  check_ t (Type)
  (types, vals, d, debug) <- ask
  let t'   = evalExpr vals t
  let env' = ((x, t') : types, vals, d, debug)
  _ <- local (const env') $ check_ e (Type)
  spy $ pure (Type)

-- APP
infer ((App e e')) = label "APP" $ do
  trace $ "APP " ++ pp ((App e e'))
  (types, vals, _, _) <- ask
  e_type              <- infer_ e
  trace $ "e: " ++ pp e
  trace $ "e': " ++ pp e'
  trace $ "e_type: " ++ pp e_type
  case e_type of
    (Pi x t t') -> do
      check_ e' t
      trace $ "x: " ++ pp x
      trace $ "e': " ++ pp e'
      trace $ show vals
      trace $ "t': " ++ pp t'
      let t'n = evalExpr ((x, e') : vals) t'
      trace $ x ++ " = " ++ pp e'
      trace $ "t': " ++ pp t'
      trace $ "t'n: " ++ pp t'n
      trace $ "types: " ++ show types
      trace $ "vals: " ++ show vals
      spy $ pure t'n
    t ->
      throw
        $  "expected "
        <> pp e
        <> " to be a Pi type, but was inferred to have type "
        <> pp t
        <> " ( "
        <> show (evalExpr vals e)
        <> " )"

-- Nat
infer (Nat    ) = pure Type
infer (Zero   ) = pure Nat
infer ((Suc n)) = label "SUC" $ do
  check_ n Nat
  pure Nat

-- Product
infer ((Prod (Type) (Type))) = pure Type
infer ((Prod a      b     )) = do
  ta <- infer_ a
  tb <- infer_ b
  pure $ if ta == Type && tb == Type then Type else Prod ta tb

-- Sum
infer ((Sum l r)) = do
  check_ r Type
  check_ l Type
  pure Type

-- List
infer ((List t)) = label "LIST" $ do
  check_ t Type
  pure Type
-- If the list is a singleton, we can directly infer the type from the element
infer ((LCons x (LNil))) = label "LCONS" $ do
  t <- infer_ x
  pure $ List t
infer ((LCons x xs)) = label "LCONS" $ do
  t <- infer_ xs
  check (LCons x LNil) t
  pure t

-- Unit and Bottom
infer (T            ) = pure Type
infer (Void         ) = pure Type
infer ((Absurd t)   ) = check t Type >> pure t
infer (Unit         ) = pure T

-- Equality
infer ((Equal t a b)) = label "EQ" $ do
  check_ t Type
  check_ a t
  check_ b t
  pure Type

infer ((Refl a)) = label "REFL" $ do
  t <- infer_ a
  pure $ Equal t a a

infer ((EqElim a m mr x y eq)) = label "EQELIM" $ do
  (_, vals, _, _) <- ask
  check a Type
  check m $ Pi "x" a (Pi "y" a (Pi "eq" (Equal a (Var "x") (Var "y")) Type))
  check mr $ Pi "x" a (App (App (App m (Var "x")) (Var "x")) (Refl (Var "x")))
  check x a
  check y a
  check eq $ Equal a x y
  pure $ evalExpr vals $ App (App (App m x) y) eq

-- W constructor
infer ((W a b)) = label "W" $ do
  check_ a Type
  check b (Pi "x" a Type)
  pure Type
infer ((Sup a b)) = label "SUP" $ do
  ta <- infer_ a
  tb <- infer_ b
  case tb of
    (Pi _ _ ((W wa wb))) -> do
      let tx = App wb a
      check b (Pi "_" tx (W ta wb))
      pure (W wa wb)
    t ->
      throw
        $  "expected "
        ++ pp b
        ++ " to have have a type of the form "
        ++ pp (Pi "_" (Var "B(a)") (W (Var "A") (Var "B")))
        ++ " but inferred it to have type "
        ++ pp t

-- Fin
infer ((Fin   r)) = label "FIN" $ check_ r Nat >> pure Type
infer ((FZero n)) = label "FZERO" $ check_ n Nat >> pure (Fin (Suc n))
infer ((FSuc  f)) = label "FSUC" $ do
  ft <- infer_ f
  case ft of
    ((Fin n)) -> pure (Fin (Suc n))
    t ->
      throw
        $  "expected "
        ++ pp f
        ++ " to be a Fin type, but inferred it to have type "
        ++ pp t

-- Fallthrough
infer e = throw $ "could not infer type of " <> pp e

check :: Expr -> Expr -> ReaderT Env (Except String) ()

-- Short-circuit for the most common use of check
check (Type     ) (Type        ) = pure ()

-- LAM
check ((Lam x e)) ((Pi x' t t')) = label "LAM" $ do
  trace $ "LAM " ++ pp ((Lam x e)) ++ " : " ++ pp ((Pi x' t t'))
  (types, vals, d, debug) <- ask
  check_ (evalExpr vals t) (Type)
  -- Assume (x : t) and (x' : t) and add this to the environment when checking (e : t')
  let env' = ((x, t) : (x', t) : types, vals, d, debug)
  trace $ "env': " ++ show env'
  -- trace $ "e: " ++ pp e
  -- trace $ "t': " ++ pp t'
  _ <- local (const env') $ check_ e t'
  pure ()

check ((SumL l)) ((Sum lt _ )) = label "SUML" $ check_ l lt
check ((SumR r)) ((Sum _  rt)) = label "SUMR" $ check_ r rt

check (LNil    ) ((List t   )) = label "LNIL" $ check t Type

-- 𝚪 ⊢ e :↑ t
------------- (CHK)
-- 𝚪 ⊢ e :↓ t
--
-- To compare two types, we first evaluate them as much as possible, then
-- convert them to BExprs (de Bruijn indexed) and directly compare them for
-- structural equality.
-- This means we can ignore differences in variable names.
check e          t             = label "CHK" $ do
  env <- ask
  trace $ "CHK " ++ pp e ++ " : " ++ pp t
  let (types, vals, _, _) = env
  t' <- evalExpr vals <$> infer_ e
  let tn  = evalExpr [] t
      t'b = safeTranslate types t'
      tnb = safeTranslate types tn
  trace $ "types: " ++ show types
  trace $ "vals: " ++ show vals
  trace $ "t: " ++ pp t
  trace $ "t': " ++ pp t'
  trace $ "tn: " ++ pp tn
  case t'b of
    Left  err -> throw $ err ++ " (when translating " ++ pp t' ++ ")"
    Right t'b -> case tnb of
      Left  err -> throw $ err ++ " (when translating " ++ pp tn ++ ")"
      Right tnb -> do
        trace $ "t'b: " ++ pp t'b
        trace $ "tnb: " ++ pp tnb
        if t'b == tnb
          then pure ()
          else
            throw
            $  "could not infer that "
            <> pp (evalExpr vals e)
            <> " has type "
            <> pp tnb
            <> " (inferred type "
            <> pp t'b
            <> " instead)"

-- Convenience function for throwing type errors
throw :: (Monad m, MonadTrans t) => e -> t (ExceptT e m) a
throw = lift . throwE

safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []       = Nothing
safeIndex 0 (x : _ ) = Just x
safeIndex i (_ : xs) = safeIndex (i - 1) xs

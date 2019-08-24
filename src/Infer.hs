{-# LANGUAGE DerivingVia #-}
module Infer where

import           Prelude                 hiding ( pi )
import qualified Data.Monoid                   as Monoid
                                                ( Sum(..) )
import           Data.Functor.Foldable
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
infer (Fix (Ann e t)) = label "ANN" $ do
  trace "ANN"
  check_ t (Fix Type)
  (_types, vals, _, _) <- ask
  let t' = evalExpr vals t
  trace $ "t: " ++ pp t'
  check_ e t'
  spy $ pure t'

-- TYPE
infer (Fix Type   ) = pure (Fix Type)

-- VAR
infer (Fix (Var v)) = label "VAR" $ do
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
infer (Fix (Pi x t e)) = label "PI" $ do
  trace "PI"
  check_ t (Fix Type)
  (types, vals, d, debug) <- ask
  let t'   = evalExpr vals t
  let env' = ((x, t') : types, vals, d, debug)
  _ <- local (const env') $ check_ e (Fix Type)
  spy $ pure (Fix Type)

-- APP
infer (Fix (App e e')) = label "APP" $ do
  trace $ "APP " ++ pp (Fix (App e e'))
  (types, vals, _, _) <- ask
  e_type              <- infer_ e
  trace $ "e: " ++ pp e
  trace $ "e': " ++ pp e'
  trace $ "e_type: " ++ pp e_type
  case e_type of
    Fix (Pi x t t') -> do
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
infer (Fix Nat    ) = pure type_
infer (Fix Zero   ) = pure nat
infer (Fix (Suc n)) = label "SUC" $ do
  check_ n nat
  pure nat

-- Product
infer (Fix (Prod (Fix Type) (Fix Type))) = pure type_
infer (Fix (Prod a          b         )) = do
  ta <- infer_ a
  tb <- infer_ b
  pure $ if ta == type_ && tb == type_ then type_ else prod ta tb

-- Sum
infer (Fix (Sum l r)) = do
  check_ r type_
  check_ l type_
  pure type_

-- List
infer (Fix (List t)) = label "LIST" $ do
  check_ t type_
  pure type_
-- If the list is a singleton, we can directly infer the type from the element
infer (Fix (LCons x (Fix LNil))) = label "LCONS" $ do
  t <- infer_ x
  pure $ list t
infer (Fix (LCons x xs)) = label "LCONS" $ do
  t <- infer_ xs
  check (lcons x lnil) t
  pure t

-- Unit and Bottom
infer (Fix T            ) = pure type_
infer (Fix Void         ) = pure type_
infer (Fix (Absurd t)   ) = check t type_ >> pure t
infer (Fix Unit         ) = pure tt

infer (Fix (Equal t a b)) = label "EQ" $ do
  check_ t type_
  check_ a t
  check_ b t
  pure type_

infer (Fix (Refl a)) = label "REFL" $ do
  t <- infer_ a
  pure $ equal t a a

infer (Fix (EqElim a m mr x y eq)) = label "EQELIM" $ do
  (_, vals, _, _) <- ask
  check a type_
  check m $ pi "x" a (pi "y" a (pi "eq" (equal a (var "x") (var "y")) type_))
  check mr $ pi "x" a (app (app (app m (var "x")) (var "x")) (refl (var "x")))
  check x a
  check y a
  check eq $ equal a x y
  pure $ evalExpr vals $ app (app (app m x) y) eq

-- W constructor
infer (Fix (W a b)) = label "W" $ do
  check_ a type_
  check b (pi "x" a type_)
  pure type_
infer (Fix (Sup a b)) = label "SUP" $ do
  ta <- infer_ a
  tb <- infer_ b
  case tb of
    Fix (Pi _ _ (Fix (W wa wb))) -> do
      let tx = app wb a
      check b (pi "_" tx (w ta wb))
      pure (w wa wb)
    t ->
      throw
        $  "expected "
        ++ pp b
        ++ " to have have a type of the form "
        ++ pp (pi "_" (var "B(a)") (w (var "A") (var "B")))
        ++ " but inferred it to have type "
        ++ pp t

-- Fin
infer (Fix (Fin   r)) = label "FIN" $ check_ r nat >> pure type_
infer (Fix (FZero n)) = label "FZERO" $ check_ n nat >> pure (fin (suc n))
infer (Fix (FSuc  f)) = label "FSUC" $ do
  ft <- infer_ f
  case ft of
    (Fix (Fin n)) -> pure (fin (suc n))
    t ->
      throw
        $  "expected "
        ++ pp f
        ++ " to be a Fin type, but inferred it to have type "
        ++ pp t
-- finElim : forall (m : forall (n : Nat) (_ : Fin n). Type)
--                  (mz : forall (n : Nat). m (Suc n) (FZero n))
--                  (ms : forall (n : Nat) (f : Fin n) (_ : m n f). m (Suc n) (FSuc f))
--                  (n : Nat)
--                  (f : Fin n). m n f
--
-- To typecheck this, we just construct the expected type of finElim and infer
-- the result when applying it to the arguments.
infer (Fix (FinElim m mz ms n f)) =
  label "FINELIM"
    $ let
        elim' = Fix
          (Pi
            "m"
            (Fix
              (Pi "n1"
                  (Fix Nat)
                  (Fix (Pi "f" (Fix (Fin (Fix (Var "n1")))) (Fix Type)))
              )
            )
            (Fix
              (Pi
                "mz"
                (Fix
                  (Pi
                    "n2"
                    (Fix Nat)
                    (Fix
                      (App
                        (Fix (App (Fix (Var "m")) (Fix (Suc (Fix (Var "n2"))))))
                        (Fix (FZero (Fix (Var "n2"))))
                      )
                    )
                  )
                )
                (Fix
                  (Pi
                    "ms"
                    (Fix
                      (Pi
                        "n3"
                        (Fix Nat)
                        (Fix
                          (Pi
                            "f"
                            (Fix (Fin (Fix (Var "n3"))))
                            (Fix
                              (Pi
                                "rec"
                                (Fix
                                  (App
                                    (Fix (App (Fix (Var "m")) (Fix (Var "n3"))))
                                    (Fix (Var "f"))
                                  )
                                )
                                (Fix
                                  (App
                                    (Fix
                                      (App (Fix (Var "m"))
                                           (Fix (Suc (Fix (Var "n3"))))
                                      )
                                    )
                                    (Fix (FSuc (Fix (Var "f"))))
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                    (Fix
                      (Pi
                        "n4"
                        (Fix Nat)
                        (Fix
                          (Pi
                            "f"
                            (Fix (Fin (Fix (Var "n4"))))
                            (Fix
                              (App
                                (Fix (App (Fix (Var "m")) (Fix (Var "n4"))))
                                (Fix (Var "f"))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        expr = app (app (app (app (app (var "finElim") m) mz) ms) n) f
      in
        local (\(ts, vs, dep, deb) -> (("finElim", elim') : ts, vs, dep, deb))
          $ infer_ expr

-- Fallthrough
infer e = throw $ "could not infer type of " <> pp e

check :: Expr -> Expr -> ReaderT Env (Except String) ()

-- Short-circuit for the most common use of check
check (Fix Type     ) (Fix Type        ) = pure ()

-- LAM
check (Fix (Lam x e)) (Fix (Pi x' t t')) = label "LAM" $ do
  trace $ "LAM " ++ pp (Fix (Lam x e)) ++ " : " ++ pp (Fix (Pi x' t t'))
  (types, vals, d, debug) <- ask
  check_ (evalExpr vals t) (Fix Type)
  -- Assume (x : t) and (x' : t) and add this to the environment when checking (e : t')
  let env' = ((x, t) : (x', t) : types, vals, d, debug)
  trace $ "env': " ++ show env'
  -- trace $ "e: " ++ pp e
  -- trace $ "t': " ++ pp t'
  _ <- local (const env') $ check_ e t'
  pure ()

check (Fix (SumL l)) (Fix (Sum lt _ )) = label "SUML" $ check_ l lt
check (Fix (SumR r)) (Fix (Sum _  rt)) = label "SUMR" $ check_ r rt

check (Fix LNil    ) (Fix (List t   )) = label "LNIL" $ check t type_

-- 𝚪 ⊢ e :↑ t
------------- (CHK)
-- 𝚪 ⊢ e :↓ t
--
-- To compare two types, we first evaluate them as much as possible, then
-- convert them to BExprs (de Bruijn indexed) and directly compare them for
-- structural equality.
-- This means we can ignore differences in variable names.
check e              t                 = label "CHK" $ do
  env <- ask
  trace $ "CHK " ++ pp e ++ " : " ++ pp t
  let (types, vals, _, debug) = env
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
        trace $ "t: " ++ pp t
        trace $ "t': " ++ pp t'
        trace $ "tn: " ++ pp tn
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

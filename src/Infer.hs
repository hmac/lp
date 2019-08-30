{-# LANGUAGE DerivingVia #-}
module Infer where

import qualified Data.Monoid                   as Monoid
                                                ( Sum(..) )
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class      ( lift )

import           Expr
import           Expr.Pretty                    ( pp )
import           Eval                           ( evalExpr )
import           Expr.Prelude                   ( sumElimType )

import           System.IO.Unsafe               ( unsafePerformIO )

-- so we can still use mempty for Env
newtype Depth = Depth Int deriving (Semigroup, Monoid) via (Monoid.Sum Int)
                          deriving Show
                          deriving Num via Int

type Env = (Context, Context, [Expr], Debug) -- (types, values, stack depth)

data Debug = DebugOn | DebugOff deriving Show

-- TODO: merge
data Error = Error { environment :: (Context, Context)
                   , stack :: [Expr]
                   , detail :: ErrorDetail
                   }
                   deriving Show

data ErrorDetail = TypeMismatch { subject :: Expr, expected :: Expr, inferred :: Expr }
           | UnknownVar String
           | CannotInfer Expr
           | Other String
  deriving Show

check_ :: Expr -> Expr -> ReaderT Env (Except Error) ()
check_ e t = step e (check e t)

infer_ :: Expr -> ReaderT Env (Except Error) Expr
infer_ e = step e (infer e)

step :: Monad m => Expr -> ReaderT Env m a -> ReaderT Env m a
step e f = do
  (types, vals, stack, debug) <- ask
  local (const (types, vals, e : stack, debug)) f

trace :: Monad m => String -> ReaderT Env m ()
trace msg = do
  (_, _, stack, debug) <- ask
  let prefix = replicate (length stack * 2) '-'
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
-- TODO: rewrite for the new error type - error type should accumulate a stack
-- of contexts of the form (rule, subject) :: (String, Expr)
label :: String -> ReaderT Env (Except e) a -> ReaderT Env (Except e) a
label _ = id
-- label = flip (<?>)
--  where
--   e <?> s =
--     let f err = err <> " [" <> s <> "]" in mapReaderT (withExceptT f) e

askTypes :: ReaderT Env (Except e) Context
askTypes = ask >>= (\(types, _, _, _) -> pure types)

askVals :: ReaderT Env (Except e) Context
askVals = ask >>= (\(_, vals, _, _) -> pure vals)

runInfer :: (Context, Context) -> Expr -> Either Error Expr
runInfer (types, vals) expr =
  runExcept (runReaderT (infer expr) (types, vals, [expr], DebugOff))

runInferDebug :: (Context, Context) -> Expr -> Either Error Expr
runInferDebug (types, vals) expr =
  runExcept (runReaderT (infer expr) (types, vals, [expr], DebugOn))

-- for debugging
runCheck :: Env -> Expr -> Expr -> Either Error ()
runCheck env expr t = runExcept (runReaderT (check expr t) env)

-- TODO: use a custom error type instead of string, to include context
infer :: Expr -> ReaderT Env (Except Error) Expr

-- ANN
infer (Ann e t) = label "ANN" $ do
  trace "ANN"
  check_ t Type
  vals <- askVals
  let t' = evalExpr vals t
  trace $ "t: " ++ pp t'
  check_ e t'
  spy $ pure t'

-- TYPE
infer Type    = pure Type

-- VAR
infer (Var v) = label "VAR" $ do
  trace $ "VAR (" ++ v ++ ")"
  types <- askTypes
  case lookup v types of
    Just t  -> spy $ pure t
    Nothing -> throw $ UnknownVar v

-- PI
infer (Pi x t e) = label "PI" $ do
  trace "PI"
  check_ t Type
  (types, vals, d, debug) <- ask
  let t'   = evalExpr vals t
  let env' = ((x, t') : types, vals, d, debug)
  _ <- local (const env') $ check_ e Type
  spy $ pure Type

-- APP
infer (App e e') = label "APP" $ do
  trace $ "APP " ++ pp (App e e')
  vals   <- askVals
  e_type <- infer_ e
  trace $ "e: " ++ pp e
  trace $ "e': " ++ pp e'
  trace $ "e_type: " ++ pp e_type
  case e_type of
    (Pi x t t') -> do
      check_ e' t
      trace $ "x: " ++ x
      trace $ "e': " ++ pp e'
      trace $ show vals
      trace $ "t': " ++ pp t'
      let e'n = evalExpr vals e'
      let t'n = evalExpr ((x, e'n) : vals) t'
      trace $ "t': " ++ pp t'
      trace $ "t'n: " ++ pp t'n
      trace $ x ++ " = " ++ pp e'
      spy $ pure t'n
    t -> throw TypeMismatch
      { subject  = e
      , expected = Pi "<var>" (Var "<type>") (Var "<type>")
      , inferred = t
      }

-- Eliminators
-- TODO: the rest
infer SumElim = pure sumElimType

-- Nat
infer Nat     = pure Type
infer Zero    = pure Nat
infer (Suc n) = label "SUC" $ do
  check_ n Nat
  pure Nat

-- Product
infer (Prod Type Type) = pure Type
infer (Prod a    b   ) = do
  ta <- infer_ a
  tb <- infer_ b
  pure $ if ta == Type && tb == Type then Type else Prod ta tb

-- Sum
infer (Sum l r) = do
  check_ r Type
  check_ l Type
  pure Type

-- List
infer (List t) = label "LIST" $ do
  check_ t Type
  pure Type
-- If the list is a singleton, we can directly infer the type from the element
infer (LCons x LNil) = label "LCONS" $ do
  t <- infer_ x
  pure $ List t
infer (LCons x xs) = label "LCONS" $ do
  t <- infer_ xs
  check (LCons x LNil) t
  pure t

-- Unit and Bottom
infer T             = pure Type
infer Void          = pure Type
infer (Absurd t e)  = check t Type >> check e Void >> pure t
infer Unit          = pure T

-- Equality
infer (Equal t a b) = label "EQ" $ do
  check_ t Type
  check_ a t
  check_ b t
  pure Type

infer (Refl a) = label "REFL" $ do
  t <- infer_ a
  pure $ Equal t a a

infer (EqElim a m mr x y eq) = label "EQELIM" $ do
  vals <- askVals
  check a Type
  check m $ Pi "x" a (Pi "y" a (Pi "eq" (Equal a (Var "x") (Var "y")) Type))
  check mr $ Pi "x" a (App (App (App m (Var "x")) (Var "x")) (Refl (Var "x")))
  check x a
  check y a
  check eq $ Equal a x y
  pure $ evalExpr vals $ App (App (App m x) y) eq

-- W constructor
infer (W a b) = label "W" $ do
  check_ a Type
  check b (Pi "x" a Type)
  pure Type
-- a : A
-- f : forall (_ : B(a)). W A B
infer (Sup a f) = label "SUP" $ do
  ta <- infer_ a
  b  <- infer_ f
  case b of
    (Pi _ _ (W wa wb)) -> do
      let tx = App wb a
      check f (Pi "_" tx (W ta wb))
      pure (W wa wb)
    t -> throw TypeMismatch
      { subject  = f
      , expected = Pi "_" (Var "B(a)") (W (Var "A") (Var "B"))
      , inferred = t
      }
-- m : forall (_ : W a b). Type
-- w : W a b
-- r : forall (t : a)
--            (f : forall (_ : b t). W a b)
--            (rec : forall (y : b t). m (f y)). m (sup t f)
infer (Rec m w r) = label "REC" $ do
  wt <- infer_ w
  case wt of
    W a b -> do
      check_ m $ Pi "_" (W a b) Type
      check_ r $ Pi
        "t"
        a
        (Pi
          "f"
          (Pi "_" (App b (Var "t")) (W a b))
          (Pi "rec"
              (Pi "y" (App b (Var "t")) (App m (App (Var "f") (Var "y"))))
              (App m (Sup (Var "t") (Var "f")))
          )
        )
      pure $ App m w
    t -> throw $ TypeMismatch { subject  = w
                              , expected = W (Var "<a>") (Var "<b>")
                              , inferred = t
                              }

-- Fin
infer (Fin   r) = label "FIN" $ check_ r Nat >> pure Type
infer (FZero n) = label "FZERO" $ check_ n Nat >> pure (Fin (Suc n))
infer (FSuc  f) = label "FSUC" $ do
  ft <- infer_ f
  case ft of
    (Fin n) -> pure (Fin (Suc n))
    t       -> throw TypeMismatch { subject  = f
                                  , expected = Fin (Var "<some nat>")
                                  , inferred = t
                                  }

-- Booleans
infer Boolean = pure Type
infer BTrue   = pure Boolean
infer BFalse  = pure Boolean

-- Fallthrough
infer e       = throw $ CannotInfer e

check :: Expr -> Expr -> ReaderT Env (Except Error) ()

-- Short-circuit for the most common use of check
check Type      Type         = pure ()

-- LAM
check (Lam x e) (Pi x' t t') = label "LAM" $ do
  trace $ "LAM " ++ pp (Lam x e) ++ " : " ++ pp (Pi x' t t')
  (types, vals, d, debug) <- ask
  check_ (evalExpr vals t) Type
  -- Assume (x : t) and (x' : t) and add this to the environment when checking (e : t')
  let types' = if x == x' then (x, t) : types else (x, t) : (x', t) : types
      env'   = (types', vals, d, debug)
  trace $ "env': " ++ show env'
  -- trace $ "e: " ++ pp e
  -- trace $ "t': " ++ pp t'
  _ <- local (const env') $ check_ e t'
  pure ()

check (SumL l) (Sum lt _ ) = label "SUML" $ check_ l lt
check (SumR r) (Sum _  rt) = label "SUMR" $ check_ r rt

check LNil     (List t   ) = label "LNIL" $ check t Type

-- 𝚪 ⊢ e :↑ t
------------- (CHK)
-- 𝚪 ⊢ e :↓ t
--
-- To compare two types, we first evaluate them as much as possible, then
-- convert them to BExprs (de Bruijn indexed) and directly compare them for
-- structural equality.
-- This means we can ignore differences in variable names.
check e        t           = label "CHK" $ do
  trace $ "CHK " ++ pp e ++ " : " ++ pp t
  types         <- askTypes
  vals          <- askVals
  t'            <- evalExpr vals <$> infer_ e
  t'_simplified <- infer_ e -- we just use this in errors, to make things smaller
  let tn  = evalExpr vals t
      t'b = safeTranslate types t'
      tnb = safeTranslate types tn
  trace $ "t: " ++ pp t
  trace $ "t': " ++ pp t'
  trace $ "tn: " ++ pp tn
  case t'b of
    Left  err -> throw $ Other $ err ++ " (when translating " ++ pp t' ++ ")"
    Right t'b -> case tnb of
      Left  err -> throw $ Other $ err ++ " (when translating " ++ pp tn ++ ")"
      Right tnb -> do
        trace $ "t'b: " ++ pp t'b
        trace $ "tnb: " ++ pp tnb
        if t'b == tnb
          then pure ()
          else throw TypeMismatch { subject  = e
                                  , expected = tn
                                  , inferred = t'_simplified
                                  }

-- Convenience function for throwing type errors
-- ReaderT Env (Except Error) ()
throw :: ErrorDetail -> ReaderT Env (Except Error) a
throw err = do
  (types, vals, s, _) <- ask
  let e = Error { environment = (types, vals), detail = err, stack = s }
  lift $ throwE e

safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []       = Nothing
safeIndex 0 (x : _ ) = Just x
safeIndex i (_ : xs) = safeIndex (i - 1) xs

module Expr.Prelude where

import           Prelude                 hiding ( pi
                                                , sum
                                                )
import           Expr

-- Prelude
prelude :: (Context, Context)
prelude = (preludeTypes, preludeVals)

-- Builtin functions
preludeVals :: Context
preludeVals =
  [ ("natElim" , natElim)
  , ("prodElim", prodElim)
  , ("sumElim" , sumElim)
  , ("listElim", listElim)
  , ("finElim" , finElim)
  ]

-- Builtin function types
preludeTypes :: Context
preludeTypes =
  -- natElim : forall (m : forall (_ : Nat). Type)
  --                  (mz : m Zero)
  --                  (ms : forall (l : Nat) (_ : m l). m (Suc l)
  --                  (k : Nat). m k
  [ ( "natElim"
    , pi
      "m"
      (pi "_" nat type_)
      (pi
        "mz"
        (app (var "m") zero)
        (pi
          "ms"
          (pi
            "l"
            nat
            (pi "_" (app (var "m") (var "l")) (app (var "m") (suc (var "l"))))
          )
          (pi "k" nat (app (var "m") (var "k")))
        )
      )
    )
  -- prodElim : forall (a : Type) (b : Type) (c : Type)
  --                   (f : forall (x : a) (y : b). c)
  --                   (p : a*b). c
  , ( "prodElim"
    , pi
      "a"
      type_
      (pi
        "b"
        type_
        (pi
          "c"
          type_
          (pi "f"
              (pi "x" (var "a") (pi "y" (var "b") (var "c")))
              (pi "p" (prod (var "a") (var "b")) (var "c"))
          )
        )
      )
    )
  -- sumElim : forall (a : Type) (b : Type) (c : Type)
  --                  (f : forall (x : a). c)
  --                  (g : forall (y : b). c)
  --                  (s : a|b). c
  , ( "sumElim"
    , pi
      "a"
      type_
      (pi
        "b"
        type_
        (pi
          "c"
          type_
          (pi
            "f"
            (pi "x" (var "a") (var "c"))
            (pi "g"
                (pi "y" (var "b") (var "c"))
                (pi "s" (sum (var "a") (var "b")) (var "c"))
            )
          )
        )
      )
    )
  -- listElim : forall (a : Type)
  --                   (l : List a)
  --                   (m : forall (l : List a). Type)
  --                   (s : m [])
  --                   (f : forall (x : a) (l : List a) (rec : m l). m (x :: l).
  --                   m l
  , ( "listElim"
    , pi
      "a"
      type_
      (pi
        "m"
        (pi "l" (list (var "a")) type_)
        (pi
          "l"
          (list (var "a"))
          (pi
            "s"
            (app (var "m") lnil)
            (pi
              "f"
              (pi
                "x"
                (var "a")
                (pi
                  "l"
                  (list (var "a"))
                  (pi "rec"
                      (app (var "m") (var "l"))
                      (app (var "m") (lcons (var "x") (var "l")))
                  )
                )
              )
              (app (var "m") (var "l"))
            )
          )
        )
      )
    )
  -- finElim : forall (m : forall (n : Nat) (_ : Fin n). Type)
  --                  (mz : forall (n : Nat). m (Suc n) (FZero n))
  --                  (ms : forall (n : Nat) (f : Fin n) (_ : m n f). m (Suc n) (FSuc f))
  --                  (n : Nat)
  --                  (f : Fin n). m n f
  , ( "finElim"
    , pi
      "m"
      (pi "n1" nat (pi "f" (fin (var "n1")) type_))
      (pi
        "mz"
        (pi "n2" nat (app (app (var "m") (suc (var "n2"))) (fzero (var "n2"))))
        (pi
          "ms"
          (pi
            "n3"
            nat
            (pi
              "f"
              (fin (var "n3"))
              (pi "rec"
                  (app (app (var "m") (var "n3")) (var "f"))
                  (app (app (var "m") (suc (var "n3"))) (fsuc (var "f")))
              )
            )
          )
          (pi
            "n4"
            nat
            (pi "f" (fin (var "n4")) (app (app (var "m") (var "n4")) (var "f")))
          )
        )
      )
    )
  ]

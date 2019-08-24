module Expr.Prelude where

import           Expr

prelude :: (Context, Context)
prelude = (preludeTypes, preludeVals)

-- Builtin functions
preludeVals :: Context
preludeVals =
  [ ("natElim" , NatElim)
  , ("prodElim", ProdElim)
  , ("sumElim" , SumElim)
  , ("listElim", ListElim)
  , ("finElim" , FinElim)
  ]

-- Builtin function types
preludeTypes :: Context
preludeTypes =
  -- natElim : forall (m : forall (_ : Nat). Type)
  --                  (mz : m Zero)
  --                  (ms : forall (l : Nat) (_ : m l). m (Suc l)
  --                  (k : Nat). m k
  [ ( "natElim"
    , Pi
      "m"
      (Pi "_" Nat Type)
      (Pi
        "mz"
        (App (Var "m") Zero)
        (Pi
          "ms"
          (Pi
            "l"
            Nat
            (Pi "_" (App (Var "m") (Var "l")) (App (Var "m") (Suc (Var "l"))))
          )
          (Pi "k" Nat (App (Var "m") (Var "k")))
        )
      )
    )
  -- prodElim : forall (a : Type) (b : Type) (c : Type)
  --                   (f : forall (x : a) (y : b). c)
  --                   (p : a*b). c
  , ( "prodElim"
    , Pi
      "a"
      Type
      (Pi
        "b"
        Type
        (Pi
          "c"
          Type
          (Pi "f"
              (Pi "x" (Var "a") (Pi "y" (Var "b") (Var "c")))
              (Pi "p" (Prod (Var "a") (Var "b")) (Var "c"))
          )
        )
      )
    )
  -- sumElim : forall (a : Type) (b : Type) (c : Type)
  --                  (f : forall (x : a). c)
  --                  (g : forall (y : b). c)
  --                  (s : a|b). c
  , ( "sumElim"
    , Pi
      "a"
      Type
      (Pi
        "b"
        Type
        (Pi
          "c"
          Type
          (Pi
            "f"
            (Pi "x" (Var "a") (Var "c"))
            (Pi "g"
                (Pi "y" (Var "b") (Var "c"))
                (Pi "s" (Sum (Var "a") (Var "b")) (Var "c"))
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
    , Pi
      "a"
      Type
      (Pi
        "m"
        (Pi "l" (List (Var "a")) Type)
        (Pi
          "l"
          (List (Var "a"))
          (Pi
            "s"
            (App (Var "m") LNil)
            (Pi
              "f"
              (Pi
                "x"
                (Var "a")
                (Pi
                  "l"
                  (List (Var "a"))
                  (Pi "rec"
                      (App (Var "m") (Var "l"))
                      (App (Var "m") (LCons (Var "x") (Var "l")))
                  )
                )
              )
              (App (Var "m") (Var "l"))
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
    , Pi
      "m"
      (Pi "n1" Nat (Pi "f" (Fin (Var "n1")) Type))
      (Pi
        "mz"
        (Pi "n2" Nat (App (App (Var "m") (Suc (Var "n2"))) (FZero (Var "n2"))))
        (Pi
          "ms"
          (Pi
            "n3"
            Nat
            (Pi
              "f"
              (Fin (Var "n3"))
              (Pi "rec"
                  (App (App (Var "m") (Var "n3")) (Var "f"))
                  (App (App (Var "m") (Suc (Var "n3"))) (FSuc (Var "f")))
              )
            )
          )
          (Pi
            "n4"
            Nat
            (Pi "f" (Fin (Var "n4")) (App (App (Var "m") (Var "n4")) (Var "f")))
          )
        )
      )
    )
  ]

import           Test.Hspec
import           Test.Hspec.Megaparsec

import           Text.Megaparsec                ( parse
                                                , errorBundlePretty
                                                )

import           Data.Either                    ( isLeft
                                                , isRight
                                                )

import           Expr
import           Expr.Prelude
import           Parse
import           Infer
import           Eval                           ( evalExpr )

main :: IO ()
main = hspec $ do
  describe "Parsing" $ do
    "x" ~> Var "x"
    "Type" ~> Type
    "\\x. x" ~> Lam "x" (Var "x")
    "forall (x : Type). x" ~> Pi "x" Type (Var "x")
    "(\\x. x) y" ~> App (Lam "x" (Var "x")) (Var "y")
    "(\\x y. x) z" ~> App (Lam "x" (Lam "y" (Var "x"))) (Var "z")
    "x : Type" ~> Ann (Var "x") Type
    "((\\x. x) : forall (x : Type). Type) Type"
      ~> App (Ann (Lam "x" (Var "x")) (Pi "x" Type Type)) Type
    "forall (x : Type) (y : Type). x" ~> Pi "x" Type (Pi "y" Type (Var "x"))
    "Nat" ~> Nat
    "Zero" ~> Zero
    "Suc Zero" ~> Suc Zero
    "natElim m mz ms k" ~> App
      (App (App (App (Var "natElim") (Var "m")) (Var "mz")) (Var "ms"))
      (Var "k")
    "Nat*Nat" ~> Prod Nat Nat
    "Zero*(Suc Zero)" ~> Prod Zero (Suc Zero)
    "prodElim Nat Nat Nat (\\a b. a) (Zero*Zero)" ~> App
      (App (App (App (App (Var "prodElim") Nat) Nat) Nat)
           (Lam "a" (Lam "b" (Var "a")))
      )
      (Prod Zero Zero)
    "Nat|Nat" ~> Sum Nat Nat
    "Nat|(Nat|Type)" ~> Sum Nat (Sum Nat Type)
    "Nat|(Nat*Type)" ~> Sum Nat (Prod Nat Type)
    "Left Zero" ~> SumL Zero
    "sumElim Type Nat Nat (\\a. Zero) (\\b. Zero) (Left Type)" ~> App
      (App (App (App (App (App (Var "sumElim") Type) Nat) Nat) (Lam "a" Zero))
           (Lam "b" Zero)
      )
      (SumL Type)
    "[Zero, Zero]" ~> LCons Zero (LCons Zero LNil)
    "T" ~> T
    "Void" ~> Void
    "Unit" ~> Unit
    "I Nat Zero Zero" ~> Equal Nat Zero Zero
    "Refl Zero" ~> Refl Zero
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~> EqElim
      Nat
      (Lam "x" (Lam "y" (Lam "eq" Nat)))
      (Lam "x" Zero)
      Zero
      Zero
      (Refl Zero)
    "eqElim T T T T T T T" ~> App (EqElim T T T T T T) T
    "W a b" ~> W (Var "a") (Var "b")
    "sup a b" ~> Sup (Var "a") (Var "b")
    "absurd Nat" ~> Absurd Nat
    "Fin Zero" ~> Fin Zero
    "FZero Zero" ~> FZero Zero
    "FSuc (FZero Zero)" ~> FSuc (FZero Zero)

  describe "Inference" $ do
    "Type" ~~ Type
    "(\\t. t) : forall (t : Type). Type" ~~ Pi "t" Type Type
    -- id
    "(\\t x. x) : forall (t : Type) (x : t). t"
      ~~ Pi "t" Type (Pi "x" (Var "t") (Var "t"))
    -- const
    "(\\t1 x t2 y. x) : forall (t1 : Type) (x : t1) (t2 : Type) (y : t2). t1"
      ~~ Pi "t1"
            Type
            (Pi "x" (Var "t1") (Pi "t2" Type (Pi "y" (Var "t2") (Var "t1"))))
    -- (Type -> Type) Type
    "((\\t. t) : forall (t : Type). Type) Type" ~~ Type
    -- id Type Type
    "((\\t x. x) : forall (t : Type) (x : t). t) Type Type" ~~ Type

    -- function application
    "(\\a b f x. f x) : forall (a : Type) (b : Type) (f : forall (x : a). b) (x : a). b"
      ~~ Pi
           "a"
           Type
           (Pi
             "b"
             Type
             (Pi "f" (Pi "x" (Var "a") (Var "b")) (Pi "x" (Var "a") (Var "b")))
           )

    -- S combinator specialised to a single type
    "(\\a x y z. x z (y z)) : forall (a : Type) (x : forall (z : a) (yz : a). a) (y : forall (z : a). a) (z : a). a"
      ~~ Pi
           "a"
           Type
           (Pi
             "x"
             (Pi "z" (Var "a") (Pi "yz" (Var "a") (Var "a")))
             (Pi "y" (Pi "z" (Var "a") (Var "a")) (Pi "z" (Var "a") (Var "a")))
           )

    -- S combinator generalised over several types
    "(\\a b c x y z. x z (y z)) : forall (a : Type) (b : Type) (c : Type) (x : forall (z : a) (yz : b). c) (y : forall (z : a). b) (z : a). c"
      ~~ Pi
           "a"
           Type
           (Pi
             "b"
             Type
             (Pi
               "c"
               Type
               (Pi
                 "x"
                 (Pi "z" (Var "a") (Pi "yz" (Var "b") (Var "c")))
                 (Pi "y"
                     (Pi "z" (Var "a") (Var "b"))
                     (Pi "z" (Var "a") (Var "c"))
                 )
               )
             )
           )

    -- Nats
    "Nat" ~~ Type
    "Zero" ~~ Nat
    "Suc Zero" ~~ Nat
    "natElim ((\\n. Nat) : forall (n : Nat). Type) Zero ((\\k n. n) : forall (k : Nat) (n : Nat). Nat) (Suc Zero)"
      ~~ Nat
    "natElim ((\\n. Nat) : forall (n : Nat). Type) (Suc Zero) ((\\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) (Suc (Suc Zero))"
      ~~ Nat

    -- Product
    "Type*Type" ~~ Type
    "Nat*Nat" ~~ Type
    "Zero*Zero" ~~ Prod Nat Nat
    "Zero*Type" ~~ Prod Nat Type
    "Zero*(Zero*Zero)" ~~ Prod Nat (Prod Nat Nat)
    "prodElim Nat Nat Nat ((\\a b. a) : forall (a : Nat) (b : Nat). Nat) (Zero*Zero)"
      ~~ Nat
    "prodElim Nat Type Type ((\\a b. b) : forall (a : Nat) (b : Type). Type) (Zero*Nat)"
      ~~ Type
    -- uncurry
    "(\\a b c f p. prodElim a b c f p) : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c"
      ~~ Pi
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
    -- fst
    "(\\a b p. prodElim a b a ((\\x y. x) : forall (x : a) (y : b). a) p) : forall (a : Type) (b : Type) (p : a*b). a"
      ~~ Pi "a" Type (Pi "b" Type (Pi "p" (Prod (Var "a") (Var "b")) (Var "a")))
    -- snd
    "(\\a b p. prodElim a b b ((\\x y. y) : forall (x : a) (y : b). b) p) : forall (a : Type) (b : Type) (p : a*b). b"
      ~~ Pi "a" Type (Pi "b" Type (Pi "p" (Prod (Var "a") (Var "b")) (Var "b")))

    -- Sum
    "(Nat|Type)" ~~ Type
    "(Nat|(Nat*Nat))" ~~ Type
    "(Left Zero) : (Nat|Type)" ~~ Sum Nat Type
    "sumElim Nat Nat Nat (\\x. Zero) (\\x. Zero) (Left Zero))" ~~ Nat

    -- List
    "List Nat" ~~ Type
    "[Zero, Zero]" ~~ List Nat
    "[] : List Nat" ~~ List Nat
    "[[Zero, Zero]]" ~~ List (List Nat)
    "listElim Nat ((\\l. Nat) : forall (l : List Nat). Type) [Zero, Zero] Zero ((\\x xs acc. Suc acc) : forall (x : Nat) (xs : List Nat) (acc : Nat). Nat)"
      ~~ Nat

    -- Unit and Bottom
    "T" ~~ Type
    "Void" ~~ Type
    "Unit" ~~ T

    -- Equality
    "I Nat Zero Zero" ~~ Type
    "Refl Zero" ~~ Equal Nat Zero Zero
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~~ Nat

    -- W
    "W T (\\x. T)" ~~ Type
    "sup Unit ((\\x. absurd (W T (\\x. Void))) : forall (x : Void). W T (\\x. Void))"
      ~~ W T (Lam "x" Void)

    -- Fin
    "Fin Zero" ~~ Type
    "FZero Zero" ~~ Fin (Suc Zero)
    "FSuc (FZero Zero)" ~~ Fin (Suc (Suc Zero))
    "FZero (Suc Zero)" ~~ Fin (Suc (Suc Zero))
    "FZero (Suc Zero)" ~~ Fin (Suc (Suc Zero))
    "finElim (\\a b. Nat) (\\a. Zero) (\\a b rec. Suc rec) (Suc Zero) (FZero Zero)"
      ~~ Nat

    -- Rejections
    -- unannotated lambdas are forbidden
    illTyped "\\x. x"
    -- function types must end with a type, not a value (I think)
    illTyped "\\x. x : forall (x : Type). x"
    -- const that returns the wrong argument
    illTyped "(\\a x b y. y) : forall (a : Type) (x : a) (b : Type) (y : b). a"
    illTyped "(\\a b. a) : forall (a : Type). Type"
    -- function application that applies x to f instead of f to x
    illTyped
      "(\\a b f x. x f) : forall (a : Type) (b : Type) (f : forall (x : a). b) (x : a). b"
    illTyped
      "prodElim ((\\a b. a) : forall (a : Nat) (b : Nat). Nat) (Zero*Nat)"
    illTyped
      "prodElim ((\\a b. b) : forall (a : Nat) (b : Type). Nat) (Zero*Nat)"
    -- projection functions should have matching return types
    illTyped "sumElim Nat Nat Nat (\\x. Type) (\\x. Zero) (Left Zero)"

  describe "Evaluation" $ do
    "((\\t x. x) : forall (t : Type) (x : t). t) Type Type" ~* "Type"
    "((\\a b x. x) : forall (a : Type) (b : Type) (x : b). b) Type Type Type"
      ~* "Type"
    "((\\a b f x. f x) : forall (a : Type) (b : Type) (f : forall (x : a). b) (x : a). b) Type Type ((\\x. x) : forall (x : Type). Type) Type"
      ~* "Type"
    "((\\a b c x y z. x z (y z)) : forall (a : Type) (b : Type) (c : Type) (x : forall (z : a) (yz : b). c) (y : forall (z : a). b) (z : a). c) Type Type Type ((\\x. \\yz. Type) : forall (x : Type) (yz : Type). Type) ((\\z. z) : forall (z : Type). Type) Type"
      ~* "Type"
    "Nat" ~* "Nat"
    "Zero" ~* "Zero"
    "Suc Zero" ~* "Suc Zero"
    -- const Zero
    "natElim ((\\n. Nat) : forall (n : Nat). Type) Zero ((\\k n. n) : forall (k : Nat) (n : Nat). Nat) (Suc Zero)"
      ~* "Zero"
    -- Nat increment
    "natElim ((\\n. Nat) : forall (n : Nat). Type) (Suc Zero) ((\\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) (Suc (Suc Zero))"
      ~* "Suc (Suc (Suc Zero))"
    "prodElim Nat Nat Nat ((\\a b. a) : forall (a : Nat) (b : Nat). Nat) (Zero*Zero)"
      ~* "Zero"
    "prodElim Nat Type Type ((\\a b. b) : forall (a : Nat) (b : Type). Type) (Zero*Nat)"
      ~* "Nat"
    -- uncurry const Zero (Suc Zero) (== fst (Zero, Suc Zero))
    "((\\a b c f p. prodElim a b c f p) : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c) Nat Nat Nat ((\\x y. x) : forall (x : Nat) (y : Nat). Nat) (Zero*(Suc Zero))"
      ~* "Zero"
    "sumElim Nat Nat Nat ((\\x. Zero) : forall (x : Nat). Nat) ((\\x. Zero) : forall (x : Nat). Nat) ((Left Zero) : (Nat|Nat))"
      ~* "Zero"
    -- list length
    "listElim Nat ((\\l. Nat) : forall (l : List Nat). Type) [Zero, Zero] Zero ((\\x xs acc. Suc acc) : forall (x : Nat) (xs : List Nat) (acc : Nat). Nat)"
      ~* "Suc (Suc Zero)"
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~* "Zero"
    "finElim (\\a b. Nat) (\\a. Zero) (\\a b rec. Suc rec) (Suc Zero) (FZero Zero)"
      ~* "Zero"

-- Expect parse
(~>) :: String -> Expr -> Spec
(~>) input expected =
  it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

-- Expect parse & infer
(~~) :: String -> Expr -> Spec
(~~) input expected = it ("infers " ++ input) $ do
  let pe = parse expr "" input
  pe `shouldSatisfy` isRight
  let Right e = pe
  runInfer prelude e `shouldBe` Right expected

-- Expect parse, infer and reject
illTyped :: String -> Spec
illTyped input = it ("rejects " ++ input) $ do
  let Right e = parse expr "" input
  isLeft (runInfer prelude e) `shouldBe` True

-- Expect parse, infer & eval
(~*) :: String -> String -> Spec
(~*) input expected = it (input ++ " evaluates to " ++ expected) $ do
  let parsedInput    = parseExpr input
  let parsedExpected = parseExpr expected
  parsedInput `shouldSatisfy` isRight
  parsedExpected `shouldSatisfy` isRight
  (parsedInput >>= runInfer prelude) `shouldSatisfy` isRight
  (evalExpr preludeVals <$> parsedInput) `shouldBe` parsedExpected

parseExpr :: String -> Either String Expr
parseExpr input = mapLeft errorBundlePretty $ parse expr "" input

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left  e) = Left (f e)
mapLeft _ (Right x) = Right x

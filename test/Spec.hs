import           Prelude                 hiding ( pi
                                                , sum
                                                )

import           Test.Hspec
import           Test.Hspec.Megaparsec

import           Text.Megaparsec                ( parse
                                                , errorBundlePretty
                                                )

import           Data.Either                    ( isLeft
                                                , isRight
                                                )

import           Expr
import           Parse
import           Infer
import           Eval                           ( evalExpr )

main :: IO ()
main = hspec $ do
  describe "Parsing" $ do
    "x" ~> var "x"
    "Type" ~> type_
    "\\x. x" ~> lam "x" (var "x")
    "forall (x : Type). x" ~> pi "x" type_ (var "x")
    "(\\x. x) y" ~> app (lam "x" (var "x")) (var "y")
    "(\\x y. x) z" ~> app (lam "x" (lam "y" (var "x"))) (var "z")
    "x : Type" ~> ann (var "x") type_
    "((\\x. x) : forall (x : Type). Type) Type"
      ~> app (ann (lam "x" (var "x")) (pi "x" type_ type_)) type_
    "forall (x : Type) (y : Type). x" ~> pi "x" type_ (pi "y" type_ (var "x"))
    "Nat" ~> nat
    "Zero" ~> zero
    "Suc Zero" ~> suc zero
    "natElim m mz ms k" ~> natElim (var "m") (var "mz") (var "ms") (var "k")
    "Nat*Nat" ~> prod nat nat
    "Zero*(Suc Zero)" ~> prod zero (suc zero)
    "prodElim (\\a b. a) (Zero*Zero)"
      ~> prodElim (lam "a" (lam "b" (var "a"))) (prod zero zero)
    "Nat|Nat" ~> sum nat nat
    "Nat|(Nat|Type)" ~> sum nat (sum nat type_)
    "Nat|(Nat*Type)" ~> sum nat (prod nat type_)
    "Left Zero" ~> suml zero
    "sumElim (\\a. Zero) (\\b. Zero) (Left Type)"
      ~> sumElim (lam "a" zero) (lam "b" zero) (suml type_)
    "[Zero, Zero]" ~> lcons zero (lcons zero lnil)
    "T" ~> tt
    "Void" ~> void
    "Unit" ~> unit
    "I Nat Zero Zero" ~> equal nat zero zero
    "Refl Zero" ~> refl zero
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~> eqElim
      nat
      (lam "x" (lam "y" (lam "eq" nat)))
      (lam "x" zero)
      zero
      zero
      (refl zero)
    "eqElim T T T T T T T" ~> app (eqElim tt tt tt tt tt tt) tt
    "W a b" ~> w (var "a") (var "b")
    "sup a b" ~> sup (var "a") (var "b")
    "absurd Nat" ~> absurd nat

  describe "Inference" $ do
    "Type" ~~ type_
    "(\\t. t) : forall (t : Type). Type" ~~ pi "t" type_ type_
    -- id
    "(\\t x. x) : forall (t : Type) (x : t). t"
      ~~ pi "t" type_ (pi "x" (var "t") (var "t"))
    -- const
    "(\\t1 x t2 y. x) : forall (t1 : Type) (x : t1) (t2 : Type) (y : t2). t1"
      ~~ pi "t1"
            type_
            (pi "x" (var "t1") (pi "t2" type_ (pi "y" (var "t2") (var "t1"))))
    -- (Type -> Type) Type
    "((\\t. t) : forall (t : Type). Type) Type" ~~ type_
    -- id Type Type
    "((\\t x. x) : forall (t : Type) (x : t). t) Type Type" ~~ type_

    -- function application
    "(\\a b f x. f x) : forall (a : Type) (b : Type) (f : forall (x : a). b) (x : a). b"
      ~~ pi
           "a"
           type_
           (pi
             "b"
             type_
             (pi "f" (pi "x" (var "a") (var "b")) (pi "x" (var "a") (var "b")))
           )

    -- S combinator specialised to a single type
    "(\\a x y z. x z (y z)) : forall (a : Type) (x : forall (z : a) (yz : a). a) (y : forall (z : a). a) (z : a). a"
      ~~ pi
           "a"
           type_
           (pi
             "x"
             (pi "z" (var "a") (pi "yz" (var "a") (var "a")))
             (pi "y" (pi "z" (var "a") (var "a")) (pi "z" (var "a") (var "a")))
           )

    -- S combinator generalised over several types
    "(\\a b c x y z. x z (y z)) : forall (a : Type) (b : Type) (c : Type) (x : forall (z : a) (yz : b). c) (y : forall (z : a). b) (z : a). c"
      ~~ pi
           "a"
           type_
           (pi
             "b"
             type_
             (pi
               "c"
               type_
               (pi
                 "x"
                 (pi "z" (var "a") (pi "yz" (var "b") (var "c")))
                 (pi "y"
                     (pi "z" (var "a") (var "b"))
                     (pi "z" (var "a") (var "c"))
                 )
               )
             )
           )

    -- Nats
    "Nat" ~~ type_
    "Zero" ~~ nat
    "Suc Zero" ~~ nat
    "natElim ((\\n. Nat) : forall (n : Nat). Type) Zero ((\\k n. n) : forall (k : Nat) (n : Nat). Nat) (Suc Zero)"
      ~~ nat
    "natElim ((\\n. Nat) : forall (n : Nat). Type) (Suc Zero) ((\\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) (Suc (Suc Zero))"
      ~~ nat

    -- Product
    "Type*Type" ~~ type_
    "Nat*Nat" ~~ type_
    "Zero*Zero" ~~ prod nat nat
    "Zero*Type" ~~ prod nat type_
    "Zero*(Zero*Zero)" ~~ prod nat (prod nat nat)
    "prodElim ((\\a b. a) : forall (a : Nat) (b : Nat). Nat) (Zero*Zero)" ~~ nat
    "prodElim ((\\a b. b) : forall (a : Nat) (b : Type). Type) (Zero*Nat)"
      ~~ type_
    -- uncurry
    "(\\a b c f p. prodElim f p) : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c"
      ~~ pi
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
    -- fst
    "(\\a b p. prodElim ((\\x y. x) : forall (x : a) (y : b). a) p) : forall (a : Type) (b : Type) (p : a*b). a"
      ~~ pi "a"
            type_
            (pi "b" type_ (pi "p" (prod (var "a") (var "b")) (var "a")))
    -- snd
    "(\\a b p. prodElim ((\\x y. y) : forall (x : a) (y : b). b) p) : forall (a : Type) (b : Type) (p : a*b). b"
      ~~ pi "a"
            type_
            (pi "b" type_ (pi "p" (prod (var "a") (var "b")) (var "b")))

    -- Sum
    "(Nat|Type)" ~~ type_
    "(Nat|(Nat*Nat))" ~~ type_
    "(Left Zero) : (Nat|Type)" ~~ sum nat type_
    "sumElim ((\\x. Zero) : forall (x : Nat). Nat) ((\\x. Zero) : forall (x : Nat). Nat) ((Left Zero) : (Nat|Nat))"
      ~~ nat

    -- List
    "List Nat" ~~ type_
    "[Zero, Zero]" ~~ list nat
    "[] : List Nat" ~~ list nat
    "[[Zero, Zero]]" ~~ list (list nat)
    "listElim ((\\l. Nat) : forall (l : List Nat). Type) [Zero, Zero] Zero ((\\x xs acc. Suc acc) : forall (x : Nat) (xs : List Nat) (acc : Nat). Nat)"
      ~~ nat

    -- Unit and Bottom
    "T" ~~ type_
    "Void" ~~ type_
    "Unit" ~~ tt

    -- Equality
    "I Nat Zero Zero" ~~ type_
    "Refl Zero" ~~ equal nat zero zero
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~~ nat

    -- W
    "W T (\\x. T)" ~~ type_
    "sup Unit ((\\x. absurd (W T (\\x. Void))) : forall (x : Void). W T (\\x. Void))"
      ~~ w tt (lam "x" void)

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
    illTyped
      "sumElim ((\\x. Type) : forall (x : Nat). Nat) ((\\x. Zero) : forall (x : Nat). Nat) ((Left Zero) : (Nat|Nat))"

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
    "prodElim ((\\a b. a) : forall (a : Nat) (b : Nat). Nat) (Zero*Zero)"
      ~* "Zero"
    "prodElim ((\\a b. b) : forall (a : Nat) (b : Type). Type) (Zero*Nat)"
      ~* "Nat"
    -- uncurry const Zero (Suc Zero) (== fst (Zero, Suc Zero))
    "((\\a b c f p. prodElim f p) : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c) Nat Nat Nat ((\\x y. x) : forall (x : Nat) (y : Nat). Nat) (Zero*(Suc Zero))"
      ~* "Zero"
    "sumElim ((\\x. Zero) : forall (x : Nat). Nat) ((\\x. Zero) : forall (x : Nat). Nat) ((Left Zero) : (Nat|Nat))"
      ~* "Zero"
    -- list length
    "listElim ((\\l. Nat) : forall (l : List Nat). Type) [Zero, Zero] Zero ((\\x xs acc. Suc acc) : forall (x : Nat) (xs : List Nat) (acc : Nat). Nat)"
      ~* "Suc (Suc Zero)"
    "eqElim Nat (\\x y eq. Nat) (\\x. Zero) Zero Zero (Refl Zero)" ~* "Zero"

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
  runInfer mempty e `shouldBe` Right expected

-- Expect parse, infer and reject
illTyped :: String -> Spec
illTyped input = it ("rejects " ++ input) $ do
  let Right e = parse expr "" input
  isLeft (runInfer mempty e) `shouldBe` True

-- Expect parse, infer & eval
(~*) :: String -> String -> Spec
(~*) input expected = it (input ++ " evaluates to " ++ expected) $ do
  let parsedInput    = parseExpr input
  let parsedExpected = parseExpr expected
  parsedInput `shouldSatisfy` isRight
  parsedExpected `shouldSatisfy` isRight
  (parsedInput >>= runInfer mempty) `shouldSatisfy` isRight
  (evalExpr mempty <$> parsedInput) `shouldBe` parsedExpected

parseExpr :: String -> Either String Expr
parseExpr input = mapLeft errorBundlePretty $ parse expr "" input

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left  e) = Left (f e)
mapLeft _ (Right x) = Right x

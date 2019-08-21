import           Prelude                 hiding ( pi )

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

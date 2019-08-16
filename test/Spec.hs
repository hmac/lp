import           Prelude                 hiding ( pi )

import           Test.Hspec
import           Test.Hspec.Megaparsec

import           Text.Megaparsec                ( parse )

import           Data.Functor.Foldable          ( Fix )
import           Data.Either                    ( isLeft )

import           Expr
import           Parse
import           Infer                   hiding ( nfc )
import           Eval

main :: IO ()
main = hspec $ do
  describe "Parsing" $ do
    "x" ~> var "x"
    "Type" ~> type_
    "\\x. x" ~> lam "x" (var "x")
    "forall (x : Type). x" ~> pi "x" type_ (var "x")
    "(\\x. x) y" ~> app (lam "x" (var "x")) (var "y")
    "x : Type" ~> ann (var "x") type_

  describe "Inference" $ do
    "Type" ~~ type_
    "(\\t. t) : forall (t : Type). Type" ~~ pi "t" type_ type_
    "(\\t. (\\x. x)) : forall (t : Type). forall (x : t). t"
      ~~ pi "t" type_ (pi "x" (var "t") (var "t"))
    -- const
    "(\\t1. \\x. \\t2. \\y. x) : forall (t1 : Type). forall (x : t1). forall (t2 : Type). forall (y : t2). t1"
      ~~ pi "t1"
            type_
            (pi "x" (var "t1") (pi "t2" type_ (pi "y" (var "t2") (var "t1"))))
    -- TODO: the expression below should not type check
    "(\\t1. \\x. \\t2. \\y. y) : forall (t1 : Type). forall (x : t1). forall (t2 : Type). forall (y : t2). t1"
      ~~ pi "t1"
            type_
            (pi "x" (var "t1") (pi "t2" type_ (pi "y" (var "t2") (var "t1"))))

    -- unannotated lambdas are forbidden
    illTyped "\\x. x"
    -- function types must end with a type, not a value (I think)
    illTyped "\\x. x : forall (x : Type). x"
    -- const that returns the wrong argument
    illTyped
      "(\\t1. \\x. \\t2. \\y. y) : forall (t1 : Type). forall (x : t1). forall (t2 : Type). forall (y : t2). t1"

  describe "Evaluation" $ do
    it "parses and evaluates basic expressions" $ do
      parse expr "" "(\\x. x) Type"
        `shouldParse` (app (lam "x" (var "x")) type_)
      let Right e = parse expr "" "(\\x. x) Type"
      pretty (nfc mempty (translate e)) `shouldBe` "Type"


-- Expect parse
(~>) :: String -> Expr -> Spec
(~>) input expected =
  it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

-- Expect parse & infer
(~~) :: String -> Expr -> Spec
(~~) input expected = it ("infers " ++ input) $ do
  let Right e = parse expr "" input
  runInfer mempty (translate e) `shouldBe` Right (translate expected)

-- Expect parse, infer and reject
illTyped :: String -> Spec
illTyped input = it ("infers " ++ input) $ do
  let Right e = parse expr "" input
  isLeft (runInfer mempty (translate e)) `shouldBe` True

-- Expect parse, infer & eval
-- (~*) input expected =
--   it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

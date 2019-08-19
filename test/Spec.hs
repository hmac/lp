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
import           Eval                           ( nfc )

main :: IO ()
main = hspec $ do
  describe "Parsing" $ do
    "x" ~> var "x"
    "Type" ~> type_
    "\\x. x" ~> lam "x" (var "x")
    "forall (x : Type). x" ~> pi "x" type_ (var "x")
    "(\\x. x) y" ~> app (lam "x" (var "x")) (var "y")
    "x : Type" ~> ann (var "x") type_
    "((\\x. x) : forall (x : Type). Type) Type"
      ~> app (ann (lam "x" (var "x")) (pi "x" type_ type_)) type_

  describe "Inference" $ do
    "Type" ~~ type_
    "(\\t. t) : forall (t : Type). Type" ~~ pi "t" type_ type_
    -- id
    "(\\t. (\\x. x)) : forall (t : Type). forall (x : t). t"
      ~~ pi "t" type_ (pi "x" (var "t") (var "t"))
    -- const
    "(\\t1. \\x. \\t2. \\y. x) : forall (t1 : Type). forall (x : t1). forall (t2 : Type). forall (y : t2). t1"
      ~~ pi "t1"
            type_
            (pi "x" (var "t1") (pi "t2" type_ (pi "y" (var "t2") (var "t1"))))
    -- broken const: should not type check
    "(\\t1. \\x. \\t2. \\y. y) : forall (t1 : Type). forall (x : t1). forall (t2 : Type). forall (y : t2). t1"
      ~~ pi "t1"
            type_
            (pi "x" (var "t1") (pi "t2" type_ (pi "y" (var "t2") (var "t1"))))
    -- (Type -> Type) Type
    "((\\t. t) : forall (t : Type). Type) Type" ~~ type_
    -- id Type Type
    "((\\t. \\x. x) : forall (t : Type). forall (x : t). t) Type Type" ~~ type_

    -- unannotated lambdas are forbidden
    illTyped "\\x. x"
    -- function types must end with a type, not a value (I think)
    illTyped "\\x. x : forall (x : Type). x"
    -- const that returns the wrong argument
    illTyped
      "(\\a. \\x. \\b. \\y. y) : forall (a : Type). forall (x : a). forall (b : Type). forall (y : b). a"
    illTyped "(\\a. \\b. a) : forall (a : Type). Type"

  describe "Evaluation" $ do
    "((\\t. \\x. x) : forall (t : Type). forall (x : t). t) Type Type" ~* "Type"


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
  runInfer mempty (translate e) `shouldBe` Right (translate expected)

-- Expect parse, infer and reject
illTyped :: String -> Spec
illTyped input = it ("rejects " ++ input) $ do
  let Right e = parse expr "" input
  isLeft (runInfer mempty (translate e)) `shouldBe` True

-- Expect parse, infer & eval
(~*) :: String -> String -> Spec
(~*) input expected = it (input ++ " evaluates to " ++ expected) $ do
  let parsedInput    = translate <$> parseExpr input
  let parsedExpected = translate <$> parseExpr expected
  parsedInput `shouldSatisfy` isRight
  parsedExpected `shouldSatisfy` isRight
  (parsedInput >>= runInfer mempty) `shouldSatisfy` isRight
  (nfc mempty <$> parsedInput) `shouldBe` parsedExpected

parseExpr :: String -> Either String Expr
parseExpr input = mapLeft errorBundlePretty $ parse expr "" input

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left  e) = Left (f e)
mapLeft _ (Right x) = Right x

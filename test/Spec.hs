import Prelude hiding (pi)

import Test.Hspec
import Test.Hspec.Megaparsec

import Text.Megaparsec (parse)

import Data.Functor.Foldable (Fix)

import Expr
import Parse
import Infer hiding (nfc)
import Eval

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
    "(\\t. (\\x. x)) : forall (t : Type). forall (x : t). t"
      ~~ pi "t" type_ (pi "x" (var "t") (var "t"))

  describe "Evaluation" $ do
    it "parses and evaluates basic expressions" $ do
      parse expr "" "(\\x. x) Type" `shouldParse` (app (lam "x" (var "x")) type_)
      let Right e = parse expr "" "(\\x. x) Type"
      pretty (nfc mempty (translate e)) `shouldBe` "Type"


-- Expect parse
(~>) input expected =
  it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

-- Expect parse & infer
(~~) input expected =
  it ("infers " ++ input) $ do
    --parse expr "" input `shouldParse` expected
    --let Right e = parse expr "" input
    True `shouldBe` True -- TODO once we can infer BExpr

-- Expect parse, infer & eval
-- (~*) input expected =
--   it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

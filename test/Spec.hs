import Prelude hiding (pi)

import Test.Hspec
import Test.Hspec.Megaparsec

import Text.Megaparsec (parse)

import Expr
import Parse

main :: IO ()
main = hspec $ do
  describe "Parsing" $ do
    "x" ~> var "x"
    "Type" ~> type_
    "\\x. x" ~> lam "x" (var "x")
    "forall (x : Type). x" ~> pi "x" type_ (var "x")
    "(\\x. x) y" ~> app (lam "x" (var "x")) (var "y")

(~>) input expected = it ("parses " ++ input) $ parse expr "" input `shouldParse` expected

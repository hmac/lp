module Parse where

import Prelude hiding (pi)
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char

import Expr

type Parser = Parsec Void String

runParse :: String -> Either String Expr
runParse input = case parse expr "" input of
                   Left e -> Left (errorBundlePretty e)
                   Right e -> Right e

-- TODO: space consumer

expr :: Parser Expr
expr = try annotation <|> application <|> aexpr

application :: Parser Expr
application = foldl1 app <$> (aexpr `sepBy` string " ")

aexpr :: Parser Expr
aexpr = ptype <|> lambda <|> forall <|> parens expr <|> pvar

annotation :: Parser Expr
annotation = do
  e <- aexpr
  _ <- string " : " -- space consumer
  ann e <$> aexpr

ptype :: Parser Expr
ptype = string "Type" >> pure type_

lambda :: Parser Expr
lambda = do
  _ <- string "\\"
  x <- termName
  _ <- string ". " -- space consumer
  e <- expr
  pure $ lam x e

forall :: Parser Expr
forall = do
  _ <- string "forall "
  (x, t) <- parens $ do
    name <- termName
    _ <- string " : " -- space consumer
    ttype <- expr
    pure (name, ttype)
  _ <- string ". " -- space consumer
  e <- expr
  pure $ pi x t e

pvar :: Parser Expr
pvar = var <$> termName

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

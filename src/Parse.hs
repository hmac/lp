module Parse where

import           Prelude                 hiding ( pi
                                                , product
                                                )
import           Data.Void

import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Expr

type Parser = Parsec Void String

runParse :: String -> Either String Expr
runParse input = case parse expr "" input of
  Left  e -> Left (errorBundlePretty e)
  Right e -> Right e

-- TODO: space consumer

expr :: Parser Expr
expr = try annotation <|> try product <|> application <|> aexpr

application :: Parser Expr
application = foldl1 app <$> (aexpr `sepBy` string " ")

aexpr :: Parser Expr
aexpr =
  ptype
    <|> lambda
    <|> forall
    <|> naturals
    <|> pProdElim
    <|> parens expr
    <|> pvar

annotation :: Parser Expr
annotation = do
  e <- aexpr
  _ <- string " : " -- space consumer
  ann e <$> aexpr

ptype :: Parser Expr
ptype = string "Type" >> pure type_

lambda :: Parser Expr
lambda = do
  _  <- string "\\"
  xs <- termName `sepBy1` string " "
  _  <- string ". " -- space consumer
  e  <- expr
  pure $ foldr lam e xs

forall :: Parser Expr
forall = do
  _    <- string "forall "
  vars <- forallVar `sepBy1` string " "
  _    <- string ". " -- space consumer
  e    <- expr
  pure $ foldr (\(x, t) ex -> pi x t ex) e vars

forallVar :: Parser (String, Expr)
forallVar = parens $ do
  name  <- termName
  _     <- string " : " -- space consumer
  ttype <- expr
  pure (name, ttype)

naturals :: Parser Expr
naturals = pNat <|> pZero <|> pSuc <|> pNatElim
 where
  pNat     = string "Nat" >> pure nat
  pZero    = string "Zero" >> pure zero
  pSuc     = string "Suc " >> suc <$> aexpr
  pNatElim = do
    _              <- string "natElim"
    [m, mz, ms, k] <- sequenceA $ replicate 4 (string " " >> aexpr)
    pure $ natElim m mz ms k

product :: Parser Expr
product = do
  a <- aexpr
  _ <- string "*"
  prod a <$> aexpr

pProdElim :: Parser Expr
pProdElim = do
  _ <- string "prodElim "
  f <- aexpr
  _ <- string " "
  prodElim f <$> aexpr

pvar :: Parser Expr
pvar = var <$> termName

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

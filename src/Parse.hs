module Parse where

import           Data.Void                      ( Void )

import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Expr

type Parser = Parsec Void String

data Definition = Def String Expr

runParse :: String -> Either String Expr
runParse input = case parse expr "" input of
  Left  e -> Left (errorBundlePretty e)
  Right e -> Right e

runParseDefs :: String -> Either String [Definition]
runParseDefs input = case parse program "" input of
  Left  e -> Left (errorBundlePretty e)
  Right e -> Right e
 where
  program = many comment >> some (definition <* many (comment <|> eol)) <* eof

definition :: Parser Definition
definition = do
  name    <- termName
  _       <- string " : "
  typeAnn <- expr
  _       <- string "\n"
  _       <- string (name ++ " = ")
  e       <- expr
  pure $ Def name (Ann e typeAnn)

comment :: Parser String
comment = string "--" >> many (noneOf ['\n']) >> eol

-- TODO: space consumer

expr :: Parser Expr
expr = try annotation <|> try infixOperator <|> application <|> aexpr

application :: Parser Expr
application = foldl1 App <$> (aexpr `sepBy` string " ")

aexpr :: Parser Expr
aexpr =
  ptype
    <|> lambda
    <|> forall
    <|> naturals
    <|> pSumIntro
    <|> top
    <|> bottom
    <|> pAbsurd
    <|> pUnit
    <|> pRefl
    <|> pEq
    <|> pEqElim
    <|> pW
    <|> pFin
    <|> lists
    <|> parens expr
    <|> pvar

annotation :: Parser Expr
annotation = do
  e <- aexpr
  _ <- string " : " -- space consumer
  Ann e <$> aexpr

ptype :: Parser Expr
ptype = string "Type" >> pure Type

lambda :: Parser Expr
lambda = do
  _  <- string "\\"
  xs <- termName `sepBy1` string " "
  _  <- string ". " -- space consumer
  e  <- expr
  pure $ foldr Lam e xs

forall :: Parser Expr
forall = do
  _    <- string "forall "
  vars <- forallVar `sepBy1` string " "
  _    <- string ". " -- space consumer
  e    <- expr
  pure $ foldr (\(x, t) ex -> Pi x t ex) e vars

forallVar :: Parser (String, Expr)
forallVar = parens $ do
  name  <- termName
  _     <- string " : " -- space consumer
  ttype <- expr
  pure (name, ttype)

naturals :: Parser Expr
naturals = pNat <|> pZero <|> pSuc
 where
  pNat  = string "Nat" >> pure Nat
  pZero = string "Zero" >> pure Zero
  pSuc  = string "Suc " >> Suc <$> aexpr

infixOperator :: Parser Expr
infixOperator = do
  a <- aexpr
  (string "*" >> Prod a <$> expr)
    <|> (string "|" >> Sum a <$> expr)
    <|> (string "::" >> LCons a <$> expr)

pSumIntro :: Parser Expr
pSumIntro =
  (string "Left " >> SumL <$> aexpr) <|> (string "Right " >> SumR <$> aexpr)

top :: Parser Expr
top = string "T" >> pure T

bottom :: Parser Expr
bottom = string "Void" >> pure Void

pAbsurd :: Parser Expr
pAbsurd = string "absurd " >> Absurd <$> aexpr

pUnit :: Parser Expr
pUnit = string "Unit" >> pure Unit

pRefl :: Parser Expr
pRefl = string "Refl " >> Refl <$> aexpr

pEq :: Parser Expr
pEq = do
  _         <- string "I"
  [t, a, b] <- sequenceA $ replicate 3 (string " " >> aexpr)
  pure $ Equal t a b

pEqElim :: Parser Expr
pEqElim = do
  _                    <- string "eqElim"
  [a, m, mr, x, y, eq] <- sequenceA $ replicate 6 (string " " >> aexpr)
  pure $ EqElim a m mr x y eq

pW :: Parser Expr
pW = do
  f      <- (string "W" >> pure W) <|> (string "sup" >> pure Sup)
  [a, b] <- sequenceA $ replicate 2 (string " " >> aexpr)
  pure $ f a b

pFin :: Parser Expr
pFin = pFinType <|> pFZero <|> pFSuc
 where
  pFinType = string "Fin " >> Fin <$> aexpr
  pFZero   = string "FZero " >> FZero <$> aexpr
  pFSuc    = string "FSuc " >> FSuc <$> aexpr

lists :: Parser Expr
lists = pListType <|> pListNil <|> pList

pListType :: Parser Expr
pListType = do
  _ <- string "List "
  List <$> aexpr

pListNil :: Parser Expr
pListNil = string "[]" >> pure LNil

pList :: Parser Expr
pList = brackets $ do
  elems <- expr `sepBy` string ", "
  pure $ foldr LCons LNil elems

pvar :: Parser Expr
pvar = Var <$> termName

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

brackets :: Parser p -> Parser p
brackets = between (string "[") (string "]")

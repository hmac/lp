module Parse where

import           Prelude                 hiding ( pi
                                                , product
                                                , sum
                                                )
import           Data.Void

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
  where program = some (definition <* many eol) <* eof

definition :: Parser Definition
definition = do
  name    <- termName
  _       <- string " : "
  typeAnn <- expr
  _       <- string "\n"
  _       <- string (name ++ " = ")
  e       <- expr
  pure $ Def name (ann e typeAnn)

-- TODO: space consumer

expr :: Parser Expr
expr = try annotation <|> try productOrSum <|> application <|> aexpr

application :: Parser Expr
application = foldl1 app <$> (aexpr `sepBy` string " ")

aexpr :: Parser Expr
aexpr =
  ptype
    <|> lambda
    <|> forall
    <|> naturals
    <|> pProdElim
    <|> pSumIntro
    <|> pSumElim
    <|> pListType
    <|> pListNil
    <|> pList
    <|> pListElim
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

productOrSum :: Parser Expr
productOrSum = do
  a <- aexpr
  (string "*" >> prod a <$> expr) <|> (string "|" >> sum a <$> expr)

pProdElim :: Parser Expr
pProdElim = do
  _ <- string "prodElim "
  f <- aexpr
  _ <- string " "
  prodElim f <$> aexpr

pSumIntro :: Parser Expr
pSumIntro =
  (string "Left " >> suml <$> aexpr) <|> (string "Right " >> sumr <$> aexpr)

pSumElim :: Parser Expr
pSumElim = do
  _ <- string "sumElim "
  f <- aexpr
  _ <- string " "
  g <- aexpr
  _ <- string " "
  sumElim f g <$> aexpr

pListType :: Parser Expr
pListType = do
  _ <- string "List "
  list <$> aexpr

pListNil :: Parser Expr
pListNil = string "[]" >> pure lnil

pList :: Parser Expr
pList = brackets $ do
  elems <- expr `sepBy` string ", "
  pure $ foldr lcons lnil elems

pListElim :: Parser Expr
pListElim = do
  _            <- string "listElim"
  [m, l, s, f] <- sequenceA $ replicate 4 (string " " >> aexpr)
  pure $ listElim m l s f

pvar :: Parser Expr
pvar = var <$> termName

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

brackets :: Parser p -> Parser p
brackets = between (string "[") (string "]")

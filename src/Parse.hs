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
    <|> bottom
    <|> pAbsurd
    <|> pUnit
    <|> pRefl
    <|> pEq
    <|> pEqElim
    <|> pW
    <|> pFin
    <|> lists
    <|> bools
    <|> top
    <|> parens expr
    <|> pvar

annotation :: Parser Expr
annotation = do
  e <- aexpr
  _ <- string " : " -- space consumer
  Ann e <$> aexpr

ptype :: Parser Expr
ptype = Type <$ string "Type"

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
  pNat  = Nat <$ string "Nat"
  pZero = Zero <$ string "Zero"
  pSuc  = Suc <$ string "Suc " <*> aexpr

infixOperator :: Parser Expr
infixOperator = do
  a <- aexpr
  (string "*" >> Prod a <$> expr)
    <|> (string "|" >> Sum a <$> expr)
    <|> (string "::" >> LCons a <$> expr)

pSumIntro :: Parser Expr
pSumIntro =
  (SumL <$ string "Left " <*> aexpr) <|> (SumR <$ string "Right " <*> aexpr)

top :: Parser Expr
top = T <$ string "T"

bottom :: Parser Expr
bottom = Void <$ string "Void"

pAbsurd :: Parser Expr
pAbsurd = do
  _      <- string "absurd"
  [t, e] <- aexprs 2
  pure $ Absurd t e

pUnit :: Parser Expr
pUnit = Unit <$ string "Unit"

pRefl :: Parser Expr
pRefl = Refl <$ string "Refl " <*> aexpr

pEq :: Parser Expr
pEq = do
  _         <- string "I"
  [t, a, b] <- aexprs 3
  pure $ Equal t a b

pEqElim :: Parser Expr
pEqElim = do
  _                    <- string "eqElim"
  [a, m, mr, x, y, eq] <- aexprs 6
  pure $ EqElim a m mr x y eq

pW :: Parser Expr
pW = w <|> sup <|> rec
 where
  w = do
    _      <- string "W"
    [a, b] <- aexprs 2
    pure $ W a b
  sup = do
    _      <- string "sup"
    [a, b] <- aexprs 2
    pure $ Sup a b
  rec = do
    _          <- string "Rec"
    [m, w_, r] <- aexprs 3
    pure $ Rec m w_ r

pFin :: Parser Expr
pFin = pFinType <|> pFZero <|> pFSuc
 where
  pFinType = Fin <$ string "Fin " <*> aexpr
  pFZero   = FZero <$ string "FZero " <*> aexpr
  pFSuc    = FSuc <$ string "FSuc " <*> aexpr

lists :: Parser Expr
lists = pListType <|> pListNil <|> pList
 where
  pListType = do
    _ <- string "List "
    List <$> aexpr

  pListNil = LNil <$ string "[]"

  pList    = brackets $ do
    elems <- expr `sepBy` string ", "
    pure $ foldr LCons LNil elems

bools :: Parser Expr
bools = true <|> false <|> bool
 where
  true  = string "True" >> pure BTrue
  false = BFalse <$ string "False" -- does this do the right thing?
  bool  = Boolean <$ string "Bool"

pvar :: Parser Expr
pvar = Var <$> termName

aexprs :: Int -> Parser [Expr]
aexprs i = sequenceA $ replicate i (string " " >> aexpr)

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

brackets :: Parser p -> Parser p
brackets = between (string "[") (string "]")

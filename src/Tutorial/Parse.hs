module Tutorial.Parse where

import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Data.Void
import           Data.List                      ( elemIndex )

import           Tutorial.Expr
import           Data.Text.Prettyprint.Doc      ( pretty
                                                , (<+>)
                                                , Pretty
                                                )
import qualified Data.Text.Prettyprint.Doc     as Print
                                                ( parens )

type Parser = Parsec Void String

data Expr = Anno Expr Expr
          | Type
          | Forall String Expr Expr
          | Lambda String Expr
          | Var String
          | App Expr Expr
          deriving (Show)

instance Pretty Expr where
  pretty Type       = pretty "*"
  pretty (Anno e t) = pretty e <+> pretty ":" <+> pretty t
  pretty (Forall s t e) =
    pretty "forall"
      <+> Print.parens (pretty s <+> pretty ":" <+> pretty t)
      <>  pretty "."
      <+> pretty e
  pretty (Lambda s e) = pretty "\\" <> pretty s <> pretty "." <+> pretty e
  pretty (Var s     ) = pretty s
  pretty (App a b   ) = pretty a <+> pretty b

runParse :: String -> Either String Expr
runParse input = case parse expr "" input of
  Left  e -> Left (errorBundlePretty e)
  Right e -> Right e

expr :: Parser Expr
expr = try annotation <|> application <|> aexpr

application :: Parser Expr
application = foldl1 App <$> (aexpr `sepBy` string " ")

aexpr :: Parser Expr
aexpr = star <|> lambda <|> forall <|> parens expr <|> pvar

annotation :: Parser Expr
annotation = do
  e <- aexpr
  _ <- string " : " -- space consumer
  Anno e <$> aexpr

star :: Parser Expr
star = string "*" >> pure Type

lambda :: Parser Expr
lambda = do
  _ <- string "\\"
  x <- termName
  _ <- string ". " -- space consumer
  e <- expr
  pure $ Lambda x e

forall :: Parser Expr
forall = do
  _      <- string "forall "
  (x, t) <- parens $ do
    name  <- termName
    _     <- string " : " -- space consumer
    ttype <- expr
    pure (name, ttype)
  _ <- string ". " -- space consumer
  e <- expr
  pure $ Forall x t e

pvar :: Parser Expr
pvar = Var <$> termName

termName :: Parser String
termName = some alphaNumChar

parens :: Parser p -> Parser p
parens = between (string "(") (string ")")

convert :: Expr -> Either String TermI
convert e = convertI e []

convertI :: Expr -> [String] -> Either String TermI
convertI Type           ctx = pure Star
convertI (Anno e t    ) ctx = Ann <$> convertC e ctx <*> convertC t ctx
convertI (Forall x t e) ctx = do
  t' <- convertC t ctx
  Pi t' <$> convertC e (x : ctx)
convertI (Var v) ctx = case elemIndex v ctx of
  Just i  -> pure $ Bound i
  Nothing -> pure $ Free (Global v)
convertI (App    a b) ctx = (:@:) <$> convertI a ctx <*> convertC b ctx
convertI (Lambda x e) ctx = Left "Lambda cannot be converted into a TermI"

convertC :: Expr -> [String] -> Either String TermC
convertC (Lambda x e) ctx = Lam <$> convertC e (x : ctx)
convertC e            ctx = Inf <$> convertI e ctx

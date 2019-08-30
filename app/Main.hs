{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Expr
import           Expr.Pretty                    ( Document
                                                , prettyExpr
                                                )
import           Expr.Prelude
import           Infer                          ( runInfer
                                                , runInferDebug
                                                , Debug(..)
                                                , Error(..)
                                                , ErrorDetail(..)
                                                )
import           Parse                          ( runParseDefs
                                                , Definition(..)
                                                )
import           Eval                           ( evalExpr )

import           System.Environment             ( getArgs )
import           System.IO                      ( stdout )
import           Data.Foldable                  ( foldlM )
import           Data.List                      ( find
                                                , intersperse
                                                )

import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal

import           Options.Applicative

data Mode = Parse | Typecheck | Eval
data Config = Config Mode String

parseConfig :: Parser Config
parseConfig =
  Config
    <$> flag Eval Typecheck (long "typecheck" <> help "Only typecheck")
    <*> argument str (metavar "FILE")

-- Given a file path, parse it as a series of definitions, construct a context,
-- typecheck everything and evaluate the 'main' function
main :: IO ()
main = do
  Config mode file <- execParser (info parseConfig mempty)
  input            <- readFile file
  case mode of
    Parse -> case parse input of
      Left  err  -> putStrLn $ "Parse error:\n\n" ++ err
      Right defs -> mapM_
        (\(Def n e) -> do
          putStr $ n ++ " = "
          renderIO stdout $ layout $ prettyExpr e
          putStrLn ""
        )
        defs
    Typecheck -> case parse input of
      Left  err  -> putStrLn $ "Parse error:\n\n" ++ err
      Right prog -> case typecheck prog of
        Left  err -> renderIO stdout $ layout $ prettyError err
        Right _   -> putStrLn "Typechecked successfully."
    Eval -> case parse input of
      Left  err  -> putStrLn $ "Parse error:\n\n" ++ err
      Right prog -> case typecheck prog of
        Left  err            -> renderIO stdout $ layout $ prettyError err
        Right (_types, vals) -> case eval vals of
          Left  err    -> putStrLn $ "Eval error:\n\n" ++ err
          Right result -> do
            renderIO stdout $ layout $ prettyExpr result
            putStrLn ""

parse :: String -> Either String [Definition]
parse = runParseDefs

-- Type check each definition in turn, accumulating a context of types as we go
typecheck :: [Definition] -> Either Error ([(String, Expr)], [(String, Expr)])
typecheck = foldlM f (preludeTypes, preludeVals)
 where
  f (types, vals) (Def name e) = do
    inferredType <- runInfer (types, vals) e
    pure ((name, inferredType) : types, (name, e) : vals)

-- Evaluate the first expression in the list with the others as context
-- TODO: find 'main' and run that, even if it's not first in the list
eval :: Context -> Either String Expr
eval vals = case lookup "main" vals of
  Just m ->
    let ctx = delete "main" vals ++ preludeVals in pure $ evalExpr ctx m
  Nothing -> Left "'main' not found"

delete :: Eq a => a -> [(a, b)] -> [(a, b)]
delete _ [] = []
delete n ((x, y) : xs) | x == n    = delete n xs
                       | otherwise = (x, y) : delete n xs

prettyError :: Error -> Document
prettyError Error { detail = detail, environment = (types, _), stack = s } =
  let relevantBindings =
          map (\(name, e) -> pretty name <> ":" <+> prettyExpr e) types
  in  vsep
        $  [prettyErrorDetail detail, line, "relevant bindings:", line]
        ++ take 5 relevantBindings
        ++ [line, "stack:", line]
        ++ map prettyExpr s
        ++ [line]

prettyErrorDetail :: ErrorDetail -> Document
prettyErrorDetail (Other e) = pretty e
prettyErrorDetail TypeMismatch { subject = s, expected = e, inferred = i } =
  vsep
    [ "Expected"
    , line
    , prettyExpr s
    , line
    , "to have type"
    , line
    , prettyExpr e
    , line
    , "but inferred it to have type"
    , line
    , prettyExpr i
    ]
prettyErrorDetail (CannotInfer e) =
  vsep ["Cannot determine the type of", line, prettyExpr e]
prettyErrorDetail (UnknownVar v) = vsep ["Unknown variable", line, pretty v]

layout :: Doc ann -> SimpleDocStream ann
layout = layoutSmart defaultLayoutOptions
 where
  opts = defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }

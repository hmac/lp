module Main where

import           Expr
import           Expr.Pretty                    ( )
import           Expr.Prelude
import           Infer                          ( runInfer
                                                , Debug(..)
                                                )
import           Parse                          ( runParse
                                                , runParseDefs
                                                , Definition(..)
                                                )
import           Eval                           ( evalExpr )
import           Pretty                         ( pp )

import           System.Environment             ( getArgs )
import           Data.Foldable                  ( foldlM )

-- Given a file path, parse it as a series of definitions, construct a context,
-- typecheck everything and evaluate the 'main' function
main :: IO ()
main = do
  [path] <- getArgs
  input  <- readFile path
  case go input of
    Left  err    -> putStrLn err
    Right result -> putStrLn (pp result)
 where
  go input = do
    prog           <- parse input
    (_types, vals) <- typecheck prog
    eval vals

parse :: String -> Either String [Definition]
parse = runParseDefs

-- Type check each definition in turn, accumulating a context of types as we go
typecheck :: [Definition] -> Either String ([(String, Expr)], [(String, Expr)])
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

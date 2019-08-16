module Main where

import           Tutorial.Expr
import           Tutorial.Quote                 ( quote0 )
import           Tutorial.Parse                 ( runParse
                                                , convert
                                                , Expr
                                                )
import           Tutorial.Infer                 ( typeI0
                                                , Type
                                                , Context
                                                )
import           Tutorial.Eval                  ( evalI )
import           Data.Text.Prettyprint.Doc      ( pretty
                                                , Pretty
                                                )

main :: IO ()
main = go []
 where
  go env = do
    input <- getLine
    let result = run input env
    print result
    go (environment result) -- TODO: parse 'assume/let' commands that add things to the environment


run :: String -> Context -> Result
run input env =
  let simpleAST    = runParse input
      term         = simpleAST >>= convert
      inferredType = term >>= typeI0 []
      evaluated    = flip evalI [] <$> term
  in  R { simple      = simpleAST
        , parsed      = term
        , inferred    = inferredType
        , evaluated   = evaluated
        , environment = env
        }

data Result = R { simple :: Either String Expr
                , parsed :: Either String TermI
                , inferred :: Either String Type
                , evaluated :: Either String Value
                , environment :: Context
                }

instance Show Result where
  show R { simple = s, parsed = p, inferred = i, evaluated = e } =
    "R {\n"
      <> ("\tsimple = " <> printEither s <> "\n")
      <> ("\tparsed = " <> printEither p <> "\n")
      <> ("\tinferred = " <> printEither (quote0 <$> i) <> "\n")
      <> ("\tevaluated = " <> printEither (quote0 <$> e) <> "\n")
      <> "}"
   where
    printEither :: Pretty a => Either String a -> String
    printEither (Left  err) = err
    printEither (Right a  ) = show (pretty a)

forever :: Monad m => m a -> m a
forever f = f >> forever f

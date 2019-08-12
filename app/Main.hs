module Main where

import           Tutorial.Expr
import           Tutorial.Quote                 ( quote0 )
import           Tutorial.Parse                 ( runParse
                                                , convert
                                                , Expr
                                                )
import           Tutorial.Infer                 ( typeI0
                                                , Type
                                                )
import           Tutorial.Eval                  ( evalI )

main :: IO ()
main = go []
 where
  go env = do
    input <- getLine
    let result = run input env
    go (environment result) -- TODO: parse 'assume/let' commands that add things to the environment


run :: String -> Result
run input =
  let simpleAST    = runParse input
      term         = simpleAST >>= convert
      inferredType = term >>= typeI0 []
      evaluated    = flip evalI [] <$> term
  in  R { simple    = simpleAST
        , parsed    = term
        , inferred  = inferredType
        , evaluated = evaluated
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
      <> ("\tsimple = " <> show s <> "\n")
      <> ("\tparsed = " <> show p <> "\n")
      <> ("\tinferred = " <> showValue i <> "\n")
      <> ("\tevaluated = " <> showValue e <> "\n")
      <> "}"
   where
    showValue (Left  err) = err
    showValue (Right v  ) = show (quote0 v)

forever :: Monad m => m a -> m a
forever f = f >> forever f

module Pretty
  ( Pretty
  , pretty
  , pp
  , Doc
  )
where

import           Data.Text.Prettyprint.Doc      ( Pretty
                                                , pretty
                                                , Doc
                                                )

pp :: Pretty a => a -> String
pp = show . pretty

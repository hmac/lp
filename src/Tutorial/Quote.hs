module Tutorial.Quote where

import           Tutorial.Expr

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote _ VStar        = Inf Star
quote i (VLam     f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i (VPi v f) = Inf $
          Pi (quote i v) (quote (i + 1) (f (vfree (Quote i))))

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x ) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundFree :: Int -> Name -> TermI
boundFree i (Quote k) = Bound (i - k - 1)
boundFree i x         = Free x

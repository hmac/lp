module Tutorial.Expr where

data TermI = Ann TermC Type
           | Bound Int
           | Free Name
           | TermI :@: TermC
           deriving (Show, Eq)

data TermC = Inf TermI
           | Lam TermC
           deriving (Show, Eq)

data Name = Global String
          | Local Int
          | Quote Int
          deriving (Show, Eq)

data Type = TFree Name
          | Fun Type Type
          deriving (Show, Eq)

data Value = VLam (Value -> Value)
           | VNeutral Neutral

data Neutral = NFree Name
             | NApp Neutral Value

data Kind = Star
  deriving (Show)

data Info = HasKind Kind
          | HasType Type
          deriving (Show)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

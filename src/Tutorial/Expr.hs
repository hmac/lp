module Tutorial.Expr where

import           Data.Text.Prettyprint.Doc      ( pretty
                                                , (<+>)
                                                , Pretty
                                                , parens
                                                )

data TermI = Ann TermC TermC
           | Star
           | Pi TermC TermC
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

data Value = VLam (Value -> Value)
           | VNeutral Neutral
           | VStar
           | VPi Value (Value -> Value)

data Neutral = NFree Name
             | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam     f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

instance Pretty TermI where
  pretty Star      = pretty "*"
  pretty (Ann e t) = pretty e <+> pretty ":" <+> pretty t
  pretty (Pi t e) =
    pretty "forall (_ :" <+> pretty t <> pretty ")" <+> pretty e
  pretty (Bound i         ) = pretty i
  pretty (Free  (Global n)) = pretty n
  pretty (Free  (Local  i)) = pretty i
  pretty (Free  (Quote  i)) = pretty i
  pretty (a :@: b         ) = pretty a <+> pretty b

instance Pretty TermC where
  pretty (Inf t) = pretty t
  pretty (Lam e) = pretty "\\_." <+> pretty e

module IK.Type where

infix  20 ◻_
infixr 19 _⇒_
infixr 19 _∧_

data Ty : Set where
  𝕓   : Ty
  _⇒_ : (a b : Ty) → Ty
  _∧_ : (a b : Ty) → Ty
  ◻_  : (a : Ty) → Ty

variable
  a b c d : Ty

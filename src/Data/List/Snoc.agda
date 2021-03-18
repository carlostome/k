module Data.List.Snoc where

  open import Level

  private
    variable
      p q r : Level
      A : Set p
      B : Set q

  infixl 14 _∷ˢ_

  data Listˢ (A : Set p) : Set (suc p) where
    []   : Listˢ A
    _∷ˢ_ : Listˢ A → A → Listˢ A

  map : (A → B) → Listˢ A → Listˢ B
  map f [] = []
  map f (xs ∷ˢ x) = map f xs ∷ˢ f x

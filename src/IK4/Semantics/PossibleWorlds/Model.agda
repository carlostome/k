open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IK4.Semantics.PossibleWorlds.Model
  (W-Carrier  : Set)
  (let _W-≈_  = _≡_)
  (let W-set  = P.isEquivalence)
  (_R_        : Rel W-Carrier 0ℓ) -- accessibility relation
  (R-trans    : Transitive _R_)   -- !
  (_≤_        : Rel W-Carrier 0ℓ) -- Kripke relation
  (≤-preorder : IsPreorder _W-≈_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → w R v → w' ≤ w → ∃ λ v' → v' ≤ v × w' R v')
  (dom-R-monotone : ∀ {w v v'} → w R v → v ≤ v' → ∃ λ w' → w ≤ w' × w' R v')
  where

open import IK.Semantics.PossibleWorlds.Model W-Carrier _R_ _≤_ ≤-preorder cod-R-monotone dom-R-monotone public

private
  variable O P Q P' Q' : Obj

nu : Hom (□ P) (□ □ P)
nu .f x wRw' w'Rw'' = x (R-trans wRw' w'Rw'')

mu : Hom (◆ ◆ P) (◆ P)
mu = counit ∘ ◆-map (counit ∘ ◆-map (nu ∘ unit))

open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IS4.Semantics.PossibleWorlds.Model
  (W-Carrier  : Set)
  (let _W-≈_  = _≡_)
  (let W-set  = P.isEquivalence)
  (R          : Rel W-Carrier 0ℓ)     -- accessibility relation
  (R-preorder : IsPreorder _W-≈_ R)   -- !
  (_≤_        : Rel W-Carrier 0ℓ)     -- Kripke relation
  (≤-preorder : IsPreorder _W-≈_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → R w v → w' ≤ w → ∃ λ v' → v' ≤ v × R w' v')
  (dom-R-monotone : ∀ {w v v'} → R w v → v ≤ v' → ∃ λ w' → w ≤ w' × R w' v')
  where

open import IK.Semantics.PossibleWorlds.Model W-Carrier R _≤_ ≤-preorder cod-R-monotone dom-R-monotone public

open IsPreorder R-preorder renaming (refl to R-refl; trans to R-trans)

private
  variable O P Q P' Q' : Obj

epsilon : Hom (□ P) P
epsilon .f x = x R-refl

nu : Hom (□ P) (□ □ P)
nu .f x wRw' w'Rw'' = x (R-trans wRw' w'Rw'')

-- In general, L1 ⊣ R1 and L2 ⊣ R2 induces Hom(L1,L2) ≅ Hom(R2,R1) using Yoneda:

-- Here, L1 = I ⊣ I = R1 and L2 = ◆ ⊣ □ = R2
eta : Hom P (◆ P)
eta = epsilon ∘ unit

-- Here, L1 = ◆ ∘ ◆ ⊣ □ ∘ □ = R1 and L2 = ◆ ⊣ □ = R2
mu : Hom (◆ ◆ P) (◆ P)
mu = counit ∘ ◆-map (counit ∘ ◆-map (nu ∘ unit))

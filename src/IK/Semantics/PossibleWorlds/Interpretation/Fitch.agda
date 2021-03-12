open import Data.Product
open import Data.Unit
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IK.Semantics.PossibleWorlds.Interpretation.Fitch
  (W-Carrier  : Set)
  (R          : Rel W-Carrier 0ℓ) -- accessibility relation, abstract "lock with lock-free extension"
  (_≤_        : Rel W-Carrier 0ℓ) -- Kripke or index category relation, abstract "weakening"
  (T-preorder : IsPreorder _≡_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → R w v → w' ≤ w → ∃ λ v' → v' ≤ v × R w' v') -- needed for □ P to be a presheaf
  (dom-R-monotone : ∀ {w v v'} → R w v → v ≤ v' → ∃ λ w' → w ≤ w' × R w' v') -- needed for ◆ P to be a presheaf
  where

open import IK.Term renaming (_≤_ to Wk) -- reexports IK.Type and Context Ty
open import IK.Semantics.PossibleWorlds.Model W-Carrier R _≤_ T-preorder cod-R-monotone dom-R-monotone public

module _ (⟦𝕓⟧ : Obj) (⟦∧⟧ : Ty → Ty → Obj) where
  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓     ⟧Ty = ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ b ⟧Ty ^ ⟦ a ⟧Ty
  ⟦ a ∧ b ⟧Ty = ⟦∧⟧ a b -- ⟦ b ⟧Ty x ⟦ a ⟧Ty
  ⟦ ◻ a   ⟧Ty = □ ⟦ a ⟧Ty

  ⟦_⟧Ctx : Ctx → Obj
  ⟦ []     ⟧Ctx = T
  ⟦ Γ `, a ⟧Ctx = ⟦ Γ ⟧Ctx x ⟦ a ⟧Ty
  ⟦ Γ 🔒   ⟧Ctx = ◆ ⟦ Γ ⟧Ctx

  ⟦_⟧Wk : Wk Δ Γ → Hom ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx
  ⟦ base       ⟧Wk = id
  ⟦ drop   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk ∘ π₁
  ⟦ keep   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk x-map id
  ⟦ drop🔒 Γ≤Δ ⟧Wk = !
  ⟦ keep🔒 Γ≤Δ ⟧Wk = ◆-map ⟦ Γ≤Δ ⟧Wk

  ⟦_⟧Var : Var Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ ze   ⟧Var = π₂
  ⟦ su v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧Tm : Tm Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ var   v   ⟧Tm = ⟦ v ⟧Var
  ⟦ lam   t   ⟧Tm = abs ⟦ t ⟧Tm
  ⟦ app   t u ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ box   t   ⟧Tm = right ⟦ t ⟧Tm
  ⟦ unbox t x ⟧Tm = left ⟦ t ⟧Tm ∘ ⟦ wᵣ x ⟧Wk

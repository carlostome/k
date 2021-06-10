open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IS4.Semantics.PossibleWorlds.Interpretation.Fitch
  (W-Carrier  : Set)
  (R          : Rel W-Carrier 0ℓ) -- accessibility relation
  (R-preorder : IsPreorder _≡_ R) -- !
  (_≤_        : Rel W-Carrier 0ℓ) -- Kripke relation
  (≤-preorder : IsPreorder _≡_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → R w v → w' ≤ w → ∃ λ v' → v' ≤ v × R w' v')
  (dom-R-monotone : ∀ {w v v'} → R w v → v ≤ v' → ∃ λ w' → w ≤ w' × R w' v')
  where

open import IS4.Term renaming (_≤_ to Wk)
open import IS4.Semantics.PossibleWorlds.Model W-Carrier R R-preorder _≤_ ≤-preorder cod-R-monotone dom-R-monotone public

module _ (⟦𝕓⟧ : Obj) (⟦∧⟧ : Ty → Ty → Obj) where
  -- XXX: identical to IK.Semantics.PossibleWorlds.Interpretation.Fitch.⟦_⟧Ty
  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓     ⟧Ty = ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ b ⟧Ty ^ ⟦ a ⟧Ty
  ⟦ a ∧ b ⟧Ty = ⟦∧⟧ a b -- ⟦ b ⟧Ty x ⟦ a ⟧Ty
  ⟦ ◻ a   ⟧Ty = □ ⟦ a ⟧Ty

  -- XXX: identical to IK.Semantics.PossibleWorlds.Interpretation.Fitch.⟦_⟧Ctx
  ⟦_⟧Ctx : Ctx → Obj
  ⟦ []     ⟧Ctx = T
  ⟦ Γ `, a ⟧Ctx = ⟦ Γ ⟧Ctx x ⟦ a ⟧Ty
  ⟦ Γ 🔒   ⟧Ctx = ◆ ⟦ Γ ⟧Ctx

  -- XXX: identical to IK.Semantics.PossibleWorlds.Interpretation.Fitch.⟦_⟧Wk
  ⟦_⟧Wk : Wk Γ Δ → Hom ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx
  ⟦ base       ⟧Wk = id
  ⟦ drop   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk ∘ π₁
  ⟦ keep   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk x-map id
  ⟦ keep🔒 Γ≤Δ ⟧Wk = ◆-map ⟦ Γ≤Δ ⟧Wk

  ⟦_⟧Ext : Γ ⊑ Δ → Hom ⟦ Δ ⟧Ctx (◆ ⟦ Γ ⟧Ctx)
  ⟦ nil          ⟧Ext = eta
  ⟦ ext Γ⊑Δ'     ⟧Ext = ⟦ _ , Γ⊑Δ' ⟧Ext ∘ π₁
  ⟦ ext🔒 _ Γ⊑Δ' ⟧Ext = mu ∘ ◆-map ⟦ _ , Γ⊑Δ' ⟧Ext

  ⟦_⟧Var : Var Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ ze   ⟧Var = π₂
  ⟦ su v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧Tm : Tm Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ var   v   ⟧Tm = ⟦ v ⟧Var
  ⟦ lam   t   ⟧Tm = abs ⟦ t ⟧Tm
  ⟦ app   t u ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ box   t   ⟧Tm = right ⟦ t ⟧Tm
  ⟦ unbox t x ⟧Tm = left ⟦ t ⟧Tm ∘ ⟦ x ⟧Ext

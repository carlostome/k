open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IK4.Semantics.PossibleWorlds.Interpretation.Fitch
  (W-Carrier  : Set)
  (_R_        : Rel W-Carrier 0ℓ) -- accessibility relation
  (R-trans    : Transitive _R_)   -- !
  (_≤_        : Rel W-Carrier 0ℓ) -- Kripke relation
  (≤-preorder : IsPreorder _≡_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → w R v → w' ≤ w → ∃ λ v' → v' ≤ v × w' R v')
  (dom-R-monotone : ∀ {w v v'} → w R v → v ≤ v' → ∃ λ w' → w ≤ w' × w' R v')
  where

open import IK4.Term renaming (_≤_ to Wk)
open import IK4.Semantics.PossibleWorlds.Model W-Carrier _R_ R-trans _≤_ ≤-preorder cod-R-monotone dom-R-monotone public

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

  ⟦_⟧Wk : Wk Γ Δ → Hom ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx
  ⟦ base       ⟧Wk = id
  ⟦ drop   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk ∘ π₁
  ⟦ keep   Γ≤Δ ⟧Wk = ⟦ Γ≤Δ ⟧Wk x-map id
  ⟦ keep🔒 Γ≤Δ ⟧Wk = ◆-map ⟦ Γ≤Δ ⟧Wk

  ⟦_⟧Ext : Γ ⊏ Δ → Hom ⟦ Δ ⟧Ctx (◆ ⟦ Γ ⟧Ctx)
  ⟦ nil          ⟧Ext = id
  ⟦ ext Γ⊏Δ'     ⟧Ext = ⟦ _ , Γ⊏Δ' ⟧Ext ∘ π₁
  ⟦ ext🔒 _ Γ⊏Δ' ⟧Ext = mu ∘ ◆-map ⟦ _ , Γ⊏Δ' ⟧Ext

  ⟦_⟧Var : Var Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ ze   ⟧Var = π₂
  ⟦ su v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧Tm : Tm Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ var   v   ⟧Tm = ⟦ v ⟧Var
  ⟦ lam   t   ⟧Tm = abs ⟦ t ⟧Tm
  ⟦ app   t u ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ box   t   ⟧Tm = right ⟦ t ⟧Tm
  ⟦ unbox t x ⟧Tm = left ⟦ t ⟧Tm ∘ ⟦ x ⟧Ext

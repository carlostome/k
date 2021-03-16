open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module IK.Semantics.PossibleWorlds.Interpretation.DC
  (W-Carrier  : Set)
  (R          : Rel W-Carrier 0ℓ)
  (_≤_        : Rel W-Carrier 0ℓ)
  (T-preorder : IsPreorder _≡_ _≤_)
  (cod-R-monotone : ∀ {w v w'} → R w v → w' ≤ w → ∃ λ v' → v' ≤ v × R w' v')
  (dom-R-monotone : ∀ {w v v'} → R w v → v ≤ v' → ∃ λ w' → w ≤ w' × R w' v')
  where

open import IK.Calculus.DC
open import IK.Semantics.PossibleWorlds.Model W-Carrier R _≤_ T-preorder cod-R-monotone dom-R-monotone public

module _ (⟦𝕓⟧ : Obj) where
  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓 ⟧Ty =  ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ b ⟧Ty ^ ⟦ a ⟧Ty
  ⟦ a ∧ b ⟧Ty = ⟦ a ⟧Ty x ⟦ b ⟧Ty
  ⟦ ◻ a ⟧Ty = □ ⟦ a ⟧Ty

  ⟦_⟧Ctx : Ctx → Obj
  ⟦ []     ⟧Ctx = T
  ⟦ Γ `, a ⟧Ctx = ⟦ Γ ⟧Ctx x ⟦ a ⟧Ty

  ⟦_⟧MCtx : Ctx → Obj
  ⟦ Δ ⟧MCtx = □ ⟦ Δ ⟧Ctx

  ⟦_⟧Var : a ∈ Γ → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ here   ⟧Var = π₂
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧Tm : Δ ; Γ ⊢ a → Hom (⟦ Δ ⟧MCtx x ⟦ Γ ⟧Ctx) ⟦ a ⟧Ty
  ⟦ var x      ⟧Tm = ⟦ x  ⟧Var ∘ π₂
  ⟦ app t u    ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ lam t      ⟧Tm = abs (⟦ t ⟧Tm ∘ x-right-assoc)
  ⟦ fst t      ⟧Tm = π₁ ∘ ⟦ t ⟧Tm
  ⟦ snd t      ⟧Tm = π₂ ∘ ⟦ t ⟧Tm
  ⟦ prd t u    ⟧Tm = pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦_⟧Tm  {Δ = Δ} (box t)  = □-map ⟦ t ⟧Tm ∘ □-pr {Q = ⟦ Δ ⟧Ctx} (□-map □-! ∘ □-!) π₁
  ⟦_⟧Tm  {Δ = Δ} (letbox_In_ {A = A} t u) = ⟦ u ⟧Tm ∘ pr (□-pr {P = ⟦ Δ ⟧Ctx} {Q = ⟦ A ⟧Ty} π₁ ⟦ t ⟧Tm) π₂

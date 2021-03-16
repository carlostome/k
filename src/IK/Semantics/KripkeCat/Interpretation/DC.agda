open import IK.Semantics.KripkeCat.Model
module IK.Semantics.KripkeCat.Interpretation.DC (KC : KripkeCat) (let open KripkeCat KC) (⟦𝕓⟧ : Obj) where

  open import IK.Calculus.DC

  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓 ⟧Ty =  ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ a ⟧Ty ⇒̇ ⟦ b ⟧Ty
  ⟦ ◻ a ⟧Ty = □ ⟦ a ⟧Ty
  ⟦ a ∧ b ⟧Ty = ⟦ a ⟧Ty x ⟦ b ⟧Ty

  ⟦_⟧Ctx : Ctx → Obj
  ⟦ []     ⟧Ctx = 𝟙
  ⟦ Γ `, a ⟧Ctx = ⟦ Γ ⟧Ctx x ⟦ a ⟧Ty

  ⟦_⟧MCtx : Ctx → Obj
  ⟦ Δ ⟧MCtx = □ ⟦ Δ ⟧Ctx

  ⟦_⟧Var : a ∈ Γ → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ here   ⟧Var = π₂
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_;_⊢_⟧ : (Δ Γ : Ctx) (a : Ty) → Set
  ⟦ Δ ; Γ ⊢ a ⟧ = Hom (⟦ Δ ⟧MCtx x ⟦ Γ ⟧Ctx) ⟦ a ⟧Ty

  ⟦_⟧Tm : Δ ; Γ ⊢ a → ⟦ Δ ; Γ ⊢ a ⟧
  ⟦ var v      ⟧Tm = ⟦ v  ⟧Var ∘ π₂
  ⟦ app t u    ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ lam t      ⟧Tm = abs (⟦ t ⟧Tm ∘ x-right-assoc)
  ⟦ fst t      ⟧Tm = π₁ ∘ ⟦ t ⟧Tm
  ⟦ snd t      ⟧Tm = π₂ ∘ ⟦ t ⟧Tm
  ⟦ prd t u    ⟧Tm = pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦_⟧Tm  {Δ = Δ} (box t)  = □-map ⟦ t ⟧Tm ∘ □-pr {Q = ⟦ Δ ⟧Ctx} (□-map □-! ∘ □-!) π₁
  ⟦_⟧Tm  {Δ = Δ} (letbox_In_ {A = A} t u) = ⟦ u ⟧Tm ∘ pr (□-pr {P = ⟦ Δ ⟧Ctx} {Q = ⟦ A ⟧Ty} π₁ ⟦ t ⟧Tm) π₂

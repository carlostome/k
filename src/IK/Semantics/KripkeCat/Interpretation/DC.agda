open import IK.Semantics.KripkeCat.Model
module IK.Semantics.KripkeCat.Interpretation.DC (KC : KripkeCat) (let open KripkeCat KC) (⟦𝕓⟧ : Obj) where

  open import IK.Calculus.DC

  private
    variable
      Γ Δ : Ctx

  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓 ⟧Ty =  ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ a ⟧Ty ⇒̇ ⟦ b ⟧Ty
  ⟦ ◻ a ⟧Ty = □ ⟦ a ⟧Ty

  ⟦_⟧Ctx : Ctx → Obj
  ⟦ []     ⟧Ctx = 𝟙
  ⟦ Γ `, a ⟧Ctx = ⟦ Γ ⟧Ctx x ⟦ a ⟧Ty

  ⟦_⟧MCtx : Ctx → Obj
  ⟦ Δ ⟧MCtx = □ ⟦ Δ ⟧Ctx

  ⟦_⟧Var : a ∈ Γ → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Ty
  ⟦ here   ⟧Var = snd
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ fst

  ⟦_;_⊢_⟧ : (Δ Γ : Ctx) (a : Ty) → Set
  ⟦ Δ ; Γ ⊢ a ⟧ = Hom (⟦ Δ ⟧MCtx x ⟦ Γ ⟧Ctx) ⟦ a ⟧Ty

  ⟦_⟧Tm : Δ ; Γ ⊢ a → ⟦ Δ ; Γ ⊢ a ⟧
  ⟦ var v      ⟧Tm = ⟦ v  ⟧Var ∘ snd
  ⟦ app t u    ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ lam t      ⟧Tm = abs (⟦ t ⟧Tm ∘ x-right-assoc)
  ⟦_⟧Tm  {Δ = Δ} (box t)  = □-map ⟦ t ⟧Tm ∘ □-pr {Q = ⟦ Δ ⟧Ctx} (□-map □-! ∘ □-!) fst
  ⟦_⟧Tm  {Δ = Δ} (letbox {A = A} t u) = ⟦ u ⟧Tm ∘ pr (□-pr {P = ⟦ Δ ⟧Ctx} {Q = ⟦ A ⟧Ty} fst ⟦ t ⟧Tm) snd

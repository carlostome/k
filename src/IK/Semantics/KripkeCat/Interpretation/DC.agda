open import IK.Semantics.KripkeCat.Model
module IK.Semantics.KripkeCat.Interpretation.DC (KC : KripkeCat) (let open KripkeCat KC) (⟦𝕓⟧ : Obj) where

  open import IK.Calculus.DC

  ⟦_⟧Ty : Ty → Obj
  ⟦ 𝕓 ⟧Ty =  ⟦𝕓⟧
  ⟦ a ⇒ b ⟧Ty = ⟦ a ⟧Ty ⇒̇ ⟦ b ⟧Ty
  ⟦ ◻ a ⟧Ty = □ ⟦ a ⟧Ty
  ⟦ a ∧ b ⟧Ty = ⟦ a ⟧Ty x ⟦ b ⟧Ty

  ⟦_⟧LCtx : Ctx → Obj
  ⟦ []     ⟧LCtx = 𝟙
  ⟦ Γ `, a ⟧LCtx = ⟦ Γ ⟧LCtx x ⟦ a ⟧Ty

  ⟦_⟧MCtx : Ctx → Obj
  ⟦ Δ ⟧MCtx = □ ⟦ Δ ⟧LCtx

  ⟦_;_⟧DCtx : (Δ Γ : Ctx) → Obj
  ⟦ Δ ; Γ ⟧DCtx = ⟦ Δ ⟧MCtx x ⟦ Γ ⟧LCtx

  ⟦_⟧Var : a ∈ Γ → Hom ⟦ Γ ⟧LCtx ⟦ a ⟧Ty
  ⟦ here    ⟧Var = π₂
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧LWken : Γ ⊆ Γ' → Hom ⟦ Γ' ⟧LCtx ⟦ Γ ⟧LCtx
  ⟦ []        ⟧LWken = !
  ⟦ keep Γ⊆Γ' ⟧LWken = ⟦ Γ⊆Γ' ⟧LWken x-map id
  ⟦ drop Γ⊆Γ' ⟧LWken = ⟦ Γ⊆Γ' ⟧LWken ∘ π₁

  ⟦_⟧MWken : Δ ⊆ Δ' → Hom ⟦ Δ' ⟧MCtx ⟦ Δ ⟧MCtx
  ⟦ Δ⊆Δ' ⟧MWken = □-map ⟦ Δ⊆Δ' ⟧LWken

  ⟦_;_⟧Wken : Δ ⊆ Δ' → Γ ⊆ Γ' → Hom ⟦ Δ' ; Γ' ⟧DCtx ⟦ Δ ; Γ ⟧DCtx
  ⟦ Δ⊆Δ' ; Γ⊆Γ' ⟧Wken = ⟦ Δ⊆Δ' ⟧MWken x-map ⟦ Γ⊆Γ' ⟧LWken

  ⟦_;_⊢_⟧ : (Δ Γ : Ctx) (a : Ty) → Set
  ⟦ Δ ; Γ ⊢ a ⟧ = Hom ⟦ Δ ; Γ ⟧DCtx ⟦ a ⟧Ty

  ⟦_⟧Tm : Δ ; Γ ⊢ a → ⟦ Δ ; Γ ⊢ a ⟧
  ⟦ var v      ⟧Tm = ⟦ v  ⟧Var ∘ π₂
  ⟦ app t u    ⟧Tm = ev ∘ pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦ lam t      ⟧Tm = abs (⟦ t ⟧Tm ∘ x-right-assoc)
  ⟦ fst t      ⟧Tm = π₁ ∘ ⟦ t ⟧Tm
  ⟦ snd t      ⟧Tm = π₂ ∘ ⟦ t ⟧Tm
  ⟦ prd t u    ⟧Tm = pr ⟦ t ⟧Tm ⟦ u ⟧Tm
  ⟦_⟧Tm  {Δ = Δ} (box t)  = □-map ⟦ t ⟧Tm ∘ □-pr {Q = ⟦ Δ ⟧LCtx} (□-map □-! ∘ □-!) π₁
  ⟦_⟧Tm  {Δ = Δ} (letbox_In_ {a = A} t u) = ⟦ u ⟧Tm ∘ pr (□-pr {P = ⟦ Δ ⟧LCtx} {Q = ⟦ A ⟧Ty} π₁ ⟦ t ⟧Tm) π₂

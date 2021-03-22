module IK.Calculus.DC.Reduction where

  open import IK.Calculus.DC

  infixr 4 _⟶_

  -- reduction relation
  data _⟶_ : Δ ; Γ ⊢ a → Δ ; Γ ⊢ a → Set where
  
    beta-fun : {t : Δ ; (Γ `, a) ⊢ b} {u : Δ ; Γ ⊢ a}
               → app (lam t) u ⟶ lsubst-here u t
  
    cong-lam : ∀ {t t' : Δ ; (Γ `, a) ⊢ b}
                → t ⟶ t'
                → lam t ⟶ lam t'

    cong-app-l : ∀ {t t' : Δ ; Γ ⊢ (a ⇒ b)} {u : Δ ; Γ ⊢ a}
                  → t ⟶ t'
                  → app t u ⟶ app t' u
  
    cong-app-r : ∀ {t : Δ ; Γ ⊢ (a ⇒ b)} {u u' : Δ ; Γ ⊢ a}
                  → u ⟶ u'
                  → app t u ⟶ app t u'

    beta-prd-fst : {t : Δ ; Γ ⊢ a} {u : Δ ; Γ ⊢ b}
                   → fst (prd t u) ⟶ t
  
    beta-prd-snd : {t : Δ ; Γ ⊢ a} {u : Δ ; Γ ⊢ b}
                   → snd (prd t u) ⟶ u

    cong-fst : ∀ {t t' : Δ ; Γ ⊢ a ∧ b}
                → t ⟶ t'
                → fst t ⟶ fst t'

    cong-snd : ∀ {t t' : Δ ; Γ ⊢ a ∧ b}
                → t ⟶ t'
                → snd t ⟶ snd t'

    cong-prd-l : ∀ {t t' : Δ ; Γ ⊢ a} {u : Δ ; Γ ⊢ b}
                  → t ⟶ t'
                  → prd t u ⟶ prd t' u
  
    cong-prd-r : ∀ {t : Δ ; Γ ⊢ a} {u u' : Δ ; Γ ⊢ b}
                  → u ⟶ u'
                  → prd t u ⟶ prd t u'
  
    cong-box : ∀ {t t' : [] ; Δ ⊢ a}
                → t ⟶ t'
                → box {Γ = Γ} t ⟶ box t'

    beta-box : ∀ {A B} {t₁ : [] ; Δ ⊢ A} {t₂ : (Δ `, A) ; Γ ⊢ B}
                → letbox (box t₁) In t₂ ⟶ mcut t₁ t₂

    cong-let-l : ∀ {A B} {t₁ t₂ : Δ ; Γ ⊢ (◻ A)} {u : (Δ `, A) ; Γ ⊢ B}
                  → t₁ ⟶ t₂
                  → letbox t₁ In u ⟶ letbox t₂ In u

    cong-let-r : ∀ {A B} {t : Δ ; Γ ⊢ (◻ A)} {u₁ u₂ : (Δ `, A) ; Γ ⊢ B}
                  → u₁ ⟶ u₂
                  → letbox t In u₁ ⟶ letbox t In u₂

    assoc-let : ∀ {A B C} {t : Δ ; Γ ⊢ (◻ A)} {u₁ : (Δ `, A) ; Γ ⊢ (◻ B)} {u₂ : (Δ `, B) ; Γ ⊢ C}
                    → letbox (letbox t In u₁) In u₂ ⟶ letbox t In letbox u₁ In wken (keep ⊆-`,) ⊆-refl u₂

    comm-app-let : ∀ {A B C} {t₁ : Δ ; Γ ⊢ (◻ A)} {t₂ : (Δ `, A) ; Γ ⊢ (B ⇒ C)} {t₃ : Δ ; Γ ⊢ B}
                   →  app (letbox t₁ In t₂) t₃ ⟶ letbox t₁ In app t₂ (wken ⊆-`, ⊆-refl t₃)

    comm-fst-let : ∀ {t₁ : Δ ; Γ ⊢ (◻ a)} {t₂ : (Δ `, a) ; Γ ⊢ b ∧ c}
                    → fst (letbox t₁ In t₂) ⟶ letbox t₁ In fst t₂

    comm-snd-let : ∀  {t₁ : Δ ; Γ ⊢ (◻ a)} {t₂ : (Δ `, a) ; Γ ⊢ b ∧ c}
                    → snd (letbox t₁ In t₂) ⟶ letbox t₁ In snd t₂

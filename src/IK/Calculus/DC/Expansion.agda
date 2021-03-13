module IK.Calculus.DC.Expansion where

  open import IK.Calculus.DC

  infixr 4 _⇝_

  data _⇝_ : Δ ; Γ ⊢ a → Δ ; Γ ⊢ a → Set where

    eta-fun : {t : Δ ; Γ ⊢ a ⇒ b}
               → t ⇝ lam (app (lwken ⊆-`, t) v0)

    eta-prd : {t : Δ ; Γ ⊢ a ∧ b}
               → t ⇝ prd (fst t) (snd t)

    eta-box : ∀ {t : Δ ; Γ ⊢ (◻ a)}
                → t ⇝ letbox t In box v0
  
    cong-lam : ∀ {t t' : Δ ; (Γ `, a) ⊢ b}
                → t ⇝ t'
                → lam t ⇝ lam t'

    cong-app-l : ∀ {t t' : Δ ; Γ ⊢ (a ⇒ b)} {u : Δ ; Γ ⊢ a}
                  → t ⇝ t'
                  → app t u ⇝ app t' u
  
    cong-app-r : ∀ {t : Δ ; Γ ⊢ (a ⇒ b)} {u u' : Δ ; Γ ⊢ a}
                  → u ⇝ u'
                  → app t u ⇝ app t u'

    cong-fst : ∀ {t t' : Δ ; Γ ⊢ a ∧ b}
                → t ⇝ t'
                → fst t ⇝ fst t'

    cong-snd : ∀ {t t' : Δ ; Γ ⊢ a ∧ b}
                → t ⇝ t'
                → snd t ⇝ snd t'

    cong-prd-l : ∀ {t t' : Δ ; Γ ⊢ a} {u : Δ ; Γ ⊢ b}
                  → t ⇝ t'
                  → prd t u ⇝ prd t' u
  
    cong-prd-r : ∀ {t : Δ ; Γ ⊢ a} {u u' : Δ ; Γ ⊢ b}
                  → u ⇝ u'
                  → prd t u ⇝ prd t u'
  
    cong-box : ∀ {t t' : [] ; Δ ⊢ a}
                → t ⇝ t'
                → box {Γ = Γ} t ⇝ box t'

    cong-let-l : ∀ {A B} {t₁ t₂ : Δ ; Γ ⊢ (◻ A)} {u : (Δ `, A) ; Γ ⊢ B}
                  → t₁ ⇝ t₂
                  → letbox t₁ In u ⇝ letbox t₂ In u

    cong-let-r : ∀ {A B} {t : Δ ; Γ ⊢ (◻ A)} {u₁ u₂ : (Δ `, A) ; Γ ⊢ B}
                  → u₁ ⇝ u₂
                  → letbox t In u₁ ⇝ letbox t In u₂

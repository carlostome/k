module IK.Calculus.DC.EquationalTheory where

  open import Relation.Binary hiding (_⇒_)

  open import IK.Type public
  open import IK.Calculus.DC public

  infix  3  _;_⊢_∶_≈_

  -- equational theory w/o commuting conversions?
  data _;_⊢_∶_≈_ (Δ Γ : Ctx) : (A : Ty) → (t₁ t₂ : Δ ; Γ ⊢ A) → Set where

    -- rules for ⇒
    ⇒-β : ∀ {A B} {t₁ : Δ ; (Γ `, A) ⊢ B} {t₂ : Δ ; Γ ⊢ A}
            →  Δ ; Γ ⊢ B ∶ app (lam t₁) t₂ ≈ subst-here t₂ t₁

    ⇒-η : ∀ {A B} {t : Δ ; Γ ⊢ (A ⇒ B)}
           → Δ ; Γ ⊢ (A ⇒ B) ∶ t ≈ lam (app (wken ⊆-refl ⊆-`, t) (var here))

    ⇒-δ₁ : ∀ {A B} {t₁ t₂ : Δ ; (Γ `, A) ⊢ B}
           → Δ ; (Γ `, A) ⊢ B ∶ t₁ ≈ t₂
           → Δ ; Γ ⊢ (A ⇒ B) ∶ lam t₁ ≈ lam t₂

    ⇒-δ₂ : ∀ {A B} {t₁ t₂ : Δ ; Γ ⊢ (A ⇒ B)} {u₁ u₂ : Δ ; Γ ⊢ A}
           → Δ ; Γ ⊢ (A ⇒ B) ∶ t₁ ≈ t₂
           → Δ ; Γ ⊢ A ∶ u₁ ≈ u₂
           → Δ ; Γ ⊢ B ∶ app t₁ u₁ ≈ app t₂ u₂

    -- rules for the □ type
    □-β : ∀ {A B} {t₁ : [] ; Δ ⊢ A} {t₂ : (Δ `, A) ; Γ ⊢ B}
            →  Δ ; Γ ⊢ B ∶ (letbox (box t₁) In t₂) ≈ msubst-here t₁ t₂

    □-η : ∀ {A} {t : Δ ; Γ ⊢ (◻ A)}
            → Δ ; Γ ⊢ (◻ A) ∶ t ≈ letbox t In (box (var here))

    □-δ₁ : ∀ {A} {t₁ t₂ : [] ; Δ ⊢ A}
            → [] ; Δ ⊢ A ∶ t₁ ≈ t₂
            → Δ ; Γ ⊢ ◻ A ∶ box t₁ ≈ box t₂

    □-δ₂ : ∀ {A B} {t₁ t₂ : Δ ; Γ ⊢ (◻ A)} {u₁ u₂ : (Δ `, A) ; Γ ⊢ B}
            → Δ ; Γ ⊢ (◻ A)    ∶ t₁ ≈ t₂
            → (Δ `, A) ; Γ ⊢ B ∶ u₁ ≈ u₂
            → Δ ; Γ ⊢ B ∶ letbox t₁ In u₁ ≈ letbox t₂ In u₂

    -- commuting conversions?
    commlet-app : ∀ {A B C} {t₁ : Δ ; Γ ⊢ ◻ A} {t₂ : Δ `, A ; Γ ⊢ B ⇒ C} {t₃ : Δ ; Γ ⊢ B}
                  → Δ ; Γ ⊢ C ∶ letbox t₁ In (app t₂ (mwken ⊆-`, t₃)) ≈ app (letbox t₁ In t₂) t₃

    commlet-fst : ∀ {t₁ : Δ ; Γ ⊢ ◻ a} {t₂ : Δ `, a ; Γ ⊢ b ∧ c}
                  → Δ ; Γ ⊢ b ∶ fst (letbox t₁ In t₂) ≈ letbox t₁ In fst t₂

    commlet-snd : ∀ {t₁ : Δ ; Γ ⊢ ◻ a} {t₂ : Δ `, a ; Γ ⊢ b ∧ c}
                  → Δ ; Γ ⊢ c ∶ snd (letbox t₁ In t₂) ≈ letbox t₁ In snd t₂

    -- commlet-let : ∀ {A B C} {t₁ : Δ ; Γ ⊢ ◻ A} {t₂ : Δ ; Γ ⊢ ◻ B} {t₃ : Δ `, A `, B ; Γ ⊢ C}
    --             → Δ ; Γ ⊢ C ∶ letbox t₁ In (letbox (mwken ⊆-`, t₂) In t₃) ≈ letbox t₂ In (letbox (mwken ⊆-`, t₁)
    --                                                                                        In (msubst msub-swap t₃))

    -- equivalence relation
    ≈-refl : ∀ {A} {t : Δ ; Γ  ⊢ A}
            →  Δ ; Γ ⊢ A ∶ t ≈ t

    ≈-sym : ∀ {A} {t₁ t₂ : Δ ; Γ ⊢ A}
            →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₂
            →  Δ ; Γ ⊢ A ∶ t₂ ≈ t₁

    ≈-trans : ∀ {A} {t₁ t₂ t₃ : Δ ; Γ ⊢ A}
                →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₂
                →  Δ ; Γ ⊢ A ∶ t₂ ≈ t₃
                →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₃

  _≈_ : ∀ {Δ Γ : Ctx} {A : Ty} → (t₁ t₂ : Δ ; Γ ⊢ A) → Set
  t₁ ≈ t₂ = _ ; _ ⊢ _ ∶ t₁ ≈ t₂

  ≈-isEquivalence : (Δ : Ctx) → (Γ : Ctx) → (a : Ty) → IsEquivalence (Δ ; Γ ⊢ a ∶_≈_)
  ≈-isEquivalence Δ Γ a = record { refl = ≈-refl
                               ; sym = ≈-sym
                               ; trans = ≈-trans } 

  Term : Ctx → Ctx → Ty → Setoid _ _ 
  Term Δ Γ a = record { Carrier = Δ ; Γ ⊢ a
                    ; _≈_ = _≈_
                    ; isEquivalence = ≈-isEquivalence Δ Γ a}

  -- --8<-- (examples)
  -- private
  --   □-pr : Δ ; Γ `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b)
  --   □-pr = letbox v1 In (letbox v0 In (box (prd v1 v0)))

  --   □-pr-inv : Δ ; Γ `, ◻ (a ∧ b) ⊢ ◻ a ∧ ◻ b
  --   □-pr-inv = letbox v0 In prd (box (fst v0)) (box (snd v0))

  --   ex-1-lhs ex-1-rhs : [] ; [] `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b)
  --   ex-1-lhs = □-pr
  --   ex-1-rhs = letbox v0 In letbox v1 In box (prd v0 v1)

  --   ex-1 : [] ; [] `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b) ∶ ex-1-lhs ≈ ex-1-rhs
  --   ex-1 {a = a} {b = b} = begin
  --       letbox v1 In letbox v0 In (box (prd v1 v0))
  --     ≈⟨ commlet-let ⟩
  --       letbox v0 In letbox v1 In msubst msub-swap (box (prd v1 v0))
  --     ≡⟨⟩
  --       letbox v0 In letbox v1 In box (subst sub-swap (prd v1 v0))
  --     ≡⟨⟩
  --       letbox v0 In letbox v1 In box (prd (subst sub-swap v1) (subst sub-swap v0))
  --     ≡⟨⟩
  --       letbox v0 In letbox v1 In box (prd v0 v1)
  --     ∎
  --     where open import Relation.Binary.Reasoning.Setoid (Term [] ([] `, ◻ a `, ◻ b)  (◻ (a ∧ b)))
  -- -->8--

module IK.Calculus.DC where

  open import Data.Product
  open import IK.Type public

  data Ctx : Set where
    []    : Ctx
    _`,_ : Ctx → Ty → Ctx
  
  data _⊇_ : Ctx → Ctx → Set where
    base : [] ⊇ []
    keep : ∀ {T Γ Δ} → Δ ⊇ Γ → (Δ `, T) ⊇ (Γ `, T)
    drop : ∀ {T Γ Δ} → Δ ⊇ Γ → (Δ `, T) ⊇ Γ

  data _∈_ (A : Ty) : Ctx → Set where
    here : ∀ {Γ} → A ∈ (Γ `, A)
    there : ∀ {B Γ}  → A ∈ Γ → A ∈ (Γ `, B)

  -- ⊇-refl : {Γ : Ctx} → Γ ⊇ Γ
  -- ⊇-refl = {!!}

  -- wken-var : ∀ {A} {Γ₁ Γ₂} → Γ₂ ⊇ Γ₁ → A ∈ Γ₁ → A ∈ Γ₂
  -- wken-var =  {!!}

  data _;_⊢_ (Δ Γ : Ctx) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ
                    ---------
                 → Δ ; Γ ⊢ A

    app : ∀ {A B} → Δ ; Γ ⊢ (A ⇒ B) → Δ ; Γ ⊢ A
                     --------------------------
                  →          Δ ; Γ ⊢ B

    lam : ∀ {A B} → Δ ; (Γ `, A) ⊢ B
                     ----------------
                  → Δ ; Γ ⊢ (A ⇒ B)

    box : ∀ {A} → [] ; Δ ⊢ A
                   -----------
                → Δ ; Γ ⊢ (◻ A)

    letbox : ∀ {A B} → Δ ; Γ ⊢ (◻ A) → (Δ `, A) ; Γ ⊢ B
                        -------------------------------
                     →           Δ ; Γ ⊢ B


--   -- weakening is derivable for the normal context
--   wken : ∀ {Δ} {A} {Γ₁ Γ₂} → Γ₂ ⊇ Γ₁ → Δ ; Γ₁ ⊢ A → Δ ; Γ₂ ⊢ A
--   wken Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
--   wken Γ₁⊆Γ₂ (mvar x) = mvar x
--   wken Γ₁⊆Γ₂ (app t t₁) = app (wken Γ₁⊆Γ₂ t) (wken Γ₁⊆Γ₂ t₁)
--   wken Γ₁⊆Γ₂ (lam t) = lam (wken (keep Γ₁⊆Γ₂) t)
--   wken Γ₁⊆Γ₂ (box t) = box t
--   wken Γ₁⊆Γ₂ (letbox t t₁) = letbox (wken Γ₁⊆Γ₂ t) (wken Γ₁⊆Γ₂ t₁)

--   -- substitution of a modal variable / letbox is admissible
--   msubst : ∀ {Γ} {Δ₁ Δ₂} {A B} → Ø ; Δ₁ ⊢ A → (Δ₁ ++ Δ₂) ; Γ ⊢ B → (Δ₁ ++ Δ₂) ; Γ ⊢ B
--   msubst t (var x) = var x
--   msubst t (mvar x) = box {!!}
--   msubst t (app u u₁) = app (msubst t u) (msubst t u₁)
--   msubst t (lam u) = lam (msubst t u)
--   msubst t (box u) = box u
--   msubst t (letbox u k) = letbox (msubst t u) k


--   -- open import Relation.Binary.PropositionalEquality
--   -- _ : ∀ {Γ} {Δ} {A B} (t : Ø ; Δ ⊢ A)( u : (Δ `, A) ; Γ ⊢ B) → letbox (box (wken {!!} t)) {!!} ≡ msubst t u
--   mutual
--      data _;_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
--        var   : ∀ {A}   → A ∈ Γ → Δ ; Γ ⊢Ne A
--        mvar  : ∀ {A}   → A ∈ Δ → Δ ; Γ ⊢Ne □ A
--        app   : ∀ {A B} → Δ ; Γ ⊢Ne (A ⇒ B) → Δ ; Γ ⊢Nf A → Δ ; Γ ⊢Ne B

--      data _;_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
--        lam : ∀ {A B} → Δ ; (Γ `, A) ⊢Nf B → Δ ; Γ ⊢Nf A ⇒ B
--        box : ∀ {A} → Ø ; Δ ⊢Nf A → Δ ; Γ ⊢Nf □ A 
--        letbox : ∀ {A B} → Δ ; Γ ⊢Ne □ A → (Δ `, A) ; Γ ⊢Nf B → Δ ; Γ ⊢Nf B
--        lift : ∀ {A} → Δ ; Γ ⊢Ne A → Δ ; Γ ⊢Nf A 

--      wken-Ne : ∀ {Δ} {A} {Γ₁ Γ₂} → Γ₂ ⊇ Γ₁ → Δ ; Γ₁ ⊢Ne A → Δ ; Γ₂ ⊢Ne A
--      wken-Ne Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
--      wken-Ne Γ₁⊆Γ₂ (mvar x) = mvar x
--      wken-Ne Γ₁⊆Γ₂ (app t x) = app (wken-Ne Γ₁⊆Γ₂ t) (wken-Nf Γ₁⊆Γ₂ x)

--      wken-Nf : ∀ {Δ} {A} {Γ₁ Γ₂} → Γ₂ ⊇ Γ₁ → Δ ; Γ₁ ⊢Nf A → Δ ; Γ₂ ⊢Nf A
--      wken-Nf Γ₁⊆Γ₂ (lam t) = lam (wken-Nf (keep Γ₁⊆Γ₂) t)
--      wken-Nf Γ₁⊆Γ₂ (box t) = box t
--      wken-Nf Γ₁⊆Γ₂ (letbox x t) = letbox (wken-Ne Γ₁⊆Γ₂ x) (wken-Nf Γ₁⊆Γ₂ t)
--      wken-Nf Γ₁⊆Γ₂ (lift t) = lift (wken-Ne Γ₁⊆Γ₂ t)

--   -- -- Lawless Presheaf' mambo-jambo
--   -- ISet = Ctx → Set

--   -- record Psh : Set₁ where
--   --   field
--   --       iSet : ISet
--   --       Wken : ∀ {Δ Γ} (Δ⊇Γ : Δ ⊇ Γ) → (iSet Γ → iSet Δ)

--   -- open Psh

--   -- _⇒̇_ : Psh → Psh → Psh
--   -- (P ⇒̇ Q) = record { iSet  = λ Γ₁ → ∀ Γ₂ → (Δ⊇Γ : Γ₂ ⊇ Γ₁) → iSet P Γ₁ → iSet Q Γ₂
--   --                   ; Wken = λ Δ⊇Γ f x → {!!} }
--   -- _→̇_ : Psh → Psh → Set
--   -- P →̇ Q = ∀ {Γ} → iSet P Γ → iSet Q Γ
--   -- Tm : Ty → Ctx → Psh
--   -- Tm A Δ = record { iSet = Δ ;_⊢ A
--   --                 ; Wken = wken}
--   -- Ne : Ty → Ctx → Psh
--   -- Ne A Δ = record { iSet = Δ ;_⊢Ne A
--   --                 ; Wken = wken-Ne}

--   -- Nf : Ty → Ctx → Psh
--   -- Nf A Δ = record { iSet = Δ ;_⊢Nf A
--   --                 ; Wken = wken-Nf}

--   -- 𝟙 : Psh
--   -- _⊗_ : Psh → Psh → Psh

--   -- mutual
--   --   -- ⟦_⟧ : Ty → Psh
--   --   -- ⟦ ο ⟧ = Nf ο Ø
--   --   -- ⟦ A ⇒ B ⟧ = ⟦ A ⟧ →̇ ⟦ B ⟧
--   --   -- ⟦ □ A ⟧ = Nf (□ A) Ø

--   --   -- ⟦_⟧c : Ctx → Psh
--   --   -- ⟦ Ø ⟧c = 𝟙
--   --   -- ⟦ Γ `, A ⟧c = ⟦ Γ ⟧c ⊗ ⟦ A ⟧

--   --   ⟦_⟧,_ : Ty → Ctx → Psh
--   --   ⟦ ο ⟧, Δ = Nf ο Δ
--   --   ⟦ A ⇒ B ⟧, Δ = (⟦ A ⟧, Δ) ⇒̇ (⟦ B ⟧, Δ)
--   --   ⟦ □ A ⟧, Δ = {!!}

--   --   ⟦_⟧c,_ : Ctx → Ctx → Psh
--   --   ⟦ Ø ⟧c, Δ = 𝟙 
--   --   ⟦ Γ `, A ⟧c, Δ = (⟦ Γ ⟧c, Δ) ⊗ (⟦ A ⟧, Δ )

--   -- mutual
--   --   reify : ∀ {Δ} {A} → (⟦ A ⟧, Δ) →̇ Nf A Δ
--   --   reify {A = ο} n = n
--   --   reify {A = A ⇒ B} n = lam (reify (n _ (drop ⊇-refl) (reflect (var here))))
--   --   reify {A = □ A} n = box {!!}

--   --   reflect : ∀ {Δ} {A} → Ne A Δ →̇ (⟦ A ⟧, Δ)
--   --   reflect {A = ο} n = lift n
--   --   reflect {A = A ⇒ B} n = λ Γ' Γ'⊇Γ → reflect {!!}
--   --   reflect {A = □ A} n = {!!}
-- -- -- natural transformations
-- -- _→'_ : (P Q : 𝒫) → Set
-- -- _→'_ P Q = ∀ {Γ} → (P .In Γ → Q .In Γ)


-- -- open import Data.Unit
-- -- open import Data.Product
-- --   using (_×_ ; proj₁ ; proj₂ ; _,_ ; Σ)


-- -- _×'_ : 𝒫 → 𝒫 → 𝒫
-- -- In (P ×' Q) Γ = (In P Γ) × (In Q Γ)
-- -- Wken (P ×' Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

-- -- 𝟙' : 𝒫
-- -- 𝟙' = record { In = λ _ → ⊤ ; Wken = λ Γ⊆Δ _ → tt }

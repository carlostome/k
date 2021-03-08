module IK.Calculus.DC where

  open import Data.Product
  open import Relation.Binary hiding (_⇒_)
  open import IK.Type public

  data Ctx : Set where
    []   : Ctx
    _`,_ : Ctx → Ty → Ctx
  
  data _⊆_ : Ctx → Ctx → Set where
    base : [] ⊆ []
    keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
    drop : ∀ {T Γ Δ} → Γ ⊆ Δ → Γ        ⊆ (Δ `, T)

  data _∈_ (A : Ty) : Ctx → Set where
    here : ∀ {Γ} → A ∈ (Γ `, A)
    there : ∀ {B Γ}  → A ∈ Γ → A ∈ (Γ `, B)

  postulate
    wken-var : ∀ {A} {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → A ∈ Γ₁ → A ∈ Γ₂

  ⊆-refl : Reflexive _⊆_
  ⊆-refl {[]} = base
  ⊆-refl {Γ `, x} = keep ⊆-refl

  ⊆-trans : Transitive _⊆_
  ⊆-trans x base = x
  ⊆-trans (keep x) (keep x₁) = keep (⊆-trans x x₁)
  ⊆-trans (drop x) (keep x₁) = drop (⊆-trans x x₁)
  ⊆-trans x (drop x₁) = drop (⊆-trans x x₁)

  ⊆-! : ∀ {Γ} → [] ⊆ Γ
  ⊆-! {[]} = base
  ⊆-! {Γ `, x} = drop ⊆-!

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

  wken : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢ A → Δ₂ ; Γ₂ ⊢ A
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t t₁) = app (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t) = lam (wken Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t) = box (wken base Δ₁⊆Δ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox t t₁) = letbox (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t₁)

  mutual
     data _;_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
       var   : ∀ {A}   → A ∈ Γ → Δ ; Γ ⊢Ne A
       app   : ∀ {A B} → Δ ; Γ ⊢Ne (A ⇒ B) → Δ ; Γ ⊢Nf A → Δ ; Γ ⊢Ne B
       letbox : ∀ {A B} → Δ ; Γ ⊢Ne (◻ A) → (Δ `, A) ; Γ ⊢Nf B → Δ ; Γ ⊢Ne B

     data _;_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
       lam : ∀ {A B} → Δ ; (Γ `, A) ⊢Nf B → Δ ; Γ ⊢Nf (A ⇒ B)
       box : ∀ {A} → [] ; Δ ⊢Nf A → Δ ; Γ ⊢Nf (◻ A)
       up : Δ ; Γ ⊢Ne 𝕓 → Δ ; Γ ⊢Nf 𝕓

     wkNe : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Ne A → Δ₂ ; Γ₂ ⊢Ne A
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox x t) = letbox (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ x) (wkNf (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t x) = app (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ x)

     wkNf : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Nf A → Δ₂ ; Γ₂ ⊢Nf A
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t) = lam (wkNf Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t) = box (wkNf base Δ₁⊆Δ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (up t) = up (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)

  postulate
     Ne⇒Nf : ∀ {A} {Δ} {Γ}→ Δ ; Γ ⊢Ne A → Δ ; Γ ⊢Nf A
     Nf⇒Tm : ∀ {A} {Δ} {Γ}→ Δ ; Γ ⊢Nf A → Δ ; Γ ⊢ A
    

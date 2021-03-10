module IK.Calculus.DC where

  open import Data.Product
  open import Relation.Binary hiding (_⇒_)
  open import IK.Type public

  data Ctx : Set where
    []   : Ctx
    _`,_ : Ctx → Ty → Ctx

  private
    variable
      Δ Γ : Ctx

  infixl 18 _`,_
  infix  17 _∈_
  infix  17 _⊆_
  infix  3  _;_⊢_
  infix  3  _;_⊢_∶_≈_

  data _⊆_ : Ctx → Ctx → Set where
    base : [] ⊆ []
    keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
    drop : ∀ {T Γ Δ} → Γ ⊆ Δ → Γ        ⊆ (Δ `, T)

  data _∈_ (A : Ty) : Ctx → Set where
    here : ∀ {Γ} → A ∈ (Γ `, A)
    there : ∀ {B Γ}  → A ∈ Γ → A ∈ (Γ `, B)

  wken-var : ∀ {A} {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → A ∈ Γ₁ → A ∈ Γ₂
  wken-var {Γ₁ = []} x ()
  wken-var {Γ₁ = Γ₁ `, a} (keep x₁) here = here
  wken-var {Γ₁ = Γ₁ `, a} (keep x₁) (there x₂) = there (wken-var x₁ x₂)
  wken-var {Γ₁ = Γ₁ `, a} (drop x₁) x₂ = there (wken-var x₁ x₂)

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

  ⊆-`, : ∀ {Γ a} → Γ ⊆ Γ `, a
  ⊆-`, = drop ⊆-refl

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

 
    fst : ∀ {A B} → Δ ; Γ ⊢ A ∧ B
                     ----------------
                  → Δ ; Γ ⊢ A

    snd : ∀ {A B} → Δ ; Γ ⊢ A ∧ B
                     ----------------
                  → Δ ; Γ ⊢ B

    prd : ∀ {A B} → Δ ; Γ ⊢ A
                  → Δ ; Γ ⊢ B
                     ----------------
                  → Δ ; Γ ⊢ A ∧ B

    box : ∀ {A} → [] ; Δ ⊢ A
                   -----------
                → Δ ; Γ ⊢ (◻ A)

    letbox : ∀ {A B} → Δ ; Γ ⊢ (◻ A) → (Δ `, A) ; Γ ⊢ B
                        -------------------------------
                     →           Δ ; Γ ⊢ B

  --8<-- (for convenience)
  p0 : a ∈ Γ `, a
  p0 = here

  p1 : a ∈ Γ `, a `, b
  p1 = there p0

  p2 : a ∈ Γ `, a `, b `, c
  p2 = there p1

  p3 : a ∈ Γ `, a `, b `, c `, d
  p3 = there p2

  v0 : Δ ; Γ `, a ⊢ a
  v0 = var p0

  v1 : Δ ; Γ `, a `, b ⊢ a
  v1 = var p1

  v2 : Δ ; Γ `, a `, b `, c ⊢ a
  v2 = var p2

  v3 : Δ ; Γ `, a `, b `, c `, d ⊢ a
  v3 = var p3
  -->8--

  --8<-- (examples)
  private
    □-pr : Δ ; Γ `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b)
    □-pr = letbox v1 (letbox v0 (box (prd v1 v0)))

    □-pr-inv : Δ ; Γ `, ◻ (a ∧ b) ⊢ ◻ a ∧ ◻ b
    □-pr-inv = letbox v0 (prd (box (fst v0)) (box (snd v0)))

    ex-1-lhs ex-1-rhs : [] ; [] `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b)
    ex-1-lhs = □-pr
    ex-1-rhs = letbox v0 (letbox v1 (box (prd v0 v1)))

    -- ex-1 : [] ; [] `, ◻ a `, ◻ b ⊢ ◻ (a ∧ b) ∶ lhs ≈ rhs
  -->8--

  wken : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢ A → Δ₂ ; Γ₂ ⊢ A
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t t₁) = app (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t) = lam (wken Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t) = box (wken base Δ₁⊆Δ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox t t₁) = letbox (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst t) = fst (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (snd t) = snd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (prd t t₁) = prd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)

  mutual
     data _;_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
       var   :  a ∈ Γ → Δ ; Γ ⊢Ne a
       app   :  Δ ; Γ ⊢Ne (a ⇒ b) → Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Ne b
       fst   :  Δ ; Γ ⊢Ne (a ∧ b) → Δ ; Γ ⊢Ne a
       snd   :  Δ ; Γ ⊢Ne (a ∧ b) → Δ ; Γ ⊢Ne b

     data _;_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
       lam : Δ ; (Γ `, a) ⊢Nf b → Δ ; Γ ⊢Nf (a ⇒ b)
       box : [] ; Δ ⊢Nf a → Δ ; Γ ⊢Nf (◻ a)
       letbox : Δ ; Γ ⊢Ne (◻ a) → (Δ `, a) ; Γ ⊢Nf b → Δ ; Γ ⊢Nf b
       up : Δ ; Γ ⊢Ne 𝕓 → Δ ; Γ ⊢Nf 𝕓
       prd : Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Nf b → Δ ; Γ ⊢Nf (a ∧ b)

     wkNe : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Ne A → Δ₂ ; Γ₂ ⊢Ne A
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t x) = app (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ x)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst t) = fst (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (snd t) = snd (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)

     wkNf : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Nf A → Δ₂ ; Γ₂ ⊢Nf A
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t) = lam (wkNf Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox x t) = letbox (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ x) (wkNf (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t) = box (wkNf base Δ₁⊆Δ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (up t) = up (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (prd x t) = prd (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ x) (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)

  Ne⇒Nf : ∀ {a} {Δ} {Γ}→ Δ ; Γ ⊢Ne a → Δ ; Γ ⊢Nf a
  Ne⇒Nf {𝕓} t = up t
  Ne⇒Nf {a ⇒ b} t = lam (Ne⇒Nf (app (wkNe ⊆-refl ⊆-`, t) (Ne⇒Nf (var here))))
  Ne⇒Nf {◻ a} t = letbox t (box (Ne⇒Nf (var here)))
  Ne⇒Nf {a ∧ b} t = prd (Ne⇒Nf (fst t)) (Ne⇒Nf (snd t))

  mutual
    Ne⇒Tm : ∀ {a} {Δ} {Γ}→ Δ ; Γ ⊢Ne a → Δ ; Γ ⊢ a
    Ne⇒Tm (var x) = var x
    Ne⇒Tm (fst x) = fst (Ne⇒Tm x)
    Ne⇒Tm (snd x) = snd (Ne⇒Tm x)
    Ne⇒Tm (app x x₁) = app (Ne⇒Tm x) (Nf⇒Tm x₁)

    Nf⇒Tm : ∀ {A} {Δ} {Γ}→ Δ ; Γ ⊢Nf A → Δ ; Γ ⊢ A
    Nf⇒Tm (lam x) = lam (Nf⇒Tm x)
    Nf⇒Tm (box x) = box (Nf⇒Tm x)
    Nf⇒Tm (letbox x x₁) = letbox (Ne⇒Tm x) (Nf⇒Tm x₁)
    Nf⇒Tm (up x) = Ne⇒Tm x
    Nf⇒Tm (prd t t₁) = prd (Nf⇒Tm t) (Nf⇒Tm t₁)

  _⊑_ : Ctx → Ctx → Set
  Γ₁ ⊑ Γ₂ = ∀ {A} → A ∈ Γ₁ → A ∈ Γ₂

  ⊑-refl : Reflexive _⊑_
  ⊑-refl x = x

  ⊑-drop : ∀ {T Γ Δ} → Γ ⊑ Δ → Γ ⊑ (Δ `, T)
  ⊑-drop x here = there (x here)
  ⊑-drop x (there x₁) = there (x (⊑-drop ⊑-refl x₁))

  ⊑-keep : ∀ {T Γ Δ} → Γ ⊑ Δ → (Γ `, T) ⊑ (Δ `, T)
  ⊑-keep x here = here
  ⊑-keep x (there x₁) = there (x x₁)

  wken-⊑ : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊑ Δ₂ → Γ₁ ⊑ Γ₂ → Δ₁ ; Γ₁ ⊢ A → Δ₂ ; Γ₂ ⊢ A
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (var x) = var (Γ₁⊑Γ₂ x)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (app t t₁) = app (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t₁)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (lam t) = lam (wken-⊑ Δ₁⊑Δ₂ (⊑-keep Γ₁⊑Γ₂) t)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (box t) = box (wken-⊑ (λ z → z) Δ₁⊑Δ₂ t)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (letbox t t₁) = letbox (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑ (⊑-keep Δ₁⊑Δ₂) Γ₁⊑Γ₂ t₁)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (fst t) = fst (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (snd t) = snd (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t)
  wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ (prd t t₁) = prd (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t₁)

  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Induction
  open import Induction.WellFounded

  size : ∀ {Γ} {A} {Δ} → Δ ; Γ ⊢ A → ℕ
  size (var x) = zero
  size (app x x₁) = 1 + size x + size x₁
  size (lam x) = 1 + size x
  size (box x) = 1 + size x
  size (letbox x x₁) = 1 + size x + size x₁
  size (fst t) = 1 + size t
  size (snd t) = 1 + size t
  size (prd t t₁) = 1 + size t + size t₁

  wken-⊑-size : ∀ {A} {Γ₁ Γ₂} {Δ₁ Δ₂} → (Δ₁⊑Δ₂ : Δ₁ ⊑ Δ₂) → (Γ₁⊑Γ₂ : Γ₁ ⊑ Γ₂)
                   →  (t : Δ₁ ; Γ₁ ⊢ A) → size (wken-⊑ Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) ≤ size t
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (var x) = z≤n
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (app t t₁) = s≤s (+-mono-≤ (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t₁))
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (lam t) = s≤s (wken-⊑-size Δ₁⊑Δ₂ (⊑-keep Γ₁⊑Γ₂) t)
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (box t) = s≤s (wken-⊑-size (λ z → z) Δ₁⊑Δ₂ t)
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (letbox t t₁) = s≤s (+-mono-≤ (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑-size (⊑-keep Δ₁⊑Δ₂) Γ₁⊑Γ₂ t₁))
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (fst t) = s≤s (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t)
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (snd t) = s≤s (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t)
  wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ (prd t t₁) = s≤s (+-mono-≤ (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t) (wken-⊑-size Δ₁⊑Δ₂ Γ₁⊑Γ₂ t₁))

  msubst : ∀ {Γ} {Δ} {A B} → [] ; Δ ⊢ A  → (t : (Δ `, A) ; Γ ⊢ B)  → Δ ; Γ ⊢ B
  msubst t u = aux t u (<′-wellFounded (size u))
    where aux : ∀ {Γ} {Δ} {A B} → [] ; Δ ⊢ A  → (t : (Δ `, A) ; Γ ⊢ B) → Acc (_<′_) (size t) → Δ ; Γ ⊢ B
          aux t (var x) (acc rs) = var x
          aux t (app u u₁) (acc rs) = app (aux t u (rs (size u) (s≤′s (≤⇒≤′ (m≤m+n (size u) (size u₁))))))
                                          (aux t u₁ (rs (size u₁) (s≤′s (≤⇒≤′ (m≤n+m (size u₁) (size u))))))
          aux t (lam u) (acc rs) = lam (aux t u (rs (size u) (s≤′s (≤⇒≤′ ≤-refl))))
          aux t (box u) (acc rs) = box (app (lam u) t)
          aux t (fst u) (acc rs) = fst (aux t u (rs (size u) (s≤′s (≤⇒≤′ ≤-refl))))
          aux t (snd u) (acc rs) = snd (aux t u (rs (size u) (s≤′s (≤⇒≤′ ≤-refl))))
          aux t (prd u u₁) (acc rs) = prd (aux t u (rs (size u) (s≤′s (≤⇒≤′ (m≤m+n (size u) (size u₁))))))
                                          (aux t u₁ (rs (size u₁) (s≤′s (≤⇒≤′ (m≤n+m (size u₁) (size u))))))
          aux t (letbox u u₁) (acc rs) = letbox ((aux t u (rs (size u) (s≤′s (≤⇒≤′ (m≤m+n (size u) (size u₁)))))))
                                         (aux (wken-⊑ ⊑-refl (⊑-drop ⊑-refl) t) (wken-⊑ p ⊑-refl u₁)
                                         (rs (size (wken-⊑ p ⊑-refl u₁)) (s≤′s (≤⇒≤′ (≤-trans (wken-⊑-size p ⊑-refl u₁) (m≤n+m (size u₁) (size u)))))))
              where p : ∀ {Δ} {A} {B} →  ((Δ `, B) `, A) ⊑ ((Δ `, A) `, B)
                    p here = there here
                    p (there here) = here
                    p (there (there x)) = there (there x)

  postulate
    subst : ∀ {Γ} {Δ} {A B} → Δ ; Γ ⊢ A → Δ ; (Γ `, A) ⊢ B → Δ ; Γ ⊢ B

  -- equational theory w/o commuting conversions?
  data _;_⊢_∶_≈_ (Δ Γ : Ctx) : (A : Ty) → (t₁ t₂ : Δ ; Γ ⊢ A) → Set where

    -- rules for ⇒
    ⇒-β : ∀ {A B} {t₁ : Δ ; (Γ `, A) ⊢ B} {t₂ : Δ ; Γ ⊢ A}
            →  Δ ; Γ ⊢ B ∶ app (lam t₁) t₂ ≈ subst t₂ t₁

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
            →  Δ ; Γ ⊢ B ∶ letbox (box t₁) t₂ ≈ msubst t₁ t₂

    □-η : ∀ {A} {t : Δ ; Γ ⊢ (◻ A)}
            → Δ ; Γ ⊢ (◻ A) ∶ t ≈ letbox t (box (var here))

    □-δ₁ : ∀ {A} {t₁ t₂ : [] ; Δ ⊢ A}
            → [] ; Δ ⊢ A ∶ t₁ ≈ t₂
            → Δ ; Γ ⊢ ◻ A ∶ box t₁ ≈ box t₂

    □-δ₂ : ∀ {A B} {t₁ t₂ : Δ ; Γ ⊢ (◻ A)} {u₁ u₂ : (Δ `, A) ; Γ ⊢ B}
            → Δ ; Γ ⊢ (◻ A)    ∶ t₁ ≈ t₂
            → (Δ `, A) ; Γ ⊢ B ∶ u₁ ≈ u₂
            → Δ ; Γ ⊢ B ∶ letbox t₁ u₁ ≈ letbox t₂ u₂

    -- commuting conversions?
    □-⇒ : ∀ {A B C} {t₁ : Δ ; Γ ⊢ (◻ A)} {t₂ : (Δ `, A) ; Γ ⊢ (B ⇒ C)} {t₃ : Δ ; Γ ⊢ B}
            →  Δ ; Γ ⊢ C ∶ app (letbox t₁ t₂) t₃ ≈  letbox t₁ (app t₂ (wken ⊆-`, ⊆-refl t₃))

    -- equivalence relation
    ≈-refl : ∀ {A} {t : Δ ; Γ  ⊢ A}
            →  Δ ; Γ ⊢ A ∶ t ≈ t

    ≈-sym : ∀ {A} {t₁ t₂ : Δ ; Γ ⊢ A}
            →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₂
            →  Δ ; Γ ⊢ A ∶ t₂ ≈ t₁

    ≈-trasn : ∀ {A} {t₁ t₂ t₃ : Δ ; Γ ⊢ A}
                →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₂
                →  Δ ; Γ ⊢ A ∶ t₂ ≈ t₃
                →  Δ ; Γ ⊢ A ∶ t₁ ≈ t₃

  _≈_ : ∀ {Δ Γ : Ctx} {A : Ty} → (t₁ t₂ : Δ ; Γ ⊢ A) → Set
  t₁ ≈ t₂ = _ ; _ ⊢ _ ∶ t₁ ≈ t₂

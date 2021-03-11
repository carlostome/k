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

  _++_ : Ctx → Ctx → Ctx
  Γ ++ [] = Γ
  Δ ++ (Γ `, A) = (Δ ++ Γ `, A)

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

  cut : ∀ {Γ} {Δ} {A B} {Γ'} → Δ ; Γ ⊢ A  → (t : Δ ; ((Γ `, A) ++ Γ') ⊢ B)
           → Δ ; (Γ ++ Γ') ⊢ B
  cut u (var x) = aux _ x u
    where aux : ∀ {Γ} {Δ} {A B} Γ' → B ∈ (Γ `, A) ++ Γ' → (u : Δ ; Γ ⊢ A) → Δ ; Γ ++ Γ' ⊢ B
          aux [] here u = u
          aux [] (there x) u = var x
          aux (Γ' `, a) here u = var here
          aux (Γ' `, a) (there x) u = wken ⊆-refl ⊆-`, (aux Γ' x u)
  cut u (app t t₁) = app (cut u t) (cut u t₁)
  cut u (lam t) = lam (cut u t)
  cut u (fst t) = fst (cut u t)
  cut u (snd t) = snd (cut u t)
  cut u (prd t t₁) = prd (cut u t) (cut u t₁)
  cut u (box t) = box t
  cut u (letbox t t₁) = letbox (cut u t) (cut (wken ⊆-`, ⊆-refl u) t₁)

  subst : ∀ {Γ} {Δ} {A B} → Δ ; Γ ⊢ A → Δ ; (Γ `, A) ⊢ B → Δ ; Γ ⊢ B
  subst u t = cut u t

  mcut : ∀ {Γ} {Δ} {A B} {Δ'} → [] ; Δ ⊢ A  → (t : ((Δ `, A) ++ Δ') ; Γ ⊢ B)
             → (Δ ++ Δ') ; Γ ⊢ B
  mcut t (var x) = var x
  mcut t (app u u₁) = app (mcut t u) (mcut t u₁)
  mcut t (lam u) = lam (mcut t u)
  mcut t (fst u) = fst (mcut t u)
  mcut t (snd u) = snd (mcut t u)
  mcut t (prd u u₁) = prd (mcut t u) (mcut t u₁)
  mcut t (box u) = box (cut t u)
  mcut t (letbox u u₁) = letbox (mcut t u) (mcut t u₁)

  msubst : ∀ {Γ} {Δ} {A B} → [] ; Δ ⊢ A  → (t : (Δ `, A) ; Γ ⊢ B)
               → Δ ; Γ ⊢ B
  msubst = mcut

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

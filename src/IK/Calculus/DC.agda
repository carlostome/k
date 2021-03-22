module IK.Calculus.DC where

  open import Relation.Binary hiding (_⇒_)
  open import Data.List as List using ([]; _∷_; List; _++_) public
  open import IK.Type public

  infixl 20 _,_
  infixl 18 _`,_
  infixl 18 _`,,_
  infix  4 _∈_
  infix  4 _⊆_
  infix  3  _;_⊢_
  infix  3  _;_⊢Ne_
  infix  3  _;_⊢Nf_

  Ctx : Set
  Ctx = List Ty

  pattern _`,_ as a = a ∷ as

  _`,,_ : Ctx → Ctx → Ctx
  Γ `,, Γ' = Γ' ++ Γ


  variable
    Δ Δ' Δ'' : Ctx
    Γ Γ' Γ'' : Ctx
    Ε Ε' Ε'' : Ctx

  data _⊆_ : Ctx → Ctx → Set where
    base : [] ⊆ []
    keep : ∀ {T Γ Δ} → Γ ⊆ Δ → Γ `, T ⊆ Δ `, T
    drop : ∀ {T Γ Δ} → Γ ⊆ Δ → Γ      ⊆ Δ `, T

  data _∈_ (A : Ty) : Ctx → Set where
    here : ∀ {Γ} → A ∈ Γ `, A
    there : ∀ {B Γ}  → A ∈ Γ → A ∈ Γ `, B

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

  --8<-- (for convenience)
  ⊆-! : ∀ {Γ} → [] ⊆ Γ
  ⊆-! {[]}     = base
  ⊆-! {Γ `, a} = drop ⊆-!

  ⊆-`, : ∀ {Γ a} → Γ ⊆ Γ `, a
  ⊆-`, = drop ⊆-refl

  ⊆-`,, : Γ ⊆ Γ `,, Δ
  ⊆-`,, {Δ = []}     = ⊆-refl
  ⊆-`,, {Δ = Δ `, a} = drop ⊆-`,,

  ⊆-keeps : Γ ⊆ Γ' → Γ `,, Δ ⊆ Γ' `,, Δ
  ⊆-keeps {Δ = []}     Γ⊆Γ' = Γ⊆Γ'
  ⊆-keeps {Δ = Δ `, a} Γ⊆Γ' = keep (⊆-keeps Γ⊆Γ')
  -->8--

  data _;_⊢_ (Δ Γ : Ctx) : Ty → Set where
    var  : (x : a ∈ Γ)
           -----------
         → Δ ; Γ ⊢ a

    app : (t : Δ ; Γ ⊢ a ⇒ b)
        → (u : Δ ; Γ ⊢ a)
          -------------------
        →      Δ ; Γ ⊢ b

    lam : (t : Δ ; Γ `, a ⊢ b)
          -----------------------
        →      Δ ; Γ      ⊢ a ⇒ b

    fst : (t : Δ ; Γ ⊢ a ∧ b)
          -------------------
        →      Δ ; Γ ⊢ a

    snd : (t : Δ ; Γ ⊢ a ∧ b)
          -------------------
        →      Δ ; Γ ⊢ b

    prd : (t : Δ ; Γ ⊢ a)
        → (u : Δ ; Γ ⊢ b)
          ------------------
        →      Δ ; Γ ⊢ a ∧ b

    box : (t : [] ; Δ ⊢ a)
          -----------------
        →      Δ  ; Γ ⊢ ◻ a

    letbox_In_ : (t : Δ      ; Γ ⊢ ◻ a)
               → (u : Δ `, a ; Γ ⊢ b)
                 ----------------------
               →      Δ      ; Γ ⊢ b

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

  wken : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢ A → Δ₂ ; Γ₂ ⊢ A
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x) = var (wken-var Γ₁⊆Γ₂ x)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t t₁) = app (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t) = lam (wken Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t) = box (wken base Δ₁⊆Δ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox t In t₁) = letbox (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) In (wken (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst t) = fst (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (snd t) = snd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (prd t t₁) = prd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)

  --8<-- (for convenience)
  mwken : ∀ {A} {Δ Δ'} {Γ} → Δ ⊆ Δ' → Δ ; Γ ⊢ A → Δ' ; Γ ⊢ A
  mwken Δ⊆Δ' = wken Δ⊆Δ' ⊆-refl

  lwken : ∀ {A} {Δ} {Γ Γ'} → Γ ⊆ Γ' → Δ ; Γ ⊢ A → Δ ; Γ' ⊢ A
  lwken Γ⊆Γ' = wken ⊆-refl Γ⊆Γ'
  --8>--

  mutual
     data _;_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
       var : a ∈ Γ → Δ ; Γ ⊢Ne a
       app : Δ ; Γ ⊢Ne a ⇒ b → Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Ne b
       fst : Δ ; Γ ⊢Ne a ∧ b → Δ ; Γ ⊢Ne a
       snd : Δ ; Γ ⊢Ne a ∧ b → Δ ; Γ ⊢Ne b

     data _;_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
       up         : Δ ; Γ ⊢Ne 𝕓 → Δ ; Γ ⊢Nf 𝕓
       lam        : Δ ; Γ `, a ⊢Nf b → Δ ; Γ ⊢Nf a ⇒ b
       prd        : Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Nf b → Δ ; Γ ⊢Nf a ∧ b
       box        : [] ; Δ ⊢Nf a → Δ ; Γ ⊢Nf ◻ a
       letbox_In_ : Δ ; Γ ⊢Ne ◻ a → Δ `, a ; Γ ⊢Nf ◻ b → Δ ; Γ ⊢Nf ◻ b

  mutual
     wkNe : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Ne A → Δ₂ ; Γ₂ ⊢Ne A
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x)   = var (wken-var Γ₁⊆Γ₂ x)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t u) = app (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ u)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst t)   = fst (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
     wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ (snd t)   = snd (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)

     wkNf : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Nf A → Δ₂ ; Γ₂ ⊢Nf A
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (up t)          = up (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t)         = lam (wkNf Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (prd t u)       = prd (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ u)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t)         = box (wkNf base Δ₁⊆Δ₂ t)
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox t In u) = letbox wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ t In wkNf (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ u

  --8<-- (for convenience)
  mwkNf : ∀ {A} {Δ Δ'} {Γ} → Δ ⊆ Δ' → Δ ; Γ ⊢Nf A → Δ' ; Γ ⊢Nf A
  mwkNf Δ⊆Δ' = wkNf Δ⊆Δ' ⊆-refl

  lwkNf : ∀ {A} {Δ} {Γ Γ'} → Γ ⊆ Γ' → Δ ; Γ ⊢Nf A → Δ ; Γ' ⊢Nf A
  lwkNf Γ⊆Γ' = wkNf ⊆-refl Γ⊆Γ'

  mwkNe : ∀ {A} {Δ Δ'} {Γ} → Δ ⊆ Δ' → Δ ; Γ ⊢Ne A → Δ' ; Γ ⊢Ne A
  mwkNe Δ⊆Δ' = wkNe Δ⊆Δ' ⊆-refl

  lwkNe : ∀ {A} {Δ} {Γ Γ'} → Γ ⊆ Γ' → Δ ; Γ ⊢Ne A → Δ ; Γ' ⊢Ne A
  lwkNe Γ⊆Γ' = wkNe ⊆-refl Γ⊆Γ'
  --8>--

  Ne⇒Nf : ∀ {a} {Δ} {Γ}→ Δ ; Γ ⊢Ne a → Δ ; Γ ⊢Nf a
  Ne⇒Nf {𝕓}     t = up t
  Ne⇒Nf {a ⇒ b} t = lam (Ne⇒Nf (app (wkNe ⊆-refl ⊆-`, t) (Ne⇒Nf (var here))))
  Ne⇒Nf {a ∧ b} t = prd (Ne⇒Nf (fst t)) (Ne⇒Nf (snd t))
  Ne⇒Nf {◻ a}   t = letbox t In box (Ne⇒Nf (var here))

  mutual
    Ne⇒Tm : ∀ {a} {Δ} {Γ}→ Δ ; Γ ⊢Ne a → Δ ; Γ ⊢ a
    Ne⇒Tm (var x)   = var x
    Ne⇒Tm (fst t)   = fst (Ne⇒Tm t)
    Ne⇒Tm (snd t)   = snd (Ne⇒Tm t)
    Ne⇒Tm (app t u) = app (Ne⇒Tm t) (Nf⇒Tm u)

    Nf⇒Tm : ∀ {A} {Δ} {Γ}→ Δ ; Γ ⊢Nf A → Δ ; Γ ⊢ A
    Nf⇒Tm (up n)          = Ne⇒Tm n
    Nf⇒Tm (lam t)         = lam (Nf⇒Tm t)
    Nf⇒Tm (prd t u)       = prd (Nf⇒Tm t) (Nf⇒Tm u)
    Nf⇒Tm (box t)         = box (Nf⇒Tm t)
    Nf⇒Tm (letbox t In u) = letbox Ne⇒Tm t In Nf⇒Tm u

  data LSub (Δ : Ctx) (Γ' : Ctx) : Ctx → Set where
    !   : LSub Δ Γ' []
    _,_ : (σ : LSub Δ Γ' Γ) → (t : Δ ; Γ' ⊢ a) → LSub Δ Γ' (Γ `, a)

  wken-lsub : Δ ⊆ Δ' → Γ ⊆ Γ' → LSub Δ Γ Ε → LSub Δ' Γ' Ε
  wken-lsub Δ⊆Δ' Γ⊆Γ' !       = !
  wken-lsub Δ⊆Δ' Γ⊆Γ' (σ , t) = wken-lsub Δ⊆Δ' Γ⊆Γ' σ , wken Δ⊆Δ' Γ⊆Γ' t

  --8<-- (convenience)
  mwken-lsub : Δ ⊆ Δ' → LSub Δ Γ Ε → LSub Δ' Γ Ε
  mwken-lsub Δ⊆Δ' = wken-lsub Δ⊆Δ' ⊆-refl

  lwken-lsub : Γ ⊆ Γ' → LSub Δ Γ Ε → LSub Δ Γ' Ε
  lwken-lsub Γ⊆Γ' = wken-lsub ⊆-refl Γ⊆Γ'
  -->8--

  wken-to-lsub : Γ ⊆ Γ' → LSub Δ Γ' Γ
  wken-to-lsub base        = !
  wken-to-lsub (keep Γ⊆Γ') = wken-to-lsub (drop Γ⊆Γ') , v0
  wken-to-lsub (drop Γ⊆Γ') = lwken-lsub ⊆-`, (wken-to-lsub Γ⊆Γ')

  lsubst-var : LSub Δ Γ' Γ → a ∈ Γ → Δ ; Γ' ⊢ a
  lsubst-var (σ , t) here      = t
  lsubst-var (σ , t) (there v) = lsubst-var σ v

  lsubst : LSub Δ Γ' Γ → Δ ; Γ ⊢ b → Δ ; Γ' ⊢ b
  lsubst σ (var v)         = lsubst-var σ v
  lsubst σ (app t u)       = app (lsubst σ t) (lsubst σ u)
  lsubst σ (lam t)         = lam (lsubst (lwken-lsub ⊆-`, σ , v0) t)
  lsubst σ (fst t)         = fst (lsubst σ t)
  lsubst σ (snd t)         = snd (lsubst σ t)
  lsubst σ (prd t u)       = prd (lsubst σ t) (lsubst σ u)
  lsubst _ (box t)         = box t
  lsubst σ (letbox t In u) = letbox (lsubst σ t) In (lsubst (mwken-lsub ⊆-`, σ) u)

  --8<-- (for convenience)
  lsub-refl : LSub Δ Γ Γ
  lsub-refl = wken-to-lsub ⊆-refl

  lsub-`, : LSub Δ (Γ `, a) Γ
  lsub-`, = wken-to-lsub ⊆-`,

  lsub-trans : LSub Δ Γ Γ' → LSub Δ Γ' Γ'' → LSub Δ Γ Γ''
  lsub-trans σ' !       = !
  lsub-trans σ' (σ , t) = lsub-trans σ' σ , lsubst σ' t

  lsub-swap : LSub Δ (Γ `, b `, a) (Γ `, a `, b)
  lsub-swap = lsub-trans lsub-`, lsub-`, , v0 , v1

  lsub-keep : LSub Δ Γ Γ' → LSub Δ (Γ `, a) (Γ' `, a)
  lsub-keep σ = lsub-trans lsub-`, σ , v0

  lsub-keeps : LSub Δ Γ Γ' → LSub Δ (Γ `,, Ε) (Γ' `,, Ε)
  lsub-keeps {Ε = []}     σ = σ
  lsub-keeps {Ε = Ε `, a} σ = lsub-keep (lsub-keeps σ)
  -->8--

  --8<-- (for convenience)
  lsubst-here : Δ ; Γ ⊢ a → Δ ; Γ `, a ⊢ b → Δ ; Γ ⊢ b
  lsubst-here u t = lsubst (lsub-refl , u) t
  -->8--

  cut : ∀ {Γ} {Δ} {A B} {Γ'} → Δ ; Γ ⊢ A  → (t : Δ ; Γ `, A `,, Γ' ⊢ B)
           → Δ ; Γ `,, Γ' ⊢ B
  cut u t = lsubst (lsub-keeps (lsub-refl , u)) t

  data MSub (Δ : Ctx) : (Δ' : Ctx) → Set where -- = Sub [] Δ Δ'
    !   : MSub Δ []
    _,_ : (σ : MSub Δ Δ') → (t : [] ; Δ ⊢ a) → MSub Δ (Δ' `, a)

  msub-to-lsub : MSub Δ' Δ → LSub [] Δ' Δ
  msub-to-lsub ! = !
  msub-to-lsub (σ , t) = msub-to-lsub σ , t

  lsub-to-msub : LSub [] Δ' Δ → MSub Δ' Δ
  lsub-to-msub ! = !
  lsub-to-msub (σ , t) = lsub-to-msub σ , t

  mwken-msub : Δ ⊆ Δ' → MSub Δ Ε → MSub Δ' Ε
  mwken-msub Δ⊆Δ' !       = !
  mwken-msub Δ⊆Δ' (σ , t) = mwken-msub Δ⊆Δ' σ , lwken Δ⊆Δ' t

  wken-to-msub : Δ ⊆ Δ' → MSub Δ' Δ
  wken-to-msub base        = !
  wken-to-msub (keep Δ⊆Δ') = wken-to-msub (drop Δ⊆Δ') , v0
  wken-to-msub (drop Δ⊆Δ') = mwken-msub ⊆-`, (wken-to-msub Δ⊆Δ')

  msubst : MSub Δ' Δ → Δ ; Γ ⊢ b → Δ' ; Γ ⊢ b
  msubst σ (var v)         = var v
  msubst σ (app t u)       = app (msubst σ t) (msubst σ u)
  msubst σ (lam t)         = lam (lsubst (lsub-keep lsub-refl) (msubst σ t))
  msubst σ (fst t)         = fst (msubst σ t)
  msubst σ (snd t)         = snd (msubst σ t)
  msubst σ (prd t u)       = prd (msubst σ t) (msubst σ u)
  msubst σ (box t)         = box (lsubst (msub-to-lsub σ) t)
  msubst σ (letbox t In u) = letbox (msubst σ t) In (msubst (mwken-msub ⊆-`, σ , v0) u)

  --8<-- (for convenience)
  msub-refl : MSub Δ Δ
  msub-refl = wken-to-msub ⊆-refl

  msub-`, : MSub (Δ `, a) Δ
  msub-`, = wken-to-msub ⊆-`,

  msub-trans : MSub Δ Δ' → MSub Δ' Δ'' → MSub Δ Δ''
  msub-trans σ' ! = !
  msub-trans σ' (σ , t) = msub-trans σ' σ , lsubst (msub-to-lsub σ') t

  msub-keep : MSub Δ Δ' → MSub (Δ `, a) (Δ' `, a)
  msub-keep σ = mwken-msub ⊆-`, σ , v0

  msub-keeps : MSub Δ Δ' → MSub (Δ `,, Ε) (Δ' `,, Ε)
  msub-keeps {Ε = []} σ = σ
  msub-keeps {Ε = Ε `, a} σ =  msub-keep (msub-keeps σ)
  -->8--

  --8<-- (for convenience)
  msub-swap : MSub (Δ `, b `, a) (Δ `, a `, b)
  msub-swap = lsub-to-msub lsub-swap

  msubst-here : [] ; Δ ⊢ a → (Δ `, a) ; Γ ⊢ b → Δ ; Γ ⊢ b
  msubst-here u t = msubst (msub-refl , u) t
  -->8--

  mcut : [] ; Δ ⊢ a  → (t : Δ `, a `,, Δ' ; Γ ⊢ b) → Δ `,, Δ' ; Γ ⊢ b
  mcut t u = msubst (msub-keeps (msub-refl , t)) u

  -- Δ ; Γ ⊢ ◻ a → Σ λ Δ' → Δ ⊆ Δ' × Sub Δ Γ (◻ Δ') × [] ; Δ' ⊢ a

  --8<--
  data _;_⊢Nes_  (Δ Γ : Ctx) : Ctx → Set where
    []  : Δ ; Γ ⊢Nes []
    _∷_ : Δ ; Γ ⊢Ne a → Δ ; Γ ⊢Nes Γ' → Δ ; Γ ⊢Nes (Γ' `, a)

  data _;_⊢Nfs_  (Δ Γ : Ctx) : Ctx → Set where
    []  : Δ ; Γ ⊢Nfs []
    _∷_ : Δ ; Γ ⊢Ne a → Δ ; Γ ⊢Nfs Γ' → Δ ; Γ ⊢Nfs (Γ' `, a)

  wkNes : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Nes A → Δ₂ ; Γ₂ ⊢Nes A
  wkNes Δ₁⊆Δ₂ Γ₁⊆Γ₂ [] = []
  wkNes Δ₁⊆Δ₂ Γ₁⊆Γ₂ (n ∷ ns) = wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ n ∷ wkNes Δ₁⊆Δ₂ Γ₁⊆Γ₂ ns

  wkNfs : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢Nfs A → Δ₂ ; Γ₂ ⊢Nfs A
  wkNfs Δ₁⊆Δ₂ Γ₁⊆Γ₂ [] = []
  wkNfs Δ₁⊆Δ₂ Γ₁⊆Γ₂ (n ∷ ns) = wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ n ∷ wkNfs Δ₁⊆Δ₂ Γ₁⊆Γ₂ ns

  mwkNfs : ∀ {A} {Δ Δ'} {Γ} → Δ ⊆ Δ' → Δ ; Γ ⊢Nfs A → Δ' ; Γ ⊢Nfs A
  mwkNfs Δ⊆Δ' = wkNfs Δ⊆Δ' ⊆-refl

  lwkNfs : ∀ {A} {Δ} {Γ Γ'} → Γ ⊆ Γ' → Δ ; Γ ⊢Nfs A → Δ ; Γ' ⊢Nfs A
  lwkNfs Γ⊆Γ' = wkNfs ⊆-refl Γ⊆Γ'

  mwkNes : ∀ {A} {Δ Δ'} {Γ} → Δ ⊆ Δ' → Δ ; Γ ⊢Nes A → Δ' ; Γ ⊢Nes A
  mwkNes Δ⊆Δ' = wkNes Δ⊆Δ' ⊆-refl

  lwkNes : ∀ {A} {Δ} {Γ Γ'} → Γ ⊆ Γ' → Δ ; Γ ⊢Nes A → Δ ; Γ' ⊢Nes A
  lwkNes Γ⊆Γ' = wkNes ⊆-refl Γ⊆Γ'

  vars : Δ ; Γ ⊢Nes Γ
  vars {Γ = []}     = []
  vars {Γ = Γ `, a} = var here ∷ lwkNes ⊆-`, vars
  -->8--

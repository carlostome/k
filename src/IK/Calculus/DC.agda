module IK.Calculus.DC where

  open import Relation.Binary hiding (_⇒_)

  open import IK.Type public

  data Ctx : Set where
    []   : Ctx
    _`,_ : (Γ : Ctx) → (a : Ty) → Ctx

  variable
    Δ Δ' Δ'' : Ctx
    Γ Γ' Γ'' : Ctx
    Ε Ε' Ε'' : Ctx

  _++_ : Ctx → Ctx → Ctx
  Γ ++ [] = Γ
  Δ ++ (Γ `, A) = Δ ++ Γ `, A

  infixl 20 _,_
  infixl 20 _++_
  infixl 18 _`,_
  infix  17 _∈_
  infix  17 _⊆_
  infix  3  _;_⊢_

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
  ⊆-! {[]} = base
  ⊆-! {Γ `, x} = drop ⊆-!

  ⊆-`, : ∀ {Γ a} → Γ ⊆ Γ `, a
  ⊆-`, = drop ⊆-refl

  ⊆-++ : Γ ⊆ Γ ++ Δ
  ⊆-++ {Δ = []}     = ⊆-refl
  ⊆-++ {Δ = Δ `, a} = drop ⊆-++

  ⊆-keeps : Γ ⊆ Γ' → Γ ++ Δ ⊆ Γ' ++ Δ
  ⊆-keeps {Δ = []} Γ⊆Γ'     = Γ⊆Γ'
  ⊆-keeps {Δ = Δ `, a} Γ⊆Γ' = keep (⊆-keeps Γ⊆Γ')
  -->8--

  data _;_⊢_ (Δ Γ : Ctx) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ
                    ---------
                 → Δ ; Γ ⊢ A

    app : ∀ {A B} → Δ ; Γ ⊢ A ⇒ B → Δ ; Γ ⊢ A
                     --------------------------
                  →          Δ ; Γ ⊢ B

    lam : ∀ {A B} → Δ ; Γ `, A ⊢ B
                     ----------------
                  → Δ ; Γ ⊢ A ⇒ B

 
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

    letbox_In_ : ∀ {A B} → Δ ; Γ ⊢ (◻ A) → (Δ `, A) ; Γ ⊢ B
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
       var   :  a ∈ Γ → Δ ; Γ ⊢Ne a
       app   :  Δ ; Γ ⊢Ne (a ⇒ b) → Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Ne b
       fst   :  Δ ; Γ ⊢Ne (a ∧ b) → Δ ; Γ ⊢Ne a
       snd   :  Δ ; Γ ⊢Ne (a ∧ b) → Δ ; Γ ⊢Ne b

     data _;_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
       lam : Δ ; (Γ `, a) ⊢Nf b → Δ ; Γ ⊢Nf (a ⇒ b)
       box : [] ; Δ ⊢Nf a → Δ ; Γ ⊢Nf (◻ a)
       letbox : Δ ; Γ ⊢Ne (◻ a) → (Δ `, a) ; Γ ⊢Nf (◻ b) → Δ ; Γ ⊢Nf (◻ b)
       up : Δ ; Γ ⊢Ne 𝕓 → Δ ; Γ ⊢Nf 𝕓
       prd : Δ ; Γ ⊢Nf a → Δ ; Γ ⊢Nf b → Δ ; Γ ⊢Nf (a ∧ b)

  mutual
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
    Nf⇒Tm (letbox x x₁) = letbox (Ne⇒Tm x) In (Nf⇒Tm x₁)
    Nf⇒Tm (up x) = Ne⇒Tm x
    Nf⇒Tm (prd t t₁) = prd (Nf⇒Tm t) (Nf⇒Tm t₁)

  data Sub (Δ : Ctx) (Γ' : Ctx) : Ctx → Set where
    !   : Sub Δ Γ' []
    _,_ : (σ : Sub Δ Γ' Γ) → (t : Δ ; Γ' ⊢ a) → Sub Δ Γ' (Γ `, a)

  wken-sub : Δ ⊆ Δ' → Γ ⊆ Γ' → Sub Δ Γ Ε → Sub Δ' Γ' Ε
  wken-sub Δ⊆Δ' Γ⊆Γ' !       = !
  wken-sub Δ⊆Δ' Γ⊆Γ' (σ , t) = wken-sub Δ⊆Δ' Γ⊆Γ' σ , wken Δ⊆Δ' Γ⊆Γ' t

  --8<-- (convenience)
  mwken-sub : Δ ⊆ Δ' → Sub Δ Γ Ε → Sub Δ' Γ Ε
  mwken-sub Δ⊆Δ' = wken-sub Δ⊆Δ' ⊆-refl

  lwken-sub : Γ ⊆ Γ' → Sub Δ Γ Ε → Sub Δ Γ' Ε
  lwken-sub Γ⊆Γ' = wken-sub ⊆-refl Γ⊆Γ'
  -->8--

  wken-to-sub : Γ ⊆ Γ' → Sub Δ Γ' Γ
  wken-to-sub base        = !
  wken-to-sub (keep Γ⊆Γ') = wken-to-sub (drop Γ⊆Γ') , v0
  wken-to-sub (drop Γ⊆Γ') = lwken-sub ⊆-`, (wken-to-sub Γ⊆Γ')

  subst-var : Sub Δ Γ' Γ → a ∈ Γ → Δ ; Γ' ⊢ a
  subst-var (σ , t) here      = t
  subst-var (σ , t) (there v) = subst-var σ v

  subst : Sub Δ Γ' Γ → Δ ; Γ ⊢ b → Δ ; Γ' ⊢ b
  subst σ (var v)      = subst-var σ v
  subst σ (app t u)    = app (subst σ t) (subst σ u)
  subst σ (lam t)      = lam (subst (lwken-sub ⊆-`, σ , v0) t)
  subst σ (fst t)      = fst (subst σ t)
  subst σ (snd t)      = snd (subst σ t)
  subst σ (prd t u)    = prd (subst σ t) (subst σ u)
  subst _ (box t)      = box t
  subst σ (letbox t In u) = letbox (subst σ t) In (subst (mwken-sub ⊆-`, σ) u)

  --8<-- (for convenience)
  sub-refl : Sub Δ Γ Γ
  sub-refl = wken-to-sub ⊆-refl

  sub-`, : Sub Δ (Γ `, a) Γ
  sub-`, = wken-to-sub ⊆-`,

  sub-trans : Sub Δ Γ Γ' → Sub Δ Γ' Γ'' → Sub Δ Γ Γ''
  sub-trans σ' !       = !
  sub-trans σ' (σ , t) = sub-trans σ' σ , subst σ' t

  sub-swap : Sub Δ (Γ `, b `, a) (Γ `, a `, b) 
  sub-swap = sub-trans sub-`, sub-`, , v0 , v1

  sub-keep : Sub Δ Γ Γ' → Sub Δ (Γ `, a) (Γ' `, a)
  sub-keep σ = sub-trans sub-`, σ , v0

  sub-keeps : Sub Δ Γ Γ' → Sub Δ (Γ ++ Ε) (Γ' ++ Ε)
  sub-keeps {Ε = []}     σ = σ
  sub-keeps {Ε = Ε `, a} σ = sub-keep (sub-keeps σ)
  -->8--

  --8<-- (for convenience)
  subst-here : Δ ; Γ ⊢ a → Δ ; Γ `, a ⊢ b → Δ ; Γ ⊢ b
  subst-here u t = subst (sub-refl , u) t
  -->8--

  cut : ∀ {Γ} {Δ} {A B} {Γ'} → Δ ; Γ ⊢ A  → (t : Δ ; ((Γ `, A) ++ Γ') ⊢ B)
           → Δ ; (Γ ++ Γ') ⊢ B
  cut u t = subst (sub-keeps (sub-refl , u)) t

  data MSub (Δ : Ctx) : (Δ' : Ctx) → Set where -- = Sub [] Δ Δ'
    !   : MSub Δ []
    _,_ : (σ : MSub Δ Δ') → (t : [] ; Δ ⊢ a) → MSub Δ (Δ' `, a)

  msub-to-sub : MSub Δ' Δ → Sub [] Δ' Δ
  msub-to-sub ! = !
  msub-to-sub (σ , t) = msub-to-sub σ , t

  sub-to-msub : Sub [] Δ' Δ → MSub Δ' Δ 
  sub-to-msub ! = !
  sub-to-msub (σ , t) = sub-to-msub σ , t

  wken-msub : Δ ⊆ Δ' → MSub Δ Ε → MSub Δ' Ε
  wken-msub Δ⊆Δ' !       = !
  wken-msub Δ⊆Δ' (σ , t) = wken-msub Δ⊆Δ' σ , lwken Δ⊆Δ' t

  wken-to-msub : Δ ⊆ Δ' → MSub Δ' Δ
  wken-to-msub base        = !
  wken-to-msub (keep Δ⊆Δ') = wken-to-msub (drop Δ⊆Δ') , v0
  wken-to-msub (drop Δ⊆Δ') = wken-msub ⊆-`, (wken-to-msub Δ⊆Δ')

  msubst : MSub Δ' Δ → Δ ; Γ ⊢ b → Δ' ; Γ ⊢ b
  msubst σ (var v)      = var v
  msubst σ (app t u)    = app (msubst σ t) (msubst σ u)
  msubst σ (lam t)      = lam (subst (sub-keep sub-refl) (msubst σ t))
  msubst σ (fst t)      = fst (msubst σ t)
  msubst σ (snd t)      = snd (msubst σ t)
  msubst σ (prd t u)    = prd (msubst σ t) (msubst σ u)
  msubst σ (box t)      = box (subst (msub-to-sub σ) t)
  msubst σ (letbox t In u) = letbox (msubst σ t) In (msubst ((wken-msub ⊆-`, σ) , v0) u)

  -- --8<-- (for convenience)
  msub-refl : MSub Δ Δ 
  msub-refl = wken-to-msub ⊆-refl

  msub-`, : MSub (Δ `, a) Δ
  msub-`, = wken-to-msub ⊆-`,

  msub-trans : MSub Δ Δ' → MSub Δ' Δ'' → MSub Δ Δ''
  msub-trans σ' ! = !
  msub-trans σ' (σ , t) = msub-trans σ' σ , subst (msub-to-sub σ') t

  msub-keep : MSub Δ Δ' → MSub (Δ `, a) (Δ' `, a)
  msub-keep σ = wken-msub ⊆-`, σ , v0

  msub-keeps : MSub Δ Δ' → MSub (Δ ++ Ε) (Δ' ++ Ε)
  msub-keeps {Ε = []} σ = σ
  msub-keeps {Ε = Ε `, a} σ = msub-keep (msub-keeps σ)
  -- -->8--

  --8<-- (for convenience)
  msub-swap : MSub (Δ `, b `, a) (Δ `, a `, b) 
  msub-swap = sub-to-msub sub-swap

  msubst-here : [] ; Δ ⊢ a → (Δ `, a) ; Γ ⊢ b → Δ ; Γ ⊢ b
  msubst-here u t = msubst (msub-refl , u) t
  -->8--

  mcut : [] ; Δ ⊢ a  → (t : (Δ `, a) ++ Δ' ; Γ ⊢ b) → Δ ++ Δ' ; Γ ⊢ b
  mcut t u = msubst (msub-keeps (msub-refl , t)) u

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

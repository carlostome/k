module IK.Calculus.DC where

  open import Relation.Binary hiding (_⇒_)
  open import Data.List as List using ([]; _∷_; List; _++_) public
  open import Data.List.Membership.Propositional
    using (_∈_) public
  open import Data.List.Relation.Unary.Any as Any
    using (there) public
  open import Data.List.Relation.Binary.Sublist.Propositional
    renaming (lookup to wken-var) public
  open import Data.List.Relation.Binary.Sublist.Propositional.Properties public
  open import Relation.Binary.PropositionalEquality
    using (refl)
  open import Data.List.Relation.Unary.All as All hiding (here; there)
    renaming (lookup to lsubst-var)
  open import Data.List.Relation.Unary.All.Properties hiding (++⁺)
  import Data.List.Relation.Unary.All.Properties as All renaming (++⁺ to ++)
  open import IK.Type public

  infixl 20 _,_
  infixl 18 _`,_
  infixl 18 _`,,_
  infix  3  _;_⊢_
  infix  3  _;_⊢Ne_
  infix  3  _;_⊢Nf_

  Ctx : Set
  Ctx = List Ty

  pattern _`,_ as a = a ∷ as

  _`,,_ : Ctx → Ctx → Ctx
  Γ `,, Γ' = Γ' ++ Γ

  pattern here = Any.here refl

  variable
    Δ Δ' Δ'' : Ctx
    Γ Γ' Γ'' : Ctx
    Ε Ε' Ε'' : Ctx

  --8<-- (for convenience)
  pattern keep Γ⊆Γ' = refl ∷ Γ⊆Γ' -- : Γ ⊆ Γ' → Γ `, a ⊆ Γ' `, a

  pattern drop Γ⊆Γ' = _ ∷ʳ Γ⊆Γ'   -- : Γ ⊆ Γ' → Γ ⊆ Γ' `, a

  ⊆-! : [] ⊆ Γ
  ⊆-! = minimum _

  ⊆-`, : Γ ⊆ Γ `, a
  ⊆-`, = drop ⊆-refl

  ⊆-`,,ʳ : Γ ⊆ Γ `,, Δ
  ⊆-`,,ʳ = ++⁺ˡ _ ⊆-refl

  ⊆-`,, = ⊆-`,,ʳ

  ⊆-`,,ˡ : Γ ⊆ Δ `,, Γ
  ⊆-`,,ˡ = ++⁺ʳ _ ⊆-refl

  ⊆-keeps : Γ ⊆ Γ' → Γ `,, Δ ⊆ Γ' `,, Δ
  ⊆-keeps Γ⊆Γ' = ++⁺ ⊆-refl Γ⊆Γ'
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
  ◻s : Ctx → Ctx
  ◻s Γ = List.map ◻_ Γ

  mvar : (x : a ∈ Δ) → Δ ; Γ ⊢ ◻ a
  mvar x = box (var x)
  -->8--

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

  mv0 : Δ `, a ; Γ ⊢ ◻ a
  mv0 = mvar p0

  mv1 : Δ `, a `, b ; Γ ⊢ ◻ a
  mv1 = mvar p1

  mv2 : Δ `, a `, b `, c ; Γ ⊢ ◻ a
  mv2 = mvar p2

  mv3 : Δ `, a `, b `, c `, d ; Γ ⊢ ◻ a
  mv3 = mvar p3
  -->8--

  wken : ∀ {A} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Δ₁ ; Γ₁ ⊢ A → Δ₂ ; Γ₂ ⊢ A
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (var x)          = var (wken-var Γ₁⊆Γ₂ x)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (app t t₁)       = app (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (lam t)          = lam (wken Δ₁⊆Δ₂ (keep Γ₁⊆Γ₂) t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t)          = box (wken [] Δ₁⊆Δ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox t In t₁) = letbox (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) In (wken (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t₁)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst t)          = fst (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (snd t)          = snd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t)
  wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ (prd t t₁)       = prd (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t) (wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t₁)

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
     wkNf Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box t)         = box (wkNf [] Δ₁⊆Δ₂ t)
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

  LSub : (Δ : Ctx) (Γ' : Ctx) (Γ : Ctx) → Set
  LSub Δ Γ' = All (Δ ; Γ' ⊢_)

  pattern _,_ σ t = t ∷ σ

  lsub-refl : LSub Δ Γ Γ
  lsub-refl = All.tabulate var

  wken-lsub : Δ ⊆ Δ' → Γ ⊆ Γ' → LSub Δ Γ Ε → LSub Δ' Γ' Ε
  wken-lsub Δ⊆Δ' Γ⊆Γ' = All.map (wken Δ⊆Δ' Γ⊆Γ')

  --8<-- (for convenience)
  mwken-lsub : Δ ⊆ Δ' → LSub Δ Γ Ε → LSub Δ' Γ Ε
  mwken-lsub Δ⊆Δ' = wken-lsub Δ⊆Δ' ⊆-refl

  lwken-lsub : Γ ⊆ Γ' → LSub Δ Γ Ε → LSub Δ Γ' Ε
  lwken-lsub Γ⊆Γ' = wken-lsub ⊆-refl Γ⊆Γ'
  -->8--

  wken-to-lsub : Γ ⊆ Γ' → LSub Δ Γ' Γ
  wken-to-lsub Γ⊆Γ' = lwken-lsub Γ⊆Γ' lsub-refl

  --8<-- (for convenience)
  lsub-`, : Δ ; Γ ⊢ a → LSub Δ Γ (Γ `, a)
  lsub-`, t = lsub-refl , t

  lsub-drop : LSub Δ (Γ `, a) Γ
  lsub-drop = wken-to-lsub ⊆-`,

  lsub-keep : LSub Δ Γ Γ' → LSub Δ (Γ `, a) (Γ' `, a)
  lsub-keep σ = lwken-lsub ⊆-`, σ , v0

  lsub-keeps : LSub Δ Γ Γ' → LSub Δ (Γ `,, Ε) (Γ' `,, Ε)
  lsub-keeps σ = All.++ (lwken-lsub ⊆-`,,ˡ lsub-refl) (lwken-lsub ⊆-`,, σ)
  -->8--

  lsubst : LSub Δ Γ' Γ → Δ ; Γ ⊢ b → Δ ; Γ' ⊢ b
  lsubst σ (var v)         = lsubst-var σ v
  lsubst σ (app t u)       = app (lsubst σ t) (lsubst σ u)
  lsubst σ (lam t)         = lam (lsubst (lwken-lsub ⊆-`, σ , v0) t)
  lsubst σ (fst t)         = fst (lsubst σ t)
  lsubst σ (snd t)         = snd (lsubst σ t)
  lsubst σ (prd t u)       = prd (lsubst σ t) (lsubst σ u)
  lsubst _ (box t)         = box t
  lsubst σ (letbox t In u) = letbox (lsubst σ t) In (lsubst (mwken-lsub ⊆-`, σ) u)

  lsub-trans : LSub Δ Γ Γ' → LSub Δ Γ' Γ'' → LSub Δ Γ Γ''
  lsub-trans σ' = All.map (lsubst σ')

  --8<-- (for convenience)
  lsub-swap : LSub Δ (Γ `, b `, a) (Γ `, a `, b)
  lsub-swap = lsub-trans lsub-drop lsub-drop , v0 , v1

  lsubst-here : Δ ; Γ ⊢ a → Δ ; Γ `, a ⊢ b → Δ ; Γ ⊢ b
  lsubst-here u t = lsubst (lsub-`, u) t
  -->8--

  cut : ∀ {Γ} {Δ} {A B} {Γ'} → Δ ; Γ ⊢ A  → (t : Δ ; Γ `, A `,, Γ' ⊢ B)
           → Δ ; Γ `,, Γ' ⊢ B
  cut u t = lsubst (lsub-keeps (lsub-`, u)) t

  MSub : (Δ : Ctx) (Δ' : Ctx) → Set -- Sub [] Δ Δ'
  MSub Δ = All ([] ; Δ ⊢_)

  msub-refl : MSub Δ Δ
  msub-refl = All.tabulate var

  wken-msub : Δ ⊆ Δ' → MSub Δ Ε → MSub Δ' Ε
  wken-msub Δ⊆Δ' = All.map (lwken Δ⊆Δ')

  --8<-- (for convenience)
  msub-`, : [] ; Δ ⊢ a → MSub Δ (Δ `, a)
  msub-`, t = msub-refl , t

  msub-drop : MSub (Δ `, a) Δ
  msub-drop = wken-msub ⊆-`, msub-refl

  msub-keep : MSub Δ Δ' → MSub (Δ `, a) (Δ' `, a)
  msub-keep σ = wken-msub ⊆-`, σ , v0

  msub-keeps : MSub Δ Δ' → MSub (Δ `,, Ε) (Δ' `,, Ε)
  msub-keeps σ = All.++ (wken-msub ⊆-`,,ˡ msub-refl) (wken-msub ⊆-`,, σ)
  -->8--

  msubst : MSub Δ' Δ → Δ ; Γ ⊢ b → Δ' ; Γ ⊢ b
  msubst σ (var v)         = var v
  msubst σ (app t u)       = app (msubst σ t) (msubst σ u)
  msubst σ (lam t)         = lam (lsubst (lsub-keep lsub-refl) (msubst σ t))
  msubst σ (fst t)         = fst (msubst σ t)
  msubst σ (snd t)         = snd (msubst σ t)
  msubst σ (prd t u)       = prd (msubst σ t) (msubst σ u)
  msubst σ (box t)         = box (lsubst σ t)
  msubst σ (letbox t In u) = letbox (msubst σ t) In (msubst (wken-msub ⊆-`, σ , v0) u)

  msub-trans : MSub Δ Δ' → MSub Δ' Δ'' → MSub Δ Δ''
  msub-trans σ' = All.map (lsubst σ')

  --8<-- (for convenience)
  msub-swap : MSub (Δ `, b `, a) (Δ `, a `, b) 
  msub-swap = msub-trans lsub-drop msub-drop , v0 , v1

  msubst-here : [] ; Δ ⊢ a → (Δ `, a) ; Γ ⊢ b → Δ ; Γ ⊢ b
  msubst-here u t = msubst (msub-`, u) t
  -->8--

  mcut : [] ; Δ ⊢ a  → (t : Δ `, a `,, Δ' ; Γ ⊢ b) → Δ `,, Δ' ; Γ ⊢ b
  mcut t u = msubst (msub-keeps (msub-`, t)) u

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

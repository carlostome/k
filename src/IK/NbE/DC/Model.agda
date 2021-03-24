module IK.NbE.DC.Model where

  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  open import IK.Calculus.DC hiding (_,_)

  ISet = Ctx → Ctx → Set

  record Psh : Set₁ where
    field
        iSet : ISet
        Wken : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → (iSet Δ₁ Γ₁  → iSet Δ₂ Γ₂)
        -- letbox* : ∀ {Δ Γ} {a} → Δ ; Γ ⊢Ne (◻ a) → iSet (Δ `, a)  Γ → iSet Δ  Γ

  open Psh

  -- this seems to be a lax monoidal functor, not a product-preserving functor
  data Box (P : Psh) (Δ Γ : Ctx) : Set where
    box : P .iSet []  Δ → Box P Δ Γ
    letbox : ∀ {a} → Δ ; Γ ⊢Ne (◻ a) → Box P (Δ `, a) Γ → Box P Δ Γ

  wkBox : ∀ {P : Psh} {Δ₁ Δ₂ Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Box P Δ₁ Γ₁ → Box P Δ₂ Γ₂
  wkBox {P} Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box x) = box (Wken P [] Δ₁⊆Δ₂ x)
  wkBox {P} Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox x t) = letbox (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ x) (wkBox (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t)

  □_ : (P : Psh) → Psh
  □_ P = record { iSet = Box P
                  ; Wken = wkBox
                  } -- ; letbox* = letbox}

  record _→̇_ (P Q : Psh) : Set where
    field
      iFun : ∀ {Γ Δ} → iSet P Δ Γ → iSet Q Δ Γ

  open _→̇_

  Tm : Ty → Psh
  Tm A = record { iSet = _;_⊢ A
                  ; Wken = wken
                  } -- ; letbox* = λ x x₁ → letbox (Nf⇒Tm (Ne⇒Nf x)) In x₁}

  private
    mutual
      Nf-letbox* : Δ ; Γ ⊢Ne (◻ a) → (Δ `, a) ; Γ ⊢Nf b → Δ ; Γ ⊢Nf b
      Nf-letbox* x (lam t) = lam (Nf-letbox* (lwkNe ⊆-`, x) t)
      Nf-letbox* x (up x₁) = up (Ne-letbox* x x₁)
      Nf-letbox* x (prd t t₁) = prd (Nf-letbox* x t) (Nf-letbox* x t₁)
      Nf-letbox* x t@(box _) = letbox x In t
      Nf-letbox* x t@(letbox _ In _) = letbox x In t

      Ne-letbox* : Δ ; Γ ⊢Ne (◻ a) → (Δ `, a) ; Γ ⊢Ne b → Δ ; Γ ⊢Ne b
      Ne-letbox* x (var v)   = var v
      Ne-letbox* x (app t u) = app (Ne-letbox* x t) (Nf-letbox* x u)
      Ne-letbox* x (fst t) = fst (Ne-letbox* x t)
      Ne-letbox* x (snd t) = snd (Ne-letbox* x t)
 
  Ne : Ty → Psh
  Ne A = record { iSet = _;_⊢Ne A
                ; Wken = wkNe
                } -- ; letbox* = Ne-letbox*}

  Nf : Ty → Psh
  Nf A = record { iSet = _;_⊢Nf A
                ; Wken = wkNf
                } -- ; letbox* = λ x x₁ → letbox x x₁}

  _⇒̇_ : Psh → Psh → Psh
  (P ⇒̇ Q) = record { iSet  = λ Δ₁ Γ₁ → ∀ {Δ₂ Γ₂} → (Δ₁⊆Δ₂ : Δ₁ ⊆ Δ₂)
                             → (Γ₁⊆Γ₂ : Γ₁ ⊆ Γ₂) → iSet P Δ₂ Γ₂ → iSet Q Δ₂ Γ₂
                    ; Wken = λ Δ₁⊆Δ₂ Γ₁⊆Γ₂ f Δ₂⊆Δ₃ Γ₂⊆Γ₃ x → f (⊆-trans Δ₁⊆Δ₂ Δ₂⊆Δ₃) (⊆-trans Γ₁⊆Γ₂ Γ₂⊆Γ₃) x
                    } -- ; letbox* = λ n f Δ₁⊆Δ₂ Γ₁⊆Γ₂ p → Q .letbox* (Ne _ .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ n) (f (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ (P .Wken ⊆-`, ⊆-refl p)) }
  
  open import Data.Unit

  private
    variable
      P P' Q Q' O : Psh

  𝟙 : Psh
  𝟙 = record { iSet = λ x x₁ → ⊤ ; Wken = λ x x₁ x₂ → tt }

  infix 19 _x_
  _x_ : Psh → Psh → Psh
  P x Q  = record { iSet = λ Δ Γ → (P .iSet Δ Γ) × ((Q .iSet Δ Γ))
                  ; Wken = λ {Δ₁⊆Δ₂ Γ₁⊆Γ₂ (π₁ , π₂) → (P .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ π₁) , (Q .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ π₂) }
                  } -- ; letbox* = λ n (π₁ , π₂) → (P .letbox* n π₁) , (Q .letbox* n π₂)}

  Hom : Psh → Psh → Set
  Hom P Q = P →̇ Q

  id : Hom P P
  id .iFun p = p

  infixr 19 _∘_
  _∘_ : Hom P Q → Hom O P → Hom O Q
  (n ∘ m) .iFun o = n .iFun (m .iFun o)

  ! : Hom P 𝟙
  ! .iFun _ = tt

  π₁ : Hom (P x Q) P
  π₁ .iFun (p , q) = p

  π₂ : Hom (P x Q) Q
  π₂ .iFun (p , q) = q

  pr : Hom O P → Hom O Q → Hom O (P x Q)
  pr p q .iFun o = p .iFun o , q .iFun o

  private
    □-fmap : (f : ∀ {Δ'} → Δ ⊆ Δ' → P .iSet [] Δ' → Q .iSet [] Δ') → (□ P) .iSet Δ Γ → (□ Q) .iSet Δ Γ
    □-fmap f (box p)      = box (f ⊆-refl p)
    □-fmap f (letbox n p) = letbox n (□-fmap (λ Δa⊆Δ' → f (⊆-trans ⊆-`, Δa⊆Δ')) p)

  □-map :  Hom P Q → Hom (□ P) (□ Q)
  □-map n .iFun = □-fmap (λ Δ⊆Δ' → n .iFun)

  □-! : Hom P (□ 𝟙)
  □-! .iFun x = box tt

  private
    Box-pr : Box P Δ Γ → Box Q Δ Γ → Box (P x Q) Δ Γ
    Box-pr {P} (box t)      u = □-fmap (λ Δ⊆Δ' q → (P .Wken ⊆-refl Δ⊆Δ' t) , q) u
    Box-pr     (letbox t k) u = letbox t (Box-pr k (wkBox ⊆-`, ⊆-refl u))

  □-pr : Hom O (□ P) → Hom O (□ Q) → Hom O (□ (P x Q))
  □-pr n m .iFun s = Box-pr (n .iFun s) (m .iFun s)

  abs : Hom (O x P) Q → Hom O (P ⇒̇ Q)
  abs {O} n .iFun t Δ₁⊆Δ₂ Γ₁⊆Γ₂ u = n .iFun (O .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ t , u)

  ev : Hom ((P ⇒̇ Q) x P) Q
  ev .iFun (n , m) = n ⊆-refl ⊆-refl m

  open import IK.Semantics.KripkeCat.Model
  open ProductCat Psh Hom 𝟙 _x_ _∘_ π₁ π₂ pr

  postulate
    □-pr-left-unit  : ∀ {P}     → □-map x-left-unit   ∘ □-pr □-! π₂                   ≡ x-left-unit  {□ P}
    □-pr-right-unit : ∀ {P}     → □-map x-right-unit  ∘ □-pr π₁ □-!                   ≡ x-right-unit {□ P}
    □-pr-assoc      : ∀ {O P Q} → □-map x-right-assoc ∘ □-pr (□-pr π₁ π₂ ∘ π₁) π₂  ≡ □-pr π₁ (□-pr π₁ π₂ ∘ π₂) ∘ x-right-assoc {□ O} {□ P} {□ Q}

  NbEModel : KripkeCat
  NbEModel = record
               { Obj             = Psh
               ; Hom             = Hom
               ; _x_             = _x_
               ; _⇒̇_             = _⇒̇_
               ; □_              = □_
               ; 𝟙               = 𝟙
               ; id              = id
               ; _∘_             = _∘_
               ; □-map           = □-map
               ; □-pr            = □-pr
               ; □-!             = □-!
               ; π₁             = π₁
               ; π₂             = π₂
               ; pr              = pr
               ; !               = !
               ; abs             = abs
               ; ev              = ev
               ; □-pr-left-unit  = □-pr-left-unit
               ; □-pr-right-unit = □-pr-right-unit
               ; □-pr-assoc      = □-pr-assoc
               }

  Nes : Ctx → Psh
  Nes []       = 𝟙
  Nes (Γ `, a) = Nes Γ x Ne a

  Nfs : Ctx → Psh
  Nfs []       = 𝟙
  Nfs (Γ `, a) = Nfs Γ x Nf a

  Tms : Ctx → Psh
  Tms []       = 𝟙
  Tms (Γ `, a) = Tms Γ x Tm a

  open import IK.Semantics.KripkeCat.Interpretation.DC NbEModel (Nf 𝕓)

  reflect : ∀ a → Ne a →̇ ⟦ a ⟧Ty
  reify : ∀ a → ⟦ a ⟧Ty →̇ Nf a

  reflect (𝕓) .iFun n = up n
  reflect (a ⇒ b) .iFun n = λ Δ₁⊆Δ₂ Γ₁⊆Γ₂ x → reflect b .iFun (app (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ n) (reify a .iFun x))
  reflect (◻ a) .iFun n = letbox n (box (reflect a .iFun (var here)))
  reflect (a ∧ b) .iFun n = reflect a .iFun (fst n) , reflect b .iFun (snd n)

  reify (𝕓) .iFun x = x
  reify (a ⇒ b) .iFun x = lam (reify b .iFun (x ⊆-refl ⊆-`, (reflect a .iFun (var here))))
  reify (a ∧ b) .iFun x = prd (reify a .iFun (proj₁ x )) ((reify b .iFun (proj₂ x )))
  reify (◻ a) .iFun (box x) = box (reify a .iFun x)
  reify (◻ a) .iFun (letbox n k) = letbox n In reify (◻ a) .iFun k

  reflects : ∀ Γ → Nes Γ →̇ ⟦ Γ ⟧LCtx
  reflects []       = !
  reflects (Γ `, a) = reflects Γ x-map reflect a

  reifys : ∀ Γ → ⟦ Γ ⟧LCtx →̇ Nfs Γ
  reifys []       = !
  reifys (Γ `, a) = reifys Γ x-map reify a

  -- identity substitution (this is special about the NbE model)
  idN : ⟦ Γ ⟧LCtx .iSet Δ Γ
  idN {[]} {Δ} = tt
  idN {Γ `, a} {Δ} = ⟦ Γ ⟧LCtx .Wken ⊆-refl ⊆-`, (idN {Γ}) , reflect a .iFun (var here)

  idM : ⟦ Δ ⟧MCtx .iSet Δ Γ
  idM {[]} {Γ} = box tt
  idM {Δ `, a} {Γ} =  □-pr {O = ⟦ Δ ⟧MCtx x □ ⟦ a ⟧Ty} π₁ π₂ .iFun ((⟦ Δ ⟧MCtx .Wken ⊆-`, ⊆-refl idM) , box (reflect a .iFun (var here)))

  idₛ' : (⟦ Δ ⟧MCtx x ⟦ Γ ⟧LCtx) .iSet Δ Γ
  idₛ' {Δ} {Γ} = idM , (idN {Γ = Γ})
  
  -- retraction of interpretation
  quot : ⟦ Δ ; Γ ⊢ a ⟧ → Δ ; Γ ⊢Nf a
  quot {Γ} n = reify _ .iFun (n .iFun idₛ')
  
  -- normalization function
  norm : Δ ; Γ ⊢ a → Δ ; Γ ⊢Nf a
  norm t = quot (⟦ t ⟧Tm)

  -----------------------
  -- Logical Relations --
  -----------------------

  wken-sem : ∀ {a} {Δ₁ Δ₂} {Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → ⟦ Δ₁ ; Γ₁ ⊢ a ⟧ → ⟦ Δ₂ ; Γ₂ ⊢ a ⟧
  wken-sem {Δ₁ = Δ₁} {Γ₁ = Γ₁} Δ₁⊆Δ₂ Γ₁⊆Γ₂ t = t ∘ ⟦ Δ₁⊆Δ₂ ; Γ₁⊆Γ₂ ⟧Wken

  open import Relation.Binary.PropositionalEquality

  -- RTm : {a : Ty} {Δ Γ : Ctx} → Δ ; Γ ⊢ a → ⟦ Δ ; Γ ⊢ a ⟧  → Set
  -- RTm {𝕓} t x = t ≈ Nf⇒Tm (quot x)
  -- RTm {a ⇒ b} {Δ} {Γ} t f =
  --   {Δ' Γ' : Ctx} {u : Δ' ; Γ' ⊢ a} {x : Hom (⟦ Δ' ⟧MCtx x ⟦ Γ' ⟧Ctx) ⟦ a ⟧Ty}
  --    → (Δ⊆Δ' : Δ ⊆ Δ') → (Γ⊆Γ' : Γ ⊆ Γ')
  --    → RTm u x → RTm (app (wken Δ⊆Δ' Γ⊆Γ' t) u) (ev ∘ pr (wken-sem {a = a ⇒ b}  Δ⊆Δ' Γ⊆Γ' f) x)
  -- RTm {◻ a} t x = {!!}
  -- -- ∃ λ u → Rt u x × t ⟶* box u

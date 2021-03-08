module IK.NbE.DC where

  open import Data.Product
  open import IK.Calculus.DC

  ISet = Ctx → Ctx → Set

  record Psh : Set₁ where
    field
        iSet : ISet
        Wken : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → (iSet Δ₁ Γ₁  → iSet Δ₂ Γ₂)
        letbox* : ∀ {Δ Γ} {a} → Δ ; Γ ⊢Ne (◻ a) → iSet (Δ `, a)  Γ → iSet Δ  Γ

  open Psh
  private
    variable
      Γ Δ : Ctx

  data Box (P : Psh) (Δ Γ : Ctx) : Set where
    box : P .iSet []  Δ → Box P Δ Γ
    letbox : ∀ {a} → Δ ; Γ ⊢Ne (◻ a) → Box P (Δ `, a) Γ → Box P Δ Γ

  wkBox : ∀ {P : Psh} {Δ₁ Δ₂ Γ₁ Γ₂} → Δ₁ ⊆ Δ₂ → Γ₁ ⊆ Γ₂ → Box P Δ₁ Γ₁ → Box P Δ₂ Γ₂
  wkBox {P} Δ₁⊆Δ₂ Γ₁⊆Γ₂ (box x) = box (Wken P base Δ₁⊆Δ₂ x)
  wkBox {P} Δ₁⊆Δ₂ Γ₁⊆Γ₂ (letbox x t) = letbox (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ x) (wkBox (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ t)

  □_ : (P : Psh) → Psh
  □_ P = record { iSet = Box P
                  ; Wken = wkBox
                  ; letbox* = letbox}

  _⇒̇_ : Psh → Psh → Psh
  (P ⇒̇ Q) = record { iSet  = λ Δ₁ Γ₁ → ∀ {Δ₂ Γ₂} → (Δ₁⊆Δ₂ : Δ₁ ⊆ Δ₂)
                             → (Γ₁⊆Γ₂ : Γ₁ ⊆ Γ₂) → iSet P Δ₂ Γ₂ → iSet Q Δ₂ Γ₂
                    ; Wken = λ Δ₁⊆Δ₂ Γ₁⊆Γ₂ f Δ₂⊆Δ₃ Γ₂⊆Γ₃ x → f (⊆-trans Δ₁⊆Δ₂ Δ₂⊆Δ₃) (⊆-trans Γ₁⊆Γ₂ Γ₂⊆Γ₃) x
                    ; letbox* = λ n f Δ₁⊆Δ₂ Γ₁⊆Γ₂ x → Q .letbox* (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ n)
                                  (f (keep Δ₁⊆Δ₂) Γ₁⊆Γ₂ (P .letbox* (wkNe (drop Δ₁⊆Δ₂) Γ₁⊆Γ₂ n) (P .Wken (drop (drop ⊆-refl)) ⊆-refl x))) }

  record _→̇_ (P Q : Psh) : Set where
    field
      iFun : ∀ {Γ Δ} → iSet P Δ Γ → iSet Q Δ Γ

  open _→̇_
  Tm : Ty → Psh
  Tm A = record { iSet = _;_⊢ A
                  ; Wken = wken
                  ; letbox* = λ x x₁ → letbox (Nf⇒Tm (Ne⇒Nf x)) x₁}

  Ne : Ty → Psh
  Ne A = record { iSet = _;_⊢Ne A
                ; Wken = wkNe
                ; letbox* = λ n k → letbox n (Ne⇒Nf k)}

  Nf : Ty → Psh
  Nf A = record { iSet = _;_⊢Nf A
                ; Wken = wkNf
                ; letbox* = λ x x₁ → Ne⇒Nf (letbox x x₁)}

  
  open import Data.Unit

  private
    variable
      P Q O : Psh

  𝟙 : Psh
  𝟙 = record { iSet = λ x x₁ → ⊤ ; Wken = λ x x₁ x₂ → tt }

  infix 19 _x_
  _x_ : Psh → Psh → Psh
  P x Q  = record { iSet = λ Δ Γ → (P .iSet Δ Γ) × ((Q .iSet Δ Γ))
                  ; Wken = λ {Δ₁⊆Δ₂ Γ₁⊆Γ₂ (fst , snd)→ (P .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ fst) , (Q .Wken Δ₁⊆Δ₂ Γ₁⊆Γ₂ snd) }
                  ; letbox* = λ n (fst , snd) → (P .letbox* n fst) , (Q .letbox* n snd)}

  Hom : Psh → Psh → Set
  Hom P Q = P →̇ Q

  postulate
    _∘_ : Hom P Q → Hom O P → Hom O Q
    x-left-assoc : Hom (O x (P x Q)) ((O x P) x Q)
    x-right-assoc : Hom ((O x P) x Q) (O x (P x Q))
    □-map :  Hom P Q → Hom (□ P) (□ Q)
    □-pr : Hom O (□ P) → Hom O (□ Q) → Hom O (□ (P x Q))
    □-! : Hom P (□ 𝟙)
    x-left-unit : Hom P (𝟙 x P)
    x-right-unit : Hom P (P x 𝟙)
    fst : Hom (P x Q) P
    snd : Hom (P x Q) Q
    pr : Hom O P → Hom O Q → Hom O (P x Q)
    ! : Hom P 𝟙
    abs : Hom (O x P) Q → Hom O (P ⇒̇ Q)
    ev : Hom ((P ⇒̇ Q) x P) Q

  open import IK.Semantics.KripkeCat.Model

  NbEModel : KripkeCat
  NbEModel = record
               { Obj = Psh
               ; Hom = Hom
               ; _x_ = _x_
               ; _⇒̇_ = _⇒̇_
               ; □_ = □_
               ; 𝟙 = 𝟙
               ; _∘_ = _∘_
               ; x-left-assoc = x-left-assoc
               ; x-right-assoc = x-right-assoc 
               ; □-map = □-map
               ; □-pr = □-pr
               ; □-! = □-!
               ; x-left-unit = x-left-unit
               ; x-right-unit = x-right-unit
               ; fst = fst
               ; snd = snd
               ; pr = pr
               ; ! = !
               ; abs = abs
               ; ev = ev
               }

  open import IK.Semantics.KripkeCat.Interpretation.DC NbEModel (Nf 𝕓)

  reflect : ∀ {a} → Ne a →̇ ⟦ a ⟧Ty
  reify : ∀ {a} → ⟦ a ⟧Ty →̇ Nf a

  reflect {𝕓} .iFun n = up n
  reflect {a ⇒ b} .iFun n = λ Δ₁⊆Δ₂ Γ₁⊆Γ₂ x → reflect .iFun (app (wkNe Δ₁⊆Δ₂ Γ₁⊆Γ₂ n) (reify .iFun x))
  reflect {◻ a} .iFun n = letbox n (box (reflect {a = a} .iFun (var here)))

  reify {a = 𝕓} .iFun x = x
  reify {a = a ⇒ b} .iFun x = lam (reify .iFun (x ⊆-refl (drop ⊆-refl) (reflect {a = a} .iFun (var here))))
  reify {a = ◻ a} .iFun (box x) = box (reify .iFun x)
  reify {a = ◻ a} .iFun (letbox n k) = Nf _ .letbox* n (reify .iFun k)

  -- identity substitution (this is special about the NbE model)
  idN : ⟦ Γ ⟧Ctx .iSet Δ Γ
  idN {[]} {Δ} = tt
  idN {Γ `, x} {Δ} =  ⟦ Γ ⟧Ctx .Wken ⊆-refl (drop ⊆-refl) (idN {Γ}) , (reflect {x} .iFun (var here))

  idM : ⟦ Δ ⟧MCtx .iSet Δ Γ
  idM {[]} {Γ} = box tt
  idM {Δ `, a} {Γ} =  □-pr {O = ⟦ Δ ⟧MCtx x □ ⟦ a ⟧Ty} fst snd .iFun ((⟦ Δ ⟧MCtx .Wken (drop ⊆-refl) ⊆-refl idM) , box (reflect {a} .iFun (var here)))

  idₛ' : (⟦ Δ ⟧MCtx x ⟦ Γ ⟧Ctx) .iSet Δ Γ
  idₛ' {Δ} {Γ} = idM , (idN {Γ = Γ})
  
  -- retraction of interpretation
  quot : Hom (⟦ Δ ⟧MCtx x ⟦ Γ ⟧Ctx) ⟦ a ⟧Ty → Δ ; Γ ⊢Nf a
  quot {Γ} n = reify .iFun (n .iFun idₛ')
  
  -- normalization function
  norm : Δ ; Γ ⊢ a → Δ ; Γ ⊢Nf a
  norm t = quot (⟦ t ⟧Tm)

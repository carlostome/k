module IK.Semantics.KripkeCat.Model where

  open import Relation.Binary.PropositionalEquality

  module ProductCat -- XXX: make into a subrecord of KripkeKat
    (Obj : Set₁)
    (Hom : Obj → Obj → Set)
    (𝟙   : Obj)
    (_x_ : Obj → Obj → Obj)
    (_∘_ : ∀ {P Q O} → Hom P Q → Hom O P → Hom O Q)
    (π₁ : ∀ {P Q} → Hom (P x Q) P)
    (π₂ : ∀ {P Q} → Hom (P x Q) Q)
    (pr  : ∀ {P Q O} → Hom O P → Hom O Q → Hom O (P x Q))
    where
    _x-map_ : ∀ {P P' Q Q'} → Hom P P' → Hom Q Q' → Hom (P x Q) (P' x Q')
    _x-map_ n m = pr (n ∘ π₁) (m ∘ π₂)

    x-right-assoc : ∀ {O P Q} → Hom ((O x P) x Q) (O x (P x Q))
    x-right-assoc = pr (π₁ ∘ π₁) (pr (π₂ ∘ π₁) π₂)

    x-left-unit : ∀ {P} → Hom (𝟙 x P) P
    x-left-unit = π₂

    x-right-unit : ∀ {P} → Hom (P x 𝟙) P
    x-right-unit = π₁

    open import Data.List.Snoc

    fp : Listˢ Obj → Obj
    fp [] = 𝟙
    fp (ps ∷ˢ p) = fp ps x p

  record KripkeCat : Set₂ where -- OBS: locally small, lax
    field
      Obj   : Set₁
      Hom   : Obj → Obj → Set

      _x_   : Obj → Obj → Obj
      _⇒̇_   : Obj → Obj → Obj
      □_    : Obj → Obj
      𝟙     : Obj

      id    : ∀ {P} → Hom P P
      _∘_   : ∀ {P Q O} → Hom P Q → Hom O P → Hom O Q
      □-map : ∀ {P Q} → Hom P Q → Hom (□ P) (□ Q)
      □-pr  : ∀ {P Q O} → Hom O (□ P) → Hom O (□ Q) → Hom O (□ (P x Q))
      □-!   : ∀ {P} → Hom P (□ 𝟙)
      π₁   : ∀ {P Q} → Hom (P x Q) P
      π₂   : ∀ {P Q} → Hom (P x Q) Q
      pr    : ∀ {P Q O} → Hom O P → Hom O Q → Hom O (P x Q)
      !     : ∀ {P} → Hom P 𝟙
      abs   : ∀ {P Q O} → Hom (O x P) Q → Hom O (P ⇒̇ Q)
      ev    : ∀ {P Q} → Hom ((P ⇒̇ Q) x P) Q

    open ProductCat Obj Hom 𝟙 _x_ _∘_ π₁ π₂ pr public

    infixr 19 _∘_
    infixr 19 _x_

    □-pr' : ∀ {P Q} → Hom (□ P x □ Q) (□ (P x Q))
    □-pr' {P} {Q} = □-pr π₁ π₂ -- XXX: not binding the implicit arguments causes an Agda error

    field
      □-pr-left-unit  : ∀ {P}     → □-map x-left-unit   ∘ □-pr' ∘ □-!   x-map id  ≡ x-left-unit  {□ P}
      □-pr-right-unit : ∀ {P}     → □-map x-right-unit  ∘ □-pr' ∘ id    x-map □-! ≡ x-right-unit {□ P}
      □-pr-assoc      : ∀ {O P Q} → □-map x-right-assoc ∘ □-pr' ∘ □-pr' x-map id  ≡ □-pr' ∘ id x-map □-pr' ∘ x-right-assoc {□ O} {□ P} {□ Q}

    x-left-assoc : ∀ {O P Q} → Hom (O x (P x Q)) ((O x P) x Q)
    x-left-assoc = pr (pr π₁ (π₁ ∘ π₂)) (π₂ ∘ π₂)

    x-left-unit-inv : ∀ {P} → Hom P (𝟙 x P)
    x-left-unit-inv = pr ! id

    x-right-unit-inv : ∀ {P} → Hom P (P x 𝟙)
    x-right-unit-inv = pr id !

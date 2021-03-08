module IK.Semantics.KripkeCat.Model where

  record KripkeCat : Set₂ where
    field
      Obj : Set₁
      Hom : Obj → Obj → Set

      _x_ : Obj → Obj → Obj
      _⇒̇_ : Obj → Obj → Obj
      □_ : Obj → Obj
      𝟙 : Obj
    field
      _∘_ : ∀ {P Q O} → Hom P Q → Hom O P → Hom O Q
      x-left-assoc  : ∀ {P Q O} → Hom (O x (P x Q)) ((O x P) x Q)
      x-right-assoc : ∀ {P Q O} → Hom ((O x P) x Q) (O x (P x Q))
      □-map         : ∀ {P Q} →  Hom P Q → Hom (□ P) (□ Q)
      □-pr          : ∀ {P Q O} → Hom O (□ P) → Hom O (□ Q) → Hom O (□ (P x Q))
      □-!           : ∀ {P} → Hom P (□ 𝟙)
      x-left-unit   : ∀ {P} → Hom P (𝟙 x P)
      x-right-unit  : ∀ {P} → Hom P (P x 𝟙)
      fst           : ∀ {P Q} → Hom (P x Q) P
      snd           : ∀ {P Q} → Hom (P x Q) Q
      pr            : ∀ {P Q O} → Hom O P → Hom O Q → Hom O (P x Q)
      !             : ∀ {P} → Hom P 𝟙
      abs           : ∀ {P Q O} → Hom (O x P) Q → Hom O (P ⇒̇ Q)
      ev            : ∀ {P Q} → Hom ((P ⇒̇ Q) x P) Q

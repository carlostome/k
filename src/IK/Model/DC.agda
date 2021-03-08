-- Formulation of the NbE model in Norm.agda in terms of Model.agda
module IK.Model.DC where

open import Data.Product using (_,_; proj₁; proj₂; ∃; _×_)
open import Data.Unit using (tt)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import IK.Calculus.DC -- reexports IK.Type and Context Ty

W = Ctx × Ctx

_W-≤_ : W → W → Set
(Δ , Γ) W-≤ (Δ' , Γ') =
  ∀ A → Δ ; Γ ⊢ (◻ A) → A ∈ Γ'

-- -- Γ W-≤ Δ iff Δ = Γ 🔒 ,, Γ' for some 🔒-free Γ', i.e. Δ is an
-- -- extension of Γ by a single STLC context/stack frame
-- infix 3 _W-≤_
-- data _W-≤_ : Ctx → Ctx → Set where
--   drop   : ∀ {Γ Δ a} → Γ W-≤ Δ → Γ W-≤ Δ `, a
--   drop🔒 : ∀ {Γ} → Γ W-≤ Γ 🔒
-- -- _W-≤_ = λ Γ Δ → ∃ λ Γ' → LFExt Δ (Γ 🔒) Γ'

-- T = Ctx
_T-≤_ : W → W → Set
(Δ₀ , Γ₀) T-≤ (Δ₁ , Γ₁) = Δ₁ ⊇ Δ₀ × Γ₁ ⊇ Γ₀


-- -- Γ T-≤ Δ iff either 1. both Γ and Δ 🔒-free and Γ ≤ Δ, or
-- --                    2. Γ = ΓL 🔒 ,, ΓR, Δ = ΔL 🔒 ,, ΔR for some 🔒-free ΓR and ΔR s.t. ΓL T-≤ ΔL and ΓR ≤ ΔR
-- -- i.e. a weakening (possibly trivially) for each STLC context/stack
-- -- frame aka "≤ minus drop🔒"
-- infix 3 _T-≤_
-- -- data _T-≤_ : Ctx → Ctx → Set where
-- --   base   : [] T-≤ []
-- --   drop   : ∀ {Γ Δ a} → Γ T-≤ Δ → Γ T-≤ Δ `, a
-- --   keep   : ∀ {Γ Δ a} → Γ T-≤ Δ → Γ `, a T-≤ Δ `, a
-- --   keep🔒 : ∀ {Γ Δ} → Γ T-≤ Δ → Γ 🔒 T-≤ Δ 🔒
-- _T-≤_ = λ Γ Δ → Δ ≤ Γ

-- private
--   T-refl : Reflexive _T-≤_
--   -- T-refl {[]}     = base
--   -- T-refl {Γ `, a} = keep T-refl
--   -- T-refl {Γ 🔒}   = keep🔒 T-refl
--   T-refl = idWk
  
--   T-trans : Transitive _T-≤_
--   -- T-trans base       (drop y)       = drop (T-trans base     y) -- BASE DROP!
--   -- T-trans (drop x)   (drop y)       = drop (T-trans (drop x) y)
--   -- T-trans (keep x)   (drop y)       = drop (T-trans (keep x) y)
--   -- T-trans (keep🔒 x) (drop y)       = drop (T-trans (keep🔒 x) y)
--   -- T-trans Γ≤Δ          (drop Δ≤Ε)   = drop   (T-trans Γ≤Δ Δ≤Ε)
--   -- T-trans base         base         = base
--   -- T-trans (drop Γ≤Δ)   (keep Δ≤Ε)   = drop   (T-trans Γ≤Δ Δ≤Ε)
--   -- T-trans (keep Γ≤Δ)   (keep Δ≤Ε)   = keep   (T-trans Γ≤Δ Δ≤Ε)
--   -- T-trans (keep🔒 Γ≤Δ) (keep🔒 Δ≤Ε) = keep🔒 (T-trans Γ≤Δ Δ≤Ε)
--   T-trans = _∙_

--   drop🔒 : ∀ {Γ} → Γ W-≤ Γ 🔒
--   drop🔒 {Γ} = [] , nil

-- T-preorder : IsPreorder _≡_ _T-≤_
-- T-preorder = record { isEquivalence = P.isEquivalence ; reflexive = λ { P.refl → T-refl } ; trans = T-trans }

cod-R-monotone : ∀ {w v w'} → w W-≤ v → w' T-≤ w → ∃ λ v' → v' T-≤ v × w' W-≤ v'
cod-R-monotone w≤v (Δ₁⊇Δ₀ , Γ₁⊇Γ₀) = {!!} , {!!}
-- cod-R-monotone {Γ} {Δ} {Γ'} (ΓR , Δ=Γ🔒ΓR) Γ'≤Γ = (Γ' 🔒) , T-trans (keep🔒 Γ'≤Γ) (wᵣ Δ=Γ🔒ΓR) , drop🔒

-- dom-R-monotone : ∀ {w v v'} → w W-≤ v → v T-≤ v' → ∃ λ w' → w T-≤ w' × w' W-≤ v'
-- dom-R-monotone {Γ} {Δ} {Δ'} (ΓR , Δ=Γ🔒ΓR) Δ≤Δ' = ←🔒 Δ' , stashWk Δ=Γ🔒ΓR Δ≤Δ' , 🔒→ Δ' , resExt Δ=Γ🔒ΓR Δ≤Δ'

-- open import IK.Interpretation.Fitch W _W-≤_ _T-≤_ T-preorder cod-R-monotone dom-R-monotone
-- import IK.Norm as Norm
-- open Norm.Ne
-- open Norm.Nf
-- open Obj
-- open Hom

-- ---------------
-- -- Normal forms
-- ---------------

-- Ne : Ty → Obj
-- Ne a .S          Γ     = Norm.Ne Γ a
-- Ne a .isMonotone Γ≤Δ x = Norm.wkNe Γ≤Δ x

-- Nf : Ty → Obj
-- Nf a .S          Γ     = Norm.Nf Γ a
-- Nf a .isMonotone Γ≤Δ x = Norm.wkNf Γ≤Δ x

-- -- interpretation of types

-- Tm'- : Ty → Obj
-- Tm'- a = ⟦_⟧Ty (Nf 𝕓) a

-- -- interpretation of contexts
-- Sub'- : Ctx → Obj
-- Sub'- Γ = ⟦_⟧Ctx (Nf 𝕓) Γ

-- reify   : Hom (Tm'- a) (Nf a)
-- reflect : Hom (Ne a) (Tm'- a)

-- -- interpretation of neutrals
-- reflect {a = 𝕓}     .f n = up𝕓 n
-- reflect {a = a ⇒ b} .f n = λ e x → reflect .f (app (Ne (a ⇒ b) .isMonotone e n) (reify .f x))
-- reflect {a = ◻ a}   .f n = λ wRw' → reflect .f (unbox n (wRw' .proj₂))

-- -- reify values to normal forms
-- reify {a = 𝕓}     .f x = x
-- reify {a = a ⇒ b} .f x = lam (reify .f (x (drop T-refl) (reflect {a} .f (var ze))))
-- reify {a = ◻ a}   .f x = box (reify .f (x drop🔒))

-- -- identity substitution (this is special about the NbE model)
-- idₛ' : Sub'- Γ .S Γ
-- idₛ' {[]}     = tt
-- idₛ' {Γ `, a} = Sub'- Γ .isMonotone (drop T-refl) (idₛ' {Γ}) , reflect {a} .f (var ze)
-- idₛ' {Γ 🔒}   = Γ , (drop🔒 , idₛ' {Γ})

-- -- interpretation of terms
-- eval : Tm Γ a → Hom (Sub'- Γ) (Tm'- a)
-- eval t = ⟦_⟧Tm (Nf 𝕓) t

-- -- retraction of interpretation
-- quot : Hom (Sub'- Γ) (Tm'- a) → Norm.Nf Γ a
-- quot {Γ} n = reify .f (n .f (idₛ' {Γ}))

-- -- normalization function
-- norm : Tm Γ a → Norm.Nf Γ a
-- norm t = quot (eval t)

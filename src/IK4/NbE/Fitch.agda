-- Formulation of the NbE model in Norm.agda in terms of PossibleWorlds/Model.agda
module IK4.NbE.Fitch where

open import Data.Product using (_,_; proj₁; proj₂; ∃; _×_)
open import Data.Unit using (tt)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import IK4.Term

W = Ctx

private
  ≤-refl = idWk

  ≤-trans = _∙_

  infix 3 _R_
  _R_ = _⊏_

  R-trans = ⊏-trans

  drop🔒 : Γ R Γ 🔒
  drop🔒 = nil

≤-preorder : IsPreorder _≡_ _≤_
≤-preorder = record { isEquivalence = P.isEquivalence ; reflexive = λ { P.refl → ≤-refl } ; trans = ≤-trans }

cod-R-monotone : ∀ {w v w'} → w R v → w' ≤ w → ∃ λ v' → v' ≤ v × w' R v'
cod-R-monotone = factor1

dom-R-monotone : ∀ {w v v'} → w R v → v ≤ v' → ∃ λ w' → w ≤ w' × w' R v'
dom-R-monotone = factor2

open import IK4.Semantics.PossibleWorlds.Interpretation.Fitch W _R_ R-trans _≤_ ≤-preorder cod-R-monotone dom-R-monotone
import IK4.Norm as Norm
open Norm.Ne
open Norm.Nf
open Obj
open Hom

---------------
-- Normal forms
---------------

Ne : Ty → Obj
Ne a .S          Γ     = Norm.Ne Γ a
Ne a .isMonotone Γ≤Δ x = Norm.wkNe Γ≤Δ x

Nf : Ty → Obj
Nf a .S          Γ     = Norm.Nf Γ a
Nf a .isMonotone Γ≤Δ x = Norm.wkNf Γ≤Δ x

Tm'- : Ty → Obj
Tm'- a = ⟦_⟧Ty (Nf 𝕓) (λ a b → Nf (a ∧ b)) a

Sub'- : Ctx → Obj
Sub'- Γ = ⟦_⟧Ctx (Nf 𝕓) (λ a b → Nf (a ∧ b)) Γ

reify   : Hom (Tm'- a) (Nf a)
reflect : Hom (Ne a) (Tm'- a)

reflect {a = 𝕓}     .f n = up𝕓 n
reflect {a = a ⇒ b} .f n = λ e x → reflect .f (app (Ne (a ⇒ b) .isMonotone e n) (reify .f x))
reflect {a = a ∧ b} .f n = up∧ n
reflect {a = ◻ a}   .f n = λ wRw' → reflect .f (unbox n wRw')

reify {a = 𝕓}     .f x = x
reify {a = a ⇒ b} .f x = lam (reify .f (x (drop ≤-refl) (reflect {a} .f (var ze))))
reify {a = a ∧ b} .f x = x
reify {a = ◻ a}   .f x = box (reify .f (x drop🔒))

idₛ' : Sub'- Γ .S Γ
idₛ' {[]}     = tt
idₛ' {Γ `, a} = Sub'- Γ .isMonotone (drop ≤-refl) (idₛ' {Γ}) , reflect {a} .f (var ze)
idₛ' {Γ 🔒}   = Γ , drop🔒 , idₛ' {Γ}

eval : Tm Γ a → Hom (Sub'- Γ) (Tm'- a)
eval t = ⟦_⟧Tm (Nf 𝕓) (λ a b → Nf (a ∧ b)) t

quot : Hom (Sub'- Γ) (Tm'- a) → Norm.Nf Γ a
quot {Γ} n = reify .f (n .f (idₛ' {Γ}))

norm : Tm Γ a → Norm.Nf Γ a
norm t = quot (eval t)

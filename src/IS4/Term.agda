module IS4.Term where

open import Data.Unit using (tt)
open import Data.Product
open import Relation.Binary hiding (_⇒_)

open import IK.Type public
open import Context Ty as C hiding (_≤_; nil; ext; ext🔒) public
_≤_ = λ Γ Δ → Δ C.≤ Γ

variable
  Γ Γ' Δ Δ' : Ctx

_⊑_ = λ Γ Δ → ∃ λ Γ' → Ext tt Δ Γ Γ'

pattern nil       = _ , C.nil
pattern ext e     = _ , C.ext e
pattern ext🔒 f e = _ , C.ext🔒 f e

⊑-refl : Reflexive _⊑_
⊑-refl = nil

⊑-trans : Transitive _⊑_
⊑-trans (_ , Γ⊑Δ) (_ , Δ⊑Ε) = _ , extRAssoc Γ⊑Δ Δ⊑Ε

factor1 : Γ ⊑ Δ → Γ' ≤ Γ → ∃ λ Δ' → Δ' ≤ Δ × Γ' ⊑ Δ'
factor1 nil           Γ'≤Γ = _ , Γ'≤Γ , nil
factor1 (ext Γ⊑Δ)     Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
... | Δ' , Δ'≤Δ , Γ'⊑Δ' = Δ' , Δ'≤Δ ∙ fresh , Γ'⊑Δ'
factor1 (ext🔒 _ Γ⊑Δ) Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
... | Δ' , Δ'≤Δ , Γ'⊑Δ' = (Δ' 🔒) , keep🔒 Δ'≤Δ , ⊑-trans Γ'⊑Δ' (ext🔒 tt extRId)

factor2 : Γ ⊑ Δ → Δ ≤ Δ' → ∃ λ Γ' → Γ ≤ Γ' × Γ' ⊑ Δ'
factor2 nil           Δ≤Δ' = _ , Δ≤Δ' , nil
factor2 (ext Γ⊑Δ)     Δ≤Δ' = factor2 (_ , Γ⊑Δ) (fresh ∙ Δ≤Δ')
factor2 (ext🔒 _ Γ⊑Δ) Δ≤Δ' with factor2 (_ , Γ⊑Δ) (stashWk extRId Δ≤Δ')
... | Γ' , Γ≤Γ' , Γ'⊑Δ' = Γ' , Γ≤Γ' , ⊑-trans Γ'⊑Δ' (⊑-trans (ext🔒 tt extRId) (_ , embLFExt (resExt extRId Δ≤Δ')))

------------------------------------
-- Variables, terms and substituions
------------------------------------

data Tm : Ctx → Ty → Set where

  var  : Var Γ a
       ---------
       → Tm Γ a

  lam  : Tm (Γ `, a) b
         -------------
       → Tm Γ (a ⇒ b)

  app  : Tm Γ (a ⇒ b) → Tm Γ a
         ---------------------
       → Tm Γ b

  box   : Tm (Γ 🔒) a
        ------------
        → Tm Γ (◻ a)

  unbox : Tm Γ (◻ a) → Γ ⊑ Δ
        --------------------
        → Tm Δ a

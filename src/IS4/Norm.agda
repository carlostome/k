module IS4.Norm where

open import Data.Product

open import IS4.Term

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : Var Γ a → Ne Γ a
  app   : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
  unbox : Ne Γ (◻ a) → Γ ⊑ Δ → Ne Δ a

data Nf where
  up𝕓 : Ne Γ 𝕓 → Nf Γ 𝕓
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  up∧ : Ne Γ (a ∧ b) → Nf Γ (a ∧ b) -- XXX
  box : Nf (Γ 🔒) a → Nf Γ (◻ a)

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕓 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (up∧ x) = embNe x
embNf (box n) = box (embNf n)

-- weakening lemmas

wkNe : Γ ≤ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ≤ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = let _ , Δ' , Δ≤Δ' = factor2 e w in unbox (wkNe Δ' n) Δ≤Δ'

wkNf e (up𝕓 x) = up𝕓 (wkNe e x)
wkNf e (lam n) = lam (wkNf (keep e) n)
wkNf e (up∧ x) = up∧ (wkNe e x)
wkNf e (box n) = box (wkNf (keep🔒 e) n)

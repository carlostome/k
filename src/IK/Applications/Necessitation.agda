module IK.Applications.Necessitation where

open import IK.Term

private
  lemma-var : Var Γ a → Var (Γ' ,, Γ) a
  lemma-var ze = ze
  lemma-var (su x) = su (lemma-var x)

  -- we didn't find this
  lemma-lfext : LFExt Γ ΓL ΓR → LFExt (Γ' ,, Γ) (Γ' ,, ΓL) ΓR
  lemma-lfext nil = nil
  lemma-lfext (ext p) = ext (lemma-lfext p)

  -- Lemma A.1 in Clouston
  lemma : Tm Γ a → Tm (Γ' ,, Γ) a
  lemma (var v) = var (lemma-var v)
  lemma (lam t) = lam (lemma t)
  lemma (app t u) = app (lemma t) (lemma u)
  lemma (box t) = box (lemma t)
  lemma (unbox t p) = unbox (lemma t) (lemma-lfext p)

-- Neccesitation is admissible: If ⊢ a then ⊢ ◻ a
nec : Tm [] a → Tm [] (◻ a)
nec t = box (lemma t)

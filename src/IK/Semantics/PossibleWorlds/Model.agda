open import Data.Product
open import Data.Unit
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


-- A model of Fitch-style lambda calculus, i.e. an adjunction, _in
-- presheaves_ (after Goldblatt?)
module IK.Semantics.PossibleWorlds.Model
  (W-Carrier : Set)
  (R         : Rel W-Carrier 0ℓ) -- accessibility relation, abstract "lock with lock-free extension"
  (let _W-≈_ = _≡_)             -- (_W-≈_ : Rel W-Carrier 0ℓ)
  (let W-set = P.isEquivalence) -- (W-set : IsEquivalence _W-≈_)

  -- (T-Carrier : Set)
  -- (_T-≈_     : Rel T-Carrier 0ℓ)
  (_≤_        : Rel W-Carrier 0ℓ) -- Kripke or index category relation, abstract "weakening"
  (T-preorder : IsPreorder _W-≈_ _≤_)

  -- Nachi, the following two assumptions are satisfied by your
  -- lock-free extension and weakening relations on contexts (with
  -- locks). Very ad-hoc for now, motivated by your model, but should
  -- have a more high-level motivation. R can be seen as a relation on
  -- the preorder ≤ aka "profunctor", "distributor", or
  -- "correspondence".
  (cod-R-monotone : ∀ {w v w'} → R w v → w' ≤ w → ∃ λ v' → v' ≤ v × R w' v') -- needed for □ P to be a presheaf
  (dom-R-monotone : ∀ {w v v'} → R w v → v ≤ v' → ∃ λ w' → w ≤ w' × R w' v') -- needed for ◆ P to be a presheaf
  where

private
  W = W-Carrier
  open IsPreorder T-preorder renaming (refl to T-≤-refl; trans to T-≤-trans)

-- presheaves on (W,T-≤) w/o the laws
record Obj : Set₁ where
  constructor _,_
  field
    S          : W → Set
    isMonotone : ∀ {w w'} → w ≤ w' → S w → S w'
    -- _monotone_ is what Andreas called this; makes sense given S w
    -- can be interpreted as the proof-relevant way of saying that S
    -- is true at world w
open Obj

-- natural transformations w/o the law
record Hom (P Q : Obj) : Set where
  field
    f : ∀ {w} → P .S w → Q .S w
open Hom

private
  variable O P Q P' Q' : Obj

id : Hom P P
id .f p = p

_∘_ : Hom P Q → Hom O P → Hom O Q
(n ∘ m) .f o = n .f (m .f o)

-- presheaf finite products (terminal object and Cartesian products)
T : Obj
T .S          w      = ⊤
T .isMonotone w≤w' x = x

! : Hom P T
! .f _ = tt

infix 19 _x_
_x_ : Obj → Obj → Obj
((P , r) x (Q , s)) .S          w            = P w × Q w
((P , r) x (Q , s)) .isMonotone w≤w' (p , q) = r w≤w' p , s w≤w' q

π₁ : Hom (P x Q) P
π₁ .f (p , q) = p

π₂ : Hom (P x Q) Q
π₂ .f (p , q) = q

pr : Hom O P → Hom O Q → Hom O (P x Q)
pr p q .f o = p .f o , q .f o

_x-map_ : Hom P P' → Hom Q Q' → Hom (P x Q) (P' x Q')
n x-map m = pr (n ∘ π₁) (m ∘ π₂)

x-left-assoc : Hom (O x (P x Q)) ((O x P) x Q)
x-left-assoc = pr (pr π₁ (π₁ ∘ π₂)) (π₂ ∘ π₂)

x-right-assoc : Hom ((O x P) x Q) (O x (P x Q))
x-right-assoc = pr  (π₁ ∘ π₁) (pr (π₂ ∘ π₁) π₂)

x-left-unit : Hom P (T x P)
x-left-unit = pr ! id

x-right-unit : Hom P (P x T)
x-right-unit = pr id !

-- presheaf exponential
_^_ : Obj → Obj → Obj
((Q , s) ^ (P , r)) .S          w      = ∀ {w'} → w ≤ w' → P w' → Q w'
((Q , s) ^ (P , r)) .isMonotone w≤w' f = λ w'≤w'' p → f (T-≤-trans w≤w' w'≤w'') p

abs : Hom (O x P) Q → Hom O (Q ^ P)
abs {O} n .f o w≤w' p = n .f (O .isMonotone w≤w' o , p)

ev : Hom (Q ^ P x P) Q
ev .f (f , p) = f T-≤-refl p

-- Andreas' AG ("always") and its left adjoint ("sometime in the past")
□_ : Obj → Obj
(□ (P , r)) .S          w      = ∀ {v} → R w v → P v
(□ (P , r)) .isMonotone w≤w' p = λ w'Rv' → let (v , v'≤v , w'Rv') = cod-R-monotone w'Rv' w≤w' in r v'≤v (p w'Rv')

◆_ : Obj → Obj
(◆ (P , r)) .S          w                  = ∃ λ v → R v w × P v
(◆ (P , r)) .isMonotone w≤w' (v , vRw , p) = let (v' , v≤v' , v'Rw') = dom-R-monotone vRw w≤w' in v' , v'Rw' , r v≤v' p

right : Hom (◆ P) Q → Hom P (□ Q)
right n .f {w} p {w'} wRw' = n .f (w , (wRw' , p))

left : Hom P (□ Q) → Hom (◆ P) Q
left n .f {w} (v , vRw , p) = n .f p vRw

unit : Hom P (□ (◆ P))
unit = right id

counit : Hom (◆ (□ P)) P
counit = left id

□-map :  Hom P Q → Hom (□ P) (□ Q)
□-map n .f x wRw' = n .f (x wRw')

◆-map :  Hom P Q → Hom (◆ P) (◆ Q)
◆-map n = left (unit ∘ n)

□-pr : Hom O (□ P) → Hom O (□ Q) → Hom O (□ (P x Q))
□-pr  {O} {P = P} {Q = Q} n m = right {P = O} {Q =  P x Q} (pr (counit ∘ ◆-map n) ((counit ∘ ◆-map m)))

□-! : Hom P (□ T)
□-! = right !

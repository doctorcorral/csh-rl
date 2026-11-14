{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.MountainCarSuccessor
--
-- MountainCar without reward shaping: the successor condition does
-- the work that engineered rewards used to do.
--
-- Earlier MountainCar modules (MountainCarAutoController) solve the
-- environment with an *inverted-fragility* reward — a future-aware,
-- engineered signal.  Here the reward is the honest myopic signal:
-- the altitude sin(3x) of the successor's representative point,
-- discretized to the sin(3x) ordering of the zone centers.  Nothing
-- about the future is smuggled into the reward.
--
-- Abstraction: 5 position zones × 4 velocity bins (sign AND magnitude,
-- so multi-swing energy pumping is representable) + GoalN + Terminal.
-- Transitions: 10 substeps of the same fixed-point Euler integrator
-- used by MountainCarAutoController (Taylor-7 cos, scale 10⁸), from
-- each state's representative point.  The 66-entry transition table
-- used by the proofs is certified against the integrator by refl
-- (table-matches-physics).
--
-- The physics of the abstraction (all machine-checked below):
--   * ML,v∈(-0.03,0) is DEAD: absorbing under every action — a car
--     drifting slowly leftward near the valley cannot escape, and its
--     value stream is constantly 0 (the valley altitude).
--   * FL,v∈(0,0.03) is the SACRIFICE state: pushing left keeps the
--     car on the left hill (altitude 1, a self-loop — it clings
--     forever); releasing it descends into the valley (altitude 0),
--     which is the only way to build the escape swing.
--
-- Synthesis: the same condition-agnostic CEGIS loop as SacrificeSynth,
-- with two labeling oracles computed from the environment:
--   myopic oracle    — compares successor altitudes (the immediate
--                      reward; CoindHomo's head)
--   successor oracle — compares successor value streams pointwise
--                      (CoinductiveHomomorphism), decided by a
--                      depth-9 bounded check + stabilization
--
-- Certified results:
--   ✓ the successor oracle synthesizes three depth-≤1 predicates
--     (L≤N = ¬CR, N≤R = vfast, L≤R = vfast ∧ ¬vneg) whose greedy
--     policy reaches the goal from the low-energy valley start in
--     7 macro-steps — including the altitude sacrifice at FL;
--   ✓ the myopic oracle's labels are blind where it matters (the
--     dead and alive successors of the valley states have equal
--     altitude), and its synthesized policy drives straight into
--     the dead state and stays there;
--   ✓ the synthesized ranking is a verified CoinductiveHomomorphism;
--   ✗ the head-compatibility check FAILS at the sacrifice state
--     (altitudes 1 > 0 contradict the ranking), so the upgrade to
--     CoindHomo is impossible — and indeed NO CoindHomo can rank the
--     sacrifice pair at FL,+slow in either direction: the action-value
--     streams are incomparable exactly where the decision matters.
--
-- This is BinarySacrifice's separation arising from genuine physics:
-- "descend to ascend" is invisible to head-first comparison and
-- teachable by the successor condition, with zero reward engineering.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.MountainCarSuccessor where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Codata.Guarded.Stream using (Stream; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

------------------------------------------------------------------------
-- Actions and the 22-state abstraction
------------------------------------------------------------------------

data MCAction : Set where
  PushLeft NoAction PushRight : MCAction

mc-actions : List MCAction
mc-actions = PushLeft ∷ NoAction ∷ PushRight ∷ []

-- position zones: FL [-1.2,-0.7), ML [-0.7,-0.2), VB [-0.2,0.1),
-- NR [0.1,0.35), CR [0.35,0.5); x ≥ 0.5 is the goal zone
data Zone : Set where
  zFL zML zVB zNR zCR : Zone

-- velocity bins: fast/slow × negative/positive (boundary |v| = 0.03)
data Vel : Set where
  vNf vNs vPs vPf : Vel

data MCState : Set where
  st       : Zone → Vel → MCState
  goalN    : MCState        -- x ≥ 0.5 moving left
  terminal : MCState        -- x ≥ 0.5 moving right: goal reached

pattern FLNf = st zFL vNf
pattern FLNs = st zFL vNs
pattern FLPs = st zFL vPs
pattern FLPf = st zFL vPf
pattern MLNf = st zML vNf
pattern MLNs = st zML vNs
pattern MLPs = st zML vPs
pattern MLPf = st zML vPf
pattern VBNf = st zVB vNf
pattern VBNs = st zVB vNs
pattern VBPs = st zVB vPs
pattern VBPf = st zVB vPf
pattern NRNf = st zNR vNf
pattern NRNs = st zNR vNs
pattern NRPs = st zNR vPs
pattern NRPf = st zNR vPf
pattern CRNf = st zCR vNf
pattern CRNs = st zCR vNs
pattern CRPs = st zCR vPs
pattern CRPf = st zCR vPf

all-states : List MCState
all-states =
  FLNf ∷ FLNs ∷ FLPs ∷ FLPf ∷
  MLNf ∷ MLNs ∷ MLPs ∷ MLPf ∷
  VBNf ∷ VBNs ∷ VBPs ∷ VBPf ∷
  NRNf ∷ NRNs ∷ NRPs ∷ NRPf ∷
  CRNf ∷ CRNs ∷ CRPs ∷ CRPf ∷
  goalN ∷ terminal ∷ []

------------------------------------------------------------------------
-- Fixed-point Euler physics (as in MountainCarAutoController, but with
-- 10 substeps per macro-step so that low-energy states change slowly
-- enough for pumping to be visible at the abstract level)
------------------------------------------------------------------------

private
  module FE where
    open import Data.Integer.Base as ℤ
      using (ℤ; +_; -[1+_])
      renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; -_ to ℤneg)
    open import Data.Integer.Properties as ℤP
      using () renaming (_<?_ to _<?ℤ_; _≤?_ to _≤?ℤ_)
    open import Data.Nat as ℕb using ()
    open import Data.Nat.DivMod using () renaming (_/_ to _ℕ/_)
    open import Relation.Nullary using (yes; no)

    Fixed : Set
    Fixed = ℤ

    SCALE : ℕ
    SCALE = 100000000

    negℕ : ℕ → ℤ
    negℕ zero    = + 0
    negℕ (suc n) = -[1+ n ]

    _quotℕ_ : ℤ → (d : ℕ) → .{{ℕb.NonZero d}} → ℤ
    (+ m)     quotℕ d = + (m ℕ/ d)
    -[1+ m ]  quotℕ d = negℕ (suc m ℕ/ d)

    _f*_ : Fixed → Fixed → Fixed
    a f* b = (a *ℤ b) quotℕ SCALE

    _f÷_ : Fixed → (d : ℕ) → .{{ℕb.NonZero d}} → Fixed
    a f÷ d = a quotℕ d

    infixl 7 _f*_ _f÷_

    cos₇ : Fixed → Fixed
    cos₇ y =
      let y²  = y  f* y
          y⁴  = y² f* y²
          y⁶  = y⁴ f* y²
          y⁸  = y⁶ f* y²
          y¹⁰ = y⁸ f* y²
          y¹² = y¹⁰ f* y²
      in (+ SCALE)
         +ℤ ℤneg (y²  f÷ 2) +ℤ (y⁴  f÷ 24)
         +ℤ ℤneg (y⁶  f÷ 720) +ℤ (y⁸  f÷ 40320)
         +ℤ ℤneg (y¹⁰ f÷ 3628800) +ℤ (y¹² f÷ 479001600)

    fclip : Fixed → Fixed → Fixed → Fixed
    fclip lo hi x with lo ≤?ℤ x
    ... | no  _ = lo
    ... | yes _ with x ≤?ℤ hi
    ...   | yes _ = x
    ...   | no  _ = hi

    -- inelastic wall at x = -1.2 (as in Gymnasium MountainCar)
    wall : Fixed → Fixed → Fixed
    wall x' v' with x' ≤?ℤ (ℤneg (+ 120000000))
    ... | no  _ = v'
    ... | yes _ with v' <?ℤ (+ 0)
    ...   | yes _ = + 0
    ...   | no  _ = v'

    act-f : MCAction → Fixed
    act-f PushLeft  = ℤneg (+ 100000)
    act-f NoAction  = + 0
    act-f PushRight = + 100000

    step-f : Fixed × Fixed → MCAction → Fixed × Fixed
    step-f (x , v) a =
      let grav = cos₇ ((+ 300000000) f* x) f* ℤneg (+ 250000)
          v'   = fclip (ℤneg (+ 7000000)) (+ 7000000)
                   (v +ℤ act-f a +ℤ grav)
          x'   = fclip (ℤneg (+ 120000000)) (+ 60000000) (x +ℤ v')
      in (x' , wall x' v')

    multi-f : ℕ → Fixed × Fixed → MCAction → Fixed × Fixed
    multi-f zero    s _ = s
    multi-f (suc n) s a = multi-f n (step-f s a) a

    zone-x : Zone → Fixed
    zone-x zFL = ℤneg (+ 95000000)
    zone-x zML = ℤneg (+ 45000000)
    zone-x zVB = ℤneg (+ 5000000)
    zone-x zNR = + 22500000
    zone-x zCR = + 42500000

    vel-v : Vel → Fixed
    vel-v vNf = ℤneg (+ 5000000)
    vel-v vNs = ℤneg (+ 1500000)
    vel-v vPs = + 1500000
    vel-v vPf = + 5000000

    embed-f : MCState → Fixed × Fixed
    embed-f (st z w) = (zone-x z , vel-v w)
    embed-f goalN    = (+ 55000000 , ℤneg (+ 1500000))
    embed-f terminal = (+ 55000000 , + 1500000)

    vbin : Fixed → Vel
    vbin v with v <?ℤ ℤneg (+ 3000000)
    ... | yes _ = vNf
    ... | no  _ with v <?ℤ (+ 0)
    ...   | yes _ = vNs
    ...   | no  _ with v <?ℤ (+ 3000000)
    ...     | yes _ = vPs
    ...     | no  _ = vPf

    proj-f : Fixed × Fixed → MCState
    proj-f (x , v) with x <?ℤ ℤneg (+ 70000000)
    ... | yes _ = st zFL (vbin v)
    ... | no  _ with x <?ℤ ℤneg (+ 20000000)
    ...   | yes _ = st zML (vbin v)
    ...   | no  _ with x <?ℤ (+ 10000000)
    ...     | yes _ = st zVB (vbin v)
    ...     | no  _ with x <?ℤ (+ 35000000)
    ...       | yes _ = st zNR (vbin v)
    ...       | no  _ with x <?ℤ (+ 50000000)
    ...         | yes _ = st zCR (vbin v)
    ...         | no  _ with v <?ℤ (+ 0)
    ...           | yes _ = goalN
    ...           | no  _ = terminal

    euler-f : MCState → MCAction → MCState
    euler-f terminal _ = terminal
    euler-f s a = proj-f (multi-f 10 (embed-f s) a)

-- the environment's true dynamics
euler-next : MCState → MCAction → MCState
euler-next = FE.euler-f

------------------------------------------------------------------------
-- Transition table (fast form used by all proofs), certified against
-- the integrator by table-matches-physics
------------------------------------------------------------------------

next : MCState → MCAction → MCState
next FLNf _         = FLPs
next FLNs PushLeft  = FLNs
next FLNs _         = FLPs
next FLPs PushLeft  = FLPs
next FLPs _         = MLPf
next FLPf _         = MLPf
next MLNf _         = FLNf
next MLNs _         = MLNs
next MLPs PushLeft  = MLNs
next MLPs _         = MLPs
next MLPf PushLeft  = VBPs
next MLPf _         = VBPf
next VBNf _         = MLNf
next VBNs PushRight = MLNs
next VBNs _         = MLNf
next VBPs PushRight = VBPs
next VBPs _         = VBNs
next VBPf PushRight = CRPf
next VBPf _         = NRPs
next NRNf _         = MLNf
next NRNs PushRight = VBNs
next NRNs _         = VBNf
next NRPs PushRight = NRPs
next NRPs _         = NRNs
next NRPf _         = terminal
next CRNf PushLeft  = MLNf
next CRNf _         = VBNf
next CRNs PushLeft  = NRNf
next CRNs _         = NRNs
next CRPs PushLeft  = CRPs
next CRPs _         = terminal
next CRPf _         = terminal
next goalN PushLeft = NRNs
next goalN _        = CRNs
next terminal _     = terminal

-- boolean state equality, for the physics-agreement certificate
eqZ : Zone → Zone → Bool
eqZ zFL zFL = true
eqZ zML zML = true
eqZ zVB zVB = true
eqZ zNR zNR = true
eqZ zCR zCR = true
eqZ _   _   = false

eqV : Vel → Vel → Bool
eqV vNf vNf = true
eqV vNs vNs = true
eqV vPs vPs = true
eqV vPf vPf = true
eqV _   _   = false

eqMC : MCState → MCState → Bool
eqMC (st z w) (st z' w') = eqZ z z' ∧ eqV w w'
eqMC goalN    goalN      = true
eqMC terminal terminal   = true
eqMC _        _          = false

check-all : (MCState → Bool) → Bool
check-all f = foldr _∧_ true (map f all-states)

-- every table entry agrees with 10 substeps of Euler integration
table-matches-physics :
  check-all (λ s → eqMC (next s PushLeft)  (euler-next s PushLeft)
               ∧ eqMC (next s NoAction)  (euler-next s NoAction)
               ∧ eqMC (next s PushRight) (euler-next s PushRight))
  ≡ true
table-matches-physics = refl

------------------------------------------------------------------------
-- The honest reward: altitude of the successor's representative point.
-- sin(3x) at the zone centers orders them
--   ML (-0.98) < FL (-0.29) < VB (-0.15) < NR (0.63) < CR (0.96) < goal
------------------------------------------------------------------------

alt : MCState → ℕ
alt (st zML _) = 0
alt (st zFL _) = 1
alt (st zVB _) = 2
alt (st zNR _) = 3
alt (st zCR _) = 4
alt goalN      = 5
alt terminal   = 5

step-alt : MCState → MCAction → MCState × ℕ
step-alt s a = (next s a , alt (next s a))

------------------------------------------------------------------------
-- Synthesis infrastructure (Core opened publicly inside)
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis MCState MCAction step-alt mc-actions

open import CSHRL.Core.CoinductiveHomomorphism
open SuccessorCore MCState MCAction ℕ step-alt _≤_ _⊔_ 0 mc-actions
  using ( successor-value; CoinductiveHomomorphism )

------------------------------------------------------------------------
-- Features: zone and velocity indicators (no engineered combinations)
------------------------------------------------------------------------

data Feature : Set where
  fFL fML fVB fNR fCR fVneg fVfast : Feature

eval-feature : Feature → MCState → Bool
eval-feature fFL    (st zFL _) = true
eval-feature fFL    _          = false
eval-feature fML    (st zML _) = true
eval-feature fML    _          = false
eval-feature fVB    (st zVB _) = true
eval-feature fVB    _          = false
eval-feature fNR    (st zNR _) = true
eval-feature fNR    _          = false
eval-feature fCR    (st zCR _) = true
eval-feature fCR    _          = false
eval-feature fVneg  (st _ vNf) = true
eval-feature fVneg  (st _ vNs) = true
eval-feature fVneg  goalN      = true
eval-feature fVneg  _          = false
eval-feature fVfast (st _ vNf) = true
eval-feature fVfast (st _ vPf) = true
eval-feature fVfast _          = false

all-features : List Feature
all-features = fFL ∷ fML ∷ fVB ∷ fNR ∷ fCR ∷ fVneg ∷ fVfast ∷ []

open WithStateFeatures Feature eval-feature
open WithCEGIS all-features

------------------------------------------------------------------------
-- The two labeling oracles, computed from the environment
--
-- Value streams on this MDP stabilize at depth 8 (solve-stable below),
-- so a pointwise bounded check to depth 8 decides full stream
-- dominance.  The myopic oracle sees only the successor altitude —
-- CoindHomo's head.
------------------------------------------------------------------------

lebool : ℕ → ℕ → Bool
lebool zero    _       = true
lebool (suc m) zero    = false
lebool (suc m) (suc n) = lebool m n

-- pointwise dominance of value streams, depths 0..8 (right-nested)
dom9 : MCState → MCState → Bool
dom9 s₁ s₂ =
  lebool (solve s₁ 0) (solve s₂ 0) ∧
  (lebool (solve s₁ 1) (solve s₂ 1) ∧
  (lebool (solve s₁ 2) (solve s₂ 2) ∧
  (lebool (solve s₁ 3) (solve s₂ 3) ∧
  (lebool (solve s₁ 4) (solve s₂ 4) ∧
  (lebool (solve s₁ 5) (solve s₂ 5) ∧
  (lebool (solve s₁ 6) (solve s₂ 6) ∧
  (lebool (solve s₁ 7) (solve s₂ 7) ∧
   lebool (solve s₁ 8) (solve s₂ 8))))))))

succ-cmp : MCState → MCAction → MCAction → Bool
succ-cmp s a b = dom9 (next s a) (next s b)

myopic-cmp : MCState → MCAction → MCAction → Bool
myopic-cmp s a b = lebool (alt (next s a)) (alt (next s b))

------------------------------------------------------------------------
-- Observations: online CEGIS along the agent's own trajectory, plus
-- the counterexamples produced by the CEGAR verification sweep
-- (whose final soundness is certified by sound-LN / sound-LR /
-- sound-NR below).  All labels are computed by the environment
-- oracles, never written by hand.
------------------------------------------------------------------------

probes-LN probes-LR probes-NR : List MCState
probes-LN = VBNs ∷ MLNf ∷ FLNf ∷ FLPs ∷ CRNf ∷ []
probes-LR = MLPf ∷ VBPf ∷ CRPf ∷ VBNs ∷ CRNf ∷ VBPs ∷ []
probes-NR = MLPf ∷ VBPf ∷ CRPf ∷ VBNs ∷ []

obs-of : (MCState → MCAction → MCAction → Bool) →
         MCAction → MCAction → List MCState → List PredObs
obs-of cmp a b = map (λ s → s , cmp s a b)

-- The observation lists are spelled out as literals so that the
-- (expensive) oracle is evaluated once, in the honesty certificates
-- below — not on every use of the synthesized model.
obs-LN obs-LR obs-NR : List PredObs
obs-LN = (VBNs , true) ∷ (MLNf , true) ∷ (FLNf , true) ∷
         (FLPs , true) ∷ (CRNf , false) ∷ []
obs-LR = (MLPf , true) ∷ (VBPf , true) ∷ (CRPf , true) ∷
         (VBNs , false) ∷ (CRNf , false) ∷ (VBPs , false) ∷ []
obs-NR = (MLPf , true) ∷ (VBPf , true) ∷ (CRPf , true) ∷
         (VBNs , false) ∷ []

obs-LN-honest : obs-LN ≡ obs-of succ-cmp PushLeft NoAction probes-LN
obs-LN-honest = refl

obs-LR-honest : obs-LR ≡ obs-of succ-cmp PushLeft PushRight probes-LR
obs-LR-honest = refl

obs-NR-honest : obs-NR ≡ obs-of succ-cmp NoAction PushRight probes-NR
obs-NR-honest = refl

myobs-LN myobs-LR myobs-NR : List PredObs
myobs-LN = (VBNs , true) ∷ (MLNf , true) ∷ (FLNf , true) ∷
           (FLPs , false) ∷ (CRNf , true) ∷ []
myobs-LR = (MLPf , true) ∷ (VBPf , true) ∷ (CRPf , true) ∷
           (VBNs , true) ∷ (CRNf , true) ∷ (VBPs , true) ∷ []
myobs-NR = (MLPf , true) ∷ (VBPf , true) ∷ (CRPf , true) ∷
           (VBNs , true) ∷ []

myobs-LN-honest : myobs-LN ≡ obs-of myopic-cmp PushLeft NoAction probes-LN
myobs-LN-honest = refl

myobs-LR-honest : myobs-LR ≡ obs-of myopic-cmp PushLeft PushRight probes-LR
myobs-LR-honest = refl

myobs-NR-honest : myobs-NR ≡ obs-of myopic-cmp NoAction PushRight probes-NR
myobs-NR-honest = refl

from-just : Maybe PredProg → PredProg
from-just (just p) = p
from-just nothing  = falsep

------------------------------------------------------------------------
-- One CEGIS loop, two oracles
------------------------------------------------------------------------

pred-LN pred-LR pred-NR : PredProg
pred-LN = from-just (synth-rank-pred 1 obs-LN)
pred-LR = from-just (synth-rank-pred 1 obs-LR)
pred-NR = from-just (synth-rank-pred 1 obs-NR)

my-LN my-LR my-NR : PredProg
my-LN = from-just (synth-rank-pred 1 myobs-LN)
my-LR = from-just (synth-rank-pred 1 myobs-LR)
my-NR = from-just (synth-rank-pred 1 myobs-NR)

-- What was learned: three one-line predicates.
test-learned-LN : pred-LN ≡ ¬p feat fCR
test-learned-LN = refl

test-learned-NR : pred-NR ≡ feat fVfast
test-learned-NR = refl

test-learned-LR : pred-LR ≡ feat fVfast ∧p ¬p feat fVneg
test-learned-LR = refl

-- The myopic oracle learns blindness: at the valley decisions all
-- successor altitudes tie, so CEGIS keeps trivial predicates ...
test-myopic-LN : my-LN ≡ feat fVneg
test-myopic-LN = refl

test-myopic-LR : my-LR ≡ truep
test-myopic-LR = refl

test-myopic-NR : my-NR ≡ truep
test-myopic-NR = refl

-- ... and where it is NOT blind, it points the wrong way: at the
-- sacrifice state the myopic oracle refuses the ranking that the
-- successor oracle certifies.
test-labels-conflict : myopic-cmp FLPs PushLeft NoAction ≡ false
test-labels-conflict = refl

test-succ-ranks-sacrifice : succ-cmp FLPs PushLeft NoAction ≡ true
test-succ-ranks-sacrifice = refl

-- the sacrifice in rewards: clinging pays 1 now, releasing pays 0
test-cling-reward : proj₂ (step-alt FLPs PushLeft) ≡ 1
test-cling-reward = refl

test-release-reward : proj₂ (step-alt FLPs NoAction) ≡ 0
test-release-reward = refl

------------------------------------------------------------------------
-- The synthesized ranking models
------------------------------------------------------------------------

succ-model : RankModel
succ-model = record { prefer = pf }
  where
  pf : MCAction → MCAction → PredProg
  pf PushLeft  NoAction  = pred-LN
  pf PushLeft  PushRight = pred-LR
  pf NoAction  PushRight = pred-NR
  pf PushLeft  PushLeft  = truep
  pf NoAction  NoAction  = truep
  pf PushRight PushRight = truep
  pf NoAction  PushLeft  = falsep
  pf PushRight PushLeft  = falsep
  pf PushRight NoAction  = falsep

myopic-model : RankModel
myopic-model = record { prefer = pf }
  where
  pf : MCAction → MCAction → PredProg
  pf PushLeft  NoAction  = my-LN
  pf PushLeft  PushRight = my-LR
  pf NoAction  PushRight = my-NR
  pf PushLeft  PushLeft  = truep
  pf NoAction  NoAction  = truep
  pf PushRight PushRight = truep
  pf NoAction  PushLeft  = falsep
  pf PushRight PushLeft  = falsep
  pf PushRight NoAction  = falsep

------------------------------------------------------------------------
-- CEGAR verification sweep: wherever the learned ranking claims
-- a ≤ b, the environment's dominance oracle agrees — on ALL 22
-- states, not just the probed ones.  (The false-labeled probes above
-- are exactly the counterexamples this sweep produced during
-- learning.)
------------------------------------------------------------------------

impliesᵇ : Bool → Bool → Bool
impliesᵇ true  y = y
impliesᵇ false _ = true

sound-LN : check-all (λ s → impliesᵇ (rank-eval succ-model s PushLeft NoAction)
                                     (succ-cmp s PushLeft NoAction)) ≡ true
sound-LN = refl

sound-LR : check-all (λ s → impliesᵇ (rank-eval succ-model s PushLeft PushRight)
                                     (succ-cmp s PushLeft PushRight)) ≡ true
sound-LR = refl

sound-NR : check-all (λ s → impliesᵇ (rank-eval succ-model s NoAction PushRight)
                                     (succ-cmp s NoAction PushRight)) ≡ true
sound-NR = refl

------------------------------------------------------------------------
-- Deployed behavior: greedy rollouts of the two learned rankings
------------------------------------------------------------------------

greedy : RankModel → MCState → MCAction
greedy m s =
  if rank-eval m s PushLeft PushRight ∧ rank-eval m s NoAction PushRight
  then PushRight
  else (if rank-eval m s PushLeft NoAction then NoAction else PushLeft)

run : (MCState → MCAction) → ℕ → MCState → MCState
run π zero    s = s
run π (suc n) s = run π n (next s (π s))

-- start: the low-energy valley state (drifting slowly leftward at
-- the bottom).  The successor policy pumps the swing and escapes in
-- 7 macro-steps: VBNs → MLNf → FLNf → FLPs → MLPf → VBPf → CRPf → goal
start : MCState
start = VBNs

test-solves : run (greedy succ-model) 7 start ≡ terminal
test-solves = refl

-- the sacrifice, executed: at FL,+slow the policy stops pushing
test-policy-sacrifices : greedy succ-model FLPs ≡ NoAction
test-policy-sacrifices = refl

-- the myopic policy stalls in the dead state it cannot see:
-- VBNs → MLNs → MLNs → ...
test-myopic-stuck : run (greedy myopic-model) 20 start ≡ MLNs
test-myopic-stuck = refl

-- dead vs alive, in the value function
test-dead : solve MLNs 8 ≡ 0
test-dead = refl

test-alive : solve start 8 ≡ 5
test-alive = refl

------------------------------------------------------------------------
-- Stream machinery: stabilization at depth 8 turns the bounded
-- dominance checks into full coinductive stream dominance
------------------------------------------------------------------------

≤ₛ-refl : ∀ s → s ≤ₛ s
head≤ (≤ₛ-refl s) = ≤-refl
tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

tab-≤ₛ : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≤ g n) → tabulate f ≤ₛ tabulate g
head≤ (tab-≤ₛ pw) = pw zero
tail≤ (tab-≤ₛ pw) = tab-≤ₛ (λ n → pw (suc n))

-- one more step after depth 8 changes nothing (finite check, 22 states)
stable-step : ∀ s → solve s 9 ≡ solve s 8
stable-step FLNf = refl
stable-step FLNs = refl
stable-step FLPs = refl
stable-step FLPf = refl
stable-step MLNf = refl
stable-step MLNs = refl
stable-step MLPs = refl
stable-step MLPf = refl
stable-step VBNf = refl
stable-step VBNs = refl
stable-step VBPs = refl
stable-step VBPf = refl
stable-step NRNf = refl
stable-step NRNs = refl
stable-step NRPs = refl
stable-step NRPf = refl
stable-step CRNf = refl
stable-step CRNs = refl
stable-step CRPs = refl
stable-step CRPf = refl
stable-step goalN = refl
stable-step terminal = refl

max3-cong : ∀ {x y z x' y' z' : ℕ} → x ≡ x' → y ≡ y' → z ≡ z' →
            max-list (x ∷ y ∷ z ∷ []) ≡ max-list (x' ∷ y' ∷ z' ∷ [])
max3-cong refl refl refl = refl

-- ... hence nothing changes at any depth beyond 8
solve-stable : ∀ s n → solve s (8 + n) ≡ solve s 8
solve-stable s zero    = refl
solve-stable s (suc n) =
  trans (max3-cong (solve-stable (next s PushLeft)  n)
                   (solve-stable (next s NoAction)  n)
                   (solve-stable (next s PushRight) n))
        (stable-step s)

lebool-sound : ∀ m n → lebool m n ≡ true → m ≤ n
lebool-sound zero    _       _  = z≤n
lebool-sound (suc m) (suc n) eq = s≤s (lebool-sound m n eq)

-- bounded pointwise dominance (depths 0..8) + stabilization
-- ⟹ full coinductive stream dominance
dom-via : ∀ s₁ s₂ →
  solve s₁ 0 ≤ solve s₂ 0 → solve s₁ 1 ≤ solve s₂ 1 →
  solve s₁ 2 ≤ solve s₂ 2 → solve s₁ 3 ≤ solve s₂ 3 →
  solve s₁ 4 ≤ solve s₂ 4 → solve s₁ 5 ≤ solve s₂ 5 →
  solve s₁ 6 ≤ solve s₂ 6 → solve s₁ 7 ≤ solve s₂ 7 →
  solve s₁ 8 ≤ solve s₂ 8 →
  value s₁ ≤ₛ value s₂
dom-via s₁ s₂ a0 a1 a2 a3 a4 a5 a6 a7 a8 = tab-≤ₛ pw
  where
  pw : ∀ n → solve s₁ n ≤ solve s₂ n
  pw 0 = a0
  pw 1 = a1
  pw 2 = a2
  pw 3 = a3
  pw 4 = a4
  pw 5 = a5
  pw 6 = a6
  pw 7 = a7
  pw 8 = a8
  pw (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))
    rewrite solve-stable s₁ (suc m) | solve-stable s₂ (suc m) = a8

------------------------------------------------------------------------
-- The five nontrivial dominance facts (streams read off the table;
-- each bounded inequality is checked by closed normalization)
------------------------------------------------------------------------

private
  ≤! : ∀ {m n} → lebool m n ≡ true → m ≤ n
  ≤! {m} {n} = lebool-sound m n

-- (1,1,2,4,5,…) ≤ (1,2,4,5,5,…) : slowing on the left hill vs release
dom-FLNs-FLPs : value FLNs ≤ₛ value FLPs
dom-FLNs-FLPs = dom-via FLNs FLPs
  (≤! refl) (≤! refl) (≤! refl) (≤! refl) (≤! refl)
  (≤! refl) (≤! refl) (≤! refl) (≤! refl)

-- (1,2,4,5,…) ≤ (2,4,5,5,…) : THE SACRIFICE — clinging vs descending
dom-FLPs-MLPf : value FLPs ≤ₛ value MLPf
dom-FLPs-MLPf = dom-via FLPs MLPf
  (≤! refl) (≤! refl) (≤! refl) (≤! refl) (≤! refl)
  (≤! refl) (≤! refl) (≤! refl) (≤! refl)

-- (2,2,2,2,2,2,4,5,5) ≤ (4,5,…) : braking vs riding the fast swing
dom-VBPs-VBPf : value VBPs ≤ₛ value VBPf
dom-VBPs-VBPf = dom-via VBPs VBPf
  (≤! refl) (≤! refl) (≤! refl) (≤! refl) (≤! refl)
  (≤! refl) (≤! refl) (≤! refl) (≤! refl)

-- (3,3,3,3,3,3,3,4,5) ≤ (5,…) : stalling on the right slope vs goal
dom-NRPs-CRPf : value NRPs ≤ₛ value CRPf
dom-NRPs-CRPf = dom-via NRPs CRPf
  (≤! refl) (≤! refl) (≤! refl) (≤! refl) (≤! refl)
  (≤! refl) (≤! refl) (≤! refl) (≤! refl)

-- (2,0,1,1,1,2,4,5,5) ≤ (3,2,1,1,1,2,4,5,5) : falling back from goalN
dom-NRNs-CRNs : value NRNs ≤ₛ value CRNs
dom-NRNs-CRNs = dom-via NRNs CRNs
  (≤! refl) (≤! refl) (≤! refl) (≤! refl) (≤! refl)
  (≤! refl) (≤! refl) (≤! refl) (≤! refl)

-- the dead states: constant-0 streams
solve-MLNs : ∀ n → solve MLNs n ≡ 0
solve-MLNs zero    = refl
solve-MLNs (suc n) rewrite solve-MLNs n = refl

solve-MLPs : ∀ n → solve MLPs n ≡ 0
solve-MLPs zero    = refl
solve-MLPs (suc n) rewrite solve-MLNs n | solve-MLPs n = refl

dom-MLNs-MLPs : value MLNs ≤ₛ value MLPs
dom-MLNs-MLPs = tab-≤ₛ pw
  where
  pw : ∀ n → solve MLNs n ≤ solve MLPs n
  pw n rewrite solve-MLNs n = z≤n

------------------------------------------------------------------------
-- The synthesized ranking is a verified CoinductiveHomomorphism
------------------------------------------------------------------------

succ-preserves : ∀ a b s → RankHolds succ-model s a b →
                 successor-value s a ≤ₛ successor-value s b
-- diagonal entries: truep, equal successors
succ-preserves PushLeft  PushLeft  s _ = ≤ₛ-refl (successor-value s PushLeft)
succ-preserves NoAction  NoAction  s _ = ≤ₛ-refl (successor-value s NoAction)
succ-preserves PushRight PushRight s _ = ≤ₛ-refl (successor-value s PushRight)
-- reverse entries: falsep, vacuous
succ-preserves NoAction  PushLeft  _ ()
succ-preserves PushRight PushLeft  _ ()
succ-preserves PushRight NoAction  _ ()
-- L ≤ N holds where ¬CR: 18 states
succ-preserves PushLeft NoAction FLNf _ = ≤ₛ-refl (value FLPs)
succ-preserves PushLeft NoAction FLNs _ = dom-FLNs-FLPs
succ-preserves PushLeft NoAction FLPs _ = dom-FLPs-MLPf
succ-preserves PushLeft NoAction FLPf _ = ≤ₛ-refl (value MLPf)
succ-preserves PushLeft NoAction MLNf _ = ≤ₛ-refl (value FLNf)
succ-preserves PushLeft NoAction MLNs _ = ≤ₛ-refl (value MLNs)
succ-preserves PushLeft NoAction MLPs _ = dom-MLNs-MLPs
succ-preserves PushLeft NoAction MLPf _ = dom-VBPs-VBPf
succ-preserves PushLeft NoAction VBNf _ = ≤ₛ-refl (value MLNf)
succ-preserves PushLeft NoAction VBNs _ = ≤ₛ-refl (value MLNf)
succ-preserves PushLeft NoAction VBPs _ = ≤ₛ-refl (value VBNs)
succ-preserves PushLeft NoAction VBPf _ = ≤ₛ-refl (value NRPs)
succ-preserves PushLeft NoAction NRNf _ = ≤ₛ-refl (value MLNf)
succ-preserves PushLeft NoAction NRNs _ = ≤ₛ-refl (value VBNf)
succ-preserves PushLeft NoAction NRPs _ = ≤ₛ-refl (value NRNs)
succ-preserves PushLeft NoAction NRPf _ = ≤ₛ-refl (value terminal)
succ-preserves PushLeft NoAction CRNf ()
succ-preserves PushLeft NoAction CRNs ()
succ-preserves PushLeft NoAction CRPs ()
succ-preserves PushLeft NoAction CRPf ()
succ-preserves PushLeft NoAction goalN _ = dom-NRNs-CRNs
succ-preserves PushLeft NoAction terminal _ = ≤ₛ-refl (value terminal)
-- L ≤ R holds where vfast ∧ ¬vneg: the 5 fast-positive states
succ-preserves PushLeft PushRight FLNf ()
succ-preserves PushLeft PushRight FLNs ()
succ-preserves PushLeft PushRight FLPs ()
succ-preserves PushLeft PushRight FLPf _ = ≤ₛ-refl (value MLPf)
succ-preserves PushLeft PushRight MLNf ()
succ-preserves PushLeft PushRight MLNs ()
succ-preserves PushLeft PushRight MLPs ()
succ-preserves PushLeft PushRight MLPf _ = dom-VBPs-VBPf
succ-preserves PushLeft PushRight VBNf ()
succ-preserves PushLeft PushRight VBNs ()
succ-preserves PushLeft PushRight VBPs ()
succ-preserves PushLeft PushRight VBPf _ = dom-NRPs-CRPf
succ-preserves PushLeft PushRight NRNf ()
succ-preserves PushLeft PushRight NRNs ()
succ-preserves PushLeft PushRight NRPs ()
succ-preserves PushLeft PushRight NRPf _ = ≤ₛ-refl (value terminal)
succ-preserves PushLeft PushRight CRNf ()
succ-preserves PushLeft PushRight CRNs ()
succ-preserves PushLeft PushRight CRPs ()
succ-preserves PushLeft PushRight CRPf _ = ≤ₛ-refl (value terminal)
succ-preserves PushLeft PushRight goalN ()
succ-preserves PushLeft PushRight terminal ()
-- N ≤ R holds where vfast: the 10 fast states
succ-preserves NoAction PushRight FLNf _ = ≤ₛ-refl (value FLPs)
succ-preserves NoAction PushRight FLNs ()
succ-preserves NoAction PushRight FLPs ()
succ-preserves NoAction PushRight FLPf _ = ≤ₛ-refl (value MLPf)
succ-preserves NoAction PushRight MLNf _ = ≤ₛ-refl (value FLNf)
succ-preserves NoAction PushRight MLNs ()
succ-preserves NoAction PushRight MLPs ()
succ-preserves NoAction PushRight MLPf _ = ≤ₛ-refl (value VBPf)
succ-preserves NoAction PushRight VBNf _ = ≤ₛ-refl (value MLNf)
succ-preserves NoAction PushRight VBNs ()
succ-preserves NoAction PushRight VBPs ()
succ-preserves NoAction PushRight VBPf _ = dom-NRPs-CRPf
succ-preserves NoAction PushRight NRNf _ = ≤ₛ-refl (value MLNf)
succ-preserves NoAction PushRight NRNs ()
succ-preserves NoAction PushRight NRPs ()
succ-preserves NoAction PushRight NRPf _ = ≤ₛ-refl (value terminal)
succ-preserves NoAction PushRight CRNf _ = ≤ₛ-refl (value VBNf)
succ-preserves NoAction PushRight CRNs ()
succ-preserves NoAction PushRight CRPs ()
succ-preserves NoAction PushRight CRPf _ = ≤ₛ-refl (value terminal)
succ-preserves NoAction PushRight goalN ()
succ-preserves NoAction PushRight terminal ()

synthesized-homo : CoinductiveHomomorphism
synthesized-homo = record
  { _≤ₐ_      = RankHolds succ-model
  ; preserves = succ-preserves
  }

------------------------------------------------------------------------
-- The head check FAILS — and that failure certifies genuine sacrifice
--
-- The upgrade theorem CoinductiveHomomorphism+Head→CoindHomo needs
-- immediate rewards to respect the ranking.  At the sacrifice state
-- they cannot: the ranking holds PushLeft ≤ NoAction, but the
-- altitude reward pays 1 for clinging and 0 for releasing.
------------------------------------------------------------------------

head-compat-impossible :
  (∀ a b s → RankHolds succ-model s a b →
             proj₂ (step-alt s a) ≤ proj₂ (step-alt s b)) → ⊥
head-compat-impossible hc with hc PushLeft NoAction FLPs refl
... | ()

------------------------------------------------------------------------
-- Stronger: NO CoindHomo whatsoever can rank the sacrifice pair at
-- FL,+slow, in either direction — the action-value streams are
-- incomparable exactly where the decision matters.
--
--   av(FLPs, PushLeft) = 1 ∷ (1,2,4,5,…)    (cling: pay now, stall)
--   av(FLPs, NoAction) = 0 ∷ (2,4,5,5,…)    (release: sacrifice, go)
--
-- Forward fails at the head (1 ≰ 0); reverse fails one step into
-- the tail (2 ≰ 1).
------------------------------------------------------------------------

no-coindhomo-ranks-sacrifice :
  (h : CoindHomo) → CoindHomo._≤ₐ_ h FLPs PushLeft NoAction → ⊥
no-coindhomo-ranks-sacrifice h prf
  with head≤ (CoindHomo.preserves h PushLeft NoAction FLPs prf)
... | ()

no-coindhomo-ranks-cling :
  (h : CoindHomo) → CoindHomo._≤ₐ_ h FLPs NoAction PushLeft → ⊥
no-coindhomo-ranks-cling h prf
  with head≤ (tail≤ (CoindHomo.preserves h NoAction PushLeft FLPs prf))
... | s≤s ()

{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SacrificeDepthSynth
--
-- Climbing the sacrifice hierarchy: one CEGIS loop, three shift depths.
--
-- The environment is Chain 1 from Tasks.Verified.SacrificeChain — a
-- two-step bribe (sacrifice depth 2):
--
--   start ──delay (r=0)──▸ pst 1 ─r=0─▸ pst 0 ⟳ (r=1)
--         ╲─bribe (r=1)──▸ tst 1 ─r=1─▸ tst 0 ⟳ (r=0)
--
-- The labeling oracle is the SAME bounded pointwise-dominance check at
-- three shift depths k = 0, 1, 2 (compare the action-value streams
-- after discarding k entries).  Certified results:
--
--   ✗ k = 0 (CoindHomo-style) is SILENT at start: both orderings are
--     refuted by the crossing streams, CEGIS learns "never claim at
--     start", and the deployed policy falls back on its default bias —
--     the bribe.  10-step return: 2.
--   ✗ k = 1 (successor-style, the condition that solved BinarySacrifice
--     and MountainCar) is ALSO silent: one dropped entry is not enough
--     for a two-step bribe.  Same learned predicates, same return: 2.
--     The synthesized k=1 ranking is still a verified (vacuously sound)
--     ShiftedHomomorphism 1 — sound but useless where it matters.
--   ✓ k = 2 ranks the sacrifice: CEGIS learns truep for
--     bribe ≤ delay, the policy takes the paradise arm, return: 8, and
--     the synthesized ranking is a verified ShiftedHomomorphism 2.
--   ✗ The rung-2 instance cannot be upgraded to rung 1: the entry-1
--     compatibility check fails at start (second bribe installment
--     1 > 0).  And by the parametric theorems of SacrificeChain, no
--     rung-0 or rung-1 homomorphism AT ALL ranks the sacrifice — in
--     particular no CoindHomo and no CoinductiveHomomorphism — while
--     no rung, however deep, ever ranks the bribe above the delay.
--
-- Silence, not error, is the failure mode below the sacrifice depth:
-- an oracle that cannot rank the decisive pair leaves the agent to its
-- bias.  The sacrifice depth is exactly the shift at which the
-- environment's delayed reward becomes teachable.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SacrificeDepthSynth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _≤ᵇ_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- The environment and the parametric hierarchy theorems, instantiated
-- at arm length 2 (n = 1)
------------------------------------------------------------------------

open import CSHRL.Tasks.Verified.SacrificeChain
open Chain 1
  using ( State; start; pst; tst
        ; Action; delay; bribe
        ; step; all-actions
        ; sacrifice-silent-below; greed-never-ranked
        ; bribe-dominates; ranks-at-depth )

------------------------------------------------------------------------
-- Synthesis infrastructure (Core opened publicly inside)
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis State Action step all-actions

open import CSHRL.Core.CoinductiveHomomorphism
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions
  using (CoinductiveHomomorphism)

open import CSHRL.Core.ShiftedHomomorphism
open ShiftedCore State Action ℕ step _≤_ _⊔_ 0 all-actions
  using ( dropₛ; shifted-value; ShiftedHomomorphism
        ; CoindHomo→Shifted0; CoinductiveHomomorphism→Shifted1 )

------------------------------------------------------------------------
-- Features: arm indicators (identity abstraction on the three regions)
------------------------------------------------------------------------

data Feature : Set where
  at-start on-parm on-tarm : Feature

eval-feature : Feature → State → Bool
eval-feature at-start start   = true
eval-feature at-start _       = false
eval-feature on-parm  (pst _) = true
eval-feature on-parm  _       = false
eval-feature on-tarm  (tst _) = true
eval-feature on-tarm  _       = false

all-features : List Feature
all-features = at-start ∷ on-parm ∷ on-tarm ∷ []

open WithStateFeatures Feature eval-feature
open WithCEGIS all-features

------------------------------------------------------------------------
-- One oracle family: bounded pointwise dominance at shift depth k
--
-- The comparison is the SAME at every rung — only the number of
-- discarded stream entries changes.  (The 5-entry window covers the
-- crossing: both streams are constant from entry 3 on.)
------------------------------------------------------------------------

pointwise-leᵇ : ℕ → StreamR → StreamR → Bool
pointwise-leᵇ zero    _ _ = true
pointwise-leᵇ (suc m) x y =
  (head x ≤ᵇ head y) ∧ pointwise-leᵇ m (tail x) (tail y)

window : ℕ
window = 5

shift-cmp : ℕ → State → Action → Action → Bool
shift-cmp k s a b =
  pointwise-leᵇ window (dropₛ k (action-value s a)) (dropₛ k (action-value s b))

-- Labels at start: rungs 0 and 1 are silent (both orderings refuted
-- by the crossing streams); rung 2 ranks the sacrifice.
test-k0-silent     : shift-cmp 0 start bribe delay ≡ false
test-k0-silent     = refl
test-k0-silent-rev : shift-cmp 0 start delay bribe ≡ false
test-k0-silent-rev = refl

test-k1-silent     : shift-cmp 1 start bribe delay ≡ false
test-k1-silent     = refl
test-k1-silent-rev : shift-cmp 1 start delay bribe ≡ false
test-k1-silent-rev = refl

test-k2-ranks   : shift-cmp 2 start bribe delay ≡ true
test-k2-ranks   = refl
test-k2-refuses : shift-cmp 2 start delay bribe ≡ false
test-k2-refuses = refl

------------------------------------------------------------------------
-- One CEGIS loop, three rungs
------------------------------------------------------------------------

probes : List State
probes = start ∷ pst 1 ∷ pst 0 ∷ tst 1 ∷ tst 0 ∷ []

obs-at : ℕ → Action → Action → List PredObs
obs-at k a b = map (λ s → s , shift-cmp k s a b) probes

from-just : Maybe PredProg → PredProg
from-just (just p) = p
from-just nothing  = falsep

model-at : ℕ → RankModel
model-at k = record
  { prefer = λ a b → from-just (synth-rank-pred 1 (obs-at k a b)) }

k0-model k1-model k2-model : RankModel
k0-model = model-at 0
k1-model = model-at 1
k2-model = model-at 2

-- What each rung learns for the decisive pair bribe ≤ delay:
-- silence below the sacrifice depth ("claim anywhere but start"),
-- the unconditional claim at it.
test-k0-learned : RankModel.prefer k0-model bribe delay ≡ ¬p (feat at-start)
test-k0-learned = refl

test-k1-learned : RankModel.prefer k1-model bribe delay ≡ ¬p (feat at-start)
test-k1-learned = refl

test-k2-learned : RankModel.prefer k2-model bribe delay ≡ truep
test-k2-learned = refl

test-k2-learned-rev : RankModel.prefer k2-model delay bribe ≡ ¬p (feat at-start)
test-k2-learned-rev = refl

-- At the decision point:
test-k0-cannot : rank-eval k0-model start bribe delay ≡ false
test-k0-cannot = refl

test-k1-cannot : rank-eval k1-model start bribe delay ≡ false
test-k1-cannot = refl

test-k2-teaches : rank-eval k2-model start bribe delay ≡ true
test-k2-teaches = refl

------------------------------------------------------------------------
-- Deployed behavior: silence defaults to the bribe
--
-- The agent's bias is the immediately paying action; only a certified
-- ranking of bribe below delay overrides it.
------------------------------------------------------------------------

greedy : RankModel → State → Action
greedy m s = if rank-eval m s bribe delay then delay else bribe

run-return : (State → Action) → State → ℕ → ℕ
run-return π s zero    = 0
run-return π s (suc n) with step s (π s)
... | (s' , r) = r + run-return π s' n

test-k0-return : run-return (greedy k0-model) start 10 ≡ 2
test-k0-return = refl

test-k1-return : run-return (greedy k1-model) start 10 ≡ 2
test-k1-return = refl

test-k2-return : run-return (greedy k2-model) start 10 ≡ 8
test-k2-return = refl

------------------------------------------------------------------------
-- The rung-2 synthesized ranking is a verified ShiftedHomomorphism 2
--
-- Off the start state both actions coincide, so every claim there is
-- reflexive; at start the claim is exactly the certified dominance
-- from SacrificeChain.
------------------------------------------------------------------------

≤ₛ-refl : ∀ x → x ≤ₛ x
head≤ (≤ₛ-refl x) = ≤-refl
tail≤ (≤ₛ-refl x) = ≤ₛ-refl (tail x)

k2-preserves : ∀ a b s → RankHolds k2-model s a b →
               shifted-value 2 s a ≤ₛ shifted-value 2 s b
k2-preserves delay delay s             _  = ≤ₛ-refl (shifted-value 2 s delay)
k2-preserves bribe bribe s             _  = ≤ₛ-refl (shifted-value 2 s bribe)
k2-preserves bribe delay start         _  = bribe-dominates
k2-preserves bribe delay (pst zero)    _  = ≤ₛ-refl (shifted-value 2 (pst zero) bribe)
k2-preserves bribe delay (pst (suc m)) _  = ≤ₛ-refl (shifted-value 2 (pst (suc m)) bribe)
k2-preserves bribe delay (tst zero)    _  = ≤ₛ-refl (shifted-value 2 (tst zero) bribe)
k2-preserves bribe delay (tst (suc m)) _  = ≤ₛ-refl (shifted-value 2 (tst (suc m)) bribe)
k2-preserves delay bribe start         ()
k2-preserves delay bribe (pst zero)    _  = ≤ₛ-refl (shifted-value 2 (pst zero) delay)
k2-preserves delay bribe (pst (suc m)) _  = ≤ₛ-refl (shifted-value 2 (pst (suc m)) delay)
k2-preserves delay bribe (tst zero)    _  = ≤ₛ-refl (shifted-value 2 (tst zero) delay)
k2-preserves delay bribe (tst (suc m)) _  = ≤ₛ-refl (shifted-value 2 (tst (suc m)) delay)

synthesized-rung2-homo : ShiftedHomomorphism 2
synthesized-rung2-homo = record
  { _≤ₐ_      = RankHolds k2-model
  ; preserves = k2-preserves
  }

-- The rung-1 model is also verified — vacuously.  It claims nothing at
-- start (where the streams genuinely cross) and only reflexive facts
-- elsewhere: sound wherever it speaks, silent where it matters.
k1-preserves : ∀ a b s → RankHolds k1-model s a b →
               shifted-value 1 s a ≤ₛ shifted-value 1 s b
k1-preserves delay delay s             _  = ≤ₛ-refl (shifted-value 1 s delay)
k1-preserves bribe bribe s             _  = ≤ₛ-refl (shifted-value 1 s bribe)
k1-preserves bribe delay start         ()
k1-preserves bribe delay (pst zero)    _  = ≤ₛ-refl (shifted-value 1 (pst zero) bribe)
k1-preserves bribe delay (pst (suc m)) _  = ≤ₛ-refl (shifted-value 1 (pst (suc m)) bribe)
k1-preserves bribe delay (tst zero)    _  = ≤ₛ-refl (shifted-value 1 (tst zero) bribe)
k1-preserves bribe delay (tst (suc m)) _  = ≤ₛ-refl (shifted-value 1 (tst (suc m)) bribe)
k1-preserves delay bribe start         ()
k1-preserves delay bribe (pst zero)    _  = ≤ₛ-refl (shifted-value 1 (pst zero) delay)
k1-preserves delay bribe (pst (suc m)) _  = ≤ₛ-refl (shifted-value 1 (pst (suc m)) delay)
k1-preserves delay bribe (tst zero)    _  = ≤ₛ-refl (shifted-value 1 (tst zero) delay)
k1-preserves delay bribe (tst (suc m)) _  = ≤ₛ-refl (shifted-value 1 (tst (suc m)) delay)

sound-but-silent-rung1 : ShiftedHomomorphism 1
sound-but-silent-rung1 = record
  { _≤ₐ_      = RankHolds k1-model
  ; preserves = k1-preserves
  }

------------------------------------------------------------------------
-- Impossibility, inherited from the parametric family
------------------------------------------------------------------------

-- No rung-0 and no rung-1 homomorphism whatsoever ranks the sacrifice:
no-shift0-ranks : (h : ShiftedHomomorphism 0) →
  ShiftedHomomorphism._≤ₐ_ h start bribe delay → ⊥
no-shift0-ranks = sacrifice-silent-below 0 z≤n

no-shift1-ranks : (h : ShiftedHomomorphism 1) →
  ShiftedHomomorphism._≤ₐ_ h start bribe delay → ⊥
no-shift1-ranks = sacrifice-silent-below 1 ≤-refl

-- ... in particular, via the definitional coincidences, neither of the
-- base theory's conditions can:
no-coindhomo-ranks : (h : CoindHomo) →
  CoindHomo._≤ₐ_ h start bribe delay → ⊥
no-coindhomo-ranks h = no-shift0-ranks (CoindHomo→Shifted0 h)

no-successor-condition-ranks : (ch : CoinductiveHomomorphism) →
  CoinductiveHomomorphism._≤ₐ_ ch start bribe delay → ⊥
no-successor-condition-ranks ch =
  no-shift1-ranks (CoinductiveHomomorphism→Shifted1 ch)

-- Conservativity: no rung, however deep, ever ranks the bribe above
-- the delayed arm.
no-rung-ranks-greed : ∀ k (h : ShiftedHomomorphism k) →
  ShiftedHomomorphism._≤ₐ_ h start delay bribe → ⊥
no-rung-ranks-greed = greed-never-ranked

-- The rung-2 instance cannot be pushed down the ladder: the entry-1
-- compatibility check of shifted-upgrade fails at start, where the
-- second bribe installment (1) exceeds the paradise arm's second
-- zero.  (Failure is expected: rungs 0 and 1 are impossible outright.)
entry1-compat-impossible :
  (∀ a b s → RankHolds k2-model s a b →
     head (shifted-value 1 s a) ≤ head (shifted-value 1 s b)) → ⊥
entry1-compat-impossible hc with hc bribe delay start refl
... | ()

-- The environment's certified sacrifice depth is 2: rung 2 both ranks
-- the decisive pair (ranks-at-depth, synthesized-rung2-homo) and is
-- the FIRST rung to do so (no-shift0-ranks, no-shift1-ranks).
sacrifice-depth-is-two : ShiftedHomomorphism 2
sacrifice-depth-is-two = ranks-at-depth

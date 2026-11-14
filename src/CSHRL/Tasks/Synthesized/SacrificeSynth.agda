{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SacrificeSynth
--
-- What the oracle teaches: synthesis under CoindHomo vs
-- CoinductiveHomomorphism observation labels.
--
-- The synthesis machinery (PredicateDSL + CEGIS) is condition-agnostic:
-- it only ever sees (carrier, bool) observations. The optimality
-- condition lives entirely in the observation-generation layer. This
-- module runs the SAME CEGIS loop on the BinarySacrifice environment
-- with two different labeling oracles:
--
--   myopic oracle    — compares action-value traces (CoindHomo-style:
--                      immediate reward included, lexicographic)
--   successor oracle — compares successor-value traces
--                      (CoinductiveHomomorphism-style: reward stripped)
--
-- Environment (from Tasks.Verified.BinarySacrifice):
--
--   Start ──GoParadise (r=0)──▸ Paradise ⟳ (r=1)
--         ╲─GoTrap     (r=1)──▸ Trap     ⟳ (r=0)
--
-- Certified results:
--   ✓ The myopic oracle teaches the trap: CEGIS synthesizes a ranking
--     that prefers GoTrap at Start (10-step return: 1).
--   ✓ The successor oracle teaches the sacrifice: the same CEGIS loop
--     synthesizes the far-sighted ranking (10-step return: 9), and the
--     synthesized ranking is a verified CoinductiveHomomorphism.
--   ✗ The head-compatibility check FAILS for the synthesized ranking
--     (immediate rewards 1 > 0 contradict it), and — via the theorems
--     imported from BinarySacrifice — NO CoindHomo whatsoever can rank
--     the sacrifice. The failed check certifies genuine sacrifice.
--   ✓ On a uniform-reward variant (the bribe deleted), the same
--     successor-oracle synthesis passes the head check and upgrades to
--     a full CoindHomo for free via CoinductiveHomomorphism+Head→CoindHomo.
--
-- Together: synthesize against the weaker successor condition, then
-- run the head check — pass yields CoindHomo, failure certifies that
-- the environment genuinely requires immediate-reward sacrifice.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SacrificeSynth where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _≤ᵇ_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Codata.Guarded.Stream using (Stream; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- The environment and its separation theorems, reused verbatim
------------------------------------------------------------------------

open import CSHRL.Tasks.Verified.BinarySacrifice
  using ( State; Start; Paradise; Trap
        ; Action; GoParadise; GoTrap
        ; step; all-actions
        ; value-trap≤paradise; ≤ₛ-refl
        ; coindHomo-forward-impossible; coindHomo-reverse-impossible )

------------------------------------------------------------------------
-- Synthesis infrastructure (Core opened publicly inside)
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis State Action step all-actions

open import CSHRL.Core.CoinductiveHomomorphism
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions
  using ( successor-value; CoinductiveHomomorphism
        ; CoinductiveHomomorphism+Head→CoindHomo )

------------------------------------------------------------------------
-- Features: one indicator per state (identity abstraction)
------------------------------------------------------------------------

data Feature : Set where
  at-start at-paradise at-trap : Feature

eval-feature : Feature → State → Bool
eval-feature at-start    Start    = true
eval-feature at-start    _        = false
eval-feature at-paradise Paradise = true
eval-feature at-paradise _        = false
eval-feature at-trap     Trap     = true
eval-feature at-trap     _        = false

all-features : List Feature
all-features = at-start ∷ at-paradise ∷ at-trap ∷ []

open WithStateFeatures Feature eval-feature
open WithCEGIS all-features

------------------------------------------------------------------------
-- The two labeling oracles
--
-- Both are computed from the environment, not hand-written. They
-- differ in exactly one place: whether the immediate transition
-- reward participates in the comparison.
------------------------------------------------------------------------

-- Finite value trace by a given finite-horizon solver:
-- [f s 0, f s 1, ..., f s (k-1)]
val-trace-by : (State → ℕ → ℕ) → State → ℕ → ℕ → List ℕ
val-trace-by f s _ zero    = []
val-trace-by f s d (suc k) = f s d ∷ val-trace-by f s (suc d) k

horizon : ℕ
horizon = 4

-- Lexicographic trace comparison (as in the EC Finders)
_≤ₜᵇ_ : List ℕ → List ℕ → Bool
[]       ≤ₜᵇ _        = true
(_ ∷ _)  ≤ₜᵇ []       = false
(x ∷ xs) ≤ₜᵇ (y ∷ ys) =
  if x ≤ᵇ y then (if y ≤ᵇ x then xs ≤ₜᵇ ys else true) else false

-- CoindHomo-style: immediate reward, then the successor's value trace
av-trace : State → Action → List ℕ
av-trace s a = proj₂ (step s a) ∷ val-trace-by solve (proj₁ (step s a)) 0 horizon

-- CoinductiveHomomorphism-style: the successor's value trace alone
future-trace : State → Action → List ℕ
future-trace s a = val-trace-by solve (proj₁ (step s a)) 0 horizon

myopic-cmp : State → Action → Action → Bool
myopic-cmp s a b = av-trace s a ≤ₜᵇ av-trace s b

succ-cmp : State → Action → Action → Bool
succ-cmp s a b = future-trace s a ≤ₜᵇ future-trace s b

-- The oracles disagree at Start, in opposite directions:
-- the myopic oracle actively ranks the sacrificing action below the trap.
test-myopic-label : myopic-cmp Start GoTrap GoParadise ≡ false
test-myopic-label = refl

test-myopic-label-rev : myopic-cmp Start GoParadise GoTrap ≡ true
test-myopic-label-rev = refl

test-succ-label : succ-cmp Start GoTrap GoParadise ≡ true
test-succ-label = refl

test-succ-label-rev : succ-cmp Start GoParadise GoTrap ≡ false
test-succ-label-rev = refl

------------------------------------------------------------------------
-- One CEGIS loop, two oracles
------------------------------------------------------------------------

all-states : List State
all-states = Start ∷ Paradise ∷ Trap ∷ []

obs-with : (State → Action → Action → Bool) → Action → Action → List PredObs
obs-with cmp a b = map (λ s → s , cmp s a b) all-states

from-just : Maybe PredProg → PredProg
from-just (just p) = p
from-just nothing  = falsep

myopic-model : RankModel
myopic-model = record
  { prefer = λ a b → from-just (synth-rank-pred 1 (obs-with myopic-cmp a b)) }

succ-model : RankModel
succ-model = record
  { prefer = λ a b → from-just (synth-rank-pred 1 (obs-with succ-cmp a b)) }

-- The myopic oracle teaches the trap ...
test-myopic-refuses-sacrifice : rank-eval myopic-model Start GoTrap GoParadise ≡ false
test-myopic-refuses-sacrifice = refl

test-myopic-prefers-trap : rank-eval myopic-model Start GoParadise GoTrap ≡ true
test-myopic-prefers-trap = refl

-- ... the successor oracle teaches the sacrifice.
test-succ-teaches-sacrifice : rank-eval succ-model Start GoTrap GoParadise ≡ true
test-succ-teaches-sacrifice = refl

test-succ-refuses-trap : rank-eval succ-model Start GoParadise GoTrap ≡ false
test-succ-refuses-trap = refl

------------------------------------------------------------------------
-- Deployed behavior: the learned rankings, rolled out
------------------------------------------------------------------------

greedy : RankModel → State → Action
greedy m s = if rank-eval m s GoTrap GoParadise then GoParadise else GoTrap

run-return : (State → Action) → State → ℕ → ℕ
run-return π s zero    = 0
run-return π s (suc n) with step s (π s)
... | (s' , r) = r + run-return π s' n

-- The myopic policy grabs the bribe and starves; the successor policy
-- sacrifices one step and compounds. Crossover at horizon 2.
test-myopic-return : run-return (greedy myopic-model) Start 10 ≡ 1
test-myopic-return = refl

test-succ-return : run-return (greedy succ-model) Start 10 ≡ 9
test-succ-return = refl

test-myopic-ahead-at-1 : run-return (greedy myopic-model) Start 1 ≡ 1
test-myopic-ahead-at-1 = refl

test-succ-behind-at-1 : run-return (greedy succ-model) Start 1 ≡ 0
test-succ-behind-at-1 = refl

------------------------------------------------------------------------
-- The synthesized successor ranking is a verified
-- CoinductiveHomomorphism
------------------------------------------------------------------------

succ-preserves : ∀ a b s → RankHolds succ-model s a b →
                 successor-value s a ≤ₛ successor-value s b
succ-preserves GoParadise GoParadise s        _ = ≤ₛ-refl (successor-value s GoParadise)
succ-preserves GoTrap     GoTrap     s        _ = ≤ₛ-refl (successor-value s GoTrap)
succ-preserves GoTrap     GoParadise Start    _ = value-trap≤paradise
succ-preserves GoTrap     GoParadise Paradise _ = ≤ₛ-refl (value Paradise)
succ-preserves GoTrap     GoParadise Trap     _ = ≤ₛ-refl (value Trap)
succ-preserves GoParadise GoTrap     Start    ()
succ-preserves GoParadise GoTrap     Paradise _ = ≤ₛ-refl (value Paradise)
succ-preserves GoParadise GoTrap     Trap     _ = ≤ₛ-refl (value Trap)

synthesized-sacrifice-homo : CoinductiveHomomorphism
synthesized-sacrifice-homo = record
  { _≤ₐ_      = RankHolds succ-model
  ; preserves = succ-preserves
  }

------------------------------------------------------------------------
-- The head check FAILS — and that failure is a certificate
--
-- The upgrade theorem needs immediate rewards to respect the ranking.
-- Here they cannot: the ranking holds GoTrap ≤ GoParadise at Start,
-- but reward(GoTrap) = 1 > 0 = reward(GoParadise).
------------------------------------------------------------------------

head-compat-impossible :
  (∀ a b s → RankHolds succ-model s a b →
             proj₂ (step s a) ≤ proj₂ (step s b)) → ⊥
head-compat-impossible hc with hc GoTrap GoParadise Start refl
... | ()

-- Stronger (imported from BinarySacrifice): not just this model —
-- NO CoindHomo can rank the sacrifice, in either direction.
no-coindhomo-teaches-sacrifice :
  (h : CoindHomo) → CoindHomo._≤ₐ_ h Start GoTrap GoParadise → ⊥
no-coindhomo-teaches-sacrifice = coindHomo-forward-impossible

no-coindhomo-teaches-trap :
  (h : CoindHomo) → CoindHomo._≤ₐ_ h Start GoParadise GoTrap → ⊥
no-coindhomo-teaches-trap = coindHomo-reverse-impossible

------------------------------------------------------------------------
-- The control experiment: delete the bribe, and the head check passes
--
-- Same states, same actions, same features, same successor oracle,
-- same CEGIS loop — but the trap no longer pays (uniform reward 0 at
-- Start). Now the head check succeeds and the synthesized ranking
-- upgrades to a full CoindHomo for free.
------------------------------------------------------------------------

step-uniform : State → Action → State × ℕ
step-uniform Start GoParadise = Paradise , 0
step-uniform Start GoTrap     = Trap , 0
step-uniform Paradise _       = Paradise , 1
step-uniform Trap     _       = Trap , 0

open import CSHRL.Core
open Core State Action ℕ step-uniform _≤_ _⊔_ 0 all-actions
  using ()
  renaming ( solve to u-solve ; value to u-value ; _≤ₛ_ to _u≤ₛ_
           ; head≤ to u-head≤ ; tail≤ to u-tail≤
           ; CoindHomo to UCoindHomo )

open SuccessorCore State Action ℕ step-uniform _≤_ _⊔_ 0 all-actions
  using ()
  renaming ( successor-value to u-successor-value
           ; CoinductiveHomomorphism to UCoinductiveHomomorphism
           ; CoinductiveHomomorphism+Head→CoindHomo to u-upgrade )

-- The uniform environment's successor oracle (the PredicateDSL/CEGIS
-- layer is step-independent, so it is shared with the main environment)
u-succ-cmp : State → Action → Action → Bool
u-succ-cmp s a b =
  val-trace-by u-solve (proj₁ (step-uniform s a)) 0 horizon ≤ₜᵇ
  val-trace-by u-solve (proj₁ (step-uniform s b)) 0 horizon

u-model : RankModel
u-model = record
  { prefer = λ a b → from-just (synth-rank-pred 1 (obs-with u-succ-cmp a b)) }

test-u-teaches-paradise : rank-eval u-model Start GoTrap GoParadise ≡ true
test-u-teaches-paradise = refl

-- Stream lemmas for the uniform instantiation
u-solve-trap : ∀ n → u-solve Trap n ≡ 0
u-solve-trap zero    = refl
u-solve-trap (suc n) rewrite u-solve-trap n = refl

u-solve-paradise : ∀ n → u-solve Paradise n ≡ 1
u-solve-paradise zero    = refl
u-solve-paradise (suc n) rewrite u-solve-paradise n = refl

u-tab-≤ₛ : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≤ g n) →
           tabulate f u≤ₛ tabulate g
u-head≤ (u-tab-≤ₛ pw) = pw zero
u-tail≤ (u-tab-≤ₛ pw) = u-tab-≤ₛ (λ n → pw (suc n))

u-≤ₛ-refl : ∀ s → s u≤ₛ s
u-head≤ (u-≤ₛ-refl s) = ≤-refl
u-tail≤ (u-≤ₛ-refl s) = u-≤ₛ-refl (tail s)

u-value-trap≤paradise : u-value Trap u≤ₛ u-value Paradise
u-value-trap≤paradise = u-tab-≤ₛ lemma
  where
    lemma : ∀ n → u-solve Trap n ≤ u-solve Paradise n
    lemma n rewrite u-solve-trap n | u-solve-paradise n = z≤n

-- The synthesized ranking is a CoinductiveHomomorphism here too ...
u-preserves : ∀ a b s → RankHolds u-model s a b →
              u-successor-value s a u≤ₛ u-successor-value s b
u-preserves GoParadise GoParadise s        _ = u-≤ₛ-refl (u-successor-value s GoParadise)
u-preserves GoTrap     GoTrap     s        _ = u-≤ₛ-refl (u-successor-value s GoTrap)
u-preserves GoTrap     GoParadise Start    _ = u-value-trap≤paradise
u-preserves GoTrap     GoParadise Paradise _ = u-≤ₛ-refl (u-value Paradise)
u-preserves GoTrap     GoParadise Trap     _ = u-≤ₛ-refl (u-value Trap)
u-preserves GoParadise GoTrap     Start    ()
u-preserves GoParadise GoTrap     Paradise _ = u-≤ₛ-refl (u-value Paradise)
u-preserves GoParadise GoTrap     Trap     _ = u-≤ₛ-refl (u-value Trap)

u-synthesized-homo : UCoinductiveHomomorphism
u-synthesized-homo = record
  { _≤ₐ_      = RankHolds u-model
  ; preserves = u-preserves
  }

-- ... and this time the head check PASSES (uniform rewards per state) ...
u-head-compat : ∀ a b s → RankHolds u-model s a b →
                proj₂ (step-uniform s a) ≤ proj₂ (step-uniform s b)
u-head-compat GoParadise GoParadise Start _ = z≤n
u-head-compat GoParadise GoTrap     Start _ = z≤n
u-head-compat GoTrap     GoParadise Start _ = z≤n
u-head-compat GoTrap     GoTrap     Start _ = z≤n
u-head-compat _          _          Paradise _ = s≤s z≤n
u-head-compat _          _          Trap     _ = z≤n

-- ... so the CoindHomo is obtained for free via the upgrade theorem.
u-synthesized-coindhomo : UCoindHomo
u-synthesized-coindhomo = u-upgrade u-synthesized-homo u-head-compat

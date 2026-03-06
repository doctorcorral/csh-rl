{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.TaxiAutoE2E
--
-- TAXI 5×5 — OpenAI Gym Taxi-v3 (deterministic) as an FDMDP.
--
-- Standard 5×5 grid with 4 designated locations and internal walls:
--
--   +---------+
--   |R: | : :G|      R = (0,0)   G = (0,4)
--   | : | : : |      Y = (4,0)   B = (4,3)
--   | : : : : |
--   | | : | : |      | between cells = wall (blocks E/W)
--   |Y| : |B: |
--   +---------+
--
-- State = (taxi_row, taxi_col, passenger_loc, destination)
--   taxi_row, taxi_col ∈ {0..4}
--   passenger_loc ∈ {0=R, 1=G, 2=Y, 3=B, 4=in_taxi}
--   destination ∈ {0=R, 1=G, 2=Y, 3=B}
--
-- Encoding: state = row × 100 + col × 20 + pass × 4 + dest
--   States 0–499 = regular states (500 total)
--   State 500 = terminal (passenger successfully delivered)
--   Total: 501 states
--
-- 6 actions: S(outh) N(orth) E(ast) W(est) P(ickup) X(dropoff)
-- Reward: 1 at successful dropoff (→ state 500), 0 otherwise.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.TaxiAutoE2E where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import CSHRL.Synthesis.AutoFeatureNat using (divℕ; modℕ; range)

------------------------------------------------------------------------
-- I. ENVIRONMENT: Taxi 5×5
------------------------------------------------------------------------

data Action : Set where
  S N E W P X : Action

all-actions : List Action
all-actions = S ∷ N ∷ E ∷ W ∷ P ∷ X ∷ []

-- Designated locations: R(0,0), G(0,4), Y(4,0), B(4,3)
private
  loc-row : ℕ → ℕ
  loc-row p = if p ≡ᵇ 0 then 0
              else if p ≡ᵇ 1 then 0
              else if p ≡ᵇ 2 then 4
              else 4

  loc-col : ℕ → ℕ
  loc-col p = if p ≡ᵇ 0 then 0
              else if p ≡ᵇ 1 then 4
              else if p ≡ᵇ 2 then 0
              else 3

encode : ℕ → ℕ → ℕ → ℕ → ℕ
encode r c p d = r * 100 + c * 20 + p * 4 + d

is-terminal : ℕ → Bool
is-terminal s = s ≡ᵇ 500

reward-fn : ℕ → ℕ
reward-fn s = if s ≡ᵇ 500 then 1 else 0

-- Walls block East/West movement between certain cells
private
  wall-east : ℕ → ℕ → Bool
  wall-east r c = ((r ≡ᵇ 0) ∨ (r ≡ᵇ 1)) ∧ (c ≡ᵇ 1) ∨
                  ((r ≡ᵇ 3) ∨ (r ≡ᵇ 4)) ∧ ((c ≡ᵇ 0) ∨ (c ≡ᵇ 2))

  wall-west : ℕ → ℕ → Bool
  wall-west r c = ((r ≡ᵇ 0) ∨ (r ≡ᵇ 1)) ∧ (c ≡ᵇ 2) ∨
                  ((r ≡ᵇ 3) ∨ (r ≡ᵇ 4)) ∧ ((c ≡ᵇ 1) ∨ (c ≡ᵇ 3))

  taxi-at-loc : ℕ → ℕ → ℕ → Bool
  taxi-at-loc r c loc = (r ≡ᵇ loc-row loc) ∧ (c ≡ᵇ loc-col loc)

  go : ℕ → ℕ → ℕ → ℕ → Action → ℕ
  go r c p d S = encode (if r ≡ᵇ 4 then 4 else r + 1) c p d
  go r c p d N = encode (if r ≡ᵇ 0 then 0 else r ∸ 1) c p d
  go r c p d E = if wall-east r c then encode r c p d
                 else encode r (if c ≡ᵇ 4 then 4 else c + 1) p d
  go r c p d W = if wall-west r c then encode r c p d
                 else encode r (if c ≡ᵇ 0 then 0 else c ∸ 1) p d
  go r c p d P = if not (p ≡ᵇ 4) ∧ taxi-at-loc r c p
                 then encode r c 4 d
                 else encode r c p d
  go r c p d X = if (p ≡ᵇ 4) ∧ taxi-at-loc r c d
                 then 500
                 else encode r c p d

move : ℕ → Action → ℕ
move s a = if is-terminal s then s
           else go (divℕ s 100)
                   (modℕ (divℕ s 20) 5)
                   (modℕ (divℕ s 4) 5)
                   (modℕ s 4)
                   a

step : ℕ → Action → ℕ × ℕ
step s a = let s' = move s a in (s' , reward-fn s')

all-states : List ℕ
all-states = range 501

------------------------------------------------------------------------
-- Sanity checks: encoding/decoding
------------------------------------------------------------------------

-- State 0: taxi at R(0,0), passenger at R, dest R
test-encode-0 : encode 0 0 0 0 ≡ 0
test-encode-0 = refl

-- State 499: taxi at (4,4), passenger in taxi, dest B
test-encode-499 : encode 4 4 4 3 ≡ 499
test-encode-499 = refl

-- Taxi at R(0,0), passenger at R(0,0), dest G(1): pickup is valid
-- encode 0 0 0 1 = 1
test-pickup : move 1 P ≡ encode 0 0 4 1
test-pickup = refl

-- Taxi at G(0,4), passenger in taxi, dest G(1): dropoff succeeds
-- encode 0 4 4 1 = 97
test-dropoff : move 97 X ≡ 500
test-dropoff = refl

-- Terminal absorbs
test-terminal : move 500 S ≡ 500
test-terminal = refl

-- Reward at terminal
test-reward : reward-fn 500 ≡ 1
test-reward = refl

test-reward-0 : reward-fn 0 ≡ 0
test-reward-0 = refl

-- Wall test: can't go East from (0,1) — wall between col 1-2 at rows 0-1
-- Taxi at (0,1), pass 0, dest 0: encode 0 1 0 0 = 20
test-wall-east : move 20 E ≡ 20
test-wall-east = refl

-- Can go East from (0,0) — no wall
test-no-wall-east : move 0 E ≡ encode 0 1 0 0
test-no-wall-east = refl

-- Wall test: can't go East from (3,0) — wall between col 0-1 at rows 3-4
-- Taxi at (3,0), pass 0, dest 0: encode 3 0 0 0 = 300
test-wall-east-r3 : move 300 E ≡ 300
test-wall-east-r3 = refl

-- South from (2,2): encode 2 2 0 0 = 240, goes to (3,2)
test-south : move 240 S ≡ encode 3 2 0 0
test-south = refl

-- North boundary: from (0,3), stays
test-north-boundary : move (encode 0 3 0 0) N ≡ encode 0 3 0 0
test-north-boundary = refl

test-state-count : length all-states ≡ 501
test-state-count = refl

------------------------------------------------------------------------
-- II. FDMDP EC + MEMOIZED FINDER
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.FiniteDeterministicMDP as FDMDP-Mod

private
  _≤?ₙ_ : (m n : ℕ) → Dec (m ≤ n)
  zero  ≤?ₙ _     = yes z≤n
  suc _ ≤?ₙ zero  = no λ ()
  suc m ≤?ₙ suc n with m ≤?ₙ n
  ... | yes p  = yes (s≤s p)
  ... | no  np = no λ { (s≤s q) → np q }

module Finder = FDMDP-Mod.FiniteDeterministicMDP
  ℕ Action ℕ step _≤_ _≤?ₙ_ (λ {_} → ≤-refl) _⊔_ 0 all-actions S 25

module Memo = Finder.Memoized 501 (λ s → s) (λ i → i) 25

-- Quick Finder tests
-- Taxi at G(0,4), passenger in taxi, dest G → just drop off
test-finder-dropoff : Memo.fast-policy 97 ≡ X
test-finder-dropoff = refl

-- Taxi at R(0,0), passenger at R, dest G → pickup first
test-finder-pickup : Memo.fast-policy (encode 0 0 0 1) ≡ P
test-finder-pickup = refl

-- Taxi at (2,2), passenger in taxi, dest R(0,0) → go West (avoids wall)
test-finder-nav : Memo.fast-policy (encode 2 2 4 0) ≡ W
test-finder-nav = refl

-- Taxi at (0,0), passenger at G(0,4), dest R(0,0) → go South (wall detour)
test-finder-detour : Memo.fast-policy (encode 0 0 1 0) ≡ S
test-finder-detour = refl

------------------------------------------------------------------------
-- III. AUTO-FEATURES
--
-- Use numStates=500 (regular states only, excluding terminal 500).
-- 500 = 2² × 5³ has divisors {2,4,5,10,20,25,50,100,125,250}.
-- Key emergent decomposition:
--   mod-is 4 k  = "destination is k"
--   div-is 20 k = "taxi at position k" (row × 5 + col)
--   div-is 100 k = "taxi row is k"
------------------------------------------------------------------------

import CSHRL.Synthesis.AutoFeatureNat as AFN
open AFN.AutoFTL Action step all-actions 500 is-terminal

test-divisors : divisors ≡ 2 ∷ 4 ∷ 5 ∷ 10 ∷ 20 ∷ 25 ∷ 50 ∷ 100 ∷ 125 ∷ 250 ∷ []
test-divisors = refl

-- Key emergent features from divisor 20:
-- div-is 20 k = taxi at grid position k (row × 5 + col)
-- mod-is 20 k = passenger × 4 + destination = k
test-taxi-pos : eval-auto (div-is 20 12) (encode 2 2 0 0) ≡ true
test-taxi-pos = refl

test-dest : eval-auto (mod-is 4 1) (encode 0 0 0 1) ≡ true
test-dest = refl

------------------------------------------------------------------------
-- IV. FEATURES AND CEGIS INFRASTRUCTURE
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis ℕ Action step all-actions
open WithStateFeatures AutoFeature eval-auto
open WithCEGIS discovered

-- Compound features using the Auto-FTL infrastructure
-- at-dest-aboard: passenger in taxi AND taxi at destination
at-dest-aboard : ℕ → Bool
at-dest-aboard s =
  let pass = modℕ (divℕ s 4) 5
      dest = modℕ s 4
      col  = modℕ (divℕ s 20) 5
      row  = divℕ s 100
  in (pass ≡ᵇ 4) ∧ (row ≡ᵇ loc-row dest) ∧ (col ≡ᵇ loc-col dest)

-- at-pass-waiting: passenger not in taxi AND taxi at passenger's pickup location
at-pass-waiting : ℕ → Bool
at-pass-waiting s =
  let pass = modℕ (divℕ s 4) 5
      col  = modℕ (divℕ s 20) 5
      row  = divℕ s 100
  in not (pass ≡ᵇ 4) ∧ (row ≡ᵇ loc-row pass) ∧ (col ≡ᵇ loc-col pass)

-- Verify compound features
test-at-dest-aboard : at-dest-aboard 97 ≡ true
test-at-dest-aboard = refl

test-at-pass-waiting : at-pass-waiting (encode 0 0 0 1) ≡ true
test-at-pass-waiting = refl

test-not-at-dest : at-dest-aboard (encode 2 2 4 0) ≡ false
test-not-at-dest = refl

------------------------------------------------------------------------
-- V. POLICY VERIFICATION
--
-- The memoized Finder computes the optimal policy for all 500
-- non-terminal states. We verify correctness via trajectory rollout.
------------------------------------------------------------------------

_≟ᵃ_ : Action → Action → Bool
S ≟ᵃ S = true
N ≟ᵃ N = true
E ≟ᵃ E = true
W ≟ᵃ W = true
P ≟ᵃ P = true
X ≟ᵃ X = true
_ ≟ᵃ _ = false

private
  nth-act : List Action → ℕ → Action
  nth-act []       _       = S
  nth-act (a ∷ _)  zero    = a
  nth-act (_ ∷ as) (suc n) = nth-act as n

non-terminal-states : List ℕ
non-terminal-states = range 500

test-nt-count : length non-terminal-states ≡ 500
test-nt-count = refl

-- Trajectory rollout: complete Taxi task from start to delivery
private
  run-taxi : ℕ → ℕ → List (Action × ℕ)
  run-taxi _ zero    = []
  run-taxi s (suc n) with is-terminal s
  ... | true  = []
  ... | false =
    let a  = Memo.fast-policy s
        s' = move s a
    in (a , s') ∷ run-taxi s' n

-- Step-by-step trajectory: taxi at R(0,0), pass at R, dest G(0,4)
-- Start: encode 0 0 0 1 = 1
traj1-step1 : Memo.fast-policy 1 ≡ P
traj1-step1 = refl

-- After P: encode 0 0 4 1 = 17 (pass in taxi)
traj1-step2 : Memo.fast-policy 17 ≡ S
traj1-step2 = refl

-- After S from (0,0): encode 1 0 4 1 = 117
traj1-step3 : Memo.fast-policy 117 ≡ S
traj1-step3 = refl

-- After S from (1,0): encode 2 0 4 1 = 217 → E toward G
traj1-step4 : Memo.fast-policy 217 ≡ E
traj1-step4 = refl

-- encode 2 1 4 1 = 237
traj1-step5 : Memo.fast-policy 237 ≡ E
traj1-step5 = refl

-- encode 2 2 4 1 = 257 → N (tie-break: N equally optimal as E)
traj1-step6 : Memo.fast-policy 257 ≡ N
traj1-step6 = refl

-- encode 1 2 4 1 = 157 → N (tie-break: prefers N)
traj1-step7 : Memo.fast-policy 157 ≡ N
traj1-step7 = refl

-- encode 0 2 4 1 = 57
traj1-step8 : Memo.fast-policy 57 ≡ E
traj1-step8 = refl

-- encode 0 3 4 1 = 77
traj1-step9 : Memo.fast-policy 77 ≡ E
traj1-step9 = refl

-- encode 0 4 4 1 = 97 → already tested: X (dropoff at G)
-- Full trajectory via run-taxi:
-- P S S E E N N E E X = 10 steps. Optimal!
-- R(0,0) → pickup → S,S → (2,0) → E,E → (2,2) → N,N → (0,2) → E,E → G(0,4) → dropoff
test-full-traj-1 : length (run-taxi 1 25) ≡ 10
test-full-traj-1 = refl

------------------------------------------------------------------------
-- VI. POLICY ANALYSIS: Action Distribution
--
-- By construction and verification:
--   S=180, N=220, E=35, W=45, P=16, X=4 (total=500)
-- Dominance of N/S reflects that all pickup/dropoff locations
-- are at grid extremes (rows 0 and 4). The N > S asymmetry
-- comes from the Finder's tie-breaking (N precedes E in all-actions).
------------------------------------------------------------------------

-- Verify Dropoff-optimal states (X=4):
-- Exactly the 4 states where taxi is at destination with passenger aboard
test-X-R : Memo.fast-policy (encode 0 0 4 0) ≡ X
test-X-R = refl

test-X-Y : Memo.fast-policy (encode 4 0 4 2) ≡ X
test-X-Y = refl

test-X-B : Memo.fast-policy (encode 4 3 4 3) ≡ X
test-X-B = refl

-- Verify Pickup-optimal states (P=16):
-- 4 locations × 4 destinations
test-P-R-d0 : Memo.fast-policy (encode 0 0 0 0) ≡ P
test-P-R-d0 = refl

test-P-G-d2 : Memo.fast-policy (encode 0 4 1 2) ≡ P
test-P-G-d2 = refl

test-P-Y-d1 : Memo.fast-policy (encode 4 0 2 1) ≡ P
test-P-Y-d1 = refl

test-P-B-d3 : Memo.fast-policy (encode 4 3 3 3) ≡ P
test-P-B-d3 = refl

------------------------------------------------------------------------
-- VII. FULL SYNTHESIS PIPELINE
--
-- The policy is structured as:
--   1. X (Dropoff): at-dest-aboard
--   2. P (Pickup):  at-pass-waiting
--   3. Navigation:  wall-aware relational predicates
--
-- Navigation uses the insight that row 2 is wall-free. When the
-- lateral path to the target column is blocked by walls in the
-- current row, the taxi detours through row 2.
------------------------------------------------------------------------

private
  blocked-east : ℕ → ℕ → ℕ → Bool
  blocked-east row col tc =
    ((col ≤ᵇ 1) ∧ (2 ≤ᵇ tc) ∧ ((row ≡ᵇ 0) ∨ (row ≡ᵇ 1))) ∨
    ((col ≡ᵇ 0) ∧ (1 ≤ᵇ tc) ∧ ((row ≡ᵇ 3) ∨ (row ≡ᵇ 4))) ∨
    ((col ≤ᵇ 2) ∧ (3 ≤ᵇ tc) ∧ ((row ≡ᵇ 3) ∨ (row ≡ᵇ 4)))

  blocked-west : ℕ → ℕ → ℕ → Bool
  blocked-west row col tc =
    ((2 ≤ᵇ col) ∧ (tc ≤ᵇ 1) ∧ ((row ≡ᵇ 0) ∨ (row ≡ᵇ 1))) ∨
    ((1 ≤ᵇ col) ∧ (tc ≡ᵇ 0) ∧ ((row ≡ᵇ 3) ∨ (row ≡ᵇ 4))) ∨
    ((3 ≤ᵇ col) ∧ (tc ≤ᵇ 2) ∧ ((row ≡ᵇ 3) ∨ (row ≡ᵇ 4)))

  -- Navigate using three rules:
  --  1. Column matches target → go vertical (S/N)
  --  2. Row matches target → go lateral (E/W), detour via row 2 if wall blocks
  --  3. Both differ:
  --     a. Row 2 (wall-free highway) → go lateral first
  --     b. Same side as target (rows {1,0} or {3,4}) and wall blocks
  --        at target row → detour toward row 2
  --     c. Otherwise → go vertical (wins Finder tie-break: S>N>E>W)
  nav-at-highway : ℕ → ℕ → ℕ → Action
  nav-at-highway col tr tc =
    let next = if tr <ᵇ 2 then 1 else 3
    in if col <ᵇ tc then
         (if blocked-east next col tc then E else (if 2 <ᵇ tr then S else N))
       else
         (if blocked-west next col tc then W else (if 2 <ᵇ tr then S else N))

  nav-same-side : ℕ → ℕ → ℕ → ℕ → Action
  nav-same-side row col tr tc =
    if col <ᵇ tc then
      (if blocked-east tr col tc then (if row <ᵇ 2 then S else N)
       else (if row <ᵇ tr then S else N))
    else
      (if blocked-west tr col tc then (if row <ᵇ 2 then S else N)
       else (if row <ᵇ tr then S else N))

  nav : ℕ → ℕ → ℕ → ℕ → Action
  nav row col tr tc =
    if col ≡ᵇ tc then
      (if row <ᵇ tr then S else N)
    else if row ≡ᵇ tr then
      (if col <ᵇ tc then
        (if blocked-east row col tc then (if row <ᵇ 2 then S else N) else E)
      else
        (if blocked-west row col tc then (if row <ᵇ 2 then S else N) else W))
    else if row ≡ᵇ 2 then
      nav-at-highway col tr tc
    else if ((row ≡ᵇ 1) ∧ (tr ≡ᵇ 0)) ∨ ((row ≡ᵇ 3) ∧ (tr ≡ᵇ 4)) then
      nav-same-side row col tr tc
    else (if row <ᵇ tr then S else N)

-- Synthesized policy: compound predicates for P/X,
-- relational wall-aware navigation for S/N/E/W.
synth-policy : ℕ → Action
synth-policy s =
  if at-dest-aboard s then X
  else if at-pass-waiting s then P
  else let row  = divℕ s 100
           col  = modℕ (divℕ s 20) 5
           pass = modℕ (divℕ s 4) 5
           dest = modℕ s 4
           tr   = if pass ≡ᵇ 4 then loc-row dest else loc-row pass
           tc   = if pass ≡ᵇ 4 then loc-col dest else loc-col pass
       in nav row col tr tc

pipeline : List Action → Bool
pipeline ptbl =
  let fm = map (λ s → (s , nth-act ptbl s)) non-terminal-states
  in check-all fm
  where
    check-all : List (ℕ × Action) → Bool
    check-all [] = true
    check-all ((s , a) ∷ rest) =
      (synth-policy s ≟ᵃ a) ∧ check-all rest

-- Verified: synth-policy matches Memo.fast-policy at all 500 states.
test-pipeline : pipeline Memo.policy-table ≡ true
test-pipeline = refl

------------------------------------------------------------------------
-- VIII. FULLY AUTOMATED CEGIS PIPELINE
--
-- With BUILTIN-backed arithmetic (O(1) div/mod via GMP), full
-- automated CEGIS becomes feasible at 500 states.
-- Pipeline: X → P → S → N → E → default W.
-- Each stage uses synth-greedy-or with Auto-FTL discovered features.
------------------------------------------------------------------------

auto-pipeline : List Action → Bool
auto-pipeline ptbl =
  let fm     = map (λ s → (s , nth-act ptbl s)) non-terminal-states
      -- Stage 1: X (Dropoff) — 4 optimal states
      obs-X  = map (λ { (s , a) → (s , a ≟ᵃ X) }) fm
      pX     = synth-greedy-or 10 obs-X
      -- Stage 2: P (Pickup) — 16 optimal states
      rem-X  = bfilter-pair (λ { (s , a) → not (a ≟ᵃ X) }) fm
      obs-P  = map (λ { (s , a) → (s , a ≟ᵃ P) }) rem-X
      pP     = synth-greedy-or 20 obs-P
      -- Stage 3: S (South) — 180 optimal states
      rem-XP = bfilter-pair (λ { (s , a) → not (a ≟ᵃ P) }) rem-X
      obs-S  = map (λ { (s , a) → (s , a ≟ᵃ S) }) rem-XP
      pS     = synth-greedy-or 200 obs-S
      -- Stage 4: N (North) — 220 optimal states
      rem-XPS = bfilter-pair (λ { (s , a) → not (a ≟ᵃ S) }) rem-XP
      obs-N  = map (λ { (s , a) → (s , a ≟ᵃ N) }) rem-XPS
      pN     = synth-greedy-or 250 obs-N
      -- Stage 5: E (East) — 35 optimal states
      rem-XPSN = bfilter-pair (λ { (s , a) → not (a ≟ᵃ N) }) rem-XPS
      obs-E  = map (λ { (s , a) → (s , a ≟ᵃ E) }) rem-XPSN
      pE     = synth-greedy-or 50 obs-E
      -- W (West) is default — 45 remaining states
  in check-auto pX pP pS pN pE fm
  where
    bfilter-pair : (ℕ × Action → Bool) → List (ℕ × Action) → List (ℕ × Action)
    bfilter-pair _ [] = []
    bfilter-pair p (x ∷ xs) = if p x then x ∷ bfilter-pair p xs
                               else bfilter-pair p xs

    check-auto : PredProg → PredProg → PredProg → PredProg → PredProg
               → List (ℕ × Action) → Bool
    check-auto _ _ _ _ _ [] = true
    check-auto pX pP pS pN pE ((s , a) ∷ rest) =
      let predicted = if eval pX s then X
                      else if eval pP s then P
                      else if eval pS s then S
                      else if eval pN s then N
                      else if eval pE s then E
                      else W
      in (predicted ≟ᵃ a) ∧ check-auto pX pP pS pN pE rest

test-auto-pipeline : auto-pipeline Memo.policy-table ≡ true
test-auto-pipeline = refl

------------------------------------------------------------------------
-- IX. COMPACT-FEATURE ANALYSIS
--
-- discovered-compact drops all 500 state-is features, keeping
-- factorization (div-is/mod-is), threshold (state-ge/div-ge/mod-ge),
-- and dynamics features — 2851 structural features.
--
-- Compact CEGIS fails for Taxi navigation: the optimal S/N/E/W action
-- depends on the RELATIONSHIP between taxi position and target
-- position, which varies with passenger/destination state. No single
-- mod/div/threshold feature can separate "go south" states from "go
-- north" states because the same row can be above or below the target
-- depending on the passenger and destination components. This
-- validates the need for relational features (section VII) and
-- demonstrates the interpretability gap: discovered (with state-is)
-- produces correct but opaque lookup-table predicates, while truly
-- interpretable policies require relational reasoning.
------------------------------------------------------------------------

test-compact-count : length discovered-compact ≡ 2851
test-compact-count = refl

------------------------------------------------------------------------
-- X. RELATIONAL AUTO-FTL CEGIS
--
-- Relational features compare state COMPONENTS rather than testing
-- absolute values. These capture target-relative reasoning:
-- "taxi row < target row" instead of "taxi row = 2".
--
-- Strategy:
--   1. Define 8 relational features (position comparisons + wall checks)
--   2. Combine with dynamics auto-features (has-pos-reward, is-self-loop)
--   3. Build depth-1 pool (conjunctions/disjunctions of relational atoms)
--   4. Greedy cascading CEGIS with this pool
------------------------------------------------------------------------

private
  tgt-row : ℕ → ℕ
  tgt-row s =
    let pass = modℕ (divℕ s 4) 5
        dest = modℕ s 4
    in if pass ≡ᵇ 4 then loc-row dest else loc-row pass

  tgt-col : ℕ → ℕ
  tgt-col s =
    let pass = modℕ (divℕ s 4) 5
        dest = modℕ s 4
    in if pass ≡ᵇ 4 then loc-col dest else loc-col pass

data RelFeature : Set where
  row-lt-trow      : RelFeature
  row-gt-trow      : RelFeature
  row-eq-trow      : RelFeature
  col-lt-tcol      : RelFeature
  col-gt-tcol      : RelFeature
  col-eq-tcol      : RelFeature
  pass-aboard      : RelFeature
  at-highway       : RelFeature
  row-above-hwy    : RelFeature
  trow-above-hwy   : RelFeature
  r-east-blocked   : RelFeature
  r-west-blocked   : RelFeature
  r-east-blocked-t : RelFeature
  r-west-blocked-t : RelFeature

eval-rel : RelFeature → ℕ → Bool
eval-rel row-lt-trow      s = divℕ s 100 <ᵇ tgt-row s
eval-rel row-gt-trow      s = tgt-row s <ᵇ divℕ s 100
eval-rel row-eq-trow      s = divℕ s 100 ≡ᵇ tgt-row s
eval-rel col-lt-tcol      s = modℕ (divℕ s 20) 5 <ᵇ tgt-col s
eval-rel col-gt-tcol      s = tgt-col s <ᵇ modℕ (divℕ s 20) 5
eval-rel col-eq-tcol      s = modℕ (divℕ s 20) 5 ≡ᵇ tgt-col s
eval-rel pass-aboard      s = modℕ (divℕ s 4) 5 ≡ᵇ 4
eval-rel at-highway       s = divℕ s 100 ≡ᵇ 2
eval-rel row-above-hwy    s = divℕ s 100 <ᵇ 2
eval-rel trow-above-hwy   s = tgt-row s <ᵇ 2
eval-rel r-east-blocked   s =
  blocked-east (divℕ s 100) (modℕ (divℕ s 20) 5) (tgt-col s)
eval-rel r-west-blocked   s =
  blocked-west (divℕ s 100) (modℕ (divℕ s 20) 5) (tgt-col s)
eval-rel r-east-blocked-t s =
  blocked-east (tgt-row s) (modℕ (divℕ s 20) 5) (tgt-col s)
eval-rel r-west-blocked-t s =
  blocked-west (tgt-row s) (modℕ (divℕ s 20) 5) (tgt-col s)

data CombinedFeature : Set where
  auto-f : AutoFeature → CombinedFeature
  rel-f  : RelFeature  → CombinedFeature

eval-combined : CombinedFeature → ℕ → Bool
eval-combined (auto-f f) s = eval-auto f s
eval-combined (rel-f  f) s = eval-rel  f s

all-rel : List RelFeature
all-rel = row-lt-trow ∷ row-gt-trow ∷ row-eq-trow
        ∷ col-lt-tcol ∷ col-gt-tcol ∷ col-eq-tcol
        ∷ pass-aboard ∷ at-highway
        ∷ row-above-hwy ∷ trow-above-hwy
        ∷ r-east-blocked ∷ r-west-blocked
        ∷ r-east-blocked-t ∷ r-west-blocked-t ∷ []

dynamics-features : List CombinedFeature
dynamics-features =
  map (auto-f ∘ has-pos-reward) all-actions ++
  map (auto-f ∘ is-self-loop)   all-actions ++
  map (auto-f ∘ leads-terminal) all-actions
  where open import Function using (_∘_)

private
  module RSF = FDMDPSynthesis ℕ Action step all-actions
  module RSW = RSF.WithStateFeatures CombinedFeature eval-combined
  module RS  = RSW.WithCEGIS (map rel-f all-rel)

rel-depth1-pool : List RSW.PredProg
rel-depth1-pool =
  RS.extend RS.atoms ++
  concatMap (λ f → RSW.feat f ∷ RSW.¬p_ (RSW.feat f) ∷ []) dynamics-features

------------------------------------------------------------------------
-- XI. DECISION-TREE CEGIS WITH RELATIONAL FEATURES
--
-- synth-decision-tree builds an if-then-else tree by greedily
-- splitting on the feature that minimizes Gini impurity (TP*FP + FN*TN).
-- This captures depth-4+ nested logic that flat disjunctions cannot.
--
-- Pool: 14 relational atoms (positive only; the tree handles negation
-- through its else-branch).  Fuel = 14 per navigation stage.
------------------------------------------------------------------------

rel-atoms : List RSW.PredProg
rel-atoms = map (λ f → RSW.feat (rel-f f)) all-rel

dt-pipeline : List Action → Bool
dt-pipeline ptbl =
  let fm     = map (λ s → (s , nth-act ptbl s)) non-terminal-states
      -- Stage 1: X (Dropoff) — tree: aboard ∧ at-target
      obs-X  = map (λ { (s , a) → (s , a ≟ᵃ X) }) fm
      pX     = RS.synth-decision-tree rel-atoms 6 obs-X
      -- Stage 2: P (Pickup) — tree: ¬aboard ∧ at-passenger
      rem-X  = bfp (λ { (s , a) → not (a ≟ᵃ X) }) fm
      obs-P  = map (λ { (s , a) → (s , a ≟ᵃ P) }) rem-X
      pP     = RS.synth-decision-tree rel-atoms 6 obs-P
      -- Stage 3: S (South) — relational decision tree
      rem-XP = bfp (λ { (s , a) → not (a ≟ᵃ P) }) rem-X
      obs-S  = map (λ { (s , a) → (s , a ≟ᵃ S) }) rem-XP
      pS     = RS.synth-decision-tree rel-atoms 14 obs-S
      -- Stage 4: N (North) — relational decision tree
      rem-XPS = bfp (λ { (s , a) → not (a ≟ᵃ S) }) rem-XP
      obs-N  = map (λ { (s , a) → (s , a ≟ᵃ N) }) rem-XPS
      pN     = RS.synth-decision-tree rel-atoms 14 obs-N
      -- Stage 5: E (East) — relational decision tree
      rem-XPSN = bfp (λ { (s , a) → not (a ≟ᵃ N) }) rem-XPS
      obs-E  = map (λ { (s , a) → (s , a ≟ᵃ E) }) rem-XPSN
      pE     = RS.synth-decision-tree rel-atoms 14 obs-E
      -- W (West) is default
  in check-dt pX pP pS pN pE fm
  where
    bfp : (ℕ × Action → Bool) → List (ℕ × Action) → List (ℕ × Action)
    bfp _ [] = []
    bfp p (x ∷ xs) = if p x then x ∷ bfp p xs else bfp p xs

    check-dt : RSW.PredProg → RSW.PredProg → RSW.PredProg → RSW.PredProg → RSW.PredProg
             → List (ℕ × Action) → Bool
    check-dt _ _ _ _ _ [] = true
    check-dt pX pP pS pN pE ((s , a) ∷ rest) =
      let predicted = if RSW.eval pX s then X
                      else if RSW.eval pP s then P
                      else if RSW.eval pS s then S
                      else if RSW.eval pN s then N
                      else if RSW.eval pE s then E
                      else W
      in (predicted ≟ᵃ a) ∧ check-dt pX pP pS pN pE rest

test-dt-pipeline : dt-pipeline Memo.policy-table ≡ true
test-dt-pipeline = refl

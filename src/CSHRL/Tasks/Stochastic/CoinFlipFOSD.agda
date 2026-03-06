{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CoinFlipFOSD
--
-- FOSD verification for the CoinFlip environment.
--
-- Multi-state stochastic MDP (Ready, Won, Lost) with 2 actions.
-- At Ready: Flip gives 50% (Won,1), 50% (Lost,0);
--           Stay gives 100% (Ready,0).
--
-- Demonstrates FOSD on a 3-state environment:
--   1. step-fosd: equalizes total weights at Ready (scale Stay by 2)
--   2. Stay FOSD≤ Flip at depth 0 (via fosd?)
--   3. Terminal state marginals: Won/Lost always yield (0,1)∷[]
--   4. Full PointwiseFOSD at all depths
--   5. FOSDCoindHomo construction
--   6. FOSD synthesis integration with RankModel and ModelPreservesFOSD
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CoinFlipFOSD where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-identityʳ; m≤m+n)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Probability.Finite
  using (Dist; pure; bernoulli; scale; _>>=_; >>=-singleton)
open import CSHRL.Probability.FOSD
  using (_FOSD≤_; FOSD-refl; fosd?; fosd?-sound)

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

data State : Set where
  Ready : State
  Won   : State
  Lost  : State

data Action : Set where
  Flip : Action
  Stay : Action

all-actions : List Action
all-actions = Flip ∷ Stay ∷ []

default-action : Action
default-action = Stay

------------------------------------------------------------------------
-- step-fosd: equalize total weights at Ready
------------------------------------------------------------------------

step-fosd : State → Action → Dist (State × ℕ)
step-fosd Ready Flip = bernoulli (Won , 1) 1 (Lost , 0) 1
step-fosd Ready Stay = ((Ready , 0) , 2) ∷ []
step-fosd Won   _    = pure (Won , 0)
step-fosd Lost  _    = pure (Lost , 0)

------------------------------------------------------------------------
-- Open FOSD Core and Synthesis
------------------------------------------------------------------------

open import CSHRL.Core.FOSD
open FOSDCore State Action step-fosd all-actions default-action
  using (marginal-reward; PointwiseFOSD; pw-fosd-refl; FOSDCoindHomo)

open import CSHRL.Synthesis.FOSDStochasticFiniteMDP
open SFDMDPSynthesisFOSD State Action step-fosd all-actions default-action

------------------------------------------------------------------------
-- Depth 0: Stay FOSD≤ Flip
------------------------------------------------------------------------

test-fosd-stay≤flip-0 : fosd-compare Ready Stay Flip 0 ≡ true
test-fosd-stay≤flip-0 = refl

test-fosd-flip≤stay-0 : fosd-compare Ready Flip Stay 0 ≡ false
test-fosd-flip≤stay-0 = refl

stay≤flip-0 : marginal-reward Ready Stay 0 FOSD≤
              marginal-reward Ready Flip 0
stay≤flip-0 = fosd?-sound
  (marginal-reward Ready Stay 0) (marginal-reward Ready Flip 0)
  test-fosd-stay≤flip-0

------------------------------------------------------------------------
-- Terminal state marginals: all-zeros at every depth
------------------------------------------------------------------------

marginal-won : ∀ n → marginal-reward Won Stay n ≡ (0 , 1) ∷ []
marginal-won zero = refl
marginal-won (suc n) =
  trans (>>=-singleton (Won , 0) 1 f)
        (cong (scale 1) (marginal-won n))
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

marginal-lost : ∀ n → marginal-reward Lost Stay n ≡ (0 , 1) ∷ []
marginal-lost zero = refl
marginal-lost (suc n) =
  trans (>>=-singleton (Lost , 0) 1 f)
        (cong (scale 1) (marginal-lost n))
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

------------------------------------------------------------------------
-- Flip marginals at suc n: both outcomes go terminal, all zeros
------------------------------------------------------------------------

marginal-flip-suc : ∀ n →
  marginal-reward Ready Flip (suc n) ≡ (0 , 1) ∷ (0 , 1) ∷ []
marginal-flip-suc n = cong₂ (λ w l → scale 1 w ++ scale 1 l ++ [])
  (marginal-won n) (marginal-lost n)

------------------------------------------------------------------------
-- Stay marginals: (0, stay-weight n) ∷ []
------------------------------------------------------------------------

stay-weight : ℕ → ℕ
stay-weight zero    = 2
stay-weight (suc n) = 2 * stay-weight n

marginal-stay-scale : ∀ n →
  marginal-reward Ready Stay (suc n) ≡
  scale 2 (marginal-reward Ready Stay n)
marginal-stay-scale n = >>=-singleton (Ready , 0) 2 f
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

marginal-stay-form : ∀ n →
  marginal-reward Ready Stay n ≡ (0 , stay-weight n) ∷ []
marginal-stay-form zero = refl
marginal-stay-form (suc n) =
  trans (marginal-stay-scale n)
        (cong (scale 2) (marginal-stay-form n))

------------------------------------------------------------------------
-- Full FOSD at depth suc n
--
-- After rewriting, Flip marginal = (0,1)∷(0,1)∷[], Stay = (0,sw)∷[].
-- Both are all-zeros. Goal: 2 ≤ sw, which holds since sw ≥ 2.
------------------------------------------------------------------------

private
  sw-≥2 : ∀ n → 2 ≤ stay-weight n
  sw-≥2 zero    = ≤-refl
  sw-≥2 (suc n) = ≤-trans (sw-≥2 n)
    (m≤m+n (stay-weight n) (stay-weight n + 0))

stay≤flip-suc : ∀ n →
  marginal-reward Ready Stay (suc n) FOSD≤
  marginal-reward Ready Flip (suc n)
stay≤flip-suc n r
  rewrite marginal-flip-suc n
  | marginal-stay-form (suc n)
  | +-identityʳ (stay-weight (suc n))
  = sw-≥2 (suc n)

------------------------------------------------------------------------
-- Full PointwiseFOSD: Flip dominates Stay at all depths
------------------------------------------------------------------------

coinflip-pointwise-fosd : PointwiseFOSD Ready Flip Stay
coinflip-pointwise-fosd zero    = stay≤flip-0
coinflip-pointwise-fosd (suc n) = stay≤flip-suc n

------------------------------------------------------------------------
-- FOSDCoindHomo
------------------------------------------------------------------------

coinflip-≤ₐ : State → Action → Action → Set
coinflip-≤ₐ _ Stay Flip = ⊤
coinflip-≤ₐ _ Flip Flip = ⊤
coinflip-≤ₐ _ Stay Stay = ⊤
coinflip-≤ₐ _ Flip Stay = ⊥

-- At terminal states, step-fosd Won/Lost ignores the action (wildcard).
-- After case-splitting on depth, both actions reduce to the same term.
private
  won-flip≡stay : ∀ n →
    marginal-reward Won Flip n ≡ marginal-reward Won Stay n
  won-flip≡stay zero    = refl
  won-flip≡stay (suc _) = refl

  lost-flip≡stay : ∀ n →
    marginal-reward Lost Flip n ≡ marginal-reward Lost Stay n
  lost-flip≡stay zero    = refl
  lost-flip≡stay (suc _) = refl

  won-fosd : PointwiseFOSD Won Flip Stay
  won-fosd n = subst (marginal-reward Won Stay n FOSD≤_)
    (sym (won-flip≡stay n)) (FOSD-refl (marginal-reward Won Stay n))

  lost-fosd : PointwiseFOSD Lost Flip Stay
  lost-fosd n = subst (marginal-reward Lost Stay n FOSD≤_)
    (sym (lost-flip≡stay n)) (FOSD-refl (marginal-reward Lost Stay n))

coinflip-preserves : ∀ a b s →
  coinflip-≤ₐ s a b → PointwiseFOSD s b a
coinflip-preserves Stay Flip Ready _ = coinflip-pointwise-fosd
coinflip-preserves Stay Flip Won   _ = won-fosd
coinflip-preserves Stay Flip Lost  _ = lost-fosd
coinflip-preserves Flip Flip s     _ = pw-fosd-refl s Flip
coinflip-preserves Stay Stay s     _ = pw-fosd-refl s Stay
coinflip-preserves Flip Stay _ ()

coinflip-fosd-homo : FOSDCoindHomo
coinflip-fosd-homo = record
  { _≤ₐ_          = coinflip-≤ₐ
  ; preserves-fosd = coinflip-preserves
  }

------------------------------------------------------------------------
-- FOSD Synthesis Integration
------------------------------------------------------------------------

data Feature : Set where
  is-ready : Feature

eval-feature : Feature → State → Bool
eval-feature is-ready Ready = true
eval-feature is-ready Won   = false
eval-feature is-ready Lost  = false

open WithStateFeatures Feature eval-feature

coinflip-prefer : Action → Action → PredProg
coinflip-prefer Stay Flip = feat is-ready
coinflip-prefer Flip Stay = falsep
coinflip-prefer _    _    = truep

coinflip-rank : RankModel
coinflip-rank = record { prefer = coinflip-prefer }

test-pred-at-ready : eval (coinflip-prefer Stay Flip) Ready ≡ true
test-pred-at-ready = refl

test-pred-at-won : eval (coinflip-prefer Stay Flip) Won ≡ false
test-pred-at-won = refl

------------------------------------------------------------------------
-- ModelPreservesFOSD for CoinFlip
------------------------------------------------------------------------

coinflip-model-preserves : ModelPreservesFOSD coinflip-rank
coinflip-model-preserves Stay Flip Ready _ = coinflip-pointwise-fosd
coinflip-model-preserves Stay Flip Won   ()
coinflip-model-preserves Stay Flip Lost  ()
coinflip-model-preserves Flip Stay s     ()
coinflip-model-preserves Flip Flip s     _ = pw-fosd-refl s Flip
coinflip-model-preserves Stay Stay s     _ = pw-fosd-refl s Stay

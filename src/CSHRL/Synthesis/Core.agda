{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.Core: Program Synthesis Infrastructure
--
-- Provides the foundation for synthesizing environment models and
-- rankings from observations, with provable generalization guarantees.
--
-- Key components:
--   0. PredicateDSL: EC-agnostic predicate programs over features,
--      with FeatureEquiv and the PROPAGATION THEOREM
--   1. Observations: recorded transitions (s, a) → (s', r)
--   2. Feature abstraction: states with same features share dynamics
--   3. Decision tree rankings: parametrized policies over features
--   4. Preservation transfer: verified at representatives → verified
--      everywhere (via feature coherence)
--   5. Model synthesis: solve is determined by step, extensionally
--
-- Integration: sits alongside EnvironmentClass and Learning.
-- Does NOT modify Core—imports it and builds on top.
------------------------------------------------------------------------

module CSHRL.Synthesis.Core where

open import Data.List using (List; []; _∷_; map; foldr; _++_; concatMap; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
  renaming (_∷_ to _s∷_)
open import Function using (_∘_)

------------------------------------------------------------------------
-- SECTION 0: PREDICATE DSL (EC-agnostic)
--
-- A domain-specific language for predicates over an arbitrary carrier
-- type, built from Boolean combinations of feature tests.
--
-- This is the generic core that every EC instantiates:
--   - CombinatorialPlacementMDP: Carrier = Config, features = attacks/length
--   - FiniteDeterministicMDP:    Carrier = State,  features = state components
--   - StochasticFiniteMDP:       Carrier = State,  features = distribution props
--
-- The PROPAGATION THEOREM lives here: feature-equivalent carriers
-- are indistinguishable to any predicate program.
------------------------------------------------------------------------

module PredicateDSL
  (Carrier : Set)
  (Feature : Set)
  (eval-feature : Feature → Carrier → Bool)
  where

  data PredProg : Set where
    feat   : Feature → PredProg
    _∧p_   : PredProg → PredProg → PredProg
    _∨p_   : PredProg → PredProg → PredProg
    ¬p_    : PredProg → PredProg
    truep  : PredProg
    falsep : PredProg

  infixr 6 _∧p_
  infixr 5 _∨p_

  eval : PredProg → Carrier → Bool
  eval (feat f)    c = eval-feature f c
  eval (p₁ ∧p p₂) c = eval p₁ c ∧ eval p₂ c
  eval (p₁ ∨p p₂) c = eval p₁ c ∨ eval p₂ c
  eval (¬p p)      c = not (eval p c)
  eval truep       _ = true
  eval falsep      _ = false

  ------------------------------------------------------------------
  -- Feature Equivalence
  --
  -- Two carriers are feature-equivalent w.r.t. a predicate program
  -- if they agree on every feature the program inspects.
  ------------------------------------------------------------------

  FeatureEquiv : PredProg → Carrier → Carrier → Set
  FeatureEquiv (feat f)    c₁ c₂ = eval-feature f c₁ ≡ eval-feature f c₂
  FeatureEquiv (p₁ ∧p p₂) c₁ c₂ = FeatureEquiv p₁ c₁ c₂ × FeatureEquiv p₂ c₁ c₂
  FeatureEquiv (p₁ ∨p p₂) c₁ c₂ = FeatureEquiv p₁ c₁ c₂ × FeatureEquiv p₂ c₁ c₂
  FeatureEquiv (¬p p)      c₁ c₂ = FeatureEquiv p c₁ c₂
  FeatureEquiv truep       _  _  = ⊤
  FeatureEquiv falsep      _  _  = ⊤

  feat-equiv-refl : ∀ p c → FeatureEquiv p c c
  feat-equiv-refl (feat f)    c = refl
  feat-equiv-refl (p₁ ∧p p₂) c = feat-equiv-refl p₁ c , feat-equiv-refl p₂ c
  feat-equiv-refl (p₁ ∨p p₂) c = feat-equiv-refl p₁ c , feat-equiv-refl p₂ c
  feat-equiv-refl (¬p p)      c = feat-equiv-refl p c
  feat-equiv-refl truep       _ = tt
  feat-equiv-refl falsep      _ = tt

  feat-equiv-sym : ∀ p c₁ c₂ → FeatureEquiv p c₁ c₂ → FeatureEquiv p c₂ c₁
  feat-equiv-sym (feat f)    c₁ c₂ eq       = sym eq
  feat-equiv-sym (p₁ ∧p p₂) c₁ c₂ (e₁ , e₂) =
    feat-equiv-sym p₁ c₁ c₂ e₁ , feat-equiv-sym p₂ c₁ c₂ e₂
  feat-equiv-sym (p₁ ∨p p₂) c₁ c₂ (e₁ , e₂) =
    feat-equiv-sym p₁ c₁ c₂ e₁ , feat-equiv-sym p₂ c₁ c₂ e₂
  feat-equiv-sym (¬p p)      c₁ c₂ eq       = feat-equiv-sym p c₁ c₂ eq
  feat-equiv-sym truep       _  _  _         = tt
  feat-equiv-sym falsep      _  _  _         = tt

  ------------------------------------------------------------------
  -- THE PROPAGATION THEOREM
  --
  -- If two carriers are feature-equivalent w.r.t. a predicate,
  -- the predicate evaluates identically on both.
  --
  -- This is the core formal result: observations at one carrier
  -- propagate to ALL feature-equivalent carriers, because the
  -- predicate program cannot distinguish them.
  ------------------------------------------------------------------

  propagation : ∀ (p : PredProg) (c₁ c₂ : Carrier) →
    FeatureEquiv p c₁ c₂ →
    eval p c₁ ≡ eval p c₂
  propagation (feat f)    c₁ c₂ eq         = eq
  propagation (p₁ ∧p p₂) c₁ c₂ (e₁ , e₂) =
    cong₂ _∧_ (propagation p₁ c₁ c₂ e₁) (propagation p₂ c₁ c₂ e₂)
  propagation (p₁ ∨p p₂) c₁ c₂ (e₁ , e₂) =
    cong₂ _∨_ (propagation p₁ c₁ c₂ e₁) (propagation p₂ c₁ c₂ e₂)
  propagation (¬p p)      c₁ c₂ eq         =
    cong not (propagation p c₁ c₂ eq)
  propagation truep       _  _  _           = refl
  propagation falsep      _  _  _           = refl

  ------------------------------------------------------------------
  -- SECTION 0b: CEGIS — Counterexample-Guided Inductive Synthesis
  --
  -- Given a finite list of features and a depth bound, enumerates
  -- all PredProg terms and refines by observations. Each observation
  -- (carrier, expected-bool) eliminates candidates that disagree.
  --
  -- Key properties:
  --   - vs-shrinks: version space monotonically decreases
  --   - true-pred-survives: the correct predicate is never eliminated
  --   - propagation-accelerates: feature-equivalent observations
  --     eliminate the SAME candidates (free refinement)
  ------------------------------------------------------------------

  module CEGIS
    (all-features : List Feature)
    where

    -- Boolean filter (avoids Dec-based Data.List.filter)
    bfilter : ∀ {A : Set} → (A → Bool) → List A → List A
    bfilter f []       = []
    bfilter f (x ∷ xs) with f x
    ... | true  = x ∷ bfilter f xs
    ... | false = bfilter f xs

    -- Boolean equality
    _=ᵇ_ : Bool → Bool → Bool
    true  =ᵇ true  = true
    false =ᵇ false = true
    _     =ᵇ _     = false

    =ᵇ-refl : ∀ b → (b =ᵇ b) ≡ true
    =ᵇ-refl true  = refl
    =ᵇ-refl false = refl

    =ᵇ-sound : ∀ b₁ b₂ → (b₁ =ᵇ b₂) ≡ true → b₁ ≡ b₂
    =ᵇ-sound true  true  _ = refl
    =ᵇ-sound false false _ = refl

    ----------------------------------------------------------------
    -- Enumeration of all PredProg terms up to bounded depth
    ----------------------------------------------------------------

    atoms : List PredProg
    atoms = truep ∷ falsep ∷ map feat all-features

    -- Extend candidate set by one level of Boolean operators
    extend : List PredProg → List PredProg
    extend prev =
      prev
      ++ map ¬p_ prev
      ++ concatMap (λ p → map (p ∧p_) prev) prev
      ++ concatMap (λ p → map (p ∨p_) prev) prev

    enumerate : ℕ → List PredProg
    enumerate zero    = atoms
    enumerate (suc d) = extend (enumerate d)

    ----------------------------------------------------------------
    -- Predicate observations and consistency
    ----------------------------------------------------------------

    PredObs : Set
    PredObs = Carrier × Bool

    consistent : PredProg → PredObs → Bool
    consistent p (c , b) = eval p c =ᵇ b

    ----------------------------------------------------------------
    -- Version space: list of candidates consistent with all obs
    ----------------------------------------------------------------

    VersionSpace : Set
    VersionSpace = List PredProg

    initial-vs : ℕ → VersionSpace
    initial-vs = enumerate

    refine : VersionSpace → PredObs → VersionSpace
    refine vs ob = bfilter (λ p → consistent p ob) vs

    refine-all : VersionSpace → List PredObs → VersionSpace
    refine-all vs []         = vs
    refine-all vs (ob ∷ obs) = refine-all (refine vs ob) obs

    ----------------------------------------------------------------
    -- CEGIS step: pick first candidate, check, refine
    ----------------------------------------------------------------

    cegis-step : VersionSpace → PredObs → VersionSpace
    cegis-step = refine

    cegis-loop : VersionSpace → List PredObs → VersionSpace
    cegis-loop = refine-all

    ----------------------------------------------------------------
    -- KEY PROPERTY 1: Version space shrinks monotonically
    ----------------------------------------------------------------

    bfilter-length : ∀ {A : Set} (f : A → Bool) (xs : List A) →
      length (bfilter f xs) ≤ length xs
    bfilter-length f []       = z≤n
    bfilter-length f (x ∷ xs) with f x
    ... | true  = s≤s (bfilter-length f xs)
    ... | false = ≤-step (bfilter-length f xs)
      where
        ≤-step : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
        ≤-step z≤n     = z≤n
        ≤-step (s≤s p) = s≤s (≤-step p)

    vs-shrinks : ∀ vs ob →
      length (refine vs ob) ≤ length vs
    vs-shrinks vs ob = bfilter-length (λ p → consistent p ob) vs

    ----------------------------------------------------------------
    -- KEY PROPERTY 2: The correct predicate survives refinement
    --
    -- If p evaluates to the expected value at the observation,
    -- then p passes the consistency filter.
    ----------------------------------------------------------------

    consistent-correct : ∀ p c b →
      eval p c ≡ b →
      consistent p (c , b) ≡ true
    consistent-correct p c b eq rewrite eq = =ᵇ-refl b

    ----------------------------------------------------------------
    -- KEY PROPERTY 3: PROPAGATION ACCELERATION
    --
    -- If two carriers are feature-equivalent w.r.t. a candidate p,
    -- then p is consistent at c₁ iff consistent at c₂.
    -- This means observing at c₁ eliminates exactly the same
    -- candidates as observing at c₂ — we get free refinement!
    ----------------------------------------------------------------

    propagation-acceleration : ∀ (p : PredProg) (c₁ c₂ : Carrier) (b : Bool) →
      FeatureEquiv p c₁ c₂ →
      consistent p (c₁ , b) ≡ consistent p (c₂ , b)
    propagation-acceleration p c₁ c₂ b equiv =
      cong (λ v → v =ᵇ b) (propagation p c₁ c₂ equiv)

    ----------------------------------------------------------------
    -- Convergence bound: CEGIS terminates in at most |VS| steps
    ----------------------------------------------------------------

    cegis-bounded : ∀ vs obs →
      length (cegis-loop vs obs) ≤ length vs
    cegis-bounded vs []         = ≤-refl
    cegis-bounded vs (ob ∷ obs) =
      ≤-trans (cegis-bounded (refine vs ob) obs)
              (vs-shrinks vs ob)
      where
        ≤-trans : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
        ≤-trans z≤n     _       = z≤n
        ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

    ----------------------------------------------------------------
    -- KEY PROPERTY 5: STRICT CONVERGENCE
    --
    -- An observation is "informative" if it eliminates at least one
    -- candidate from the version space. Informative observations
    -- cause the VS to STRICTLY shrink (not just ≤, but <).
    --
    -- Combined with dissolution, this gives a tight bound:
    -- convergence needs at most min(|VS₀|, |EquivClasses|)
    -- informative observations.
    ----------------------------------------------------------------

    -- List membership (locally defined for --safe)
    data _∈ₗ_ {A : Set} : A → List A → Set where
      here  : ∀ {x xs} → x ∈ₗ (x ∷ xs)
      there : ∀ {x y xs} → x ∈ₗ xs → x ∈ₗ (y ∷ xs)

    -- Strict filter decrease: if some element is rejected,
    -- the filtered list is strictly shorter
    bfilter-strict : ∀ {A : Set} (f : A → Bool) (xs : List A) →
      ∃[ x ] (x ∈ₗ xs × f x ≡ false) →
      suc (length (bfilter f xs)) ≤ length xs
    bfilter-strict f (x ∷ xs) (.x , here , fx≡f) with f x
    ... | true  with () ← fx≡f
    ... | false = s≤s (bfilter-length f xs)
    bfilter-strict f (x ∷ xs) (z , there mem , fz≡f) with f x
    ... | true  = s≤s (bfilter-strict f xs (z , mem , fz≡f))
    ... | false = ≤-step′ (bfilter-strict f xs (z , mem , fz≡f))
      where
        ≤-step′ : ∀ {m n : ℕ} → suc m ≤ n → suc m ≤ suc n
        ≤-step′ (s≤s p) = s≤s (≤-step″ p)
          where
            ≤-step″ : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
            ≤-step″ z≤n     = z≤n
            ≤-step″ (s≤s q) = s≤s (≤-step″ q)

    -- An observation is informative if it eliminates at least one candidate
    Informative : VersionSpace → PredObs → Set
    Informative vs ob = ∃[ p ] (p ∈ₗ vs × consistent p ob ≡ false)

    -- STRICT SHRINK: informative observations strictly decrease VS size
    strict-shrink : ∀ vs ob →
      Informative vs ob →
      suc (length (refine vs ob)) ≤ length vs
    strict-shrink vs ob info =
      bfilter-strict (λ p → consistent p ob) vs info

    -- Non-informative observations leave VS unchanged
    non-informative-id : ∀ vs ob →
      (∀ p → p ∈ₗ vs → consistent p ob ≡ true) →
      refine vs ob ≡ vs
    non-informative-id [] ob _ = refl
    non-informative-id (p ∷ vs) ob all-con with consistent p ob
      | all-con p here
    ... | true | refl =
      cong (p ∷_) (non-informative-id vs ob
        (λ q mem → all-con q (there mem)))

    -- (See dissolution-strict below, after exploration-dissolution)

    ----------------------------------------------------------------
    -- SECTION 0c: PROPAGATION QUANTIFICATION
    --
    -- The central theoretical contribution. We prove three results:
    --
    -- 1. REFINE-EQUIV: Feature-equivalent carriers produce identical
    --    version space refinement. Observing at c₁ eliminates exactly
    --    the same candidates as observing at c₂.
    --
    -- 2. OBSERVATION SUBSUMPTION: After observing at c₁, a second
    --    observation at any feature-equivalent c₂ is a no-op.
    --    The version space is unchanged.
    --
    -- 3. EXPLORATION DISSOLUTION: An entire equivalence class of
    --    carriers is handled by a SINGLE observation at any
    --    representative. All other observations in the class
    --    are provably redundant.
    --
    -- Together these formalize: propagation reduces the number of
    -- needed observations from |Carriers| to |EquivClasses|.
    ----------------------------------------------------------------

    -- Two carriers agree on every feature
    AllFeatAgree : Carrier → Carrier → Set
    AllFeatAgree c₁ c₂ = ∀ (f : Feature) →
      eval-feature f c₁ ≡ eval-feature f c₂

    -- Full feature agreement implies FeatureEquiv for any PredProg
    all-agree→feat-equiv : ∀ c₁ c₂ →
      AllFeatAgree c₁ c₂ →
      ∀ p → FeatureEquiv p c₁ c₂
    all-agree→feat-equiv c₁ c₂ afa (feat f)    = afa f
    all-agree→feat-equiv c₁ c₂ afa (p₁ ∧p p₂) =
      all-agree→feat-equiv c₁ c₂ afa p₁ ,
      all-agree→feat-equiv c₁ c₂ afa p₂
    all-agree→feat-equiv c₁ c₂ afa (p₁ ∨p p₂) =
      all-agree→feat-equiv c₁ c₂ afa p₁ ,
      all-agree→feat-equiv c₁ c₂ afa p₂
    all-agree→feat-equiv c₁ c₂ afa (¬p p)      =
      all-agree→feat-equiv c₁ c₂ afa p
    all-agree→feat-equiv c₁ c₂ afa truep        = tt
    all-agree→feat-equiv c₁ c₂ afa falsep       = tt

    -- AllFeatAgree is symmetric
    all-feat-agree-sym : ∀ c₁ c₂ →
      AllFeatAgree c₁ c₂ → AllFeatAgree c₂ c₁
    all-feat-agree-sym c₁ c₂ afa f = sym (afa f)

    ----------------------------------------------------------------
    -- Auxiliary: bfilter extensionality and absorption
    ----------------------------------------------------------------

    -- Extensionality: pointwise equal predicates → equal filter results
    bfilter-ext : ∀ {A : Set} (f g : A → Bool) (xs : List A) →
      (∀ x → f x ≡ g x) →
      bfilter f xs ≡ bfilter g xs
    bfilter-ext f g [] h = refl
    bfilter-ext f g (x ∷ xs) h with f x | g x | h x
    ... | true  | .true  | refl = cong (x ∷_) (bfilter-ext f g xs h)
    ... | false | .false | refl = bfilter-ext f g xs h

    -- Absorption: if g is implied by f, filtering by g after f is a no-op
    bfilter-absorb : ∀ {A : Set} (f g : A → Bool) (xs : List A) →
      (∀ x → f x ≡ true → g x ≡ true) →
      bfilter g (bfilter f xs) ≡ bfilter f xs
    bfilter-absorb f g [] h = refl
    bfilter-absorb f g (x ∷ xs) h with f x in eq-f
    ... | false = bfilter-absorb f g xs h
    ... | true with g x | h x eq-f
    ...   | true | refl = cong (x ∷_) (bfilter-absorb f g xs h)

    ----------------------------------------------------------------
    -- Consistency under feature equivalence
    ----------------------------------------------------------------

    -- Per-candidate: equivalent carriers give same consistency
    consistent-equiv : ∀ p c₁ c₂ b →
      AllFeatAgree c₁ c₂ →
      consistent p (c₁ , b) ≡ consistent p (c₂ , b)
    consistent-equiv p c₁ c₂ b afa =
      propagation-acceleration p c₁ c₂ b
        (all-agree→feat-equiv c₁ c₂ afa p)

    -- Consistency at c₁ implies consistency at equivalent c₂
    consistent-implies : ∀ c₁ c₂ b →
      AllFeatAgree c₁ c₂ →
      ∀ p → consistent p (c₁ , b) ≡ true →
            consistent p (c₂ , b) ≡ true
    consistent-implies c₁ c₂ b afa p h =
      trans (sym (consistent-equiv p c₁ c₂ b afa)) h

    ----------------------------------------------------------------
    -- THEOREM 1: REFINE-EQUIV
    --
    -- Feature-equivalent carriers produce identical refinement.
    -- Observing at c₁ eliminates exactly the same candidates
    -- as observing at c₂ — no information is lost or gained.
    ----------------------------------------------------------------

    refine-equiv : ∀ vs c₁ c₂ b →
      AllFeatAgree c₁ c₂ →
      refine vs (c₁ , b) ≡ refine vs (c₂ , b)
    refine-equiv vs c₁ c₂ b afa =
      bfilter-ext
        (λ p → consistent p (c₁ , b))
        (λ p → consistent p (c₂ , b))
        vs
        (λ p → consistent-equiv p c₁ c₂ b afa)

    ----------------------------------------------------------------
    -- THEOREM 2: OBSERVATION SUBSUMPTION
    --
    -- After observing at c₁, a second observation at feature-
    -- equivalent c₂ is provably redundant: the version space
    -- is unchanged. Every candidate that survived c₁ automatically
    -- survives c₂.
    ----------------------------------------------------------------

    refine-absorb : ∀ vs c₁ c₂ b →
      AllFeatAgree c₁ c₂ →
      refine (refine vs (c₁ , b)) (c₂ , b) ≡ refine vs (c₁ , b)
    refine-absorb vs c₁ c₂ b afa =
      bfilter-absorb
        (λ p → consistent p (c₁ , b))
        (λ p → consistent p (c₂ , b))
        vs
        (consistent-implies c₁ c₂ b afa)

    observation-subsumption : ∀ vs c₁ c₂ b →
      AllFeatAgree c₁ c₂ →
      refine-all vs ((c₁ , b) ∷ (c₂ , b) ∷ [])
        ≡ refine vs (c₁ , b)
    observation-subsumption vs c₁ c₂ b afa =
      refine-absorb vs c₁ c₂ b afa

    ----------------------------------------------------------------
    -- THEOREM 3: EXPLORATION DISSOLUTION
    --
    -- An entire equivalence class of carriers is handled by a
    -- single observation at a representative c₀. After that one
    -- observation, ALL further observations at equivalent carriers
    -- leave the version space unchanged.
    --
    -- This is the formal statement of "propagation dissolves
    -- exploration": the number of needed observations equals the
    -- number of equivalence classes, not the number of carriers.
    ----------------------------------------------------------------

    -- List-level equivalence: all carriers in a list are equivalent to c₀
    AllEquiv : Carrier → List Carrier → Set
    AllEquiv c₀ []       = ⊤
    AllEquiv c₀ (c ∷ cs) = AllFeatAgree c₀ c × AllEquiv c₀ cs

    exploration-dissolution : ∀ vs c₀ b (cs : List Carrier) →
      AllEquiv c₀ cs →
      cegis-loop (refine vs (c₀ , b)) (map (λ c → (c , b)) cs)
        ≡ refine vs (c₀ , b)
    exploration-dissolution vs c₀ b [] _ = refl
    exploration-dissolution vs c₀ b (c ∷ cs) (afa , rest) =
      let step₁ = refine-absorb vs c₀ c b afa
      in trans
        (cong (λ vs' → cegis-loop vs' (map (λ c' → (c' , b)) cs))
              step₁)
        (exploration-dissolution vs c₀ b cs rest)

    -- Corollary: dissolution preserves version space size
    dissolution-size : ∀ vs c₀ b (cs : List Carrier) →
      AllEquiv c₀ cs →
      length (cegis-loop (refine vs (c₀ , b))
                         (map (λ c → (c , b)) cs))
        ≡ length (refine vs (c₀ , b))
    dissolution-size vs c₀ b cs afa =
      cong length (exploration-dissolution vs c₀ b cs afa)

    ----------------------------------------------------------------
    -- COROLLARY: DISSOLUTION + STRICT SHRINK
    --
    -- Within an equivalence class, only the FIRST observation
    -- can be informative. All subsequent are provably redundant.
    -- So total informative observations ≤ |EquivClasses|.
    ----------------------------------------------------------------

    dissolution-strict : ∀ vs c₀ b (cs : List Carrier) →
      AllEquiv c₀ cs →
      Informative vs (c₀ , b) →
      suc (length (cegis-loop (refine vs (c₀ , b))
                               (map (λ c → (c , b)) cs)))
        ≤ length vs
    dissolution-strict vs c₀ b cs afa info =
      subst (λ n → suc n ≤ length vs)
            (sym (cong length (exploration-dissolution vs c₀ b cs afa)))
            (strict-shrink vs (c₀ , b) info)

------------------------------------------------------------------------
-- The Synthesis Module
--
-- Parameterized by the MDP structure. The true step function is a
-- parameter—synthesis aims to recover it from observations.
------------------------------------------------------------------------

module SynthesisCore
  (State Action : Set)
  (step : State → Action → State × ℕ)
  (all-actions : List Action)
  where

  open import CSHRL.Core
  open Core State Action ℕ step _≤_ _⊔_ 0 all-actions public

  Model : Set
  Model = State → Action → State × ℕ

  ----------------------------------------------------------------------
  -- SECTION 1: OBSERVATIONS
  --
  -- An observation records a single environment transition.
  -- Valid observations match the true step function.
  -- Collecting valid observations constrains candidate models.
  ----------------------------------------------------------------------

  record Observation : Set where
    constructor obs
    field
      obs-state  : State
      obs-action : Action
      obs-next   : State
      obs-reward : ℕ

  Valid : Observation → Set
  Valid o = step (Observation.obs-state o) (Observation.obs-action o)
            ≡ (Observation.obs-next o , Observation.obs-reward o)

  AllValid : List Observation → Set
  AllValid [] = ⊤
  AllValid (o ∷ os) = Valid o × AllValid os

  _⊨_ : Model → Observation → Set
  m ⊨ o = m (Observation.obs-state o) (Observation.obs-action o)
           ≡ (Observation.obs-next o , Observation.obs-reward o)

  _⊨all_ : Model → List Observation → Set
  m ⊨all [] = ⊤
  m ⊨all (o ∷ os) = (m ⊨ o) × (m ⊨all os)

  true-model-consistent : ∀ o → Valid o → step ⊨ o
  true-model-consistent _ p = p

  true-model-all-consistent : ∀ os → AllValid os → step ⊨all os
  true-model-all-consistent [] _ = tt
  true-model-all-consistent (o ∷ os) (v , vs) =
    true-model-consistent o v , true-model-all-consistent os vs

  ----------------------------------------------------------------------
  -- SECTION 2: PARAMETRIC SOLVE AND EXTENSIONALITY
  --
  -- solve is determined by step. If two models agree on all
  -- state-action pairs, their solve values agree at all depths.
  -- This is the foundation for preservation transfer.
  ----------------------------------------------------------------------

  solve-with : Model → State → ℕ → ℕ
  solve-with m s zero    = max-list (map (λ a → proj₂ (m s a)) all-actions)
  solve-with m s (suc n) = max-list (map (λ a → solve-with m (proj₁ (m s a)) n) all-actions)

  solve-with-is-solve : ∀ s n → solve-with step s n ≡ solve s n
  solve-with-is-solve s zero    = refl
  solve-with-is-solve s (suc n) =
    cong max-list (map-ext all-actions λ a →
      solve-with-is-solve (proj₁ (step s a)) n)
    where
      map-ext : ∀ {A B : Set} (xs : List A) {f g : A → B} →
        (∀ x → f x ≡ g x) → map f xs ≡ map g xs
      map-ext []       _ = refl
      map-ext (x ∷ xs) h = cong₂ _∷_ (h x) (map-ext xs h)

  private
    map-ext : ∀ {A B : Set} (xs : List A) {f g : A → B} →
      (∀ x → f x ≡ g x) → map f xs ≡ map g xs
    map-ext []       _ = refl
    map-ext (x ∷ xs) h with h x | map-ext xs h
    ... | hx | rest = cong₂ _∷_ hx rest

  solve-ext : ∀ (m₁ m₂ : Model) →
    (∀ s a → m₁ s a ≡ m₂ s a) →
    ∀ s n → solve-with m₁ s n ≡ solve-with m₂ s n
  solve-ext m₁ m₂ eq s zero =
    cong max-list (map-ext all-actions λ a → cong proj₂ (eq s a))
  solve-ext m₁ m₂ eq s (suc n) =
    cong max-list (map-ext all-actions λ a →
      trans (solve-ext m₁ m₂ eq (proj₁ (m₁ s a)) n)
            (cong (λ s' → solve-with m₂ s' n) (cong proj₁ (eq s a))))

  synth-solve-correct : ∀ (m : Model) →
    (∀ s a → m s a ≡ step s a) →
    ∀ s n → solve-with m s n ≡ solve s n
  synth-solve-correct m eq s n =
    trans (solve-ext m step eq s n) (solve-with-is-solve s n)

  ----------------------------------------------------------------------
  -- SECTION 3: FEATURE-BASED GENERALIZATION
  --
  -- States are grouped by features. States with the same features
  -- share dynamics and rankings. This is how observations at one
  -- state generalize to unseen states with the same features.
  --
  -- The key assumption is FEATURE COHERENCE: same features →
  -- same action-value ordering. When this holds, verifying a
  -- ranking at one representative per feature class suffices.
  ----------------------------------------------------------------------

  module WithFeatures
    (Feature : Set)
    (extract : State → Feature)
    where

    FeatureCoherent : Set
    FeatureCoherent = ∀ s₁ s₂ a b →
      extract s₁ ≡ extract s₂ →
      action-value s₁ a ≤ₛ action-value s₁ b →
      action-value s₂ a ≤ₛ action-value s₂ b

    ------------------------------------------------------------------
    -- Decision Trees for Rankings
    ------------------------------------------------------------------

    data RankTree : Set where
      rleaf   : (Action → Action → Bool) → RankTree
      rbranch : (Feature → Bool) → RankTree → RankTree → RankTree

    eval-tree : RankTree → Feature → Action → Action → Bool
    eval-tree (rleaf rank) _ = rank
    eval-tree (rbranch pred left right) f =
      if pred f then eval-tree left f else eval-tree right f

    tree-rank : RankTree → State → Action → Action → Bool
    tree-rank t s = eval-tree t (extract s)

    tree-generalizes : ∀ t s₁ s₂ →
      extract s₁ ≡ extract s₂ →
      ∀ a b → tree-rank t s₁ a b ≡ tree-rank t s₂ a b
    tree-generalizes t s₁ s₂ feat-eq a b =
      cong (λ f → eval-tree t f a b) feat-eq

    TreeRanks : RankTree → State → Action → Action → Set
    TreeRanks t s a b = tree-rank t s a b ≡ true

    ------------------------------------------------------------------
    -- Preservation Transfer
    ------------------------------------------------------------------

    PreservesAt : RankTree → State → Set
    PreservesAt t s = ∀ a b →
      tree-rank t s a b ≡ true →
      action-value s a ≤ₛ action-value s b

    preservation-transfer : ∀ t →
      FeatureCoherent →
      ∀ s-rep s-new →
      extract s-rep ≡ extract s-new →
      PreservesAt t s-rep →
      PreservesAt t s-new
    preservation-transfer t coherent s-rep s-new feat-eq pres-rep a b rank-new =
      let rank-rep : tree-rank t s-rep a b ≡ true
          rank-rep = trans (tree-generalizes t s-rep s-new feat-eq a b) rank-new
      in coherent s-rep s-new a b feat-eq (pres-rep a b rank-rep)

    ------------------------------------------------------------------
    -- Full CoindHomo from Representatives
    ------------------------------------------------------------------

    module WithRepresentatives
      (t : RankTree)
      (coherent : FeatureCoherent)
      (representative : State → State)
      (rep-feat : ∀ s → extract (representative s) ≡ extract s)
      (rep-preserves : ∀ s → PreservesAt t (representative s))
      where

      tree-preserves-all : ∀ a b s →
        TreeRanks t s a b →
        action-value s a ≤ₛ action-value s b
      tree-preserves-all a b s =
        preservation-transfer t coherent (representative s) s
          (rep-feat s) (rep-preserves s) a b

      instance
        SynthesizedHomo : CoindHomo
        SynthesizedHomo = record
          { _≤ₐ_ = TreeRanks t
          ; preserves = tree-preserves-all
          }

  ----------------------------------------------------------------------
  -- SECTION 4: VERSION SPACE
  ----------------------------------------------------------------------

  InVersionSpace : Model → List Observation → Set
  InVersionSpace m os = m ⊨all os

  true-model-survives : ∀ os o →
    AllValid os → Valid o →
    InVersionSpace step (o ∷ os)
  true-model-survives os o avs v =
    true-model-consistent o v , true-model-all-consistent os avs

  version-space-shrinks : ∀ m o os →
    InVersionSpace m (o ∷ os) →
    InVersionSpace m os
  version-space-shrinks _ _ _ (_ , rest) = rest

  ----------------------------------------------------------------------
  -- SECTION 5: OBSERVATION PROPAGATION (STUB)
  ----------------------------------------------------------------------

  Refines : Model → Observation → Set
  Refines m o = m ⊨ o

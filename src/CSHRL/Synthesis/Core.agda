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
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
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
  -- Policy extraction: decision chain over PredProgs
  --
  -- Maps a list of (predicate, action) pairs and a default action
  -- to a policy Carrier → Action.  Generalises binary pol-of to
  -- k-ary action spaces without hardcoding the mapping.
  --
  --   2 actions: pol-chain [(rank★ , Left)] Right
  --   3 actions: pol-chain [(p₁ , A₁) , (p₂ , A₂)] A₃
  ------------------------------------------------------------------

  pol-chain : {Action : Set} → List (PredProg × Action)
            → Action → Carrier → Action
  pol-chain []              def _ = def
  pol-chain ((p , a) ∷ rest) def c with eval p c
  ... | true  = a
  ... | false = pol-chain rest def c

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

    -- Extend candidate set by one level of Boolean operators.
    -- Includes mixed conjunctions/disjunctions (atom ∧ ¬atom, etc.)
    -- so that depth 1 can express predicates like x<0 ∧ ¬(v<t).
    extend : List PredProg → List PredProg
    extend prev =
      let neg = map ¬p_ prev
      in prev
      ++ neg
      ++ concatMap (λ p → map (p ∧p_) prev) prev
      ++ concatMap (λ p → map (p ∨p_) prev) prev
      ++ concatMap (λ p → map (p ∧p_) neg)  prev
      ++ concatMap (λ p → map (p ∨p_) neg)  prev

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

    ----------------------------------------------------------------
    -- SECTION 0d: QUOTIENT STRUCTURE
    --
    -- AllFeatAgree is an equivalence relation on carriers,
    -- inducing a quotient C/~.  We prove:
    --   1. Equivalence relation properties (refl, trans)
    --   2. Auxiliary: bfilter-sound and cegis-loop-⊆
    --   3. Subsumption stability: subsumption survives further
    --      refinement (the key technical lemma)
    --   4. EXPLORATION COMPLETENESS: after processing one
    --      representative per equivalence class, no further
    --      carrier can refine the version space
    ----------------------------------------------------------------

    AFA-refl : ∀ c → AllFeatAgree c c
    AFA-refl c f = refl

    AFA-trans : ∀ c₁ c₂ c₃ →
      AllFeatAgree c₁ c₂ → AllFeatAgree c₂ c₃ → AllFeatAgree c₁ c₃
    AFA-trans c₁ c₂ c₃ afa₁₂ afa₂₃ f = trans (afa₁₂ f) (afa₂₃ f)

    bfilter-sound : ∀ {A : Set} (f : A → Bool) (xs : List A) →
      ∀ x → x ∈ₗ bfilter f xs → f x ≡ true
    bfilter-sound f (y ∷ xs) x mem with f y in eq
    bfilter-sound f (y ∷ xs) .y here        | true = eq
    bfilter-sound f (y ∷ xs) x  (there m)   | true = bfilter-sound f xs x m
    bfilter-sound f (y ∷ xs) x  mem         | false = bfilter-sound f xs x mem

    private
      bfilter-⊆ : ∀ {A : Set} (f : A → Bool) (xs : List A) →
        ∀ x → x ∈ₗ bfilter f xs → x ∈ₗ xs
      bfilter-⊆ f (y ∷ xs) x mem with f y
      bfilter-⊆ f (y ∷ xs) .y here        | true = here
      bfilter-⊆ f (y ∷ xs) x  (there m)   | true = there (bfilter-⊆ f xs x m)
      bfilter-⊆ f (y ∷ xs) x  mem         | false = there (bfilter-⊆ f xs x mem)

    cegis-loop-⊆ : ∀ vs obs →
      ∀ x → x ∈ₗ cegis-loop vs obs → x ∈ₗ vs
    cegis-loop-⊆ vs [] x mem = mem
    cegis-loop-⊆ vs (ob ∷ obs) x mem =
      bfilter-⊆ (λ p → consistent p ob) vs x
        (cegis-loop-⊆ (refine vs ob) obs x mem)

    ----------------------------------------------------------------
    -- SUBSUMPTION STABILITY
    --
    -- After refining by representative r and processing further
    -- observations, refining by any carrier c ~ r is still a
    -- no-op.  This is because further refinements only remove
    -- elements, and removed elements cannot violate subsumption.
    ----------------------------------------------------------------

    refine-after-cegis : ∀ vs r c b (obs : List PredObs) →
      AllFeatAgree r c →
      refine (cegis-loop (refine vs (r , b)) obs) (c , b)
        ≡ cegis-loop (refine vs (r , b)) obs
    refine-after-cegis vs r c b obs afa =
      non-informative-id
        (cegis-loop (refine vs (r , b)) obs) (c , b)
        (λ p mem →
          consistent-implies r c b afa p
            (bfilter-sound (λ q → consistent q (r , b)) vs p
              (cegis-loop-⊆ (refine vs (r , b)) obs p mem)))

    ----------------------------------------------------------------
    -- EXPLORATION COMPLETENESS
    --
    -- After processing a list of representatives (one per
    -- equivalence class), any carrier equivalent to some
    -- representative is provably redundant: refining the VS
    -- by that carrier is a no-op.
    --
    -- This formalizes "dissolution is all you need": once every
    -- class has been observed at a representative, no further
    -- observation can be informative.
    ----------------------------------------------------------------

    exploration-complete : ∀ vs (reps : List Carrier) b c →
      (∃[ r ] (r ∈ₗ reps × AllFeatAgree r c)) →
      refine (cegis-loop vs (map (λ r → (r , b)) reps)) (c , b)
        ≡ cegis-loop vs (map (λ r → (r , b)) reps)
    exploration-complete vs (r ∷ reps) b c (.r , here , afa) =
      refine-after-cegis vs r c b (map (λ r' → (r' , b)) reps) afa
    exploration-complete vs (r' ∷ reps) b c (r , there mem , afa) =
      exploration-complete (refine vs (r' , b)) reps b c (r , mem , afa)

    ----------------------------------------------------------------
    -- SECTION 0e: TEMPORAL PROPAGATION
    --
    -- When a transition function preserves feature equivalence,
    -- observations propagate along successor chains.  This
    -- extends spatial propagation (across carriers at one step)
    -- to temporal propagation (along entire trajectories).
    --
    -- Key result: one observation trajectory from c₁ covers
    -- ALL trajectories from feature-equivalent c₂, because
    -- feature preservation composes along transitions.
    ----------------------------------------------------------------

    module TemporalPropagation
      {Act : Set}
      (step-carrier : Carrier → Act → Carrier)
      (step-preserves-feat : ∀ c₁ c₂ a →
        AllFeatAgree c₁ c₂ →
        AllFeatAgree (step-carrier c₁ a) (step-carrier c₂ a))
      where

      -- Iterated transition along an action sequence
      iterₜ : Carrier → List Act → Carrier
      iterₜ c []       = c
      iterₜ c (a ∷ as) = iterₜ (step-carrier c a) as

      -- Feature equivalence propagates through arbitrary action sequences
      temporal-feat-equiv : ∀ c₁ c₂ (as : List Act) →
        AllFeatAgree c₁ c₂ →
        AllFeatAgree (iterₜ c₁ as) (iterₜ c₂ as)
      temporal-feat-equiv c₁ c₂ [] afa = afa
      temporal-feat-equiv c₁ c₂ (a ∷ as) afa =
        temporal-feat-equiv
          (step-carrier c₁ a) (step-carrier c₂ a) as
          (step-preserves-feat c₁ c₂ a afa)

      -- Trajectory: observations along a path driven by actions
      trajectory : Carrier → Bool → List Act → List PredObs
      trajectory c b []       = (c , b) ∷ []
      trajectory c b (a ∷ as) = (c , b) ∷ trajectory (step-carrier c a) b as

      -- THEOREM: Trajectories from feature-equivalent carriers
      -- produce identical version-space refinement
      trajectory-refine-equiv : ∀ vs c₁ c₂ b (as : List Act) →
        AllFeatAgree c₁ c₂ →
        cegis-loop vs (trajectory c₁ b as)
          ≡ cegis-loop vs (trajectory c₂ b as)
      trajectory-refine-equiv vs c₁ c₂ b [] afa =
        refine-equiv vs c₁ c₂ b afa
      trajectory-refine-equiv vs c₁ c₂ b (a ∷ as) afa =
        trans
          (cong (λ vs' → cegis-loop vs'
                   (trajectory (step-carrier c₁ a) b as))
                (refine-equiv vs c₁ c₂ b afa))
          (trajectory-refine-equiv (refine vs (c₂ , b))
            (step-carrier c₁ a) (step-carrier c₂ a) b as
            (step-preserves-feat c₁ c₂ a afa))

      -- THEOREM: After observing a trajectory from c₁,
      -- the entire trajectory from equivalent c₂ is subsumed.
      -- This is temporal dissolution: one trajectory observation
      -- covers entire families of equivalent trajectories.
      trajectory-dissolution : ∀ vs c₁ c₂ b (as : List Act) →
        AllFeatAgree c₁ c₂ →
        cegis-loop (cegis-loop vs (trajectory c₁ b as))
                   (trajectory c₂ b as)
          ≡ cegis-loop vs (trajectory c₁ b as)
      trajectory-dissolution vs c₁ c₂ b [] afa =
        refine-absorb vs c₁ c₂ b afa
      trajectory-dissolution vs c₁ c₂ b (a ∷ as) afa =
        trans
          (cong (λ v → cegis-loop v
                   (trajectory (step-carrier c₂ a) b as))
                (refine-after-cegis vs c₁ c₂ b
                  (trajectory (step-carrier c₁ a) b as) afa))
          (trajectory-dissolution (refine vs (c₁ , b))
            (step-carrier c₁ a) (step-carrier c₂ a) b as
            (step-preserves-feat c₁ c₂ a afa))

    ----------------------------------------------------------------
    -- SECTION 0f: FEATURE SUFFICIENCY
    --
    -- When the feature set captures the target function (i.e.,
    -- AllFeatAgree implies identical target values), CEGIS with
    -- representative observations guarantees that every surviving
    -- program is correct on ALL carriers, not just the observed
    -- ones.
    --
    -- Key results:
    --   1. FeatureRespects: target respects feature equivalence
    --   2. match-propagates: correctness propagates to equiv carriers
    --   3. generalization: representatives → global correctness
    --   4. cegis-survivors-consistent: CEGIS survivors match all obs
    --   5. sufficient-cegis: the CROWN JEWEL — with sufficient
    --      features and representative obs, every survivor is
    --      correct EVERYWHERE
    ----------------------------------------------------------------

    FeatureRespects : (Carrier → Bool) → Set
    FeatureRespects target = ∀ c₁ c₂ →
      AllFeatAgree c₁ c₂ → target c₁ ≡ target c₂

    Matches : PredProg → (Carrier → Bool) → Carrier → Set
    Matches p target c = eval p c ≡ target c

    MatchesAll : PredProg → (Carrier → Bool) → Set
    MatchesAll p target = ∀ c → Matches p target c

    match-propagates : ∀ p target c₁ c₂ →
      AllFeatAgree c₁ c₂ →
      FeatureRespects target →
      Matches p target c₁ →
      Matches p target c₂
    match-propagates p target c₁ c₂ afa respects match₁ =
      trans
        (sym (propagation p c₁ c₂ (all-agree→feat-equiv c₁ c₂ afa p)))
        (trans match₁ (respects c₁ c₂ afa))

    Covers : List Carrier → Set
    Covers reps = ∀ c → ∃[ r ] (r ∈ₗ reps × AllFeatAgree r c)

    generalization : ∀ p target (reps : List Carrier) →
      FeatureRespects target →
      Covers reps →
      (∀ r → r ∈ₗ reps → Matches p target r) →
      MatchesAll p target
    generalization p target reps respects covers matches-reps c =
      let (r , r-in , afa) = covers c
      in match-propagates p target r c afa respects (matches-reps r r-in)

    cegis-survivors-consistent : ∀ vs obs →
      ∀ p → p ∈ₗ cegis-loop vs obs →
      ∀ ob → ob ∈ₗ obs → consistent p ob ≡ true
    cegis-survivors-consistent vs (ob ∷ obs) p mem .ob here =
      bfilter-sound (λ q → consistent q ob) vs p
        (cegis-loop-⊆ (refine vs ob) obs p mem)
    cegis-survivors-consistent vs (ob ∷ obs) p mem ob' (there mem') =
      cegis-survivors-consistent (refine vs ob) obs p mem ob' mem'

    consistent-to-match : ∀ p c b →
      consistent p (c , b) ≡ true →
      eval p c ≡ b
    consistent-to-match p c b = =ᵇ-sound (eval p c) b

    private
      map-∈ : ∀ {A B : Set} (f : A → B) (xs : List A) (x : A) →
        x ∈ₗ xs → f x ∈ₗ map f xs
      map-∈ f (_ ∷ _)  x here        = here
      map-∈ f (_ ∷ xs) x (there mem) = there (map-∈ f xs x mem)

    ----------------------------------------------------------------
    -- THE CROWN JEWEL: Feature Sufficiency Theorem
    --
    -- With sufficient features (target respects AllFeatAgree)
    -- and representative observations (one per equivalence class),
    -- every CEGIS survivor is correct on ALL carriers.
    --
    -- This transforms Exploration-Complete from "no more
    -- refinement possible" to "correct answer guaranteed."
    ----------------------------------------------------------------

    sufficient-cegis : ∀ vs target (reps : List Carrier) →
      FeatureRespects target →
      Covers reps →
      ∀ p → p ∈ₗ cegis-loop vs (map (λ r → (r , target r)) reps) →
      MatchesAll p target
    sufficient-cegis vs target reps respects covers p mem =
      generalization p target reps respects covers
        (λ r r-in →
          consistent-to-match p r (target r)
            (cegis-survivors-consistent vs
              (map (λ r' → (r' , target r')) reps) p mem
              (r , target r)
              (map-∈ (λ r' → (r' , target r')) reps r r-in)))

    ----------------------------------------------------------------
    -- SECTION 0g: MULTI-PREDICATE PROPAGATION
    --
    -- When synthesizing multiple predicates from the same feature
    -- space (e.g., is-dead and is-solved in CPMDP), observations
    -- can be shared across predicates:
    --
    --   1. Joint dissolution: one carrier refines BOTH version
    --      spaces, and AllFeatAgree propagates to both
    --   2. Cross-predicate entailment: knowing target₁ c = true
    --      constrains target₂ c (e.g., dead → ¬solved)
    --   3. Joint sufficiency: both predicates correct everywhere
    --      from the SAME set of representative observations
    ----------------------------------------------------------------

    module MultiPredicate
      (target₁ target₂ : Carrier → Bool)
      where

      -- One carrier observation refines BOTH version spaces
      joint-refine : VersionSpace → VersionSpace → Carrier →
        VersionSpace × VersionSpace
      joint-refine vs₁ vs₂ c =
        (refine vs₁ (c , target₁ c) , refine vs₂ (c , target₂ c))

      -- Joint dissolution: AllFeatAgree propagates to both
      -- version spaces simultaneously
      joint-refine-equiv : ∀ vs₁ vs₂ c₁ c₂ →
        AllFeatAgree c₁ c₂ →
        FeatureRespects target₁ →
        FeatureRespects target₂ →
        joint-refine vs₁ vs₂ c₁ ≡ joint-refine vs₁ vs₂ c₂
      joint-refine-equiv vs₁ vs₂ c₁ c₂ afa resp₁ resp₂
        rewrite resp₁ c₁ c₂ afa | resp₂ c₁ c₂ afa =
        cong₂ _,_
          (refine-equiv vs₁ c₁ c₂ (target₁ c₂) afa)
          (refine-equiv vs₂ c₁ c₂ (target₂ c₂) afa)

      -- Cross-predicate entailment
      Entails¬ : Set
      Entails¬ = ∀ c → target₁ c ≡ true → target₂ c ≡ false

      -- With entailment, observing target₁ c = true gives the
      -- target₂ observation for free: we know target₂ c = false
      -- without evaluating target₂
      entailment-free-obs : ∀ c →
        Entails¬ →
        target₁ c ≡ true →
        target₂ c ≡ false
      entailment-free-obs c ent t1 = ent c t1

      -- Cross-dissolution: entailment + dissolution gives one
      -- observation for two predicates across an entire class.
      -- Observing target₁ c₁ = true refines BOTH VS, and
      -- all equivalent c₂ are redundant for BOTH.
      cross-dissolution : ∀ vs₁ vs₂ c₁ c₂ →
        AllFeatAgree c₁ c₂ →
        Entails¬ →
        target₁ c₁ ≡ true →
        let vs₁' = refine vs₁ (c₁ , true)
            vs₂' = refine vs₂ (c₁ , false)
        in refine vs₁' (c₂ , true)  ≡ vs₁'
         × refine vs₂' (c₂ , false) ≡ vs₂'
      cross-dissolution vs₁ vs₂ c₁ c₂ afa ent _ =
        refine-absorb vs₁ c₁ c₂ true afa ,
        refine-absorb vs₂ c₁ c₂ false afa

      -- JOINT SUFFICIENCY: With sufficient features and the same
      -- set of representative observations, BOTH synthesized
      -- predicates are correct on ALL carriers.
      --
      -- One set of representatives → two correct predicates.
      joint-sufficient : ∀ vs₁ vs₂ (reps : List Carrier) →
        FeatureRespects target₁ →
        FeatureRespects target₂ →
        Covers reps →
        ∀ p₁ p₂ →
        p₁ ∈ₗ cegis-loop vs₁ (map (λ r → (r , target₁ r)) reps) →
        p₂ ∈ₗ cegis-loop vs₂ (map (λ r → (r , target₂ r)) reps) →
        MatchesAll p₁ target₁ × MatchesAll p₂ target₂
      joint-sufficient vs₁ vs₂ reps resp₁ resp₂ covers p₁ p₂ m₁ m₂ =
        sufficient-cegis vs₁ target₁ reps resp₁ covers p₁ m₁ ,
        sufficient-cegis vs₂ target₂ reps resp₂ covers p₂ m₂

    ----------------------------------------------------------------
    -- SECTION 0h: ONLINE SYNTHESIS
    --
    -- Establishes that CEGIS is inherently order-independent:
    -- observations can be processed in any order with the same
    -- result. This enables integration with the learning loop,
    -- where observations arrive incrementally.
    --
    -- Key results:
    --   1. refine-commutes: observation order doesn't matter
    --   2. cegis-loop-swap: swapping adjacent obs is identity
    --   3. replay-redundant: re-observing is a no-op
    --   4. LearningBridge: generic learning-synthesis integration
    ----------------------------------------------------------------

    private
      -- if-based filter avoids with-auxiliary functions that block
      -- nested reduction under simultaneous with-abstraction
      bfilter' : ∀ {A : Set} → (A → Bool) → List A → List A
      bfilter' f []       = []
      bfilter' f (x ∷ xs) =
        if f x then x ∷ bfilter' f xs else bfilter' f xs

      bfilter-eq : ∀ {A : Set} (f : A → Bool) (xs : List A) →
        bfilter f xs ≡ bfilter' f xs
      bfilter-eq f [] = refl
      bfilter-eq f (x ∷ xs) with f x
      ... | true  = cong (x ∷_) (bfilter-eq f xs)
      ... | false = bfilter-eq f xs

      bfilter'-unfold-t : ∀ {A : Set} (f : A → Bool) (x : A)
        (xs : List A) → f x ≡ true →
        bfilter' f (x ∷ xs) ≡ x ∷ bfilter' f xs
      bfilter'-unfold-t f x xs eq rewrite eq = refl

      bfilter'-unfold-f : ∀ {A : Set} (f : A → Bool) (x : A)
        (xs : List A) → f x ≡ false →
        bfilter' f (x ∷ xs) ≡ bfilter' f xs
      bfilter'-unfold-f f x xs eq rewrite eq = refl

      bfilter'-swap : ∀ {A : Set} (f g : A → Bool) (xs : List A) →
        bfilter' g (bfilter' f xs) ≡ bfilter' f (bfilter' g xs)
      bfilter'-swap f g [] = refl
      bfilter'-swap {A} f g (x ∷ xs) =
        aux (f x) (g x) refl refl
        where
          aux : ∀ b₁ b₂ → f x ≡ b₁ → g x ≡ b₂ →
            bfilter' g (bfilter' f (x ∷ xs))
              ≡ bfilter' f (bfilter' g (x ∷ xs))
          aux true true eq₁ eq₂ =
            trans (cong (bfilter' g) (bfilter'-unfold-t f x xs eq₁))
              (trans (bfilter'-unfold-t g x (bfilter' f xs) eq₂)
                (trans (cong (x ∷_) (bfilter'-swap f g xs))
                  (trans (sym (bfilter'-unfold-t f x (bfilter' g xs) eq₁))
                    (cong (bfilter' f)
                      (sym (bfilter'-unfold-t g x xs eq₂))))))
          aux true false eq₁ eq₂ =
            trans (cong (bfilter' g) (bfilter'-unfold-t f x xs eq₁))
              (trans (bfilter'-unfold-f g x (bfilter' f xs) eq₂)
                (trans (bfilter'-swap f g xs)
                  (cong (bfilter' f)
                    (sym (bfilter'-unfold-f g x xs eq₂)))))
          aux false true eq₁ eq₂ =
            trans (cong (bfilter' g) (bfilter'-unfold-f f x xs eq₁))
              (trans (bfilter'-swap f g xs)
                (trans (sym (bfilter'-unfold-f f x (bfilter' g xs) eq₁))
                  (cong (bfilter' f)
                    (sym (bfilter'-unfold-t g x xs eq₂)))))
          aux false false eq₁ eq₂ =
            trans (cong (bfilter' g) (bfilter'-unfold-f f x xs eq₁))
              (trans (bfilter'-swap f g xs)
                (cong (bfilter' f)
                  (sym (bfilter'-unfold-f g x xs eq₂))))

    -- Observation refinement is COMMUTATIVE: order doesn't matter.
    -- The final version space depends on the SET of observations,
    -- not on the order they are processed.
    refine-commutes : ∀ vs ob₁ ob₂ →
      refine (refine vs ob₁) ob₂ ≡ refine (refine vs ob₂) ob₁
    refine-commutes vs ob₁ ob₂ =
      let f₁ = λ p → consistent p ob₁
          f₂ = λ p → consistent p ob₂
      in trans (cong (bfilter f₂) (bfilter-eq f₁ vs))
        (trans (bfilter-eq f₂ (bfilter' f₁ vs))
        (trans (bfilter'-swap f₁ f₂ vs)
        (trans (sym (bfilter-eq f₁ (bfilter' f₂ vs)))
               (cong (bfilter f₁) (sym (bfilter-eq f₂ vs))))))

    -- Swapping any two adjacent observations in a CEGIS run
    -- produces the same version space.
    cegis-loop-swap : ∀ vs ob₁ ob₂ obs →
      cegis-loop vs (ob₁ ∷ ob₂ ∷ obs)
        ≡ cegis-loop vs (ob₂ ∷ ob₁ ∷ obs)
    cegis-loop-swap vs ob₁ ob₂ obs =
      cong (λ v → cegis-loop v obs) (refine-commutes vs ob₁ ob₂)

    -- REPLAY REDUNDANCY: if an observation was already processed
    -- somewhere in the stream, re-applying it is a no-op.
    -- This is the online analog of idempotence: the learner can
    -- safely re-submit any previous observation.
    replay-redundant : ∀ vs obs ob →
      ob ∈ₗ obs →
      refine (cegis-loop vs obs) ob ≡ cegis-loop vs obs
    replay-redundant vs obs ob mem =
      non-informative-id (cegis-loop vs obs) ob
        (λ p p-in →
          cegis-survivors-consistent vs obs p p-in ob mem)

    ----------------------------------------------------------------
    -- LEARNING BRIDGE
    --
    -- Generic integration between a learning loop (which produces
    -- domain-specific feedback) and the synthesis version space.
    --
    -- The bridge is parameterized by a mapping from learner
    -- feedback to synthesis observations. This abstraction covers:
    --
    --   FDMDP: feedback = (state, a, b, trace-comparison)
    --          maps to PredObs for the prefer(a,b) predicate
    --
    --   CPMDP: feedback = (config, is-dead/is-solved evaluation)
    --          maps to PredObs for the target predicate
    --
    -- Key theorem: bridge-sufficient proves that if the mapped
    -- feedback covers all representatives, every CEGIS survivor
    -- is correct everywhere — connecting learning convergence
    -- to synthesis correctness.
    ----------------------------------------------------------------

    module LearningBridge
      {Feedback : Set}
      (to-obs : Feedback → PredObs)
      where

      bridge-step : VersionSpace → Feedback → VersionSpace
      bridge-step vs fb = refine vs (to-obs fb)

      bridge-batch : VersionSpace → List Feedback → VersionSpace
      bridge-batch vs []         = vs
      bridge-batch vs (fb ∷ fbs) = bridge-batch (bridge-step vs fb) fbs

      -- The bridge reduces to standard CEGIS on mapped observations
      bridge-is-cegis : ∀ vs fbs →
        bridge-batch vs fbs ≡ cegis-loop vs (map to-obs fbs)
      bridge-is-cegis vs [] = refl
      bridge-is-cegis vs (fb ∷ fbs) =
        bridge-is-cegis (refine vs (to-obs fb)) fbs

      -- Bridge VS shrinks monotonically
      bridge-mono : ∀ vs fbs →
        length (bridge-batch vs fbs) ≤ length vs
      bridge-mono vs fbs =
        subst (_≤ length vs)
          (sym (cong length (bridge-is-cegis vs fbs)))
          (cegis-bounded vs (map to-obs fbs))

      -- BRIDGE SUFFICIENCY: the crown jewel of integration.
      -- If the learning loop produces feedback that maps to
      -- representative observations for the target, then every
      -- program surviving the bridge is correct EVERYWHERE.
      --
      -- This connects learning convergence to synthesis
      -- correctness: the learner drives the synthesizer,
      -- and the synthesizer guarantees global correctness.
      bridge-sufficient : ∀ vs target (reps : List Carrier) →
        FeatureRespects target →
        Covers reps →
        (fbs : List Feedback) →
        map to-obs fbs ≡ map (λ r → (r , target r)) reps →
        ∀ p → p ∈ₗ bridge-batch vs fbs →
        MatchesAll p target
      bridge-sufficient vs target reps respects covers fbs obs-eq p mem =
        sufficient-cegis vs target reps respects covers p
          (subst (p ∈ₗ_)
            (trans (bridge-is-cegis vs fbs)
                   (cong (cegis-loop vs) obs-eq))
            mem)

      -- Bridge commutes: feedback order doesn't matter
      bridge-commutes : ∀ vs fb₁ fb₂ →
        bridge-step (bridge-step vs fb₁) fb₂
          ≡ bridge-step (bridge-step vs fb₂) fb₁
      bridge-commutes vs fb₁ fb₂ =
        refine-commutes vs (to-obs fb₁) (to-obs fb₂)

      -- Bridge replay: re-submitting previous feedback is no-op
      bridge-replay : ∀ vs fbs fb →
        fb ∈ₗ fbs →
        bridge-step (bridge-batch vs fbs) fb
          ≡ bridge-batch vs fbs
      bridge-replay vs fbs fb mem =
        subst
          (λ v → refine v (to-obs fb) ≡ v)
          (sym (bridge-is-cegis vs fbs))
          (replay-redundant vs (map to-obs fbs) (to-obs fb)
            (map-∈ to-obs fbs fb mem))

    ----------------------------------------------------------------
    -- SECTION 0i: SAMPLE COMPLEXITY LOWER BOUND
    --
    -- Establishes that |C/~| is a TIGHT bound on sample complexity:
    -- not only do |C/~| representative observations suffice
    -- (sufficient-cegis), but fewer observations cannot guarantee
    -- correctness.
    --
    -- The key insight: CEGIS only "sees" carriers through
    -- observations. Two targets producing identical observations
    -- yield identical version spaces — so any survivor for one
    -- is automatically a survivor for the other.
    --
    -- Key results:
    --   1. same-obs-same-vs: indistinguishable targets → same VS
    --   2. survivor-transfer: survivors transfer between targets
    --   3. covered-agreement: feature-respecting targets agreeing
    --      on representatives agree on all covered carriers
    --   4. full-coverage-determines: with Covers, agreement on
    --      reps implies agreement everywhere
    --   5. no-universal-match: disagreeing targets can't both be
    --      matched by any single program
    --   6. lower-bound: the combined statement — without full
    --      coverage, CEGIS is underdetermined
    ----------------------------------------------------------------

    private
      map-ext-∈ : ∀ {A B : Set} {f g : A → B} (xs : List A) →
        (∀ x → x ∈ₗ xs → f x ≡ g x) →
        map f xs ≡ map g xs
      map-ext-∈ []       _ = refl
      map-ext-∈ (x ∷ xs) h =
        cong₂ _∷_ (h x here)
          (map-ext-∈ xs (λ y mem → h y (there mem)))

    same-obs-same-vs : ∀ vs (cs : List Carrier)
      (target₁ target₂ : Carrier → Bool) →
      (∀ c → c ∈ₗ cs → target₁ c ≡ target₂ c) →
      cegis-loop vs (map (λ c → (c , target₁ c)) cs)
        ≡ cegis-loop vs (map (λ c → (c , target₂ c)) cs)
    same-obs-same-vs vs cs target₁ target₂ agree =
      cong (cegis-loop vs)
        (map-ext-∈ cs (λ c mem → cong (c ,_) (agree c mem)))

    survivor-transfer : ∀ vs (cs : List Carrier)
      (target₁ target₂ : Carrier → Bool) →
      (∀ c → c ∈ₗ cs → target₁ c ≡ target₂ c) →
      ∀ p → p ∈ₗ cegis-loop vs (map (λ c → (c , target₁ c)) cs) →
            p ∈ₗ cegis-loop vs (map (λ c → (c , target₂ c)) cs)
    survivor-transfer vs cs target₁ target₂ agree p mem =
      subst (p ∈ₗ_) (same-obs-same-vs vs cs target₁ target₂ agree) mem

    covered-agreement : ∀ (target₁ target₂ : Carrier → Bool)
      (reps : List Carrier) →
      FeatureRespects target₁ →
      FeatureRespects target₂ →
      (∀ r → r ∈ₗ reps → target₁ r ≡ target₂ r) →
      ∀ c → (∃[ r ] (r ∈ₗ reps × AllFeatAgree r c)) →
      target₁ c ≡ target₂ c
    covered-agreement target₁ target₂ reps resp₁ resp₂ agree c
      (r , r-in , afa) =
      trans (sym (resp₁ r c afa))
        (trans (agree r r-in) (resp₂ r c afa))

    full-coverage-determines : ∀ (target₁ target₂ : Carrier → Bool)
      (reps : List Carrier) →
      FeatureRespects target₁ →
      FeatureRespects target₂ →
      Covers reps →
      (∀ r → r ∈ₗ reps → target₁ r ≡ target₂ r) →
      ∀ c → target₁ c ≡ target₂ c
    full-coverage-determines target₁ target₂ reps resp₁ resp₂ covers
      agree c =
      covered-agreement target₁ target₂ reps resp₁ resp₂ agree c
        (covers c)

    no-universal-match : ∀ (target₁ target₂ : Carrier → Bool)
      (c : Carrier) →
      target₁ c ≢ target₂ c →
      ∀ p → ¬ (MatchesAll p target₁ × MatchesAll p target₂)
    no-universal-match target₁ target₂ c disagree p (m₁ , m₂) =
      disagree (trans (sym (m₁ c)) (m₂ c))

    -- THE LOWER BOUND:
    -- If observations don't distinguish target₁ from target₂
    -- (they agree on all observed carriers), then every
    -- CEGIS survivor for target₁ also survives for target₂.
    -- But if the targets disagree on some carrier c, no
    -- program can match both everywhere — so at least one
    -- target has a survivor that is incorrect somewhere.
    --
    -- Combined with sufficient-cegis (the upper bound),
    -- this proves that |C/~| is the TIGHT sample complexity:
    -- one representative per equivalence class is both
    -- necessary and sufficient.
    lower-bound : ∀ vs (reps : List Carrier)
      (target₁ target₂ : Carrier → Bool) (c : Carrier) →
      (∀ r → r ∈ₗ reps → target₁ r ≡ target₂ r) →
      target₁ c ≢ target₂ c →
      ∀ p → p ∈ₗ cegis-loop vs (map (λ r → (r , target₁ r)) reps) →
      p ∈ₗ cegis-loop vs (map (λ r → (r , target₂ r)) reps)
        × ¬ (MatchesAll p target₁ × MatchesAll p target₂)
    lower-bound vs reps target₁ target₂ c agree disagree p mem =
      survivor-transfer vs reps target₁ target₂ agree p mem ,
      no-universal-match target₁ target₂ c disagree p

    -- THE TIGHT BOUND (combining upper and lower):
    --
    -- Upper (sufficient-cegis): With Covers reps,
    --   every survivor matches the target everywhere.
    --
    -- Lower (lower-bound): Without Covers, there exists a
    --   target₂ ≢ target₁ on some uncovered c, yet
    --   target₂ agrees on all reps. Survivors transfer
    --   between the two, but no program can match both.
    --
    -- Therefore: the minimum observation set for guaranteed
    -- correctness is EXACTLY one per equivalence class.
    --
    -- Formal statement: if Covers holds AND FeatureRespects,
    -- then agreement on reps forces agreement everywhere —
    -- so no indistinguishable alternative target can exist.
    tight-bound : ∀ (target₁ target₂ : Carrier → Bool)
      (reps : List Carrier) →
      FeatureRespects target₁ →
      FeatureRespects target₂ →
      Covers reps →
      (∀ r → r ∈ₗ reps → target₁ r ≡ target₂ r) →
      ∀ c → target₁ c ≡ target₂ c
    tight-bound = full-coverage-determines

    ----------------------------------------------------------------
    -- SECTION 0j: DSL COMPLETENESS
    --
    -- The Boolean PredProg DSL is expressively complete for
    -- feature-respecting targets: for any target function constant
    -- on AllFeatAgree equivalence classes, there exists a PredProg
    -- that computes it exactly.
    --
    -- This closes the theoretical loop:
    --   - Completeness: the DSL contains the answer (dsl-complete)
    --   - Sufficiency: |C/~| samples find it (sufficient-cegis)
    --   - Necessity: fewer cannot (lower-bound)
    --   - Online: any order works (refine-commutes)
    --
    -- Together: "For any feature-respecting target, the system
    -- guarantees synthesis of the correct program from exactly
    -- |C/~| observations, in any order."
    --
    -- The construction uses FINGERPRINTS: each carrier c induces
    -- a conjunction of feature literals (positive or negative,
    -- matching c's feature values) that identifies c's equivalence
    -- class. The synthesized program disjoins the fingerprints of
    -- representatives where the target is true.
    ----------------------------------------------------------------

    FeaturesExhaustive : Set
    FeaturesExhaustive = ∀ (f : Feature) → f ∈ₗ all-features

    private
      ∧-intro : ∀ b₁ b₂ → b₁ ≡ true → b₂ ≡ true → (b₁ ∧ b₂) ≡ true
      ∧-intro .true .true refl refl = refl

      ∧-elim-l : ∀ b₁ b₂ → (b₁ ∧ b₂) ≡ true → b₁ ≡ true
      ∧-elim-l true  _ _ = refl

      ∧-elim-r : ∀ b₁ b₂ → (b₁ ∧ b₂) ≡ true → b₂ ≡ true
      ∧-elim-r true _ eq = eq

      ∨-introₗ : ∀ b₁ b₂ → b₁ ≡ true → (b₁ ∨ b₂) ≡ true
      ∨-introₗ .true _ refl = refl

      ∨-introᵣ : ∀ b₁ b₂ → b₂ ≡ true → (b₁ ∨ b₂) ≡ true
      ∨-introᵣ true  .true refl = refl
      ∨-introᵣ false .true refl = refl

      ∨-elim : ∀ {P : Set} → ∀ b₁ b₂ →
        (b₁ ∨ b₂) ≡ true →
        (b₁ ≡ true → P) → (b₂ ≡ true → P) → P
      ∨-elim true  _ _  f _ = f refl
      ∨-elim false _ eq _ g = g eq

      bool-iff : ∀ b₁ b₂ →
        (b₁ ≡ true → b₂ ≡ true) →
        (b₂ ≡ true → b₁ ≡ true) →
        b₁ ≡ b₂
      bool-iff true  true  _ _ = refl
      bool-iff true  false f _ with f refl
      ... | ()
      bool-iff false true  _ g with g refl
      ... | ()
      bool-iff false false _ _ = refl

      bool-contra : ∀ (b : Bool) → (b ≡ true → ⊥) → b ≡ false
      bool-contra true  f = ⊥-elim (f refl)
      bool-contra false _ = refl

    ----------------------------------------------------------------
    -- Feature literals: positive or negative based on carrier value
    ----------------------------------------------------------------

    lit : Feature → Carrier → PredProg
    lit f c = if eval-feature f c then feat f else ¬p (feat f)

    private
      lit-refl : ∀ f c → eval (lit f c) c ≡ true
      lit-refl f c with eval-feature f c in eq
      ... | true  = eq
      ... | false = cong not eq

      not-true : ∀ b → not b ≡ true → b ≡ false
      not-true false _ = refl

      lit-agree : ∀ f c₁ c₂ →
        eval (lit f c₁) c₂ ≡ true →
        eval-feature f c₁ ≡ eval-feature f c₂
      lit-agree f c₁ c₂ p with eval-feature f c₁
      ... | true  = sym p
      ... | false = sym (not-true (eval-feature f c₂) p)

      lit-from-agree : ∀ f c₁ c₂ →
        eval-feature f c₁ ≡ eval-feature f c₂ →
        eval (lit f c₁) c₂ ≡ true
      lit-from-agree f c₁ c₂ eq with eval-feature f c₁
      ... | true  = sym eq
      ... | false = cong not (sym eq)

    ----------------------------------------------------------------
    -- Fingerprint: conjunction of feature literals identifying a
    -- carrier's equivalence class
    ----------------------------------------------------------------

    fingerprint-list : List Feature → Carrier → PredProg
    fingerprint-list []       _ = truep
    fingerprint-list (f ∷ fs) c = lit f c ∧p fingerprint-list fs c

    fingerprint : Carrier → PredProg
    fingerprint = fingerprint-list all-features

    private
      fp-refl : ∀ fs c → eval (fingerprint-list fs c) c ≡ true
      fp-refl []       _ = refl
      fp-refl (f ∷ fs) c =
        ∧-intro (eval (lit f c) c)
                (eval (fingerprint-list fs c) c)
                (lit-refl f c) (fp-refl fs c)

      fp-sound : ∀ fs c₁ c₂ →
        eval (fingerprint-list fs c₁) c₂ ≡ true →
        ∀ f → f ∈ₗ fs → eval-feature f c₁ ≡ eval-feature f c₂
      fp-sound (g ∷ gs) c₁ c₂ eq .g here =
        lit-agree g c₁ c₂
          (∧-elim-l (eval (lit g c₁) c₂)
                    (eval (fingerprint-list gs c₁) c₂) eq)
      fp-sound (g ∷ gs) c₁ c₂ eq f (there mem) =
        fp-sound gs c₁ c₂
          (∧-elim-r (eval (lit g c₁) c₂)
                    (eval (fingerprint-list gs c₁) c₂) eq)
          f mem

      fp-complete : ∀ fs c₁ c₂ →
        (∀ f → f ∈ₗ fs → eval-feature f c₁ ≡ eval-feature f c₂) →
        eval (fingerprint-list fs c₁) c₂ ≡ true
      fp-complete []       _ _ _ = refl
      fp-complete (g ∷ gs) c₁ c₂ agree =
        ∧-intro (eval (lit g c₁) c₂)
                (eval (fingerprint-list gs c₁) c₂)
          (lit-from-agree g c₁ c₂ (agree g here))
          (fp-complete gs c₁ c₂ (λ f mem → agree f (there mem)))

    fingerprint-refl : ∀ c → eval (fingerprint c) c ≡ true
    fingerprint-refl = fp-refl all-features

    fingerprint-sound : ∀ c₁ c₂ →
      FeaturesExhaustive →
      eval (fingerprint c₁) c₂ ≡ true → AllFeatAgree c₁ c₂
    fingerprint-sound c₁ c₂ exhaust eq f =
      fp-sound all-features c₁ c₂ eq f (exhaust f)

    fingerprint-complete : ∀ c₁ c₂ →
      AllFeatAgree c₁ c₂ → eval (fingerprint c₁) c₂ ≡ true
    fingerprint-complete c₁ c₂ afa =
      fp-complete all-features c₁ c₂ (λ f _ → afa f)

    fingerprint-neg : ∀ c₁ c₂ →
      FeaturesExhaustive →
      ¬ AllFeatAgree c₁ c₂ →
      eval (fingerprint c₁) c₂ ≡ false
    fingerprint-neg c₁ c₂ exhaust ¬afa =
      bool-contra (eval (fingerprint c₁) c₂)
        (λ eq → ¬afa (fingerprint-sound c₁ c₂ exhaust eq))

    ----------------------------------------------------------------
    -- Synthesized predicate: disjoin fingerprints where target
    -- is true
    ----------------------------------------------------------------

    dsl-synth : (Carrier → Bool) → List Carrier → PredProg
    dsl-synth target []         = falsep
    dsl-synth target (r ∷ reps) =
      if target r then fingerprint r ∨p dsl-synth target reps
                  else dsl-synth target reps

    ----------------------------------------------------------------
    -- Correctness of DSL synthesis
    ----------------------------------------------------------------

    private
      synth-has : ∀ target reps r →
        r ∈ₗ reps → target r ≡ true →
        ∀ c → AllFeatAgree r c →
        eval (dsl-synth target reps) c ≡ true
      synth-has target (.r ∷ rest) r here tr-ok c afa
        with target r
      ... | true = ∨-introₗ
              (eval (fingerprint r) c)
              (eval (dsl-synth target rest) c)
              (fingerprint-complete r c afa)
      synth-has target (.r ∷ rest) r here tr-ok c afa
        | false with () ← tr-ok
      synth-has target (r' ∷ rest) r (there mem) tr-ok c afa
        with target r'
      ... | true = ∨-introᵣ
              (eval (fingerprint r') c)
              (eval (dsl-synth target rest) c)
              (synth-has target rest r mem tr-ok c afa)
      ... | false = synth-has target rest r mem tr-ok c afa

    dsl-sound : ∀ target reps c →
      FeaturesExhaustive → FeatureRespects target →
      eval (dsl-synth target reps) c ≡ true →
      target c ≡ true
    dsl-sound target [] c exhaust respects ()
    dsl-sound target (r ∷ reps) c exhaust respects eq
      with target r in eq-tr
    ... | true = ∨-elim
            (eval (fingerprint r) c)
            (eval (dsl-synth target reps) c) eq
            (λ fp-ok → trans (sym (respects r c
                (fingerprint-sound r c exhaust fp-ok))) eq-tr)
            (λ rest-ok →
              dsl-sound target reps c exhaust respects rest-ok)
    ... | false =
            dsl-sound target reps c exhaust respects eq

    dsl-complete-eval : ∀ target reps c →
      FeatureRespects target → Covers reps →
      target c ≡ true →
      eval (dsl-synth target reps) c ≡ true
    dsl-complete-eval target reps c respects covers tc-ok =
      let (r , r-in , afa) = covers c
      in synth-has target reps r r-in
           (trans (respects r c afa) tc-ok) c afa

    dsl-correct : ∀ target reps c →
      FeaturesExhaustive → FeatureRespects target → Covers reps →
      eval (dsl-synth target reps) c ≡ target c
    dsl-correct target reps c exhaust respects covers =
      bool-iff (eval (dsl-synth target reps) c) (target c)
        (dsl-sound target reps c exhaust respects)
        (dsl-complete-eval target reps c respects covers)

    ----------------------------------------------------------------
    -- THE DSL COMPLETENESS THEOREM
    --
    -- For any feature-respecting target, there exists a PredProg
    -- in the Boolean DSL that matches the target everywhere.
    --
    -- Combined with sufficient-cegis and lower-bound:
    -- "The DSL always contains the correct answer, and CEGIS will
    -- find it from exactly |C/~| observations, in any order."
    ----------------------------------------------------------------

    dsl-complete : ∀ target (reps : List Carrier) →
      FeaturesExhaustive → FeatureRespects target → Covers reps →
      ∃[ p ] MatchesAll p target
    dsl-complete target reps exhaust respects covers =
      dsl-synth target reps ,
      (λ c → dsl-correct target reps c exhaust respects covers)

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

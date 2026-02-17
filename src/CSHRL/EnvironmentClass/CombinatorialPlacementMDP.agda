{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Combinatorial Placement MDP Environment Class
--
-- Captures the essence of constraint satisfaction placement problems:
--   - N-Queens, Sudoku, Graph Coloring, etc.
--
-- Structure:
--   - States are: Ongoing (partial solution), Dead (constraint violated), 
--                 Solved (complete valid solution)
--   - Actions are placements
--   - Sparse rewards: 0 during placement, positive at Solved
--   - Dead and Solved are absorbing
--
-- Key insight for preservation:
--   - Dead states have value stream [0, 0, 0, ...]
--   - Solved states have value stream [R, R, R, ...] where R > 0
--   - Any path to Solved dominates any path to Dead
--   - The Finder's trace comparison correctly orders actions
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.CombinatorialPlacementMDP where

open import Data.List using (List; []; _∷_; map; foldr; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s; _<_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; ≤-total; ≰⇒>; n≤1+n; ≤⇒≤′;
         m≤m⊔n; m≤n⊔m; m≤n⇒m⊔n≡n; ⊔-identityʳ; ⊔-idem;
         ⊔-assoc; ⊔-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong; cong₂; trans)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- The Environment Class Module
------------------------------------------------------------------------

module CombinatorialPlacementMDP
  -- Placement configuration
  (Config : Set)           -- Type of partial/complete configurations
  (Action : Set)           -- Placement actions
  
  -- State classification
  (is-dead : Config → Bool)      -- Constraint violated?
  (is-solved : Config → Bool)    -- Complete valid solution?
  
  -- Transition
  (place : Config → Action → Config)  -- Apply placement
  
  -- Rewards
  (solved-reward : ℕ)     -- Reward for being in Solved state (e.g., 100)
  
  -- Finiteness
  (all-actions : List Action)
  (default-action : Action)
  
  -- Horizon (max placements needed)
  (horizon : ℕ)
  
  where

  ------------------------------------------------------------------------
  -- State Definition
  ------------------------------------------------------------------------
  
  data State : Set where
    Ongoing : Config → State
    Dead    : State
    Solved  : Config → State  -- Keep config for verification

  Reward : Set
  Reward = ℕ

  -- Propositional ordering on rewards
  _≤ᵣ_ : Reward → Reward → Set
  n ≤ᵣ m = n ≤ m

  -- Decidable ordering (returns proof or refutation)
  _≤?_ : (m n : Reward) → Dec (m ≤ᵣ n)
  zero  ≤? _     = yes z≤n
  suc _ ≤? zero  = no λ()
  suc m ≤? suc n with m ≤? n
  ... | yes p = yes (s≤s p)
  ... | no ¬p = no λ{ (s≤s p) → ¬p p }

  -- Boolean version for computational use in Finder
  _≤?ᵇ_ : Reward → Reward → Bool
  zero  ≤?ᵇ _     = true
  suc _ ≤?ᵇ zero  = false
  suc m ≤?ᵇ suc n = m ≤?ᵇ n

  -- Soundness: Boolean true implies propositional proof
  ≤?ᵇ-sound : ∀ r s → r ≤?ᵇ s ≡ true → r ≤ᵣ s
  ≤?ᵇ-sound zero    _       _  = z≤n
  ≤?ᵇ-sound (suc r) (suc s) p  = s≤s (≤?ᵇ-sound r s p)

  ------------------------------------------------------------------------
  -- Step Function
  ------------------------------------------------------------------------
  
  step : State → Action → State × Reward
  step Dead _ = (Dead , 0)
  step (Solved c) _ = (Solved c , solved-reward)  -- Absorbing with reward
  step (Ongoing c) a = 
    let c' = place c a
    in if is-dead c' then (Dead , 0)
       else if is-solved c' then (Solved c' , solved-reward)
       else (Ongoing c' , 0)

  ------------------------------------------------------------------------
  -- Import Core
  ------------------------------------------------------------------------
  
  open import CSHRL.Core
  open Core State Action Reward step _≤ᵣ_ _⊔_ 0 all-actions 
    hiding (preserves) public

  ------------------------------------------------------------------------
  -- Finder Algorithm (same structure as FiniteDeterministicMDP)
  ------------------------------------------------------------------------

  Trace : Set
  Trace = List Reward

  -- Lexicographic comparison (Boolean version for computation)
  _≤ₜᵇ_ : Trace → Trace → Bool
  []       ≤ₜᵇ []       = true
  []       ≤ₜᵇ (_ ∷ _)  = true
  (_ ∷ _)  ≤ₜᵇ []       = false
  (r₁ ∷ t₁) ≤ₜᵇ (r₂ ∷ t₂) = 
    if r₁ ≤?ᵇ r₂ then
      if r₂ ≤?ᵇ r₁ then (t₁ ≤ₜᵇ t₂)
      else true
    else false

  -- Lexicographic comparison (Propositional version for proofs)
  _≤ₜ_ : Trace → Trace → Set
  []       ≤ₜ []       = ⊤
  []       ≤ₜ (_ ∷ _)  = ⊤
  (_ ∷ _)  ≤ₜ []       = ⊥
  (r₁ ∷ t₁) ≤ₜ (r₂ ∷ t₂) = (r₁ ≤ᵣ r₂) × ((r₂ ≤ᵣ r₁) → t₁ ≤ₜ t₂)

  -- Short-circuit traces for absorbing states (avoids exponential blowup)
  dead-trace : ℕ → Trace
  dead-trace zero    = []
  dead-trace (suc k) = 0 ∷ dead-trace k

  solved-trace : ℕ → Trace
  solved-trace zero    = []
  solved-trace (suc k) = solved-reward ∷ solved-trace k

  mutual
    best-trace : State → ℕ → Trace
    best-trace _          zero    = []
    best-trace Dead       (suc k) = 0 ∷ dead-trace k
    best-trace (Solved _) (suc k) = solved-reward ∷ solved-trace k
    best-trace (Ongoing c) (suc k) = max-trace (map (λ a → trace-action (Ongoing c) a k) all-actions)

    trace-action : State → Action → ℕ → Trace
    trace-action s a k = 
      let (s' , r) = step s a
      in r ∷ best-trace s' k

    max-trace : List Trace → Trace
    max-trace []       = []
    max-trace (t ∷ ts) = max-helper t ts

    max-helper : Trace → List Trace → Trace
    max-helper current []       = current
    max-helper current (t ∷ ts) = 
      if current ≤ₜᵇ t 
      then max-helper t ts 
      else max-helper current ts

  insert : (Action × Trace) → List (Action × Trace) → List (Action × Trace)
  insert x [] = x ∷ []
  insert (a₁ , t₁) ((a₂ , t₂) ∷ xs) = 
    if t₂ ≤ₜᵇ t₁ 
    then (a₁ , t₁) ∷ (a₂ , t₂) ∷ xs
    else (a₂ , t₂) ∷ insert (a₁ , t₁) xs

  sort-scored : List (Action × Trace) → List (Action × Trace)
  sort-scored []       = []
  sort-scored (x ∷ xs) = insert x (sort-scored xs)

  find-ranking : State → ℕ → List Action
  find-ranking s k = 
    let scored = map (λ a → (a , trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  find-policy : State → ℕ → Action
  find-policy s k with find-ranking s k
  ... | []      = default-action
  ... | (a ∷ _) = a

  -- The ranking relation derived from finder (Boolean version for computation)
  _ranks_≤ᵇ_ : State → Action → Action → Bool
  s ranks a ≤ᵇ b = trace-action s a (suc horizon) ≤ₜᵇ trace-action s b (suc horizon)

  -- The ranking relation as a proposition (directly using propositional trace ordering)
  _ranks_≤_ : State → Action → Action → Set
  s ranks a ≤ b = trace-action s a (suc horizon) ≤ₜ trace-action s b (suc horizon)

  ------------------------------------------------------------------------
  -- Preservation Helpers
  ------------------------------------------------------------------------

  ≤ₛ-refl : ∀ (s : StreamR) → s ≤ₛ s
  head≤ (≤ₛ-refl s) = ≤-refl
  tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

  ------------------------------------------------------------------------
  -- Value Stream Analysis
  --
  -- Key property of placement problems:
  --   solve Dead n     = 0          (dead is absorbing with 0)
  --   solve (Solved c) n = solved-reward  (solved is absorbing with R)
  --   solve (Ongoing c) n = depends on reachable states
  --
  -- For preservation, we need:
  --   - value Dead = [0, 0, 0, ...]
  --   - value (Solved c) = [R, R, R, ...]
  --   - Any action leading to Solved ≥ action leading to Dead
  ------------------------------------------------------------------------

  -- iter-head for accessing stream elements
  iter-head : ℕ → StreamR → Reward
  iter-head zero s = head s
  iter-head (suc n) s = iter-head n (tail s)

  iter-head-tabulate : ∀ (f : ℕ → ℕ) n → iter-head n (tabulate f) ≡ f n
  iter-head-tabulate f zero = refl
  iter-head-tabulate f (suc n) = iter-head-tabulate (f ∘ suc) n

  iter-head-value : ∀ s n → iter-head n (value s) ≡ solve s n
  iter-head-value s n = iter-head-tabulate (solve s) n

  -- HeadGen pattern for building stream orderings
  HeadGen : StreamR → StreamR → Set
  HeadGen s₁ s₂ = ∀ n → iter-head n s₁ ≤ iter-head n s₂

  shift-gen : ∀ {s₁ s₂} → HeadGen s₁ s₂ → HeadGen (tail s₁) (tail s₂)
  shift-gen gen n = gen (suc n)

  build-≤ₛ : ∀ (s₁ s₂ : StreamR) → HeadGen s₁ s₂ → s₁ ≤ₛ s₂
  head≤ (build-≤ₛ s₁ s₂ gen) = gen 0
  tail≤ (build-≤ₛ s₁ s₂ gen) = build-≤ₛ (tail s₁) (tail s₂) (shift-gen gen)

  ------------------------------------------------------------------------
  -- Absorbing State Properties (provided by instance)
  --
  -- These depend on the specific action list, so instances must provide them.
  ------------------------------------------------------------------------

  module WithAbsorbingLemmas
    -- solve Dead n = 0 for all n (Dead is absorbing with 0 reward)
    (solve-Dead-is-0 : ∀ n → solve Dead n ≡ 0)
    -- solve (Solved c) n = solved-reward for all n
    (solve-Solved-is-R : ∀ c n → solve (Solved c) n ≡ solved-reward)
    where

    -- iter-head at Dead is always 0
    iter-head-Dead-0 : ∀ n → iter-head n (value Dead) ≡ 0
    iter-head-Dead-0 n = 
      subst (λ x → x ≡ 0) (sym (iter-head-value Dead n)) (solve-Dead-is-0 n)

    -- iter-head at Solved is always solved-reward
    iter-head-Solved-R : ∀ c n → iter-head n (value (Solved c)) ≡ solved-reward
    iter-head-Solved-R c n = 
      subst (λ x → x ≡ solved-reward) (sym (iter-head-value (Solved c) n)) (solve-Solved-is-R c n)

    ----------------------------------------------------------------------
    -- Ordering: Dead ≤ anything, anything ≤ Solved
    ----------------------------------------------------------------------

    -- value Dead ≤ₛ value s for any s
    gen-Dead-≤-any : ∀ s → HeadGen (value Dead) (value s)
    gen-Dead-≤-any s n = 
      subst (λ x → x ≤ iter-head n (value s)) 
            (sym (iter-head-Dead-0 n)) 
            z≤n

    Dead-≤ₛ-any : ∀ s → value Dead ≤ₛ value s
    Dead-≤ₛ-any s = build-≤ₛ (value Dead) (value s) (gen-Dead-≤-any s)

  ----------------------------------------------------------------------
  -- Direct Preservation Module
  ----------------------------------------------------------------------

  module WithDirectPreservation
    (preserves-direct : ∀ a b s → 
                        s ranks a ≤ b → 
                        action-value s a ≤ₛ action-value s b)
    where

    instance
      PlacementMDPHomo : CoindHomo
      PlacementMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves-direct
        }

  ----------------------------------------------------------------------
  -- Binary Structure: solve is always 0 or solved-reward
  --
  -- These lemmas depend only on the absorbing-state properties and
  -- 0 < solved-reward. They are separated so that domain-specific
  -- proofs (e.g. solve-horizon-sufficient) can use them.
  ----------------------------------------------------------------------

  module WithBinaryStructure
    (solve-Dead-is-0    : ∀ n → solve Dead n ≡ 0)
    (solve-Solved-is-R  : ∀ c n → solve (Solved c) n ≡ solved-reward)
    (0<R                : 0 < solved-reward)
    where

    -- 0 ≢ solved-reward (from 0 < R)
    0≢R : 0 ≡ solved-reward → ⊥
    0≢R p = lem (subst (0 <_) (sym p) 0<R)
      where lem : 0 < 0 → ⊥
            lem ()

    -- For binary values: x ≤ R
    binary-≤R : ∀ x → (x ≡ 0 ⊎ x ≡ solved-reward) → x ≤ solved-reward
    binary-≤R .0             (inj₁ refl) = z≤n
    binary-≤R .solved-reward (inj₂ refl) = ≤-refl

    -- R ⊔ (binary n) ≡ R
    R-⊔-binary : ∀ n → (n ≡ 0 ⊎ n ≡ solved-reward) →
                  solved-reward ⊔ n ≡ solved-reward
    R-⊔-binary .0             (inj₁ refl) = ⊔-identityʳ solved-reward
    R-⊔-binary .solved-reward (inj₂ refl) = ⊔-idem solved-reward

    -- (binary m) ⊔ R ≡ R
    ⊔-R-binary : ∀ m → (m ≡ 0 ⊎ m ≡ solved-reward) →
                  m ⊔ solved-reward ≡ solved-reward
    ⊔-R-binary .0             (inj₁ refl) = refl
    ⊔-R-binary .solved-reward (inj₂ refl) = ⊔-idem solved-reward

    --------------------------------------------------------------------
    -- Step reward is binary
    --------------------------------------------------------------------

    step-reward-binary : ∀ s a →
      proj₂ (step s a) ≡ 0 ⊎ proj₂ (step s a) ≡ solved-reward
    step-reward-binary Dead       _ = inj₁ refl
    step-reward-binary (Solved c) _ = inj₂ refl
    step-reward-binary (Ongoing c) a with is-dead (place c a)
    ... | true  = inj₁ refl
    ... | false with is-solved (place c a)
    ...   | true  = inj₂ refl
    ...   | false = inj₁ refl

    --------------------------------------------------------------------
    -- solve is always 0 or R (binary)
    --------------------------------------------------------------------

    max-list-map-binary : ∀ {A : Set} (f : A → ℕ) (xs : List A) →
      (∀ x → f x ≡ 0 ⊎ f x ≡ solved-reward) →
      max-list (map f xs) ≡ 0 ⊎ max-list (map f xs) ≡ solved-reward
    max-list-map-binary f []       _ = inj₁ refl
    max-list-map-binary f (x ∷ xs) h
      with h x | max-list-map-binary f xs h
    ... | inj₁ p | inj₁ q =
      inj₁ (trans (cong (_⊔ max-list (map f xs)) p) q)
    ... | inj₁ p | inj₂ q =
      inj₂ (trans (cong (_⊔ max-list (map f xs)) p) q)
    ... | inj₂ p | rest-bin =
      inj₂ (trans (cong (_⊔ max-list (map f xs)) p)
                  (R-⊔-binary (max-list (map f xs)) rest-bin))

    solve-binary : ∀ s n →
      solve s n ≡ 0 ⊎ solve s n ≡ solved-reward
    solve-binary s zero    =
      max-list-map-binary (λ a → proj₂ (step s a)) all-actions
                          (step-reward-binary s)
    solve-binary s (suc n) =
      max-list-map-binary (λ a → solve (proj₁ (step s a)) n) all-actions
                          (λ a → solve-binary (proj₁ (step s a)) n)

    --------------------------------------------------------------------
    -- solve is monotone: solve s n ≡ R → solve s (suc n) ≡ R
    --------------------------------------------------------------------

    -- If step gives R, successor's solve 0 is R
    step-R-to-solve-R : ∀ c a →
      proj₂ (step (Ongoing c) a) ≡ solved-reward →
      solve (proj₁ (step (Ongoing c) a)) 0 ≡ solved-reward
    step-R-to-solve-R c a p with is-dead (place c a)
    ... | true  = ⊥-elim (0≢R p)
    ... | false with is-solved (place c a)
    ...   | true  = solve-Solved-is-R (place c a) 0
    ...   | false = ⊥-elim (0≢R p)

    -- Propagation: if f(x) = R implies g(x) = R, then max f = R implies max g = R
    max-list-R-propagate : ∀ {A : Set} (f g : A → ℕ) (xs : List A) →
      (∀ x → f x ≡ 0 ⊎ f x ≡ solved-reward) →
      (∀ x → f x ≡ solved-reward → g x ≡ solved-reward) →
      (∀ x → g x ≡ 0 ⊎ g x ≡ solved-reward) →
      max-list (map f xs) ≡ solved-reward →
      max-list (map g xs) ≡ solved-reward
    max-list-R-propagate _ _ []       _    _    _    p = ⊥-elim (0≢R p)
    max-list-R-propagate f g (x ∷ xs) fbin prop gbin p
      with fbin x
    ... | inj₂ fx≡R =
      trans (cong (_⊔ max-list (map g xs)) (prop x fx≡R))
            (R-⊔-binary (max-list (map g xs))
                        (max-list-map-binary g xs gbin))
    ... | inj₁ fx≡0 =
      let rest-f≡R : max-list (map f xs) ≡ solved-reward
          rest-f≡R = subst (λ z → z ⊔ max-list (map f xs) ≡ solved-reward)
                           fx≡0 p
          rest-g≡R = max-list-R-propagate f g xs fbin prop gbin rest-f≡R
      in trans (cong (g x ⊔_) rest-g≡R) (⊔-R-binary (g x) (gbin x))

    solve-mono : ∀ s n →
      solve s n ≡ solved-reward → solve s (suc n) ≡ solved-reward
    solve-mono Dead       n p = ⊥-elim (0≢R (trans (sym (solve-Dead-is-0 n)) p))
    solve-mono (Solved c) n _ = solve-Solved-is-R c (suc n)
    solve-mono (Ongoing c) zero p =
      max-list-R-propagate
        (λ a → proj₂ (step (Ongoing c) a))
        (λ a → solve (proj₁ (step (Ongoing c) a)) 0)
        all-actions
        (step-reward-binary (Ongoing c))
        (step-R-to-solve-R c)
        (λ a → solve-binary (proj₁ (step (Ongoing c) a)) 0)
        p
    solve-mono (Ongoing c) (suc n) p =
      max-list-R-propagate
        (λ a → solve (proj₁ (step (Ongoing c) a)) n)
        (λ a → solve (proj₁ (step (Ongoing c) a)) (suc n))
        all-actions
        (λ a → solve-binary (proj₁ (step (Ongoing c) a)) n)
        (λ a → solve-mono (proj₁ (step (Ongoing c) a)) n)
        (λ a → solve-binary (proj₁ (step (Ongoing c) a)) (suc n))
        p

    -- Any solve value is ≤ R
    solve-any-≤R : ∀ s n → solve s n ≤ solved-reward
    solve-any-≤R s n = binary-≤R (solve s n) (solve-binary s n)

    -- Backward: if solve = 0, all earlier depths are 0
    solve-0-backward : ∀ s n →
      solve s (suc n) ≡ 0 → solve s n ≡ 0
    solve-0-backward s n p with solve-binary s n
    ... | inj₁ eq0 = eq0
    ... | inj₂ eqR = ⊥-elim (0≢R (trans (sym p) (solve-mono s n eqR)))

    -- Iterated backward via ≤′: if solve s m = 0, then solve s n = 0 for n ≤′ m
    private
      solve-0-bwd : ∀ s m n → n ≤′ m →
        solve s m ≡ 0 → solve s n ≡ 0
      solve-0-bwd s m .m      ≤′-refl      p = p
      solve-0-bwd s (suc m) n (≤′-step le) p =
        solve-0-bwd s m n le (solve-0-backward s m p)

    -- Iterated backward: if solve s m = 0, then solve s n = 0 for all n ≤ m
    solve-0-backward* : ∀ s m n → n ≤ m →
      solve s m ≡ 0 → solve s n ≡ 0
    solve-0-backward* s m n n≤m = solve-0-bwd s m n (≤⇒≤′ n≤m)

    -- max-list of all-zero list is 0
    max-list-all-0 : ∀ {A : Set} (f : A → ℕ) (xs : List A) →
      (∀ x → f x ≡ 0) →
      max-list (map f xs) ≡ 0
    max-list-all-0 f []       _ = refl
    max-list-all-0 f (x ∷ xs) h =
      trans (cong (_⊔ max-list (map f xs)) (h x))
            (max-list-all-0 f xs h)

    -- Witness that some element of a list satisfies a predicate
    data AnyElem {A : Set} (P : A → Set) : List A → Set where
      here  : ∀ {x xs} → P x → AnyElem P (x ∷ xs)
      there : ∀ {x xs} → AnyElem P xs → AnyElem P (x ∷ xs)

    -- If any element's image is R and all images are binary, max-list is R
    -- Key: matches on binary PROOFS (not stuck values), so always terminates.
    any-R⇒max-R : ∀ {A : Set} (f : A → ℕ) (xs : List A) →
      (∀ x → f x ≡ 0 ⊎ f x ≡ solved-reward) →
      AnyElem (λ x → f x ≡ solved-reward) xs →
      max-list (map f xs) ≡ solved-reward
    any-R⇒max-R f (x ∷ xs) fbin (here fx≡R) =
      trans (cong (_⊔ max-list (map f xs)) fx≡R)
            (R-⊔-binary (max-list (map f xs)) (max-list-map-binary f xs fbin))
    any-R⇒max-R f (x ∷ xs) fbin (there rest) =
      trans (cong (f x ⊔_) (any-R⇒max-R f xs fbin rest))
            (⊔-R-binary (f x) (fbin x))

  ----------------------------------------------------------------------
  -- Trace Bridge: The Finder's ranking forms a CoindHomo
  --
  -- Key insight: in CombinatorialPlacementMDP, solve is always 0 or
  -- solved-reward (binary). This makes best-trace elements coincide
  -- with solve values, and lex trace ordering implies pointwise
  -- solve ordering.
  ----------------------------------------------------------------------

  module WithTraceBridge
    (solve-Dead-is-0    : ∀ n → solve Dead n ≡ 0)
    (solve-Solved-is-R  : ∀ c n → solve (Solved c) n ≡ solved-reward)
    (0<R                : 0 < solved-reward)
    (solve-horizon-suf  : ∀ c → solve (Ongoing c) horizon ≡ 0 →
                          ∀ n → solve (Ongoing c) n ≡ 0)
    where

    open WithAbsorbingLemmas solve-Dead-is-0 solve-Solved-is-R
    open WithBinaryStructure solve-Dead-is-0 solve-Solved-is-R 0<R public

    --------------------------------------------------------------------
    -- Basic helpers
    --------------------------------------------------------------------

    -- Safe list indexing (returns 0 for out-of-bounds)
    nth : ℕ → List Reward → Reward
    nth _       []       = 0
    nth zero    (x ∷ _)  = x
    nth (suc i) (_ ∷ xs) = nth i xs

    -- m ⊔ 0 ≡ m
    ⊔-0 : ∀ m → m ⊔ 0 ≡ m
    ⊔-0 = ⊔-identityʳ

    -- Boolean comparison: reflexivity
    ≤?ᵇ-refl : ∀ n → n ≤?ᵇ n ≡ true
    ≤?ᵇ-refl zero    = refl
    ≤?ᵇ-refl (suc n) = ≤?ᵇ-refl n

    -- Boolean comparison: completeness (false ⇒ reverse ordering)
    ≤?ᵇ-complete : ∀ m n → m ≤?ᵇ n ≡ false → n ≤ m
    ≤?ᵇ-complete zero    _       ()
    ≤?ᵇ-complete (suc m) zero    _  = z≤n
    ≤?ᵇ-complete (suc m) (suc n) p  = s≤s (≤?ᵇ-complete m n p)

    --------------------------------------------------------------------
    -- Trace ordering infrastructure
    --------------------------------------------------------------------

    -- Completeness of ≤?ᵇ: m ≤ n → m ≤?ᵇ n ≡ true
    ≤?ᵇ-complete₂ : ∀ m n → m ≤ n → m ≤?ᵇ n ≡ true
    ≤?ᵇ-complete₂ zero    _       _       = refl
    ≤?ᵇ-complete₂ (suc m) (suc n) (s≤s p) = ≤?ᵇ-complete₂ m n p

    -- true ≢ false
    true≢false : true ≡ false → ⊥
    true≢false ()

    -- Soundness: ≤ₜᵇ true → ≤ₜ
    ≤ₜᵇ-sound : ∀ t₁ t₂ → t₁ ≤ₜᵇ t₂ ≡ true → t₁ ≤ₜ t₂
    ≤ₜᵇ-sound []       []       _ = tt
    ≤ₜᵇ-sound []       (_ ∷ _)  _ = tt
    ≤ₜᵇ-sound (r₁ ∷ t₁) (r₂ ∷ t₂) = go (r₁ ≤?ᵇ r₂) (r₂ ≤?ᵇ r₁) refl refl
      where
        go : ∀ b₁ b₂ → r₁ ≤?ᵇ r₂ ≡ b₁ → r₂ ≤?ᵇ r₁ ≡ b₂ →
          (if b₁ then (if b₂ then t₁ ≤ₜᵇ t₂ else true) else false) ≡ true →
          (r₁ ≤ r₂) × ((r₂ ≤ r₁) → t₁ ≤ₜ t₂)
        go true  true  eq₁ _   p = ≤?ᵇ-sound r₁ r₂ eq₁ , λ _ → ≤ₜᵇ-sound t₁ t₂ p
        go true  false eq₁ eq₂ _ = ≤?ᵇ-sound r₁ r₂ eq₁ , λ r₂≤r₁ →
          ⊥-elim (true≢false (trans (sym (≤?ᵇ-complete₂ r₂ r₁ r₂≤r₁)) eq₂))
        go false _     _   _   ()

    -- Totality: ≤ₜᵇ false → reverse ≤ₜ
    ≤ₜᵇ-flip : ∀ t₁ t₂ → t₁ ≤ₜᵇ t₂ ≡ false → t₂ ≤ₜ t₁
    ≤ₜᵇ-flip []       []       ()
    ≤ₜᵇ-flip []       (_ ∷ _)  ()
    ≤ₜᵇ-flip (_ ∷ _)  []       _ = tt
    ≤ₜᵇ-flip (r₁ ∷ t₁) (r₂ ∷ t₂) = go (r₁ ≤?ᵇ r₂) (r₂ ≤?ᵇ r₁) refl refl
      where
        go : ∀ b₁ b₂ → r₁ ≤?ᵇ r₂ ≡ b₁ → r₂ ≤?ᵇ r₁ ≡ b₂ →
          (if b₁ then (if b₂ then t₁ ≤ₜᵇ t₂ else true) else false) ≡ false →
          (r₂ ≤ r₁) × ((r₁ ≤ r₂) → t₂ ≤ₜ t₁)
        go true  true  _   eq₂ p = ≤?ᵇ-sound r₂ r₁ eq₂ , λ _ → ≤ₜᵇ-flip t₁ t₂ p
        go true  false _   _   ()
        go false _     eq₁ _   _ = ≤?ᵇ-complete r₁ r₂ eq₁ , λ r₁≤r₂ →
          ⊥-elim (true≢false (trans (sym (≤?ᵇ-complete₂ r₁ r₂ r₁≤r₂)) eq₁))

    -- Lex reflexivity
    ≤ₜ-refl : ∀ t → t ≤ₜ t
    ≤ₜ-refl []       = tt
    ≤ₜ-refl (r ∷ t)  = ≤-refl , λ _ → ≤ₜ-refl t

    -- When heads are equal, lex comparison reduces to tail comparison
    ≤ₜᵇ-cons-eq : ∀ v t₁ t₂ → (v ∷ t₁) ≤ₜᵇ (v ∷ t₂) ≡ t₁ ≤ₜᵇ t₂
    ≤ₜᵇ-cons-eq v t₁ t₂ rewrite ≤?ᵇ-refl v = refl

    --------------------------------------------------------------------
    -- max-helper structural lemma: same-head decomposition
    --------------------------------------------------------------------

    max-helper-same-head : ∀ v t ts →
      max-helper (v ∷ t) (map (v ∷_) ts) ≡ v ∷ max-helper t ts
    max-helper-same-head v t [] = refl
    max-helper-same-head v t (u ∷ us)
      rewrite ≤ₜᵇ-cons-eq v t u with t ≤ₜᵇ u
    ... | true  = max-helper-same-head v u us
    ... | false = max-helper-same-head v t us

    -- All elements of a trace list satisfy P
    AllP : (Trace → Set) → List Trace → Set
    AllP P []       = ⊤
    AllP P (t ∷ ts) = P t × AllP P ts

    -- max-helper preserves any property that holds for all inputs
    max-helper-preserves : ∀ (P : Trace → Set) t ts →
      P t → AllP P ts → P (max-helper t ts)
    max-helper-preserves P t []       pt _          = pt
    max-helper-preserves P t (u ∷ us) pt (pu , pus) with t ≤ₜᵇ u
    ... | true  = max-helper-preserves P u us pu pus
    ... | false = max-helper-preserves P t us pt pus


    --------------------------------------------------------------------
    -- Binary monotone R-propagation through sequences
    --------------------------------------------------------------------

    -- If head is R and trace is monotone (bounded), all elements up to j are R
    -- Mono bound uses suc i ≤ j (i.e., i < j) so for j=0, no mono needed.
    all-R-from-head : ∀ (t : Trace) j →
      nth 0 t ≡ solved-reward →
      (∀ i → suc i ≤ j → nth i t ≡ solved-reward → nth (suc i) t ≡ solved-reward) →
      nth j t ≡ solved-reward
    all-R-from-head t zero    h _    = h
    all-R-from-head t (suc j) h mono =
      let ih = all-R-from-head t j h (λ i si≤j → mono i (≤-trans si≤j (n≤1+n j)))
      in mono j ≤-refl ih

    --------------------------------------------------------------------
    -- Lex ordering of binary monotone traces → pointwise ordering
    -- (bounded version: bin/mono only needed up to index j)
    --------------------------------------------------------------------

    lex-ge-pointwise : ∀ (t₁ t₂ : Trace) j →
      (∀ i → i ≤ j → nth i t₁ ≡ 0 ⊎ nth i t₁ ≡ solved-reward) →
      (∀ i → i ≤ j → nth i t₂ ≡ 0 ⊎ nth i t₂ ≡ solved-reward) →
      (∀ i → suc i ≤ j → nth i t₁ ≡ solved-reward → nth (suc i) t₁ ≡ solved-reward) →
      (∀ i → suc i ≤ j → nth i t₂ ≡ solved-reward → nth (suc i) t₂ ≡ solved-reward) →
      t₂ ≤ₜ t₁ →
      nth j t₂ ≤ nth j t₁
    lex-ge-pointwise []       []       j _    _    _     _     _           = ≤-refl
    lex-ge-pointwise (_ ∷ _)  []       j _    _    _     _     _           = z≤n
    lex-ge-pointwise []       (_ ∷ _)  j _    _    _     _     ()
    lex-ge-pointwise (h₁ ∷ t₁) (h₂ ∷ t₂) zero _ _ _ _ (h₂≤h₁ , _)       = h₂≤h₁
    lex-ge-pointwise (h₁ ∷ t₁) (h₂ ∷ t₂) (suc j) bin₁ bin₂ mono₁ mono₂ (h₂≤h₁ , rest)
      with h₁ ≤? h₂
    ... | yes h₁≤h₂ =
      lex-ge-pointwise t₁ t₂ j
        (λ i i≤j → bin₁ (suc i) (s≤s i≤j))
        (λ i i≤j → bin₂ (suc i) (s≤s i≤j))
        (λ i si≤j → mono₁ (suc i) (s≤s si≤j))
        (λ i si≤j → mono₂ (suc i) (s≤s si≤j))
        (rest h₁≤h₂)
    ... | no ¬h₁≤h₂ with bin₁ 0 z≤n
    ...   | inj₁ h₁≡0 = ⊥-elim (¬h₁≤h₂ (subst (_≤ h₂) (sym h₁≡0) z≤n))
    ...   | inj₂ h₁≡R =
      subst (nth j t₂ ≤_)
            (sym (all-R-from-head t₁ j
                   (mono₁ 0 (s≤s z≤n) h₁≡R)
                   (λ i si≤j → mono₁ (suc i) (s≤s si≤j))))
            (binary-≤R (nth j t₂) (bin₂ (suc j) ≤-refl))

    --------------------------------------------------------------------
    -- Pointwise max property for max-helper on binary monotone traces
    --
    -- For binary monotone traces, the lex-max trace achieves the
    -- pointwise maximum at every position.
    -- (bounded version: bin/mono only needed up to index j)
    --------------------------------------------------------------------

    -- n ≤ m ⊔ n (second argument of ⊔)
    ⊔-ge-right : ∀ m n → n ≤ m ⊔ n
    ⊔-ge-right zero    n       = ≤-refl
    ⊔-ge-right (suc m) zero    = z≤n
    ⊔-ge-right (suc m) (suc n) = s≤s (⊔-ge-right m n)

    -- Helper: base ≤ foldr _⊔_ base xs
    foldr-⊔-ge-base : ∀ (base : ℕ) (xs : List ℕ) →
      base ≤ foldr _⊔_ base xs
    foldr-⊔-ge-base base []       = ≤-refl
    foldr-⊔-ge-base base (x ∷ xs) =
      ≤-trans (foldr-⊔-ge-base base xs) (⊔-ge-right x (foldr _⊔_ base xs))

    -- Binary monotone witness for all traces in a list (bounded)
    -- Mono uses suc i ≤ bound (i.e., i < bound) to avoid boundary issues.
    BinMonoAll : ℕ → List Trace → Set
    BinMonoAll _     []       = ⊤
    BinMonoAll bound (u ∷ us) =
      ((∀ i → i ≤ bound → nth i u ≡ 0 ⊎ nth i u ≡ solved-reward)
       × (∀ i → suc i ≤ bound → nth i u ≡ solved-reward → nth (suc i) u ≡ solved-reward))
      × BinMonoAll bound us

    -- m ≤ m ⊔ n (left argument of ⊔)
    ⊔-ge-left : ∀ m n → m ≤ m ⊔ n
    ⊔-ge-left zero    _       = z≤n
    ⊔-ge-left (suc m) zero    = ≤-refl
    ⊔-ge-left (suc m) (suc n) = s≤s (⊔-ge-left m n)

    -- If m ≤ n, then m ⊔ (n ⊔ p) ≡ n ⊔ p
    ⊔-absorb-left : ∀ m n p → m ≤ n → m ⊔ (n ⊔ p) ≡ n ⊔ p
    ⊔-absorb-left m n p m≤n =
      trans (sym (⊔-assoc m n p))
            (cong (_⊔ p) (m≤n⇒m⊔n≡n m≤n))

    -- If n ≤ m, then m ⊔ (n ⊔ p) ≡ m ⊔ p
    ⊔-absorb-right : ∀ m n p → n ≤ m → m ⊔ (n ⊔ p) ≡ m ⊔ p
    ⊔-absorb-right m n p n≤m =
      trans (sym (⊔-assoc m n p))
            (cong (_⊔ p) (trans (⊔-comm m n) (m≤n⇒m⊔n≡n n≤m)))

    -- The key property: nth j of max-helper = nth j t ⊔ max-list of tails
    -- For binary monotone traces, the lex-max achieves pointwise max.
    -- (bounded version)
    max-helper-nth-max : ∀ t ts j →
      (∀ i → i ≤ j → nth i t ≡ 0 ⊎ nth i t ≡ solved-reward) →
      (∀ i → suc i ≤ j → nth i t ≡ solved-reward → nth (suc i) t ≡ solved-reward) →
      BinMonoAll j ts →
      nth j (max-helper t ts) ≡
        nth j t ⊔ max-list (map (λ u → nth j u) ts)
    max-helper-nth-max t [] j _ _ _ = sym (⊔-identityʳ (nth j t))
    max-helper-nth-max t (u ∷ us) j tbin tmono ((ubin , umono) , usall)
      with t ≤ₜᵇ u in eq
    ... | true =
      let t≤ₜu   = ≤ₜᵇ-sound t u eq
          nj-t≤u = lex-ge-pointwise u t j ubin tbin umono tmono t≤ₜu
          ih      = max-helper-nth-max u us j ubin umono usall
          Y       = max-list (map (λ w → nth j w) us)
      in trans ih (sym (⊔-absorb-left (nth j t) (nth j u) Y nj-t≤u))
    ... | false =
      let u≤ₜt   = ≤ₜᵇ-flip t u eq
          nj-u≤t = lex-ge-pointwise t u j tbin ubin tmono umono u≤ₜt
          ih      = max-helper-nth-max t us j tbin tmono usall
          Y       = max-list (map (λ w → nth j w) us)
      in trans ih (sym (⊔-absorb-right (nth j t) (nth j u) Y nj-u≤t))

    --------------------------------------------------------------------
    -- best-trace-is-solve: the KEY LEMMA
    --
    -- For binary monotone solve, the i-th element of best-trace s (suc k)
    -- equals solve s i, for i ≤ k.
    --------------------------------------------------------------------

    -- Helper: dead/solved trace elements
    dead-trace-nth : ∀ k i → nth i (dead-trace k) ≡ 0
    dead-trace-nth zero    _       = refl
    dead-trace-nth (suc k) zero    = refl
    dead-trace-nth (suc k) (suc i) = dead-trace-nth k i

    solved-trace-nth : ∀ k i → suc i ≤ k → nth i (solved-trace k) ≡ solved-reward
    solved-trace-nth (suc k) zero    _       = refl
    solved-trace-nth (suc k) (suc i) (s≤s p) = solved-trace-nth k i p

    -- Build BinMonoAll from uniform binary/mono witnesses (bounded)
    build-BMA : ∀ {A : Set} (f : A → Trace) (xs : List A) (bound : ℕ) →
      (∀ x i → i ≤ bound → nth i (f x) ≡ 0 ⊎ nth i (f x) ≡ solved-reward) →
      (∀ x i → suc i ≤ bound → nth i (f x) ≡ solved-reward → nth (suc i) (f x) ≡ solved-reward) →
      BinMonoAll bound (map f xs)
    build-BMA f []       _     _    _    = tt
    build-BMA f (x ∷ xs) bound hbin hmono =
      ((hbin x) , (hmono x)) , build-BMA f xs bound hbin hmono

    -- Helper for nth-ta proofs: max-list respects extensional equality
    max-list-ext : ∀ {A : Set} (f g : A → ℕ) (xs : List A) →
      (∀ x → f x ≡ g x) →
      max-list (map f xs) ≡ max-list (map g xs)
    max-list-ext f g [] _ = refl
    max-list-ext f g (x ∷ xs) h = cong₂ _⊔_ (h x) (max-list-ext f g xs h)

    -- Helper for double-map: max-list (map f (map g xs)) ≡ max-list (map h xs)
    map-double-ext : ∀ {A B : Set} (f : B → ℕ) (g : A → B) (h : A → ℕ)
      (xs : List A) →
      (∀ x → f (g x) ≡ h x) →
      max-list (map f (map g xs)) ≡ max-list (map h xs)
    map-double-ext f g h [] _ = refl
    map-double-ext f g h (x ∷ xs) eq = cong₂ _⊔_ (eq x) (map-double-ext f g h xs eq)

    -- THE KEY LEMMA (with bounds)
    best-trace-is-solve : ∀ s k i → i ≤ k →
      nth i (best-trace s (suc k)) ≡ solve s i

    -- For trace-action: nth i equals r_a (at 0) or solve s'_a (i-1) (at suc)
    ta-nth-0 : ∀ s a k → nth 0 (trace-action s a k) ≡ proj₂ (step s a)
    ta-nth-0 s a k with step s a
    ... | (s' , r) = refl

    ta-nth-suc : ∀ s a k j → j ≤ k →
      nth (suc j) (trace-action s a (suc k)) ≡ solve (proj₁ (step s a)) j
    ta-nth-suc s a k j j≤k with step s a
    ... | (s' , r) = best-trace-is-solve s' k j j≤k

    -- General version: if reward is R, successor's solve 0 is R
    step-R-to-solve-R-gen : ∀ s a →
      proj₂ (step s a) ≡ solved-reward →
      solve (proj₁ (step s a)) 0 ≡ solved-reward
    step-R-to-solve-R-gen Dead       _ p = ⊥-elim (0≢R p)
    step-R-to-solve-R-gen (Solved c) _ _ = solve-Solved-is-R c 0
    step-R-to-solve-R-gen (Ongoing c) a p = step-R-to-solve-R c a p

    -- Binary property of trace-action elements (bounded: i ≤ k)
    ta-bin : ∀ s a k i → i ≤ k →
      nth i (trace-action s a k) ≡ 0 ⊎
      nth i (trace-action s a k) ≡ solved-reward
    ta-bin s a k       zero    _          = step-reward-binary s a
    ta-bin s a (suc k') (suc j) (s≤s j≤k') with solve-binary (proj₁ (step s a)) j
    ... | inj₁ p = inj₁ (trans (best-trace-is-solve (proj₁ (step s a)) k' j j≤k') p)
    ... | inj₂ p = inj₂ (trans (best-trace-is-solve (proj₁ (step s a)) k' j j≤k') p)

    -- Mono property of trace-action elements (bounded: suc i ≤ k)
    ta-mono : ∀ s a k i → suc i ≤ k →
      nth i (trace-action s a k) ≡ solved-reward →
      nth (suc i) (trace-action s a k) ≡ solved-reward
    ta-mono s a (suc k') zero (s≤s _) p =
      trans (best-trace-is-solve (proj₁ (step s a)) k' 0 z≤n)
            (step-R-to-solve-R-gen s a p)
    ta-mono s a (suc k') (suc j) (s≤s sj≤k') p =
      let s' = proj₁ (step s a)
          j≤k' = ≤-trans (n≤1+n j) sj≤k'
      in trans (best-trace-is-solve s' k' (suc j) sj≤k')
               (solve-mono s' j
                 (trans (sym (best-trace-is-solve s' k' j j≤k')) p))

    -- max-trace-nth: nth of max-trace equals max-list of element-wise nth.
    -- Works for any list (empty or non-empty) without case-splitting
    -- on module parameters, avoiding Agda 2.8.0's 'with' restriction.
    max-trace-nth : ∀ (ts : List Trace) i →
      BinMonoAll i ts →
      nth i (max-trace ts) ≡ max-list (map (λ t → nth i t) ts)
    max-trace-nth [] i _ = refl
    max-trace-nth (t₀ ∷ ts) i ((t₀bin , t₀mono) , ts-bma) =
      max-helper-nth-max t₀ ts i t₀bin t₀mono ts-bma

    -- Dead case
    best-trace-is-solve Dead k i _ =
      trans (lem k i) (sym (solve-Dead-is-0 i))
      where
        lem : ∀ k i → nth i (0 ∷ dead-trace k) ≡ 0
        lem k zero    = refl
        lem k (suc i) = dead-trace-nth k i

    -- Solved case
    best-trace-is-solve (Solved c) k i i≤k =
      trans (lem k i i≤k) (sym (solve-Solved-is-R c i))
      where
        lem : ∀ k i → i ≤ k → nth i (solved-reward ∷ solved-trace k) ≡ solved-reward
        lem k zero    _     = refl
        lem k (suc i) si≤k  = solved-trace-nth k i si≤k

    -- Ongoing case: uses max-trace-nth + map-double-ext
    best-trace-is-solve (Ongoing c) k i i≤k =
      ongoing-proof c k i i≤k
      where
        -- step2: bridge from max-list of trace-action nth values to solve
        -- Uses ta-nth-0 (for i=0) or ta-nth-suc (for i=suc j)
        step2 : ∀ c₀ k₀ i₀ → i₀ ≤ k₀ →
          max-list (map (λ t → nth i₀ t)
            (map (λ a → trace-action (Ongoing c₀) a k₀) all-actions)) ≡
          solve (Ongoing c₀) i₀
        step2 c₀ k₀ zero z≤n =
          map-double-ext
            (λ t → nth 0 t)
            (λ a → trace-action (Ongoing c₀) a k₀)
            (λ a → proj₂ (step (Ongoing c₀) a))
            all-actions
            (λ a → ta-nth-0 (Ongoing c₀) a k₀)
        step2 c₀ (suc k₀') (suc j₀) (s≤s j₀≤k₀') =
          map-double-ext
            (λ t → nth (suc j₀) t)
            (λ a → trace-action (Ongoing c₀) a (suc k₀'))
            (λ a → solve (proj₁ (step (Ongoing c₀) a)) j₀)
            all-actions
            (λ a → ta-nth-suc (Ongoing c₀) a k₀' j₀ j₀≤k₀')

        ongoing-proof : ∀ c₀ k₀ i₀ → i₀ ≤ k₀ →
          nth i₀ (best-trace (Ongoing c₀) (suc k₀)) ≡ solve (Ongoing c₀) i₀
        ongoing-proof c₀ k₀ i₀ i₀≤k₀ =
          let ta = λ a → trace-action (Ongoing c₀) a k₀
              all-bma = build-BMA ta all-actions i₀
                          (λ a j j≤i₀ → ta-bin (Ongoing c₀) a k₀ j
                            (≤-trans j≤i₀ i₀≤k₀))
                          (λ a j sj≤i₀ → ta-mono (Ongoing c₀) a k₀ j
                            (≤-trans sj≤i₀ i₀≤k₀))
              s1 = max-trace-nth (map ta all-actions) i₀ all-bma
          in trans s1 (step2 c₀ k₀ i₀ i₀≤k₀)

    --------------------------------------------------------------------
    -- solve-mono iterated: once R, always R at greater depths
    --------------------------------------------------------------------

    solve-R-stable : ∀ s m n → m ≤′ n →
      solve s m ≡ solved-reward → solve s n ≡ solved-reward
    solve-R-stable s m .m      ≤′-refl      p = p
    solve-R-stable s m (suc n) (≤′-step le) p =
      solve-mono s n (solve-R-stable s m n le p)

    -- Corollary using standard ≤
    solve-R-ge : ∀ s m n → m ≤ n →
      solve s m ≡ solved-reward → solve s n ≡ solved-reward
    solve-R-ge s m n m≤n = solve-R-stable s m n (≤⇒≤′ m≤n)

    -- For any state, solve at n > horizon is determined by solve at horizon:
    -- If solve s horizon = 0 (for Ongoing), then solve s n = 0 for all n.
    -- If solve s horizon = R, then solve s n = R for all n ≥ horizon.
    solve-determined : ∀ s n → horizon ≤ n →
      solve s horizon ≤ solve s n
    solve-determined s n H≤n with solve-binary s horizon
    ... | inj₁ eq0 = subst (_≤ solve s n) (sym eq0) z≤n
    ... | inj₂ eqR =
      subst (_≤ solve s n) (sym eqR)
        (subst (solved-reward ≤_) (sym (solve-R-ge s horizon n H≤n eqR)) ≤-refl)

    -- Converse direction for Ongoing: if solve s horizon = 0, solve s n = 0
    solve-ongoing-0-stable : ∀ c n → solve (Ongoing c) horizon ≡ 0 →
      solve (Ongoing c) n ≡ 0
    solve-ongoing-0-stable c n p = solve-horizon-suf c p n

    --------------------------------------------------------------------
    -- Trace-to-Solve ordering: lex trace order → pointwise solve order
    --------------------------------------------------------------------

    trace-to-solve-at : ∀ s a b n → n ≤ horizon →
      s ranks a ≤ b →
      solve (proj₁ (step s a)) n ≤ solve (proj₁ (step s b)) n
    trace-to-solve-at s a b n n≤H lex-ab =
      let ta-a = trace-action s a (suc horizon)
          ta-b = trace-action s b (suc horizon)
          sn≤sH : suc n ≤ suc horizon
          sn≤sH = s≤s n≤H
          bin-a = λ i i≤sn → ta-bin s a (suc horizon) i
                    (≤-trans i≤sn sn≤sH)
          bin-b = λ i i≤sn → ta-bin s b (suc horizon) i
                    (≤-trans i≤sn sn≤sH)
          mono-a = λ i si≤sn → ta-mono s a (suc horizon) i
                     (≤-trans si≤sn sn≤sH)
          mono-b = λ i si≤sn → ta-mono s b (suc horizon) i
                     (≤-trans si≤sn sn≤sH)
          pw = lex-ge-pointwise ta-b ta-a (suc n) bin-b bin-a mono-b mono-a lex-ab
      in subst₂ _≤_
           (ta-nth-suc s a horizon n n≤H)
           (ta-nth-suc s b horizon n n≤H)
           pw

    -- For n > horizon: use the fact that solve is determined by its value at horizon
    trace-to-solve-above : ∀ s a b n → horizon < n →
      s ranks a ≤ b →
      solve (proj₁ (step s a)) n ≤ solve (proj₁ (step s b)) n
    trace-to-solve-above s a b n H<n lex-ab =
      -- Strategy: solve s'_a n and solve s'_b n are both binary.
      -- We know solve s'_a horizon ≤ solve s'_b horizon from trace ordering.
      -- Case split on solve s'_a n:
      --   = 0: trivially 0 ≤ solve s'_b n
      --   = R: must show solve s'_b n = R
      let s'a = proj₁ (step s a)
          s'b = proj₁ (step s b)
          -- Get ordering at horizon from trace
          H≤H = ≤-refl {horizon}
          sa-H≤sb-H = trace-to-solve-at s a b horizon H≤H lex-ab
      in case-split s'a s'b n H<n sa-H≤sb-H
      where
        -- If solve s'a horizon = 0 and solve s'a n = R, derive contradiction
        sa-H-from-n : ∀ s'a n → horizon < n →
          solve s'a n ≡ solved-reward →
          solve s'a horizon ≡ 0 →
          solve s'a horizon ≡ solved-reward
        sa-H-from-n Dead       n H<n eqR _   = ⊥-elim (0≢R (trans (sym (solve-Dead-is-0 n)) eqR))
        sa-H-from-n (Solved c) n _   _   eq0 = ⊥-elim (0≢R (trans (sym eq0) (solve-Solved-is-R c horizon)))
        sa-H-from-n (Ongoing c) n _ eqR eq0 =
          ⊥-elim (0≢R (trans (sym (solve-horizon-suf c eq0 n)) eqR))

        -- Derive: solve s'a horizon = R from binary case split
        get-sa-H-R : ∀ s'a n → horizon < n →
          solve s'a n ≡ solved-reward →
          solve s'a horizon ≡ solved-reward
        get-sa-H-R s'a n H<n eqR with solve-binary s'a horizon
        ... | inj₂ p = p
        ... | inj₁ p = sa-H-from-n s'a n H<n eqR p

        -- Derive: solve s'b n = R from solve s'b horizon = R
        get-sb-n-R : ∀ s'b n → horizon < n →
          solve s'b horizon ≡ solved-reward →
          solve s'b n ≡ solved-reward
        get-sb-n-R s'b n H<n sb-H-R with solve-binary s'b horizon
        ... | inj₂ _ = solve-R-ge s'b horizon n (≤-trans (n≤1+n horizon) H<n) sb-H-R
        ... | inj₁ eq0 = ⊥-elim (0≢R (trans (sym eq0) sb-H-R))

        case-split : ∀ s'a s'b n → horizon < n →
          solve s'a horizon ≤ solve s'b horizon →
          solve s'a n ≤ solve s'b n
        case-split s'a s'b n H<n ord with solve-binary s'a n
        ... | inj₁ eq0 = subst (_≤ solve s'b n) (sym eq0) z≤n
        ... | inj₂ eqR =
          let sa-H-R = get-sa-H-R s'a n H<n eqR
              sb-H-R = ≤-antisym (solve-any-≤R s'b horizon)
                                 (subst (_≤ solve s'b horizon) sa-H-R ord)
              sb-n-R = get-sb-n-R s'b n H<n sb-H-R
          in subst₂ _≤_ (sym eqR) (sym sb-n-R) ≤-refl

    -- Combined: trace ordering → solve ordering at ALL depths
    trace-to-solve-ordering : ∀ s a b →
      s ranks a ≤ b →
      ∀ n → solve (proj₁ (step s a)) n ≤ solve (proj₁ (step s b)) n
    trace-to-solve-ordering s a b lex n with n ≤? horizon
    ... | yes n≤H = trace-to-solve-at s a b n n≤H lex
    ... | no  n>H = trace-to-solve-above s a b n (≰⇒> n>H) lex

    --------------------------------------------------------------------
    -- Preservation and CoindHomo assembly
    --------------------------------------------------------------------

    preserves : ∀ a b s →
      s ranks a ≤ b →
      action-value s a ≤ₛ action-value s b
    head≤ (preserves a b s lex) = proj₁ lex
    tail≤ (preserves a b s lex) =
      build-≤ₛ (value (proj₁ (step s a))) (value (proj₁ (step s b)))
        (λ n → subst₂ _≤_
          (sym (iter-head-value (proj₁ (step s a)) n))
          (sym (iter-head-value (proj₁ (step s b)) n))
          (trace-to-solve-ordering s a b lex n))

    instance
      PlacementMDPTraceBridgeHomo : CoindHomo
      PlacementMDPTraceBridgeHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves
        }

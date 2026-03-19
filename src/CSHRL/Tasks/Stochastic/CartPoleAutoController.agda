{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPoleAutoController
--
-- Fully automatic CartPole controller via ContinuousControlMDP EC.
--
-- Human input: state variables, dynamics, terminal condition,
-- grid resolution, reward-level mapping + monotonicity proof.
-- Everything else is derived automatically by the EC.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPoleAutoController where

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; -_; _+_; _*_; _-_; _÷_)
open import Data.Rational.Properties using (_<?_)

open import CSHRL.Probability.Finite using (Dist; pure)
open import CSHRL.Probability.FOSD using (_FOSD≤_; FOSD-refl; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)

open import CSHRL.EnvironmentClass.ContinuousControlMDP

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

ConcreteState : Set
ConcreteState = ℚ × ℚ × ℚ × ℚ

data Action : Set where
  Left  : Action
  Right : Action

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Left  ≟ₐ Left  = yes refl
Left  ≟ₐ Right = no (λ ())
Right ≟ₐ Left  = no (λ ())
Right ≟ₐ Right = yes refl

all-actions : List Action
all-actions = Left ∷ Right ∷ []

default-action : Action
default-action = Left

------------------------------------------------------------------------
-- 25-state grid: 6 angle bins × 4 velocity bins + terminal
------------------------------------------------------------------------

data GridState : Set where
  FLFN FLSN FLSP FLFP : GridState
  MLFN MLSN MLSP MLFP : GridState
  NLFN NLSN NLSP NLFP : GridState
  NRFN NRSN NRSP NRFP : GridState
  MRFN MRSN MRSP MRFP : GridState
  FRFN FRSN FRSP FRFP : GridState
  Terminal : GridState

all-grid-states : List GridState
all-grid-states =
  FLFN ∷ FLSN ∷ FLSP ∷ FLFP ∷
  MLFN ∷ MLSN ∷ MLSP ∷ MLFP ∷
  NLFN ∷ NLSN ∷ NLSP ∷ NLFP ∷
  NRFN ∷ NRSN ∷ NRSP ∷ NRFP ∷
  MRFN ∷ MRSN ∷ MRSP ∷ MRFP ∷
  FRFN ∷ FRSN ∷ FRSP ∷ FRFP ∷
  Terminal ∷ []

private
  grid-index : GridState → ℕ
  grid-index FLFN = 0
  grid-index FLSN = 1
  grid-index FLSP = 2
  grid-index FLFP = 3
  grid-index MLFN = 4
  grid-index MLSN = 5
  grid-index MLSP = 6
  grid-index MLFP = 7
  grid-index NLFN = 8
  grid-index NLSN = 9
  grid-index NLSP = 10
  grid-index NLFP = 11
  grid-index NRFN = 12
  grid-index NRSN = 13
  grid-index NRSP = 14
  grid-index NRFP = 15
  grid-index MRFN = 16
  grid-index MRSN = 17
  grid-index MRSP = 18
  grid-index MRFP = 19
  grid-index FRFN = 20
  grid-index FRSN = 21
  grid-index FRSP = 22
  grid-index FRFP = 23
  grid-index Terminal = 24

  list-nth : ℕ → List GridState → GridState
  list-nth _       []       = Terminal
  list-nth zero    (x ∷ _)  = x
  list-nth (suc n) (_ ∷ xs) = list-nth n xs

  from-index : ℕ → GridState
  from-index n = list-nth n all-grid-states

  from-section : (s : GridState) → from-index (grid-index s) ≡ s
  from-section FLFN = refl
  from-section FLSN = refl
  from-section FLSP = refl
  from-section FLFP = refl
  from-section MLFN = refl
  from-section MLSN = refl
  from-section MLSP = refl
  from-section MLFP = refl
  from-section NLFN = refl
  from-section NLSN = refl
  from-section NLSP = refl
  from-section NLFP = refl
  from-section NRFN = refl
  from-section NRSN = refl
  from-section NRSP = refl
  from-section NRFP = refl
  from-section MRFN = refl
  from-section MRSN = refl
  from-section MRSP = refl
  from-section MRFP = refl
  from-section FRFN = refl
  from-section FRSN = refl
  from-section FRSP = refl
  from-section FRFP = refl
  from-section Terminal = refl

open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)

_≟g_ : (s₁ s₂ : GridState) → Dec (s₁ ≡ s₂)
s₁ ≟g s₂ with grid-index s₁ ≟ℕ grid-index s₂
... | yes p = yes (trans (sym (from-section s₁)) (trans (cong from-index p) (from-section s₂)))
... | no ¬p = no (λ eq → ¬p (cong grid-index eq))

terminal? : GridState → Bool
terminal? Terminal = true
terminal? _        = false

------------------------------------------------------------------------
-- Transitions: 2nd-order Euler integration (lookup table)
------------------------------------------------------------------------

next-state : GridState → Action → GridState
next-state FLFN Left  = FLSP
next-state FLFN Right = Terminal
next-state FLSN Left  = MLFP
next-state FLSN Right = Terminal
next-state FLSP Left  = MLFP
next-state FLSP Right = Terminal
next-state FLFP Left  = NRFP
next-state FLFP Right = FLFN
next-state MLFN Left  = MLSP
next-state MLFN Right = Terminal
next-state MLSN Left  = NLFP
next-state MLSN Right = FLFN
next-state MLSP Left  = NRFP
next-state MLSP Right = FLFN
next-state MLFP Left  = MRFP
next-state MLFP Right = MLFN
next-state NLFN Left  = MLSP
next-state NLFN Right = FLFN
next-state NLSN Left  = NRFP
next-state NLSN Right = MLFN
next-state NLSP Left  = MRFP
next-state NLSP Right = MLFN
next-state NLFP Left  = FRFP
next-state NLFP Right = NRSN
next-state NRFN Left  = NLSP
next-state NRFN Right = FLFN
next-state NRSN Left  = MRFP
next-state NRSN Right = MLFN
next-state NRSP Left  = MRFP
next-state NRSP Right = NLFN
next-state NRFP Left  = FRFP
next-state NRFP Right = MRSN
next-state MRFN Left  = MRFP
next-state MRFN Right = MLFN
next-state MRSN Left  = FRFP
next-state MRSN Right = NLFN
next-state MRSP Left  = FRFP
next-state MRSP Right = NRFN
next-state MRFP Left  = Terminal
next-state MRFP Right = MRSN
next-state FRFN Left  = FRFP
next-state FRFN Right = NLFN
next-state FRSN Left  = Terminal
next-state FRSN Right = MRFN
next-state FRSP Left  = Terminal
next-state FRSP Right = MRFN
next-state FRFP Left  = Terminal
next-state FRFP Right = FRSN
next-state Terminal _ = Terminal

------------------------------------------------------------------------
-- State abstraction: ℚ⁴ → GridState
------------------------------------------------------------------------

private
  data AngleZone : Set where
    az-terminal az-FL az-ML az-NL az-NR az-MR az-FR : AngleZone

  angle-zone : ℚ → AngleZone
  angle-zone θ with θ <? (- (+ 209 / 1000))
  ... | yes _ = az-terminal
  ... | no  _ with (+ 209 / 1000) <? θ
  ...   | yes _ = az-terminal
  ...   | no  _ with θ <? (- (+ 3 / 25))
  ...     | yes _ = az-FL
  ...     | no  _ with θ <? (- (+ 1 / 25))
  ...       | yes _ = az-ML
  ...       | no  _ with θ <? 0ℚ
  ...         | yes _ = az-NL
  ...         | no  _ with θ <? (+ 1 / 25)
  ...           | yes _ = az-NR
  ...           | no  _ with θ <? (+ 3 / 25)
  ...             | yes _ = az-MR
  ...             | no  _ = az-FR

  data VelZone : Set where
    vz-FN vz-SN vz-SP vz-FP : VelZone

  vel-zone : ℚ → VelZone
  vel-zone v with v <? (- (+ 1 / 2))
  ... | yes _ = vz-FN
  ... | no  _ with v <? 0ℚ
  ...   | yes _ = vz-SN
  ...   | no  _ with v <? (+ 1 / 2)
  ...     | yes _ = vz-SP
  ...     | no  _ = vz-FP

project : ConcreteState → GridState
project (_ , _ , θ , θ̇) with angle-zone θ | vel-zone θ̇
... | az-terminal | _     = Terminal
... | az-FL | vz-FN = FLFN
... | az-FL | vz-SN = FLSN
... | az-FL | vz-SP = FLSP
... | az-FL | vz-FP = FLFP
... | az-ML | vz-FN = MLFN
... | az-ML | vz-SN = MLSN
... | az-ML | vz-SP = MLSP
... | az-ML | vz-FP = MLFP
... | az-NL | vz-FN = NLFN
... | az-NL | vz-SN = NLSN
... | az-NL | vz-SP = NLSP
... | az-NL | vz-FP = NLFP
... | az-NR | vz-FN = NRFN
... | az-NR | vz-SN = NRSN
... | az-NR | vz-SP = NRSP
... | az-NR | vz-FP = NRFP
... | az-MR | vz-FN = MRFN
... | az-MR | vz-SN = MRSN
... | az-MR | vz-SP = MRSP
... | az-MR | vz-FP = MRFP
... | az-FR | vz-FN = FRFN
... | az-FR | vz-SN = FRSN
... | az-FR | vz-SP = FRSP
... | az-FR | vz-FP = FRFP

embed : GridState → ConcreteState
embed FLFN = (0ℚ , 0ℚ , - (+ 3 / 20) , - (+ 1 / 1))
embed FLSN = (0ℚ , 0ℚ , - (+ 3 / 20) , - (+ 1 / 4))
embed FLSP = (0ℚ , 0ℚ , - (+ 3 / 20) ,   + 1 / 4)
embed FLFP = (0ℚ , 0ℚ , - (+ 3 / 20) ,   + 1 / 1)
embed MLFN = (0ℚ , 0ℚ , - (+ 2 / 25) , - (+ 1 / 1))
embed MLSN = (0ℚ , 0ℚ , - (+ 2 / 25) , - (+ 1 / 4))
embed MLSP = (0ℚ , 0ℚ , - (+ 2 / 25) ,   + 1 / 4)
embed MLFP = (0ℚ , 0ℚ , - (+ 2 / 25) ,   + 1 / 1)
embed NLFN = (0ℚ , 0ℚ , - (+ 1 / 50) , - (+ 1 / 1))
embed NLSN = (0ℚ , 0ℚ , - (+ 1 / 50) , - (+ 1 / 4))
embed NLSP = (0ℚ , 0ℚ , - (+ 1 / 50) ,   + 1 / 4)
embed NLFP = (0ℚ , 0ℚ , - (+ 1 / 50) ,   + 1 / 1)
embed NRFN = (0ℚ , 0ℚ ,   + 1 / 50   , - (+ 1 / 1))
embed NRSN = (0ℚ , 0ℚ ,   + 1 / 50   , - (+ 1 / 4))
embed NRSP = (0ℚ , 0ℚ ,   + 1 / 50   ,   + 1 / 4)
embed NRFP = (0ℚ , 0ℚ ,   + 1 / 50   ,   + 1 / 1)
embed MRFN = (0ℚ , 0ℚ ,   + 2 / 25   , - (+ 1 / 1))
embed MRSN = (0ℚ , 0ℚ ,   + 2 / 25   , - (+ 1 / 4))
embed MRSP = (0ℚ , 0ℚ ,   + 2 / 25   ,   + 1 / 4)
embed MRFP = (0ℚ , 0ℚ ,   + 2 / 25   ,   + 1 / 1)
embed FRFN = (0ℚ , 0ℚ ,   + 3 / 20   , - (+ 1 / 1))
embed FRSN = (0ℚ , 0ℚ ,   + 3 / 20   , - (+ 1 / 4))
embed FRSP = (0ℚ , 0ℚ ,   + 3 / 20   ,   + 1 / 4)
embed FRFP = (0ℚ , 0ℚ ,   + 3 / 20   ,   + 1 / 1)
embed Terminal = (0ℚ , 0ℚ , + 1 / 1 , 0ℚ)

section : ∀ g → project (embed g) ≡ g
section FLFN = refl ; section FLSN = refl
section FLSP = refl ; section FLFP = refl
section MLFN = refl ; section MLSN = refl
section MLSP = refl ; section MLFP = refl
section NLFN = refl ; section NLSN = refl
section NLSP = refl ; section NLFP = refl
section NRFN = refl ; section NRSN = refl
section NRSP = refl ; section NRFP = refl
section MRFN = refl ; section MRSN = refl
section MRSP = refl ; section MRFP = refl
section FRFN = refl ; section FRSN = refl
section FRSP = refl ; section FRFP = refl
section Terminal = refl

------------------------------------------------------------------------
-- Reward configuration: 3 levels (avoidance task → fragility = reward)
------------------------------------------------------------------------

private
  bad medium good : Dist ℕ
  bad    = (0 , 1) ∷ (0 , 1) ∷ []
  medium = (1 , 1) ∷ (1 , 1) ∷ []
  good   = (2 , 1) ∷ (1 , 1) ∷ []

  reward-level : ℕ → Dist ℕ
  reward-level 0             = bad
  reward-level 1             = medium
  reward-level (suc (suc _)) = good

  reward-level-mono : ∀ m n → m ≤ n →
    reward-level m FOSD≤ reward-level n
  reward-level-mono zero     zero        _   = FOSD-refl bad
  reward-level-mono zero     (suc zero)  _   = fosd?-sound bad medium refl
  reward-level-mono zero     (suc (suc _)) _ = fosd?-sound bad good refl
  reward-level-mono (suc zero) (suc zero)  _ = FOSD-refl medium
  reward-level-mono (suc zero) (suc (suc _)) _ = fosd?-sound medium good refl
  reward-level-mono (suc (suc _)) (suc (suc _)) _ = FOSD-refl good
  reward-level-mono (suc _) zero ()
  reward-level-mono (suc (suc _)) (suc zero) (s≤s ())

------------------------------------------------------------------------
-- Policy: angle-sign tie-breaking for FOSD-tied states
------------------------------------------------------------------------

decide-grid : GridState → Action
decide-grid FLFN = Left
decide-grid FLSN = Left
decide-grid FLSP = Left
decide-grid FLFP = Left
decide-grid MLFN = Left
decide-grid MLSN = Left
decide-grid MLSP = Left
decide-grid MLFP = Left
decide-grid NLFN = Left
decide-grid NLSN = Left
decide-grid NLSP = Left
decide-grid NLFP = Right
decide-grid NRFN = Left
decide-grid NRSN = Right
decide-grid NRSP = Right
decide-grid NRFP = Right
decide-grid MRFN = Right
decide-grid MRSN = Right
decide-grid MRSP = Right
decide-grid MRFP = Right
decide-grid FRFN = Right
decide-grid FRSN = Right
decide-grid FRSP = Right
decide-grid FRFP = Right
decide-grid Terminal = Left

------------------------------------------------------------------------
-- Instantiate the ContinuousControlMDP EC
------------------------------------------------------------------------

open ContinuousControl (record
  { ConcreteState      = ConcreteState
  ; Action             = Action
  ; GridState          = GridState
  ; _≟g_              = _≟g_
  ; all-actions        = all-actions
  ; default-action     = default-action
  ; all-grid-states    = all-grid-states
  ; terminal?          = terminal?
  ; next-state         = next-state
  ; project            = project
  ; embed              = embed
  ; section            = section
  ; frag-to-reward     = λ x → x
  ; reward-level       = reward-level
  ; reward-level-mono  = reward-level-mono
  ; decide-grid        = decide-grid
  }) public

------------------------------------------------------------------------
-- Verification checks
------------------------------------------------------------------------

private
  check-frag-Terminal : fragility Terminal ≡ 0
  check-frag-Terminal = refl
  check-frag-FLFN : fragility FLFN ≡ 1
  check-frag-FLFN = refl
  check-frag-FLFP : fragility FLFP ≡ 2
  check-frag-FLFP = refl
  check-frag-MRFP : fragility MRFP ≡ 1
  check-frag-MRFP = refl

  flfn-rep nlfp-rep nrfn-rep nrsp-rep mrfp-rep : ConcreteState
  mlfp-rep nlsp-rep nrsn-rep mrfn-rep : ConcreteState
  flfn-rep = (0ℚ , 0ℚ , - (+ 3 / 20) , - (+ 1 / 1))
  nlfp-rep = (0ℚ , 0ℚ , - (+ 1 / 50) ,   + 1 / 1)
  nrfn-rep = (0ℚ , 0ℚ ,   + 1 / 50   , - (+ 1 / 1))
  nrsp-rep = (0ℚ , 0ℚ ,   + 1 / 50   ,   + 1 / 4)
  mrfp-rep = (0ℚ , 0ℚ ,   + 2 / 25   ,   + 1 / 1)
  mlfp-rep = (0ℚ , 0ℚ , - (+ 2 / 25) ,   + 1 / 1)
  nlsp-rep = (0ℚ , 0ℚ , - (+ 1 / 50) ,   + 1 / 4)
  nrsn-rep = (0ℚ , 0ℚ ,   + 1 / 50   , - (+ 1 / 4))
  mrfn-rep = (0ℚ , 0ℚ ,   + 2 / 25   , - (+ 1 / 1))

  decide-left-fl : decide flfn-rep ≡ Left
  decide-left-fl = refl

  decide-right-nlfp : decide nlfp-rep ≡ Right
  decide-right-nlfp = refl

  decide-left-nrfn : decide nrfn-rep ≡ Left
  decide-left-nrfn = refl

  decide-right-nrsp : decide nrsp-rep ≡ Right
  decide-right-nrsp = refl

  decide-right-mrfp : decide mrfp-rep ≡ Right
  decide-right-mrfp = refl

  open VerifiedRanking continuous-ranking

  decide-left-optimal-fl : _≤ₐ_ flfn-rep Right Left
  decide-left-optimal-fl = z≤n

  decide-right-optimal-nlfp : _≤ₐ_ nlfp-rep Left Right
  decide-right-optimal-nlfp = s≤s z≤n

  decide-safe-mlfp : _≤ₐ_ mlfp-rep Left Right × _≤ₐ_ mlfp-rep Right Left
  decide-safe-mlfp = ≤-refl , ≤-refl
    where open import Data.Nat.Properties using (≤-refl)

------------------------------------------------------------------------
-- Euler dynamics verification (optional cross-check)
------------------------------------------------------------------------

private
  cp-g     : ℚ ; cp-g     = + 49 / 5
  cp-total : ℚ ; cp-total = + 11 / 10
  cp-denom : ℚ ; cp-denom = + 41 / 66
  cp-τ     : ℚ ; cp-τ     = + 1 / 10

  cp-force : Action → ℚ
  cp-force Left  = - (+ 10 / 1)
  cp-force Right = + 10 / 1

  θ̈ : ℚ → ℚ → ℚ
  θ̈ θ F = (cp-g * θ - F ÷ cp-total) ÷ cp-denom

  euler₂ : ℚ → ℚ → ℚ → ℚ × ℚ
  euler₂ θ θ̇ F =
    let acc = θ̈ θ F
        τ²  = cp-τ * cp-τ
    in ( θ + cp-τ * θ̇ + (+ 1 / 2) * τ² * acc
       , θ̇ + cp-τ * acc )

  θ-rep : GridState → ℚ
  θ-rep FLFN = - (+ 3 / 20) ; θ-rep FLSN = - (+ 3 / 20)
  θ-rep FLSP = - (+ 3 / 20) ; θ-rep FLFP = - (+ 3 / 20)
  θ-rep MLFN = - (+ 2 / 25) ; θ-rep MLSN = - (+ 2 / 25)
  θ-rep MLSP = - (+ 2 / 25) ; θ-rep MLFP = - (+ 2 / 25)
  θ-rep NLFN = - (+ 1 / 50) ; θ-rep NLSN = - (+ 1 / 50)
  θ-rep NLSP = - (+ 1 / 50) ; θ-rep NLFP = - (+ 1 / 50)
  θ-rep NRFN =   + 1 / 50   ; θ-rep NRSN =   + 1 / 50
  θ-rep NRSP =   + 1 / 50   ; θ-rep NRFP =   + 1 / 50
  θ-rep MRFN =   + 2 / 25   ; θ-rep MRSN =   + 2 / 25
  θ-rep MRSP =   + 2 / 25   ; θ-rep MRFP =   + 2 / 25
  θ-rep FRFN =   + 3 / 20   ; θ-rep FRSN =   + 3 / 20
  θ-rep FRSP =   + 3 / 20   ; θ-rep FRFP =   + 3 / 20
  θ-rep Terminal = 0ℚ

  θ̇-rep : GridState → ℚ
  θ̇-rep FLFN = - (+ 1 / 1)  ; θ̇-rep FLSN = - (+ 1 / 4)
  θ̇-rep FLSP =   + 1 / 4    ; θ̇-rep FLFP =   + 1 / 1
  θ̇-rep MLFN = - (+ 1 / 1)  ; θ̇-rep MLSN = - (+ 1 / 4)
  θ̇-rep MLSP =   + 1 / 4    ; θ̇-rep MLFP =   + 1 / 1
  θ̇-rep NLFN = - (+ 1 / 1)  ; θ̇-rep NLSN = - (+ 1 / 4)
  θ̇-rep NLSP =   + 1 / 4    ; θ̇-rep NLFP =   + 1 / 1
  θ̇-rep NRFN = - (+ 1 / 1)  ; θ̇-rep NRSN = - (+ 1 / 4)
  θ̇-rep NRSP =   + 1 / 4    ; θ̇-rep NRFP =   + 1 / 1
  θ̇-rep MRFN = - (+ 1 / 1)  ; θ̇-rep MRSN = - (+ 1 / 4)
  θ̇-rep MRSP =   + 1 / 4    ; θ̇-rep MRFP =   + 1 / 1
  θ̇-rep FRFN = - (+ 1 / 1)  ; θ̇-rep FRSN = - (+ 1 / 4)
  θ̇-rep FRSP =   + 1 / 4    ; θ̇-rep FRFP =   + 1 / 1
  θ̇-rep Terminal = 0ℚ

  euler-bin : GridState → Action → GridState
  euler-bin Terminal _ = Terminal
  euler-bin gs a =
    let (θ' , θ̇') = euler₂ (θ-rep gs) (θ̇-rep gs) (cp-force a)
    in project (0ℚ , 0ℚ , θ' , θ̇')

check-FLFN-L : euler-bin FLFN Left  ≡ FLSP     ; check-FLFN-L = refl
check-FLFN-R : euler-bin FLFN Right ≡ Terminal  ; check-FLFN-R = refl
check-FLFP-L : euler-bin FLFP Left  ≡ NRFP     ; check-FLFP-L = refl
check-FLFP-R : euler-bin FLFP Right ≡ FLFN     ; check-FLFP-R = refl
check-NLFP-L : euler-bin NLFP Left  ≡ FRFP     ; check-NLFP-L = refl
check-NLFP-R : euler-bin NLFP Right ≡ NRSN     ; check-NLFP-R = refl
check-MRFP-L : euler-bin MRFP Left  ≡ Terminal  ; check-MRFP-L = refl
check-MRFP-R : euler-bin MRFP Right ≡ MRSN     ; check-MRFP-R = refl

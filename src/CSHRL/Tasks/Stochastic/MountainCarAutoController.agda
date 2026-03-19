{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCarAutoController
--
-- Fully automatic MountainCar controller via ContinuousControlMDP EC.
--
-- Key difference from CartPole: MountainCar is a GOAL-REACHING task
-- (Terminal = good), not an avoidance task.  Fragility = distance
-- to goal, so rewards are inverted: max_frag − fragility(next_state).
--
-- Dynamics: v' = v + (a−1)·0.001 + cos(3x)·(−0.0025)
--           x' = x + v'     (clipped, 25 sub-steps per abstract step)
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCarAutoController where

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; z≤n; s≤s)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; -_; _+_; _*_; _-_)
open import Data.Rational.Properties using (_<?_)

open import CSHRL.Probability.Finite using (Dist; pure)
open import CSHRL.Probability.FOSD using (_FOSD≤_; FOSD-refl; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)

open import CSHRL.EnvironmentClass.ContinuousControlMDP

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

ConcreteState : Set
ConcreteState = ℚ × ℚ

data MCAction : Set where
  PushLeft  : MCAction
  NoAction  : MCAction
  PushRight : MCAction

_≟ₐ_ : (a b : MCAction) → Dec (a ≡ b)
PushLeft  ≟ₐ PushLeft  = yes refl
PushLeft  ≟ₐ NoAction  = no (λ ())
PushLeft  ≟ₐ PushRight = no (λ ())
NoAction  ≟ₐ PushLeft  = no (λ ())
NoAction  ≟ₐ NoAction  = yes refl
NoAction  ≟ₐ PushRight = no (λ ())
PushRight ≟ₐ PushLeft  = no (λ ())
PushRight ≟ₐ NoAction  = no (λ ())
PushRight ≟ₐ PushRight = yes refl

all-actions : List MCAction
all-actions = PushLeft ∷ NoAction ∷ PushRight ∷ []

default-action : MCAction
default-action = NoAction

------------------------------------------------------------------------
-- 12-state grid: 5 position bins × 2 velocity bins + GoalN + Terminal
------------------------------------------------------------------------

data GridState : Set where
  FLN FLP MLN MLP VBN VBP NRN NRP CRN CRP GoalN : GridState
  Terminal : GridState

all-grid-states : List GridState
all-grid-states =
  FLN ∷ FLP ∷ MLN ∷ MLP ∷ VBN ∷ VBP ∷
  NRN ∷ NRP ∷ CRN ∷ CRP ∷ GoalN ∷
  Terminal ∷ []

private
  grid-index : GridState → ℕ
  grid-index FLN = 0
  grid-index FLP = 1
  grid-index MLN = 2
  grid-index MLP = 3
  grid-index VBN = 4
  grid-index VBP = 5
  grid-index NRN = 6
  grid-index NRP = 7
  grid-index CRN = 8
  grid-index CRP = 9
  grid-index GoalN = 10
  grid-index Terminal = 11

  list-nth : ℕ → List GridState → GridState
  list-nth _       []       = Terminal
  list-nth zero    (x ∷ _)  = x
  list-nth (suc n) (_ ∷ xs) = list-nth n xs

  from-index : ℕ → GridState
  from-index n = list-nth n all-grid-states

  from-section : (s : GridState) → from-index (grid-index s) ≡ s
  from-section FLN = refl
  from-section FLP = refl
  from-section MLN = refl
  from-section MLP = refl
  from-section VBN = refl
  from-section VBP = refl
  from-section NRN = refl
  from-section NRP = refl
  from-section CRN = refl
  from-section CRP = refl
  from-section GoalN = refl
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
-- Transitions: 25-step Euler integration with Taylor-7 cos(3x)
--
-- Entirely in Agda using fixed-point integer arithmetic (ℤ, scale 10⁸).
------------------------------------------------------------------------

private
  module FE where
    open import Data.Integer.Base as ℤ
      using (ℤ; +_; -[1+_]; ∣_∣; sign; _◃_)
      renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
    open import Data.Integer.Properties as ℤP
      using () renaming (_<?_ to _<?ℤ_; _≤?_ to _≤?ℤ_)
    open import Data.Nat as ℕ using (ℕ; zero; suc)
    open import Data.Nat.DivMod as ℕDM using () renaming (_/_ to _ℕ/_)
    open import Data.Product using (_×_; _,_)
    open import Relation.Nullary using (yes; no)

    Fixed : Set
    Fixed = ℤ

    SCALE : ℕ
    SCALE = 100000000

    negℕ : ℕ → ℤ
    negℕ zero    = + 0
    negℕ (suc n) = -[1+ n ]

    _quotℕ_ : ℤ → (d : ℕ) → .{{ℕ.NonZero d}} → ℤ
    (+ m)     quotℕ d = + (m ℕ/ d)
    -[1+ m ]  quotℕ d = negℕ (suc m ℕ/ d)

    _f*_ : Fixed → Fixed → Fixed
    a f* b = (a *ℤ b) quotℕ SCALE

    _f÷_ : Fixed → (d : ℕ) → .{{ℕ.NonZero d}} → Fixed
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
      in + SCALE
         −ℤ (y²  f÷ 2) +ℤ (y⁴  f÷ 24)
         −ℤ (y⁶  f÷ 720) +ℤ (y⁸  f÷ 40320)
         −ℤ (y¹⁰ f÷ 3628800) +ℤ (y¹² f÷ 479001600)

    fclip : Fixed → Fixed → Fixed → Fixed
    fclip lo hi x with lo ≤?ℤ x
    ... | no  _ = lo
    ... | yes _ with x ≤?ℤ hi
    ...   | yes _ = x
    ...   | no  _ = hi

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
    multi-f zero    st _ = st
    multi-f (suc n) st a = multi-f n (step-f st a) a

    vsplit : GridState → GridState → Fixed → GridState
    vsplit neg pos v with v <?ℤ (+ 0)
    ... | yes _ = neg
    ... | no  _ = pos

    proj-f : Fixed × Fixed → GridState
    proj-f (x , v) with x <?ℤ ℤneg (+ 70000000)
    ... | yes _ = vsplit FLN FLP v
    ... | no  _ with x <?ℤ ℤneg (+ 20000000)
    ...   | yes _ = vsplit MLN MLP v
    ...   | no  _ with x <?ℤ (+ 10000000)
    ...     | yes _ = vsplit VBN VBP v
    ...     | no  _ with x <?ℤ (+ 35000000)
    ...       | yes _ = vsplit NRN NRP v
    ...       | no  _ with x <?ℤ (+ 50000000)
    ...         | yes _ = vsplit CRN CRP v
    ...         | no  _ = vsplit GoalN Terminal v

    embed-f : GridState → Fixed × Fixed
    embed-f FLN      = (ℤneg (+ 95000000) , ℤneg (+ 3500000))
    embed-f FLP      = (ℤneg (+ 95000000) , + 3500000)
    embed-f MLN      = (ℤneg (+ 45000000) , ℤneg (+ 3500000))
    embed-f MLP      = (ℤneg (+ 45000000) , + 3500000)
    embed-f VBN      = (ℤneg (+ 5000000)  , ℤneg (+ 3500000))
    embed-f VBP      = (ℤneg (+ 5000000)  , + 3500000)
    embed-f NRN      = (+ 22500000 , ℤneg (+ 3500000))
    embed-f NRP      = (+ 22500000 , + 3500000)
    embed-f CRN      = (+ 42500000 , ℤneg (+ 3500000))
    embed-f CRP      = (+ 42500000 , + 3500000)
    embed-f GoalN    = (+ 55000000 , ℤneg (+ 3500000))
    embed-f Terminal  = (+ 55000000 , + 3500000)

    euler-f : GridState → MCAction → GridState
    euler-f Terminal _ = Terminal
    euler-f gs a = proj-f (multi-f 25 (embed-f gs) a)

next-state : GridState → MCAction → GridState
next-state = FE.euler-f

------------------------------------------------------------------------
-- State abstraction: ℚ² → GridState
------------------------------------------------------------------------

private
  data PosZone : Set where
    pz-FL pz-ML pz-VB pz-NR pz-CR pz-Goal : PosZone

  pos-zone : ℚ → PosZone
  pos-zone x with (+ 1 / 2) <? x
  ... | yes _ = pz-Goal
  pos-zone x | no _ with x <? (+ 1 / 2)
  ...   | no  _ = pz-Goal
  ...   | yes _ with x <? (- (+ 7 / 10))
  ...     | yes _ = pz-FL
  ...     | no  _ with x <? (- (+ 1 / 5))
  ...       | yes _ = pz-ML
  ...       | no  _ with x <? (+ 1 / 10)
  ...         | yes _ = pz-VB
  ...         | no  _ with x <? (+ 7 / 20)
  ...           | yes _ = pz-NR
  ...           | no  _ = pz-CR

  data VelZone : Set where
    vz-N vz-P : VelZone

  vel-zone : ℚ → VelZone
  vel-zone v with v <? 0ℚ
  ... | yes _ = vz-N
  ... | no  _ = vz-P

project : ConcreteState → GridState
project (x , v) with pos-zone x | vel-zone v
... | pz-Goal | vz-N = GoalN
... | pz-Goal | vz-P = Terminal
... | pz-FL   | vz-N = FLN
... | pz-FL   | vz-P = FLP
... | pz-ML   | vz-N = MLN
... | pz-ML   | vz-P = MLP
... | pz-VB   | vz-N = VBN
... | pz-VB   | vz-P = VBP
... | pz-NR   | vz-N = NRN
... | pz-NR   | vz-P = NRP
... | pz-CR   | vz-N = CRN
... | pz-CR   | vz-P = CRP

embed : GridState → ConcreteState
embed FLN   = (- (+ 19 / 20) , - (+ 7 / 200))
embed FLP   = (- (+ 19 / 20) ,   + 7 / 200)
embed MLN   = (- (+ 9 / 20)  , - (+ 7 / 200))
embed MLP   = (- (+ 9 / 20)  ,   + 7 / 200)
embed VBN   = (- (+ 1 / 20)  , - (+ 7 / 200))
embed VBP   = (- (+ 1 / 20)  ,   + 7 / 200)
embed NRN   = (  + 9 / 40    , - (+ 7 / 200))
embed NRP   = (  + 9 / 40    ,   + 7 / 200)
embed CRN   = (  + 17 / 40   , - (+ 7 / 200))
embed CRP   = (  + 17 / 40   ,   + 7 / 200)
embed GoalN = (  + 11 / 20   , - (+ 7 / 200))
embed Terminal = (+ 11 / 20   ,   + 7 / 200)

section : ∀ g → project (embed g) ≡ g
section FLN = refl ; section FLP = refl
section MLN = refl ; section MLP = refl
section VBN = refl ; section VBP = refl
section NRN = refl ; section NRP = refl
section CRN = refl ; section CRP = refl
section GoalN = refl ; section Terminal = refl

------------------------------------------------------------------------
-- Reward configuration: 5 levels (goal-reaching → inverted fragility)
------------------------------------------------------------------------

private
  max-frag : ℕ
  max-frag = 4

  great good medium low bad : Dist ℕ
  great  = (4 , 1) ∷ (4 , 1) ∷ (4 , 1) ∷ []
  good   = (3 , 1) ∷ (3 , 1) ∷ (3 , 1) ∷ []
  medium = (2 , 1) ∷ (2 , 1) ∷ (2 , 1) ∷ []
  low    = (1 , 1) ∷ (1 , 1) ∷ (1 , 1) ∷ []
  bad    = (0 , 1) ∷ (0 , 1) ∷ (0 , 1) ∷ []

  reward-level : ℕ → Dist ℕ
  reward-level 0                         = bad
  reward-level 1                         = low
  reward-level 2                         = medium
  reward-level 3                         = good
  reward-level (suc (suc (suc (suc _)))) = great

  reward-level-mono : ∀ m n → m ≤ n →
    reward-level m FOSD≤ reward-level n
  reward-level-mono 0 0 _ = FOSD-refl bad
  reward-level-mono 0 1 _ = fosd?-sound bad low refl
  reward-level-mono 0 2 _ = fosd?-sound bad medium refl
  reward-level-mono 0 3 _ = fosd?-sound bad good refl
  reward-level-mono 0 (suc (suc (suc (suc _)))) _ = fosd?-sound bad great refl
  reward-level-mono 1 1 _ = FOSD-refl low
  reward-level-mono 1 2 _ = fosd?-sound low medium refl
  reward-level-mono 1 3 _ = fosd?-sound low good refl
  reward-level-mono 1 (suc (suc (suc (suc _)))) _ = fosd?-sound low great refl
  reward-level-mono 2 2 _ = FOSD-refl medium
  reward-level-mono 2 3 _ = fosd?-sound medium good refl
  reward-level-mono 2 (suc (suc (suc (suc _)))) _ = fosd?-sound medium great refl
  reward-level-mono 3 3 _ = FOSD-refl good
  reward-level-mono 3 (suc (suc (suc (suc _)))) _ = fosd?-sound good great refl
  reward-level-mono (suc (suc (suc (suc _)))) (suc (suc (suc (suc _)))) _ = FOSD-refl great
  reward-level-mono (suc _) 0 ()
  reward-level-mono (suc (suc _)) 1 (s≤s ())
  reward-level-mono (suc (suc (suc _))) 2 (s≤s (s≤s ()))
  reward-level-mono (suc (suc (suc (suc _)))) 3 (s≤s (s≤s (s≤s ())))

------------------------------------------------------------------------
-- Policy: velocity-sign tie-breaking
------------------------------------------------------------------------

decide-grid : GridState → MCAction
decide-grid FLN   = PushLeft
decide-grid FLP   = PushRight
decide-grid MLN   = PushLeft
decide-grid MLP   = PushRight
decide-grid VBN   = PushLeft
decide-grid VBP   = PushRight
decide-grid NRN   = PushLeft
decide-grid NRP   = PushRight
decide-grid CRN   = PushLeft
decide-grid CRP   = PushRight
decide-grid GoalN = PushLeft
decide-grid Terminal = PushRight

------------------------------------------------------------------------
-- Instantiate the ContinuousControlMDP EC
------------------------------------------------------------------------

open ContinuousControl (record
  { ConcreteState      = ConcreteState
  ; Action             = MCAction
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
  ; frag-to-reward     = λ x → max-frag ∸ x
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
  check-frag-NRP : fragility NRP ≡ 1
  check-frag-NRP = refl
  check-frag-CRP : fragility CRP ≡ 1
  check-frag-CRP = refl
  check-frag-FLP : fragility FLP ≡ 2
  check-frag-FLP = refl
  check-frag-FLN : fragility FLN ≡ 3
  check-frag-FLN = refl
  check-frag-GoalN : fragility GoalN ≡ 4
  check-frag-GoalN = refl

  fln-rep flp-rep vbn-rep vbp-rep nrn-rep nrp-rep : ConcreteState
  fln-rep = (- (+ 19 / 20) , - (+ 7 / 200))
  flp-rep = (- (+ 19 / 20) ,   + 7 / 200)
  vbn-rep = (- (+ 1 / 20)  , - (+ 7 / 200))
  vbp-rep = (- (+ 1 / 20)  ,   + 7 / 200)
  nrn-rep = (  + 9 / 40    , - (+ 7 / 200))
  nrp-rep = (  + 9 / 40    ,   + 7 / 200)

  decide-left-fln : decide fln-rep ≡ PushLeft
  decide-left-fln = refl

  decide-right-flp : decide flp-rep ≡ PushRight
  decide-right-flp = refl

  decide-left-vbn : decide vbn-rep ≡ PushLeft
  decide-left-vbn = refl

  decide-right-vbp : decide vbp-rep ≡ PushRight
  decide-right-vbp = refl

  decide-right-nrp : decide nrp-rep ≡ PushRight
  decide-right-nrp = refl

  open VerifiedRanking continuous-ranking

  decide-left-optimal-vbn : _≤ₐ_ vbn-rep NoAction PushLeft
  decide-left-optimal-vbn = s≤s z≤n

  decide-right-optimal-flp : _≤ₐ_ flp-rep PushLeft PushRight
  decide-right-optimal-flp = s≤s (s≤s z≤n)

  decide-goal-nrp : _≤ₐ_ nrp-rep PushLeft PushRight
  decide-goal-nrp = z≤n

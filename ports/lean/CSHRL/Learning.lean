/-
CSHRL portability kernel, Lean 4 port.
T5: the learning kernel (paper section 14, Agda reference
src/CSHRL/Learning/Base.agda).

Explicit rankings are lists of actions, best first.  We port exactly the
machine-checked lemmas of the Agda reference: reflexivity and totality of
the induced order, swap_fixes_pair, state-updater locality, and the
demotion-preservation chain.  As in the Agda reference, the global
violation-decrease statement is an assumption record there, not a closed
proof, so it is not part of the kernel.
-/

namespace CSHRL

variable {State Action : Type} [DecidableEq Action]

/-- A ranking list per state, best action first. -/
def ExplicitRanking (State Action : Type) : Type := State → List Action

/-- `isDominatedBy xs a b = true` means a ≤ b in the order given by xs
(b appears no later than a; absent actions rank equal). -/
def isDominatedBy : List Action → Action → Action → Bool
  | [], _, _ => true
  | x :: xs, a, b =>
    if a = x then (if b = x then true else false)
    else if b = x then true else isDominatedBy xs a b

/-- D8 support: the induced order is reflexive. -/
theorem isDominatedBy_refl (xs : List Action) (a : Action) :
    isDominatedBy xs a a = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : a = x <;> simp [isDominatedBy, h, ih]

/-- D8 support: the induced order is total. -/
theorem dominated_total (xs : List Action) (a b : Action) :
    isDominatedBy xs a b = true ∨ isDominatedBy xs b a = true := by
  induction xs with
  | nil => left; rfl
  | cons x xs ih =>
    by_cases ha : a = x <;> by_cases hb : b = x <;>
      simp [isDominatedBy, ha, hb, ih]

/-- Skipping a head that is neither a nor b leaves dominance unchanged. -/
theorem isDominatedBy_skip (x a b : Action) (xs : List Action)
    (hax : a ≠ x) (hbx : b ≠ x) :
    isDominatedBy (x :: xs) a b = isDominatedBy xs a b := by
  simp [isDominatedBy, hax, hbx]

/-- Appending one action c never changes the dominance of a pair (a, b)
when neither a nor b equals c. -/
theorem dominated_snoc_irrelevant (c a b : Action) (xs : List Action)
    (hac : a ≠ c) (hbc : b ≠ c) :
    isDominatedBy (xs ++ [c]) a b = isDominatedBy xs a b := by
  induction xs with
  | nil => simp [isDominatedBy, hac, hbc]
  | cons x xs ih =>
    by_cases ha : a = x <;> by_cases hb : b = x <;>
      simp [isDominatedBy, ha, hb, ih]

/-! ### Swap: the violation repair (a transposition) -/

def removeAction (a : Action) : List Action → List Action
  | [] => []
  | y :: ys => if y = a then ys else y :: removeAction a ys

/-- Put better immediately before worse at worse's old position. -/
def swapInList (better worse : Action) : List Action → List Action
  | [] => []
  | x :: xs =>
    if x = worse then better :: worse :: removeAction better xs
    else x :: swapInList better worse xs

/-- T5a: the swap fixes the violated pair (Agda: swap-fixes-pair). -/
theorem swap_fixes_pair (better worse : Action) (xs : List Action)
    (hbw : better ≠ worse) :
    isDominatedBy (swapInList better worse xs) worse better = true := by
  have hwb : worse ≠ better := fun e => hbw e.symm
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = worse
    · simp [swapInList, hx, isDominatedBy, hwb]
    · have hwx : worse ≠ x := fun e => hx e.symm
      by_cases hbx : better = x
      · simp [swapInList, hx, isDominatedBy, hwx, hbx]
      · simp [swapInList, hx, isDominatedBy, hwx, hbx, ih]

/-! ### State-specific updater locality -/

section StateSpecific

variable [DecidableEq State]

def stateSwapUpdater (violState : State) (better worse : Action)
    (ranking : ExplicitRanking State Action) : ExplicitRanking State Action :=
  fun s =>
    if s = violState then swapInList better worse (ranking s) else ranking s

/-- T5b: the state-specific updater only modifies the violated state
(Agda: state-updater-locality). -/
theorem state_updater_locality (violState : State) (better worse : Action)
    (ranking : ExplicitRanking State Action) (s : State)
    (h : s ≠ violState) :
    stateSwapUpdater violState better worse ranking s = ranking s := by
  simp [stateSwapUpdater, h]

end StateSpecific

/-! ### Demotion: O(1) adaptation to action unavailability -/

def demoteToEnd (target : Action) : List Action → List Action
  | [] => []
  | x :: xs =>
    if x = target then xs ++ [target] else x :: demoteToEnd target xs

/-- T5c: demotion preserves the dominance relation between any two actions
other than the demoted one (Agda: demote-preserves-dominance). -/
theorem demote_preserves_dominance (target a b : Action) (xs : List Action)
    (hat : a ≠ target) (hbt : b ≠ target) :
    isDominatedBy (demoteToEnd target xs) a b = isDominatedBy xs a b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = target
    · subst hx
      rw [demoteToEnd, if_pos rfl,
          dominated_snoc_irrelevant x a b xs hat hbt,
          isDominatedBy_skip x a b xs hat hbt]
    · by_cases ha : a = x <;> by_cases hb : b = x <;>
        simp [demoteToEnd, hx, isDominatedBy, ha, hb, ih]

/-- Corollary: if the ranking realizes a target relation on a pair of
non-demoted actions, the demoted ranking realizes the same relation
(Agda: demote-preserves-homomorphism). -/
theorem demote_preserves_homomorphism (target a b : Action)
    (xs : List Action) (Rel : Action → Action → Bool)
    (hat : a ≠ target) (hbt : b ≠ target)
    (heq : isDominatedBy xs a b = Rel a b) :
    isDominatedBy (demoteToEnd target xs) a b = Rel a b := by
  rw [demote_preserves_dominance target a b xs hat hbt]; exact heq

/-- The public runtime API (Agda: make-action-unavailable). -/
def makeActionUnavailable (forbidden : Action)
    (ranking : ExplicitRanking State Action) : ExplicitRanking State Action :=
  fun s => demoteToEnd forbidden (ranking s)

/-- The runtime API inherits the result pointwise at every state
(Agda: make-action-unavailable-preserves-dominance). -/
theorem makeActionUnavailable_preserves_dominance (forbidden a b : Action)
    (ranking : ExplicitRanking State Action) (s : State)
    (haf : a ≠ forbidden) (hbf : b ≠ forbidden) :
    isDominatedBy (makeActionUnavailable forbidden ranking s) a b
      = isDominatedBy (ranking s) a b :=
  demote_preserves_dominance forbidden a b (ranking s) haf hbf

end CSHRL

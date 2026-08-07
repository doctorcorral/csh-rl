/-
CSHRL portability kernel, Lean 4 port.
D5-D11, T2: the deterministic MDP interface, the two optimality conditions,
and the decomposition theorem.
-/

import CSHRL.Streams

namespace CSHRL

open Stream'

variable {R State Action : Type}

/-- D8: a ranking of actions at each state. -/
def Ranking (State Action : Type) : Type := State → Action → Action → Prop

section Core

variable (le : R → R → Prop)
variable (next : State → Action → State)
variable (reward : State → Action → R)
variable (value : State → Stream' R)

/-- D7: action-value stream = immediate reward consed onto the successor's
value stream. -/
def qvalue (s : State) (a : Action) : Stream' R :=
  cons (reward s a) (value (next s a))

/-- D9: the successor condition (paper: CoinductiveHomomorphism). -/
def CoinductiveHomomorphism (rank : Ranking State Action) (s : State) : Prop :=
  ∀ a b, rank s a b → Dominance le (value (next s a)) (value (next s b))

/-- D10: immediate-reward compatibility. -/
def RewardCompatible (rank : Ranking State Action) (s : State) : Prop :=
  ∀ a b, rank s a b → le (reward s a) (reward s b)

/-- D11: the action-value condition (paper: CoindHomo). -/
def CoindHomo (rank : Ranking State Action) (s : State) : Prop :=
  ∀ a b, rank s a b →
    Dominance le (qvalue next reward value s a) (qvalue next reward value s b)

/-- T2: the decomposition theorem (paper Theorem 2).  Since `head (cons r s)`
and `tail (cons r s)` reduce definitionally, the proof is a single
application of the unfolding lemma, exactly as in Agda and Rocq. -/
theorem decomposition (rank : Ranking State Action) (s : State) :
    CoindHomo le next reward value rank s ↔
      CoinductiveHomomorphism le next value rank s ∧
      RewardCompatible le reward rank s := by
  constructor
  · intro h
    constructor
    · intro a b hab
      exact (dominance_unfold.mp (h a b hab)).2
    · intro a b hab
      exact (dominance_unfold.mp (h a b hab)).1
  · rintro ⟨hc, hr⟩ a b hab
    exact dominance_unfold.mpr ⟨hr a b hab, hc a b hab⟩

end Core

end CSHRL

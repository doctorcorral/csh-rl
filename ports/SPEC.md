# CSHRL Portability Kernel — Specification

This document specifies the *portability kernel*: the minimal, system-agnostic
core of the CSHRL framework that every port must implement. It corresponds to
Sections 3–7 of the MICAI 2026 paper. The Agda development
(`src/CSHRL/…`) is the reference implementation.

The guiding fact (paper §8, *Stream Isomorphism*) is that coinductive stream
dominance is equivalent to pointwise dominance at every timestep. Systems with
native coinduction (Agda, Rocq) implement the coinductive form and prove the
equivalence; systems without it (Lean 4) may take the pointwise form as the
definition, at no loss of mathematical content.

## Definitions

| # | Name | Statement | Agda reference |
|---|------|-----------|----------------|
| D1 | Reward order | A type `R` with a relation `≤ᵣ : R → R → Prop` | `paper.lagda.tex` §3, `CSHRL.Core` |
| D2 | Stream | Infinite sequence over `R`, with `head`/`tail` (coinductive) or `ℕ → R` (functional) | `Codata.Guarded.Stream` |
| D3 | Stream dominance `⊑` | Coinductive: `head x ≤ᵣ head y` and `tail x ⊑ tail y` | `_≤ₛ_` |
| D4 | Pointwise dominance | `∀ n, x(n) ≤ᵣ y(n)` | `PointwiseDominance` |
| D5 | Deterministic MDP interface | `State`, `Action`, `next : State → Action → State`, `reward : State → Action → R` | `CSHRL.Core` |
| D6 | Value stream | `value : State → Stream R`, the capability profile of a state (best achievable reward at each depth). The kernel treats it as an abstract parameter; instantiations may construct it (`solve`) | `CSHRL.Core.solve` |
| D7 | Action-value stream | `qvalue s a = cons (reward s a) (value (next s a))` | `action-value` |
| D8 | Ranking | `rank : State → Action → Action → Prop`, intended as a total preorder (an element of S_{\|A\|} when strict and total) | `Ranking` |
| D9 | CoinductiveHomomorphism (successor condition) | `∀ a b, rank s a b → value (next s a) ⊑ value (next s b)` | `CoinductiveHomomorphism` |
| D10 | Reward compatibility | `∀ a b, rank s a b → reward s a ≤ᵣ reward s b` | — |
| D11 | CoindHomo (action-value condition) | `∀ a b, rank s a b → qvalue s a ⊑ qvalue s b` | `CoindHomo` |

## Theorems

| # | Name | Statement | Agda reference |
|---|------|-----------|----------------|
| T1 | Stream isomorphism | `x ⊑ y ↔ ∀ n, x(n) ≤ᵣ y(n)` | §8, `src/appendix/StreamIsomorphism.agda` |
| T2 | Decomposition | `CoindHomo s ↔ CoinductiveHomomorphism s ∧ RewardCompatible s` | Theorem 2 (§5) |
| T3 | Strict generality | In `BinarySacrifice`, the ranking `GoTrap ≼ GoParadise` satisfies CoinductiveHomomorphism at `Start`, and *no* ranking relating the two actions (in either direction) satisfies CoindHomo at `Start` | §6, `CSHRL.Tasks.Verified.BinarySacrifice` |
| T4 | Subsumption | Given `add`/`zero` with `add` monotone: a CoindHomo ranking dominates every partial sum of the action-value stream at every finite horizon (successor form for CoinductiveHomomorphism) | §7, `src/appendix/Arithmetic.agda` (`partial-sum-mono`, `subsumes-partial-sum`) |
| T5 | Learning kernel | For explicit list rankings: (a) `swap_fixes_pair` — the transposition repair makes the ranking agree with the oracle on the violated pair; (b) `state_updater_locality` — the state-specific updater touches only the violated state; (c) `demote_preserves_dominance` and `make_action_unavailable_preserves_dominance` — demotion preserves dominance among all other pairs (Remark 2, O(1) adaptation). Plus reflexivity and totality of the induced order | §14, `src/CSHRL/Learning/Base.agda` |
| T6 | Q-learning failure | In `BinarySacrifice`: GoTrap wins the immediate-reward comparison while GoParadise's successor dominates at every horizon (sums are exactly `N` versus `0`); hence Q-learning with γ < ½ selects the action with the strictly inferior successor | §7.2, `src/CSHRL/Analysis/QLearningFailure.agda` |

Note on T5: as in the Agda reference, the *global* violation-decrease
statement (`ViolationMonotonicityTheorem`) is an assumption record in
`Learning/Base.agda`, not a closed proof; it is therefore not part of the
kernel in any system. The kernel contains exactly the machine-checked swap
and demotion lemmas.

## Ports

| System | Directory | Style | Status |
|--------|-----------|-------|--------|
| Agda 2.8.0 | `src/CSHRL/` | coinductive records + copatterns, `--safe --guardedness` | reference (complete, beyond kernel) |
| Rocq 9.2 | `ports/rocq/` | negative coinductives (primitive projections), `cofix` | kernel (T1–T6) |
| Lean 4.32 | `ports/lean/` | functional streams (`Nat → R`), pointwise-first | kernel (T1–T6) |

In the Lean port, T1 takes the form of two facts that together carry the
coinductive content: `dominance_unfold` (pointwise dominance unfolds one step
exactly like the coinductive record) and `dominance_coind` (pointwise
dominance is the greatest relation closed under that unfolding, i.e. the
coinduction principle).

## Conformance

A port conforms to the kernel when it defines D1–D11 and proves T1–T6 without
axioms beyond the system's base theory (no `admit`/`sorry`/`postulate`).
Verified: Rocq via `Print Assumptions` (all theorems closed under the global
context); Lean via `#print axioms` (only the base-theory axioms `propext` and
`Quot.sound` appear; no `Classical.choice`, no `sorryAx`).

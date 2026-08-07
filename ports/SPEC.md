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
| D12 | Finite distribution monad | `Dist A = List (A × ℕ)` (unnormalized weights), with `pure`, `scale`, `map`, `bind`, mixture (`++`), `total_weight`, and the CDF `cdf_weight d r` (total weight of outcomes ≤ r) | `CSHRL.Probability.Finite` |
| D13 | Lexicographic dominance + stochastic condition | `x ≤lex y`: heads compare, tails compare *when heads are equal* (coinductive; functionally: at every position, agreement on all earlier positions implies ≤). `StochasticCoindHomo`: the ranking preserves `≤lex` on expected action-value streams | `CSHRL.Core.Stochastic` |
| D14 | FOSD and the SD[k] hierarchy | `μ FOSD≤ ν ⟺ ∀ r, cdf ν r ≤ cdf μ r`; `sd_weight k` = k-fold prefix sum of the CDF; `μ SD[k]≤ ν ⟺ ∀ r, sd_weight k ν r ≤ sd_weight k μ r`. SD[0] = FOSD, SD[1] = SOSD, SD[2] = TOSD | `CSHRL.Probability.FOSD`, `CSHRL.Probability.SD` |
| D15 | VerifiedRanking | An action ordering per state plus a proof that it preserves `SD[k]` on a marginal-reward function `State → Action → ℕ → Dist ℕ` at every timestep | `CSHRL.Core.Compose` |
| D16 | StateAbstraction | `project : Concrete → Abstract`, `embed : Abstract → Concrete`, with the section law `project ∘ embed = id` | `CSHRL.Core.Abstraction` |

## Theorems

| # | Name | Statement | Agda reference |
|---|------|-----------|----------------|
| T1 | Stream isomorphism | `x ⊑ y ↔ ∀ n, x(n) ≤ᵣ y(n)` | §8, `src/appendix/StreamIsomorphism.agda` |
| T2 | Decomposition | `CoindHomo s ↔ CoinductiveHomomorphism s ∧ RewardCompatible s` | Theorem 2 (§5) |
| T3 | Strict generality | In `BinarySacrifice`, the ranking `GoTrap ≼ GoParadise` satisfies CoinductiveHomomorphism at `Start`, and *no* ranking relating the two actions (in either direction) satisfies CoindHomo at `Start`. Same separation for `SkillInvestment` (Work vs Train at Novice) and `PreparationDilemma` (Rush vs Prepare at Idle), whose value streams are the verified `solve` characterizations | §6, `CSHRL.Tasks.Verified.{BinarySacrifice, SkillInvestment, PreparationDilemma}` |
| T4 | Subsumption | Given `add`/`zero` with `add` monotone: a CoindHomo ranking dominates every partial sum of the action-value stream at every finite horizon (successor form for CoinductiveHomomorphism) | §7, `src/appendix/Arithmetic.agda` (`partial-sum-mono`, `subsumes-partial-sum`) |
| T5 | Learning kernel | For explicit list rankings: (a) `swap_fixes_pair` — the transposition repair makes the ranking agree with the oracle on the violated pair; (b) `state_updater_locality` — the state-specific updater touches only the violated state; (c) `demote_preserves_dominance` and `make_action_unavailable_preserves_dominance` — demotion preserves dominance among all other pairs (Remark 2, O(1) adaptation). Plus reflexivity and totality of the induced order | §14, `src/CSHRL/Learning/Base.agda` |
| T6 | Q-learning failure | In `BinarySacrifice`: GoTrap wins the immediate-reward comparison while GoParadise's successor dominates at every horizon (sums are exactly `N` versus `0`); hence Q-learning with γ < ½ selects the action with the strictly inferior successor | §7.2, `src/CSHRL/Analysis/QLearningFailure.agda` |
| T7 | Convergence of swap learning (**closed**) | For an explicit list ranking and a total, transitive boolean oracle: (a) `swap_adjacent_decreases` — repairing a violated *adjacent* pair (a transposition, generator of S_n) decreases the violation count by exactly 1; (b) `fix_first_progress` — the first-violation repair either certifies zero violations or strictly decreases them; (c) `swap_convergence_bound` — iterating the repair reaches zero violations within `C(n,2)` steps; (d) `violations_zero_iff` — zero violations means the ranking realizes the oracle on *every* ordered pair (the homomorphism property). This CLOSES the statement that is an assumption record (`ViolationMonotonicityTheorem`) in the Agda reference | §14 (bound `\|S\|·C(\|A\|,2)` per state); Rocq/Lean `Convergence` |
| T8 | Pointwise ⇒ lexicographic | `x ⊑ y → x ≤lex y`: every deterministic verification transfers to the stochastic order for free; a ranking preserving pointwise dominance of expected streams is a `StochasticCoindHomo` | `CSHRL.Core.Stochastic` (`pointwise→lex`) |
| T9 | SD hierarchy + closure | (a) `SD_subsumes`: `SD[k] ⇒ SD[k+1]` (prefix sums preserve dominance); (b) `sd_weight` is linear (distributes over `++` and `scale`), hence FOSD and every `SD[k]` are closed under mixture and reward scaling | `CSHRL.Probability.SD`, `CSHRL.Probability.Compose` |
| T10 | Convolution closure | If `μ₁ FOSD≤ ν₁` (equal total weights) and `μ₂ FOSD≤ ν₂` then `conv μ₁ μ₂ FOSD≤ conv ν₁ ν₂`, and the closure lifts to every `SD[k]`. Proof by discrete Abel summation: the CDF of a convolution is a generalized weighted sum of shifted CDFs; monotone direction pointwise, base direction by induction on the support bound | `CSHRL.Probability.Convolution` (`FOSD-conv`, `FOSD→SD-conv`) |
| T11 | Ranking algebra | VerifiedRankings compose: hierarchy subsumption (k → k+1), product composition for any SD[k]-preserving operation (mixture `++`, convolution, scaling as instances), and sum composition for disjoint environments | `CSHRL.Core.Compose` |
| T12 | Abstraction lifting | Under marginal-invariance (same abstract class ⇒ same marginals), `abstract_lift` transfers a VerifiedRanking from the abstract to the concrete system; abstractions compose (identity, product, vertical), and combine with the convolution product (`abstract_conv_product`) | `CSHRL.Core.Abstraction` |

Note on T7: the Rocq and Lean ports prove the convergence theorem in
*closed* form for the adjacent-transposition repair; in the Agda reference
the corresponding global statement is still an assumption record
(`ViolationMonotonicityTheorem` in `Learning/Base.agda`). T7 is therefore
the one place where the ports are ahead of the reference.

## Ports

| System | Directory | Style | Status |
|--------|-----------|-------|--------|
| Agda 2.8.0 | `src/CSHRL/` | coinductive records + copatterns, `--safe --guardedness` | reference (complete, except T7 which is an assumption record) |
| Rocq 9.2 | `ports/rocq/` | negative coinductives (primitive projections), `cofix`; T1–T6 use only Init, milestone-3 files (D12–D16, T7–T12) use the axiom-free Stdlib + `lia` | kernel (T1–T12) |
| Lean 4.32 | `ports/lean/` | functional streams (`Nat → R`), pointwise-first; core library only | kernel (T1–T12) |

In the Lean port, T1 takes the form of two facts that together carry the
coinductive content: `dominance_unfold` (pointwise dominance unfolds one step
exactly like the coinductive record) and `dominance_coind` (pointwise
dominance is the greatest relation closed under that unfolding, i.e. the
coinduction principle).

## Conformance

A port conforms to the kernel when it defines D1–D16 and proves T1–T12 without
axioms beyond the system's base theory (no `admit`/`sorry`/`postulate`).
Verified continuously by `theories/AxiomCheck.v` and `CSHRL/AxiomCheck.lean`:
Rocq via `Print Assumptions` (all 34 checked theorems closed under the global
context); Lean via `#print axioms` (only the base-theory axioms `propext`,
`Quot.sound`, and `Classical.choice` — the latter introduced by `omega` —
appear; no `sorryAx`).

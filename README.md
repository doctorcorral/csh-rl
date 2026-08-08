# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

[![Version 0.5.0](https://img.shields.io/badge/version-0.5.0-blue.svg)](VERSION)

A novel foundational framework for reinforcement learning that redefines optimality as **structure preservation** rather than scalar maximization.

## The Paper

The paper is a **literate Agda document**—compiling it type-checks all embedded code while producing the PDF:

```bash
cd literate
make all
```

This produces:
- `literate/CSHRL.pdf` — The main paper
- `literate/CSHRL-Appendix.pdf` — Extended proofs (subsumption, stream isomorphism, stochastic subsumption, FOSD conjecture)

**Requirements:** Agda 2.7.x, Agda StdLib 2.0, LuaLaTeX

## Key Claims (Machine-Verified)

1. **Subsumption:** The coinductive homomorphism implies classical argmax optimality for any finite horizon
2. **Monotonic Learning:** Ranking updates via violation-correction converge in at most |S| × C(|A|,2) swaps
3. **Instant Adaptation:** When actions become unavailable, the next-best action is O(1) lookup
4. **Stochastic Extension:** Rankings preserve expected stream dominance via the Giry monad
5. **Scalable EC-based Verification:** The CombinatorialPlacementMDP environment class provides a fully automatic trace-to-stream bridge, demonstrated with a full `CoindHomo` for the 8-Queens problem (8⁸ search space, zero postulates, `--safe`)

## Description

CSHRL redefines optimality not as maximizing a scalar reward sum, but as preserving a **coinductive symmetric homomorphism** between action rankings and infinite future streams. If action *a* is ranked below action *b*, then at every future timestep t = 0, 1, 2, ..., the reward from *a*'s trajectory must be dominated by *b*'s.

This structural approach:
- Eliminates the discount factor γ (no arbitrary future-devaluation)
- Dissolves the exploration/exploitation dichotomy (full rankings require full understanding)
- Enables O(1) adaptation when actions become unavailable
- Provides monotonic convergence guarantees
- Extends naturally to stochastic environments via the Giry monad
- Scales to non-trivial combinatorial problems (8-Queens verified with zero postulates)

## Installation

**Prerequisites:**
- Agda 2.7.x (2.7.0 recommended). Note: Agda 2.8.0 has a known serialization bug.
- Agda Standard Library 2.0

**Setup:**
```bash
git clone https://github.com/doctorcorral/csh-rl.git
cd csh-rl
```

Load `src/CSHRL/Core.agda` in your editor (e.g., Emacs with agda-mode: `C-c C-l`).

## Code Structure

```
src/
├── All.agda                          # Master import
├── CSHRL/
│   ├── Core.agda                     # Coinductive homomorphism theory
│   ├── Core/
│   │   └── Stochastic.agda           # Stochastic extension (Giry monad)
│   ├── Finder.agda                   # Symmetry restoration algorithm
│   ├── Probability/
│   │   └── Finite.agda               # Finite distribution monad
│   ├── EnvironmentClass/
│   │   ├── FiniteDeterministicMDP.agda
│   │   ├── CombinatorialPlacementMDP.agda
│   │   └── StochasticFiniteMDP.agda
│   ├── Learning/
│   │   ├── Base.agda                 # Universal learning infrastructure
│   │   ├── FiniteDeterministicMDP.agda  # Reuses EC, adds learning loop
│   │   ├── CombinatorialPlacementMDP.agda  # Placement learning (short-circuit traces)
│   │   └── StochasticFiniteMDP.agda  # Stochastic learning (expected traces)
│   └── Tasks/
│       ├── Classic/                  # Pedagogical examples (may use postulate)
│       │   ├── DelayedGratification.agda
│       │   ├── Energy.agda
│       │   ├── KeyDoor.agda
│       │   ├── Maze.agda
│       │   ├── Queens.agda
│       │   └── Trap.agda
│       ├── Verified/                 # Fully machine-checked (no postulates)
│       │   │
│       │   │   # Core Tasks
│       │   ├── TwoState.agda              # Minimal 2-state MDP
│       │   ├── OnePlacement.agda          # Single-slot placement
│       │   ├── Queens1.agda               # 1-queen (trivial case)
│       │   ├── Queens8.agda               # Full 8-Queens CoindHomo (--safe)
│       │   ├── Sudoku4.agda               # 4x4 Sudoku puzzle solving (--safe)
│       │   ├── GridWorld5x5.agda          # 25-state navigation
│       │   │
│       │   │   # Learning Demos
│       │   ├── TwoStateLearning.agda      # Learning on TwoState MDP
│       │   ├── CurriedLearnerDemo.agda    # Checkpointing, traces, active learning
│       │   ├── ActiveRefinementDemo.agda  # Swap-based ranking updates
│       │   ├── DelayedGratificationLearning.agda  # Marshmallow test analysis
│       │   │
│       │   │   # KeyTreasure Suite (flagship)
│       │   ├── KeyTreasure10x10.agda      # 100-state key-door-treasure
│       │   ├── KeyTreasureViolations.agda # Machine-verified monotonicity
│       │   └── KeyTreasureTests.agda      # Concrete test assertions
│       └── Stochastic/                # Stochastic MDPs (Giry monad)
│           ├── CoinFlip.agda              # 2-state coin flip MDP
│           ├── GamblersRuin.agda          # Classic absorbing chain
│           ├── RandomWalk.agda            # 1D symmetric random walk
│           └── BiasedBandit.agda          # Two-armed bandit with bias
├── appendix/
│   ├── Arithmetic.agda               # Subsumption proof extensions
│   ├── PreservationEquivalence.agda  # Pedagogical equivalences
│   ├── StreamIsomorphism.agda        # x ≤ₛ y ⟺ ∀n. xₙ ≤ yₙ
│   └── StochasticSubsumption.agda    # Stochastic argmax subsumption
│
literate/
├── CSHRL.lagda.tex                   # Main paper (literate Agda)
├── CSHRL-Appendix.lagda.tex          # Appendix document
├── Makefile                          # Build system
└── agda-spec.sty                     # Styling for spec blocks
```

### Framework Core

- **Core.agda:** Coinductive optimal value, action-value streams, stream dominance `_≤ₛ_`, and `CoindHomo` record
- **Finder.agda:** Lexicographic trace comparison for symmetry discovery

### Probability & Stochastic Extension

- **Probability/Finite.agda:** Finite distribution monad (Giry monad for discrete probability). Provides `Dist A`, monadic operations (`pure`, `>>=`, `fmap`), expected value computation.
- **Core/Stochastic.agda:** Lifts the coinductive homomorphism to stochastic environments. Defines `StochasticCoindHomo` where rankings preserve **expected** stream dominance.

### Environment Classes

Reusable templates bundling structure requirements, finder algorithms, and preservation proof machinery:

- **FiniteDeterministicMDP:** For grid worlds, mazes, navigation tasks
- **CombinatorialPlacementMDP:** For constraint satisfaction (N-Queens, etc.). Provides automatic trace-to-stream bridge via `WithTraceBridge`
- **StochasticFiniteMDP:** For stochastic MDPs with probabilistic transitions

### Learning Infrastructure

Each Learning module imports and re-exports its corresponding Environment Class, then layers learning-specific infrastructure on top:

- **Base.agda:** EC-independent definitions: `Ranking`, `Violation`, `LearnerState`, swap-based updates, convergence theorem
- **FiniteDeterministicMDP.agda:** Violation detection and learning loop for deterministic MDPs
- **CombinatorialPlacementMDP.agda:** Placement learning with short-circuit traces for absorbing states (Dead/Solved)
- **StochasticFiniteMDP.agda:** Stochastic learning using expected trace comparison

All learning modules provide:
- **Passive learning:** Increase depth on violation detection
- **Active refinement:** Swap rankings directly for faster convergence
- **Curried interface:** Checkpointing, incremental training, training traces
- **Unavailability handling:** O(1) adaptation when actions fail
- **Proven guarantees:** Monotonic violation decrease, bounded convergence

## Citation

```bibtex
@article{corral2026cshrl,
  title={Coinductive Symmetric Homomorphism Reinforcement Learning: 
         A New Foundation Where Optimality Is Pure Structure},
  author={Corral-Corral, Ricardo},
  year={2026}
}
```

## Future Work

- **Continuous distributions:** Extend the Giry monad to continuous state/action spaces
- **Risk-aware objectives:** CVaR, variance-penalized, and distributional RL extensions
- **Neural Approximations:** DNN-based ranking prediction
- **Quantum Implementations:** Amplitude amplification for violation detection

Contributions welcome—fork and PR!

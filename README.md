# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

[![Version 0.3.3](https://img.shields.io/badge/version-0.3.3-blue.svg)](VERSION)

A novel foundational framework for reinforcement learning that redefines optimality as **structure preservation** rather than scalar maximization.

## The Paper

The paper is a **literate Agda document**—compiling it type-checks all embedded code while producing the PDF:

```bash
cd literate
make all
```

This produces:
- `literate/CSHRL.pdf` — The main paper
- `literate/CSHRL-Appendix.pdf` — Extended proofs (subsumption theorem, preservation equivalence)

**Requirements:** Agda 2.7.x, Agda StdLib 2.0, LuaLaTeX

## Key Claims (Machine-Verified)

1. **Subsumption:** The coinductive homomorphism implies classical argmax optimality for any finite horizon
2. **Monotonic Learning:** Ranking updates via violation-correction converge in at most |S| × C(|A|,2) swaps
3. **Instant Adaptation:** When actions become unavailable, the next-best action is O(1) lookup

## Description

CSHRL redefines optimality not as maximizing a scalar reward sum, but as preserving a **coinductive symmetric homomorphism** between action rankings and infinite future streams. If action *a* is ranked below action *b*, then at every future timestep t = 0, 1, 2, ..., the reward from *a*'s trajectory must be dominated by *b*'s.

This structural approach:
- Eliminates the discount factor γ (no arbitrary future-devaluation)
- Dissolves the exploration/exploitation dichotomy (full rankings require full understanding)
- Enables O(1) adaptation when actions become unavailable
- Provides monotonic convergence guarantees

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
│   ├── Finder.agda                   # Symmetry restoration algorithm
│   ├── EnvironmentClass/
│   │   ├── FiniteDeterministicMDP.agda
│   │   └── CombinatorialPlacementMDP.agda
│   ├── Learning/
│   │   ├── Base.agda                 # Universal learning infrastructure
│   │   └── FiniteDeterministicMDP.agda
│   └── Tasks/
│       ├── Classic/                  # Pedagogical examples (may use postulate)
│       │   ├── DelayedGratification.agda
│       │   ├── Energy.agda
│       │   ├── KeyDoor.agda
│       │   ├── Maze.agda
│       │   ├── Queens.agda
│       │   └── Trap.agda
│       └── Verified/                 # Fully machine-checked (no postulates)
│           │
│           │   # Core Tasks
│           ├── TwoState.agda              # Minimal 2-state MDP
│           ├── OnePlacement.agda          # Single-slot placement
│           ├── Queens1.agda               # 1-queen (trivial case)
│           ├── GridWorld5x5.agda          # 25-state navigation
│           │
│           │   # Learning Demos
│           ├── TwoStateLearning.agda      # Learning on TwoState MDP
│           ├── CurriedLearnerDemo.agda    # Checkpointing, traces, active learning
│           ├── ActiveRefinementDemo.agda  # Swap-based ranking updates
│           ├── DelayedGratificationLearning.agda  # Marshmallow test analysis
│           │
│           │   # KeyTreasure Suite (flagship)
│           ├── KeyTreasure10x10.agda      # 100-state key-door-treasure
│           ├── KeyTreasure10x10Data.agda  # Tabular data extraction
│           └── KeyTreasureViolations.agda # Machine-verified monotonicity
├── appendix/
│   ├── Arithmetic.agda               # Subsumption proof extensions
│   └── PreservationEquivalence.agda  # Pedagogical equivalences
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

### Environment Classes

Reusable templates bundling structure requirements, finder algorithms, and preservation proof machinery:

- **FiniteDeterministicMDP:** For grid worlds, mazes, navigation tasks
- **CombinatorialPlacementMDP:** For constraint satisfaction (N-Queens, etc.)

### Learning Infrastructure

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

- **Stochastic Environments:** Extension via the Giry monad
- **Continuous State/Action Spaces:** Metric space parameterization
- **Neural Approximations:** DNN-based ranking prediction
- **Quantum Implementations:** Amplitude amplification for violation detection

Contributions welcome—fork and PR!

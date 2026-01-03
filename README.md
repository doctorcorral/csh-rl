# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

[![Version 0.2.0](https://img.shields.io/badge/version-0.2.0-blue.svg)](VERSION)

This repository contains the source code and paper for "Coinductive Symmetric Homomorphism Reinforcement Learning: A New Foundation Where Optimality Is Pure Structure" by Ricardo Corral-Corral.

## Description

CSHRL is a novel foundational framework for reinforcement learning that redefines optimality not as maximizing a scalar reward sum, but as preserving a coinductive symmetric homomorphism between action rankings and infinite future streams. This structural approach automatically handles constraints, exploration, and long-term credit assignment, and is verified in Agda.
The paper introduces the theory, provides Agda proofs, and demonstrates it in concrete environments like mazes and key-door-treasure worlds. The code is modular, parameterized, and ready for extension. Tasks can be machine-verified once they are instantiated under an Environment Class (EC) that packages both a verified solver and the preservation proof.

Key contributions:

- A coinductive definition of optimality as symmetry preservation.
- Machine-verified core in Agda.
- The "Symmetry Restoration Algorithm" for discovering optimal rankings.
- Instantaneous "flips" for hierarchical planning without value propagation.
- Environment Classes (ECs) let you reuse solver + proof patterns for families of environments.

### Installation

Prerequisites

- Agda 2.7.x (recommended) or 2.7.0 specifically. Note: Agda 2.8.0 has a known serialization bug that prevents compilation.
- Agda Standard Library 2.0.

No other dependencies—pure Agda!

### Setup

Clone the repo:
```
git clone https://github.com/doctorcorral/csh-rl.git
cd csh-rl/main
```
Open in your editor (e.g., Emacs with agda-mode: `M-x` `agda-mode`).
Load the core: `C-c C-l` in `CSHRL.Core.agda` (it should type-check instantly).

### Usage

Verifying the Core Theory

Load `CSHRL.Core.agda` in Agda.
The optimality theorem is `machine-checked—try` normalizing it with `C-c C-n` to see it unfold.
Extend with your own environments: define step and `_≤ᵣ_` for your MDP, instantiate CoindHomo, and the proof holds for free.

#### Running the Finder Algorithm

Load `CSHRL.Tasks.DelayedGratification.agda`.
Evaluate `test-ranking-2` with `C-c C-n` to see the symmetry flip in action.

### Code Structure

```
src/
├── All.agda                          # Master import
├── CSHRL/
│   ├── Core.agda                     # The coinductive homomorphism theory
│   ├── Finder.agda                   # The symmetry restoration algorithm
│   ├── EnvironmentClass/
│   │   ├── FiniteDeterministicMDP.agda
│   │   └── CombinatorialPlacementMDP.agda
│   └── Tasks/
│       ├── Classic/
│       │   ├── DelayedGratification.agda # Sparse reward / Marshmallow test
│       │   ├── Energy.agda               # Desert crossing (resource management)
│       │   ├── KeyDoor.agda              # Hierarchical planning (tool use)
│       │   ├── Maze.agda                 # Simple 1D navigation
│       │   ├── Queens.agda               # N-Queens (combinatorial constraints)
│       │   └── Trap.agda                 # Trap avoidance (greedy vs patient)
│       └── Verified/
│           ├── TwoState.agda            # Verified FDMDP instantiation
│           ├── OnePlacement.agda        # Verified combinatorial placement
│           └── Queens1.agda             # Verified Queens1 using EC
└── appendix/
    └── PreservationEquivalence.agda  # Pedagogical proofs
```

#### Framework Core (`CSHRL/`):

- `Core.agda`: Coinductive optimal value, action-value, stream dominance `_≤ₛ_`, and `CoindHomo` record.
- `Finder.agda`: The symmetry restoration algorithm using ordinal value iteration.

#### Environment Classes (`CSHRL/EnvironmentClass/`):

- `FiniteDeterministicMDP.agda`: Ordinal value iteration + preservation template for any finite deterministic MDP.
- `CombinatorialPlacementMDP.agda`: Constraint-placement EC with absorbing Dead/Solved analysis so Queens-like tasks reuse the solver/proof.

#### Task Implementations (`CSHRL/Tasks/`):

- `Classic/*`: Pedagogical examples that may rely on `postulate`.
- `Verified/*`: Fully machine-checked instances built by instantiating the ECs (see below).

#### Verified Tasks (`CSHRL/Tasks/Verified/`):

- `TwoState.agda`: Fully verified FDMDP instantiation.
- `OnePlacement.agda`: Verified combinatorial placement example.
- `Queens1.agda`: Verified Queens instantiation built on the combinatorial EC.

### Citation
If you use this work, please cite:

```
@article{corral2025cshrl,
  title={Coinductive Symmetric Homomorphism Reinforcement Learning: A New Foundation Where Optimality Is Pure Structure},
  author={Corral-Corral, Ricardo},
  year={2025}
}
```

### Future Work

- Full permutation groups for explicit symmetries.
- Neural approximations for learned rankings.
- Quantum implementations for large action spaces.

Contributions welcome—fork and PR!

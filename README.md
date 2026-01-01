# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

[![Version 0.2.0](https://img.shields.io/badge/version-0.2.0-blue.svg)](VERSION)

This repository contains the source code and paper for "Coinductive Symmetric Homomorphism Reinforcement Learning: A New Foundation Where Optimality Is Pure Structure" by Ricardo Corral-Corral.

## Description

CSHRL is a novel foundational framework for reinforcement learning that redefines optimality not as maximizing a scalar reward sum, but as preserving a coinductive symmetric homomorphism between action rankings and infinite future streams. This structural approach automatically handles constraints, exploration, and long-term credit assignment, and is verified in Agda.
The codebase is structured so that **tasks can be fully machine-verified** once they are instantiated under an **Environment Class (EC)** that provides both:

- a **verified solver / policy finder** (“learning” for that EC), and
- a **generic preservation proof** (`CoindHomo.preserves`) that discharges the coinductive optimality obligations for all instances of that EC.

Key contributions:

- A coinductive definition of optimality as symmetry preservation.
- Machine-verified core in Agda.
- Environment Classes (ECs): reusable, verified *families* of environments with solvers and preservation proofs.
- Instantaneous "flips" for hierarchical planning without value propagation.
- **Curried Learner**: Stateful, checkpoint-friendly learning with training traces for analysis.

### Installation

Prerequisites

- Agda 2.6.4 or later.
- Agda Standard Library 2.0.

No other dependencies—pure Agda!

### Setup

Clone the repo:
```
git clone https://github.com/doctorcorral/csh-rl.git
cd csh-rl
```
Open in your editor (e.g., Emacs with agda-mode).
Load the master entrypoint: `src/All.agda`.

### Usage

Load `src/All.agda`. This includes:

- `CSHRL.Core`: the coinductive theory (`CoindHomo`, stream order `_≤ₛ_`, etc.)
- `CSHRL.EnvironmentClass.*`: Environment Classes (ECs)
- `CSHRL.Tasks.Verified.*`: fully verified task instances (typically `--safe`)
- `CSHRL.Tasks.Classic.*`: pedagogical tasks that may use `postulate`

If you want a CLI sanity check (assuming Agda is on your PATH):
```
agda -i src src/All.agda
```

### Code Structure

```
src/
├── All.agda                          # Master import (verified + classic)
├── CSHRL/
│   ├── Core.agda                     # The coinductive homomorphism theory
│   ├── Finder.agda                   # Historical/standalone finder (not EC-specific)
│   ├── EnvironmentClass/             # Environment Classes (ECs): solver + preserves
│   │   ├── FiniteDeterministicMDP.agda
│   │   └── CombinatorialPlacementMDP.agda
│   ├── Learning/                     # Learning infrastructure
│   │   ├── Base.agda                 # Universal: LearnerState, curried interface
│   │   └── FiniteDeterministicMDP.agda  # FDMDP-specific: traces, violations
│   └── Tasks/
│       ├── Classic/                  # Pedagogical tasks (may use postulates)
│       │   ├── DelayedGratification.agda
│       │   ├── Energy.agda
│       │   ├── KeyDoor.agda
│       │   ├── Maze.agda
│       │   ├── Queens.agda
│       │   └── Trap.agda
│       └── Verified/                 # Fully verified tasks (instantiate an EC)
│           ├── TwoState.agda
│           ├── TwoStateLearning.agda
│           ├── DelayedGratificationLearning.agda
│           ├── GridWorld5x5.agda
│           ├── KeyTreasure10x10.agda
│           ├── CurriedLearnerDemo.agda
│           ├── OnePlacement.agda
│           └── Queens1.agda
└── appendix/
    └── PreservationEquivalence.agda  # Pedagogical proofs
```

#### Framework Core (`CSHRL/`):

- `Core.agda`: Coinductive optimal value, action-value, stream dominance `_≤ₛ_`, and `CoindHomo` record.
- `EnvironmentClass/*`: **Environment Classes (ECs)**. An EC packages:
  - an environment family (state/action/reward + structure like finiteness/horizon), and
  - a **verified solver** (policy/ranking finder) plus the **`preserves` proof interface** so instances become fully verified.

#### Learning Infrastructure (`CSHRL/Learning/`):

The learning module provides a **curried, stateful** interface for incremental learning with checkpointing:

- `Base.agda`: Universal (EC-independent) components:
  - `LearnerState`: Record with `current-depth`, `samples-seen`, `violations-seen`, `last-violation`
  - `Learner`: Type alias for `LearnerState → Sample → LearnerState`
  - `make-learner`, `learn-many`, `checkpoint`, `has-stabilized`, `training-trace`
  
- `FiniteDeterministicMDP.agda`: FDMDP-specific learning:
  - `fdmdp-learner`, `new-fdmdp-learner`, `train-step`, `train-batch`
  - `current-ranking`, `current-ranking-restricted`
  - `training-trace`, `depth-history`, `violation-history`

**Benefits of the curried design:**
1. **Checkpointing**: Just save the `LearnerState` record (4 numbers)
2. **Incremental learning**: Process samples one at a time
3. **Training traces**: Get full history for analysis/plotting
4. **Composability**: Chain `train-batch`, `checkpoint`, `current-ranking` freely
5. **No performance penalty**: Same computations, better organization

Example usage:
```agda
-- Initialize
learner₀ = new-fdmdp-learner

-- Train incrementally
learner₁ = train-step learner₀ sample₁
learner₂ = train-step learner₁ sample₂

-- Checkpoint
ckpt = checkpoint learner₂

-- Resume later
learner₃ = train-step ckpt sample₃

-- Get training trace for plotting
trace = training-trace learner₀ samples
depths = depth-history trace
```

#### Task Implementations (`CSHRL/Tasks/`):

- `Classic/*`: tutorial/paper-style environments; often concise but may use `postulate`.
- `Verified/*`: fully machine-checked tasks built by instantiating an EC (no postulates).

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

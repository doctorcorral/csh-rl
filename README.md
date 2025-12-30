# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

[![Version 0.1.1](https://img.shields.io/badge/version-0.1.1-blue.svg)](VERSION)

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
├── AllSafe.agda                      # Optional: fully verified subset entrypoint
├── CSHRL/
│   ├── Core.agda                     # The coinductive homomorphism theory
│   ├── Finder.agda                   # Historical/standalone finder (not EC-specific)
│   ├── EnvironmentClass/             # Environment Classes (ECs): solver + preserves
│   │   ├── FiniteDeterministicMDP.agda
│   │   └── CombinatorialPlacementMDP.agda
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

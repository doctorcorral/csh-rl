# Coinductive Symmetric Homomorphism Reinforcement Learning (CSHRL)

This repository contains the source code and paper for "Coinductive Symmetric Homomorphism Reinforcement Learning: A New Foundation Where Optimality Is Pure Structure" by Ricardo Corral-Corral.

## Description

CSHRL is a novel foundational framework for reinforcement learning that redefines optimality not as maximizing a scalar reward sum, but as preserving a coinductive symmetric homomorphism between action rankings and infinite future streams. This structural approach automatically handles constraints, exploration, and long-term credit assignment, and is verified in Agda.
The paper introduces the theory, provides Agda proofs, and demonstrates it in concrete environments like mazes and key-door-treasure worlds. The code is modular, parameterized, and ready for extension.

Key contributions:

- A coinductive definition of optimality as symmetry preservation.
- Machine-verified core in 58 lines of Agda.
- The "Symmetry Restoration Algorithm" for discovering optimal rankings.
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
cd csh-rl/main
```
Open in your editor (e.g., Emacs with agda-mode: `M-x` `agda-mode`).
Load the core: `C-c C-l` in `CSHRL-Core.agda` (it should type-check instantly).

### Usage

Verifying the Core Theory

Load `CSHRL-Core.agda` in Agda.
The optimality theorem is `machine-checked—try` normalizing it with `C-c C-n` to see it unfold.
Extend with your own environments: define step and `_≤ᵣ_` for your MDP, instantiate CoindHomo, and the proof holds for free.

#### Running the Finder Algorithm

Load `CSHRL-Finder-Test.agda`.
Evaluate `test-ranking-2` with `C-c C-n` to see the symmetry flip in action.

### Code Explanation

#### The core is in CSHRL-Core.agda (58 lines):

- `value`: Coinductive rollout of constant policies.
- `_≤ₛ_`: Coinductive stream dominance.
- `CoindHomo`: The homomorphism record, with state-dependent ranking, strict distinction, and preservation.
- `optimality`: The theorem proving top-ranked actions dominate coinductively.

#### Extensions:

- `CSHRL-Maze.agda`: Instantiates for a 1D grid world.
- `CSHRL-KeyDoor.agda`: Handles hierarchical planning via symmetry flips.
- `CSHRL-Finder-Test.agda`: Tests the ordinal symmetry finder.


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
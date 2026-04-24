# Synthex

A high-performance, concurrent synthesis engine for Continuous State Homomorphism Reinforcement Learning (CSHRL).

## Architecture

Synthex is designed to overcome the combinatorial explosion that occurs when trying to synthesize continuous control policies (Boolean Predicate Programs) inside dependent type theory normalizers like Agda. 

It acts as a **Concurrent Explorer**. It finds mathematically pure, gridless Coinductive Homomorphism (`CoindHomo`) Pairwise Rankings by aggressively map-reducing millions of candidates across the host machine's CPU cores using Elixir's `Flow` and `GenStage`. The discovered predicates are then brought back into Agda to be instantly verified and structurally composed into a `RankTree`.

### Core Modules

* **`Synthex.Environment`**: A strict behaviour defining the physics (ODE) and constraints of a continuous state space. Implementing a new environment (like LunarLander or MountainCar) only requires defining its `step`, `penalty`, `starts`, and `actions`.
* **`Synthex.Oracle`**: A pure functional oracle that performs multi-step rollouts ($K$) to determine the theoretically superior action for any given state, regardless of the environment.
* **`Synthex.StateCEGAR`**: The core execution engine. It implements the Counter-Example Guided Inductive Synthesis loop.
  * **Inner Loop (CEGIS):** Evaluates millions of candidate predicates against a small list of "anchor" states. Uses `Flow` to stream candidates and bound memory usage, completely preventing Out-Of-Memory (OOM) crashes even at Depth 2 or 3.
  * **Outer Loop (CEGAR):** Rolls out the winning candidate. If it contradicts the Oracle at any point in the continuous trajectory, that specific failing state is added to the anchors, and the loop repeats.
* **`Synthex.PairwiseMatrix`**: The master orchestrator. Given an environment with $N$ actions, it automatically generates the $N(N-1)/2$ independent pairwise combinations and spins up isolated `StateCEGAR` pipelines to synthesize the full relational matrix required by the Agda `RankTree` proof.

## Usage

To synthesize the full Pairwise RankTree for an environment:

```elixir
# solve(env_module, depth \\ 1, max_coeff \\ 3, max_fuel \\ 100)
Synthex.PairwiseMatrix.solve(Synthex.Envs.MountainCar, 1, 3, 100)
```

You can run this directly via the CLI:
```bash
mix run run_mountaincar_matrix.exs
```

## Integrating with Agda

Once Synthex outputs the solved Pairwise Matrix:
```elixir
🏆 FULL RANKTREE MATRIX SYNTHESIS COMPLETE!
:push_left >= :no_action  =>  {:and, {:feat, {:axis, ...}}, ...}
```

1. Translate the resulting Elixir tuples into the corresponding Agda `PredProg` DSL in your environment's `Pairwise` module.
2. Hook them into the `PairwiseRanking4` (or `3`) module.
3. Run `agda --check`. The typechecker will instantaneously verify the `preserves` field of the `CoindHomo` relation, guaranteeing absolute theoretical purity.
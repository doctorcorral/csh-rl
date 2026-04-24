# BipedalWalker-v3 — Binary-weighted continuous action synthesis
#
# CSHRL-grounded: each bit is an independent 2-action problem
# with CoindHomo-preserving predicate partition.
#
# 3 bits/dim × 4 dims = 12 predicates
# 8 levels per dimension in [-1, 1]
#
# Uses Synthex feature generation + CEGAR + coordinate descent
# through the standard GymOracle infrastructure.

Synthex.BinaryGym.solve(
  env: :bipedal,
  max_steps: 1600,
  depth: 1,
  max_coeff: 5,
  n_episodes: 30,
  top_k: 20,
  max_iters: 5,
  cegar_rounds: 3
)

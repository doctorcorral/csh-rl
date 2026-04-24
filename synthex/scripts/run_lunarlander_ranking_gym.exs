# CSHRL-native ranking synthesis for LunarLander-v3.
#
# Phase 1: Coordinate descent (like ChainGym) to find predicates + top actions.
# Phase 2: Full ranking determination per region via episode reward.
#
# 4 actions → 24 possible full rankings.
# Priority for coord descent: fire_left > fire_right > fire_main > do_nothing

Synthex.RankingGym.solve(
  [:fire_left, :fire_right, :fire_main, :do_nothing],
  env: :lunarlander,
  max_steps: 1000,
  depth: 1,
  max_coeff: 5,
  n_episodes: 200,
  top_k: 30,
  max_iters: 5,
  cegar_rounds: 3
)

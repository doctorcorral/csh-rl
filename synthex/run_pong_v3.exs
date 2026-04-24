# Pong synthesis v3 — improved parameters
#
# Changes from run_pong.exs:
#   n_episodes:   20 → 50  (better evaluation signal for adversarial env)
#   max_coeff:     5 → 10  (richer linear predicates)
#   depth:         1 → 2   (Boolean combinations of features)
#   max_iters:     3 → 5   (more coordinate descent passes)
#   cegar_rounds:  3 → 5   (more feature refinement)
#   top_k:        20 → 30  (keep more candidates per round)
#
# Previous best: 164/500 wins (32.8%), avg reward -2.8

actions = [:up, :noop, :down]

Synthex.RankingGym.solve(actions,
  env: :pong,
  max_steps: 10_000,
  depth: 2,
  max_coeff: 10,
  n_episodes: 50,
  top_k: 30,
  max_iters: 5,
  cegar_rounds: 5
)

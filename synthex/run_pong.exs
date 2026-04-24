# Pong synthesis via coordinate descent + full ranking
#
# ALE/Pong-v5 with RAM observations
# State: [ball_x, ball_y, player_y, ball_vx, ball_vy, enemy_y] (6D)
# Actions: UP(0), NOOP(1), DOWN(2)
# 3 actions → 2 predicates in priority chain
#
# Pong episodes are long (~5k steps for a full game to 21).
# Reward: +1/-1 per point, total ranges from -21 to +21.

actions = [:up, :noop, :down]

Synthex.RankingGym.solve(actions,
  env: :pong,
  max_steps: 10_000,
  depth: 1,
  max_coeff: 5,
  n_episodes: 20,
  top_k: 20,
  max_iters: 3,
  cegar_rounds: 3
)

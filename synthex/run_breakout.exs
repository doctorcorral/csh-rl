# Breakout (ALE/Breakout-v5): 3 effective actions (right/noop/left), 5D RAM state
# State: [ball_x, ball_y, paddle_x, ball_dx, ball_dy]
# FIRE is automatic when ball is not in play.

actions = [:right, :noop, :left]

Synthex.RankingGym.solve(actions,
  env: :breakout,
  max_steps: 10_000,
  depth: 1,
  max_coeff: 5,
  n_episodes: 30,
  top_k: 20,
  max_iters: 3,
  cegar_rounds: 3
)

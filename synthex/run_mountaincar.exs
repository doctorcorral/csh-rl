# MountainCar-v0: 3 actions (push left / none / push right), 2D state
# Sparse reward: -1 per step, max 200 steps. Reaching the goal is hard.

actions = [:push_left, :no_push, :push_right]

Synthex.RankingGym.solve(actions,
  env: :mountaincar,
  max_steps: 200,
  depth: 1,
  max_coeff: 5,
  n_episodes: 20,
  top_k: 15,
  max_iters: 3,
  cegar_rounds: 2
)

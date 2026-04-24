# CartPole-v1: 2 actions (left/right), 4D state
# Episodes are short (max 500 steps), very fast.

actions = [:left, :right]

Synthex.RankingGym.solve(actions,
  env: :cartpole,
  max_steps: 500,
  depth: 1,
  max_coeff: 5,
  n_episodes: 20,
  top_k: 15,
  max_iters: 3,
  cegar_rounds: 2
)

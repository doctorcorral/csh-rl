# Acrobot-v1: 3 actions (neg torque / none / pos torque), 6D state
# Swing-up task, -1 per step, max 500 steps.

actions = [:torque_neg, :no_torque, :torque_pos]

Synthex.RankingGym.solve(actions,
  env: :acrobot,
  max_steps: 500,
  depth: 1,
  max_coeff: 5,
  n_episodes: 20,
  top_k: 15,
  max_iters: 3,
  cegar_rounds: 2
)

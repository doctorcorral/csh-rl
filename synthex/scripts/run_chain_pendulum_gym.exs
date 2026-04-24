# Pendulum-v1: CEGAR + Coordinate Descent (Gym-in-the-loop)
#
# 3 actions: TorqueNeg (-2), NoTorque (0), TorquePos (+2)
# Chain: 2 predicates + default
# Obs: (cos θ, sin θ, ω) — 3 dims
# Goal: stabilize at upright (cos θ ≈ 1)
#
# max_steps: required — scoring, trajectories, explore/CEX, validation (Python = rollouts only).

{chain, default} = Synthex.ChainGym.solve(
  [:torque_neg, :torque_pos],
  :no_torque,
  env: :pendulum,
  depth: 1,
  max_coeff: 5,
  n_episodes: 200,
  top_k: 30,
  max_iters: 5,
  cegar_rounds: 3,
  max_steps: 500
)

IO.puts("\n=== FINAL CHAIN ===")
IO.inspect({chain, default})

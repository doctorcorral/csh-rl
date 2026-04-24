# Decision-chain synthesis for CliffWalking-v1 with Gymnasium-in-the-loop.
#
# Usage:  mix run scripts/run_chain_cliffwalking.exs
#
# 4×12 grid (48 states), 4 actions: up/right/down/left
# Start: (3,0), Goal: (3,11), Cliff: (3,1)-(3,10)
# Reward: -1 per step, -100 for cliff (resets to start)
# Optimal safe path: up→right×11→down = 13 steps = -13 reward
#
# State: (row, col) — 2D integers mapped to floats.
# Features: axis thresholds on row/col plus diagonals.
#
# Priority: [up, down, left] > right (default)
# Rationale: "right" is the dominant action along the safe path;
# predicates learn when to deviate (up from start, down to goal).

{chain, default} = Synthex.ChainGym.solve(
  [:up, :down, :left],
  :right,
  env: :cliffwalking,
  depth: 1,
  max_coeff: 5,
  n_episodes: 100,
  top_k: 30,
  max_iters: 5,
  cegar_rounds: 3,
  max_steps: 200
)

IO.puts("\n=== RESULT ===")
IO.puts("CliffWalking-v1 actions: 0=up, 1=right, 2=down, 3=left")
IO.puts("Optimal safe path reward: -13 (13 steps)\n")

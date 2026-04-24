# Decision-chain synthesis for ALE/Tetris-v5 with Gymnasium-in-the-loop.
#
# Usage:  mix run scripts/run_chain_tetris.exs
#
# Atari 2600 Tetris: 5 actions (LEFT, RIGHT, ROTATE, DOWN, NOOP)
# State: 15D from RAM (piece_x, piece_y, rotation, board stats, block positions)
# Reward: survival_steps + 100 * lines_cleared (custom, ALE score detection N/A)
#
# Priority: [left, right, rotate, down] > noop
# Rationale: NOOP (let gravity work) is the safe default;
# predicates learn when to actively move, rotate, or drop.
#
# With 4 non-default actions, coordinate descent optimizes 4 predicate positions.
# The Atari 2600 board is narrow (~6 columns), episodes last ~300-600 steps.

{chain, default} = Synthex.ChainGym.solve(
  [:left, :right, :rotate, :down],
  :noop,
  env: :tetris,
  depth: 1,
  max_coeff: 5,
  n_episodes: 15,
  top_k: 20,
  max_iters: 3,
  cegar_rounds: 2,
  max_steps: 2000
)

IO.puts("\n=== DEPLOYABLE POLICY ===")
IO.puts("ALE/Tetris-v5 actions: 0=NOOP, 1=FIRE(rot), 2=RIGHT, 3=LEFT, 4=DOWN")
IO.puts("Synthesis actions: 0=left, 1=right, 2=rotate, 3=down, 4=noop\n")

dim_names = %{
  0 => "piece_x", 1 => "piece_y", 2 => "rot_raw",
  3 => "piece_vis", 4 => "board_fill", 5 => "bottom_fill",
  6 => "occ_rows", 7 => "pieces_placed"
}

format = fn
  pred, fmt ->
    case pred do
      :truep -> "true"
      :falsep -> "false"
      {:feat, ["axis", d, t]} -> "#{dim_names[d] || "dim#{d}"} < #{t}"
      {:feat, ["diag", i, j, c]} ->
        "#{c}*#{dim_names[i] || "dim#{i}"} + #{dim_names[j] || "dim#{j}"} < 0"
      {:feat, ["sq_diag", i, j, c]} ->
        "#{c}*#{dim_names[i] || "dim#{i}"}² + #{dim_names[j] || "dim#{j}"} < 0"
      {:feat, ["prod", i, j, t]} ->
        "#{dim_names[i] || "dim#{i}"}*#{dim_names[j] || "dim#{j}"} < #{t}"
      {:not, p} -> "not (#{fmt.(p, fmt)})"
      {:and, p, q} -> "(#{fmt.(p, fmt)}) and (#{fmt.(q, fmt)})"
      {:or, p, q} -> "(#{fmt.(p, fmt)}) or (#{fmt.(q, fmt)})"
      other -> inspect(other)
    end
end

action_names = %{
  left: "LEFT (ALE 3)",
  right: "RIGHT (ALE 2)",
  rotate: "ROTATE (ALE 1)",
  down: "DOWN (ALE 4)",
  noop: "NOOP (ALE 0)"
}

IO.puts("def policy(state):")
IO.puts("    piece_x, piece_y, rot_raw, ... = extract_state(ram)")

Enum.each(chain, fn {pred, action} ->
  IO.puts("    if #{format.(pred, format)}: return #{action_names[action]}")
end)

IO.puts("    return #{action_names[default]}")

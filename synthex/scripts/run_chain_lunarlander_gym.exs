# Decision-chain synthesis for LunarLander with Gymnasium-in-the-loop.
#
# Usage:  mix run scripts/run_chain_lunarlander_gym.exs
#
# Elixir handles candidate enumeration (CEGIS).
# Python/Gymnasium handles episode evaluation (ground truth).
# No sim-to-real gap — predicates are scored against the real environment.
#
# Priority: FireLeft > FireRight > FireMain > DoNothing
# (angular control first, then altitude braking)

# CEGAR + Coordinate descent (principled CSHRL):
# - Raw Gymnasium reward, no bonuses
# - CEGAR: failure trajectories → feature refinement → re-synthesis
# - Coordinate descent: full-chain evaluation at each position
# - Seed rotation per iteration to avoid overfitting
#
# max_steps is required by ChainGym.solve/3 — set here per experiment (not in ChainGym).
{chain, default} = Synthex.ChainGym.solve(
  [:fire_left, :fire_right, :fire_main],
  :do_nothing,
  depth: 1,
  max_coeff: 5,
  n_episodes: 200,
  top_k: 30,
  max_iters: 5,
  cegar_rounds: 3,
  max_steps: 1000
)

IO.puts("\n=== DEPLOYABLE POLICY ===")
IO.puts("LunarLander-v3 actions: 0=noop, 1=left, 2=main, 3=right\n")

dim_names = %{0 => "x", 1 => "y", 2 => "vx", 3 => "vy", 4 => "θ", 5 => "ω"}

format = fn
  pred, fmt ->
    case pred do
      :truep -> "true"
      :falsep -> "false"
      {:feat, ["axis", d, t]} -> "#{dim_names[d]} < #{t}"
      {:feat, ["diag", i, j, c]} -> "#{c}*#{dim_names[i]} + #{dim_names[j]} < 0"
      {:not, p} -> "not (#{fmt.(p, fmt)})"
      {:and, p, q} -> "(#{fmt.(p, fmt)}) and (#{fmt.(q, fmt)})"
      {:or, p, q} -> "(#{fmt.(p, fmt)}) or (#{fmt.(q, fmt)})"
      other -> inspect(other)
    end
end

action_names = %{fire_left: "fire_left (1)", fire_right: "fire_right (3)",
                 fire_main: "fire_main (2)", do_nothing: "noop (0)"}

IO.puts("def policy(obs):")
IO.puts("    x, y, vx, vy, theta, omega = obs[:6]")

Enum.each(chain, fn {pred, action} ->
  IO.puts("    if #{format.(pred, format)}: return #{action_names[action]}")
end)

IO.puts("    return #{action_names[default]}")

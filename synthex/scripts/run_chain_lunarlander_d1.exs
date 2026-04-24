# Decision-chain synthesis for LunarLander at depth 1 (pure Elixir).
#
# Usage:  mix run scripts/run_chain_lunarlander_d1.exs
#
# Uses the Gym-calibrated Elixir model (LunarLanderGym).
# Depth 1 allows conjunctions and disjunctions of features.
# Priority: FireLeft > FireRight > FireMain > DoNothing

{chain, default} = Synthex.Chain.solve(
  Synthex.Envs.LunarLanderGym,
  [:fire_left, :fire_right, :fire_main],
  :do_nothing,
  depth: 1,
  max_coeff: 5,
  cegar_rounds: 3
)

IO.puts("\n\n=== DEPLOYABLE POLICY ===")

Enum.each(chain, fn {pred, action} ->
  IO.puts("  if #{inspect(pred)} -> #{inspect(action)}")
end)

IO.puts("  else -> #{inspect(default)}")

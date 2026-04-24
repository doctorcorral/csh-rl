# Decision-chain synthesis for LunarLander
#
# Usage:  mix run scripts/run_chain_lunarlander.exs
#
# Priority order: FireMain > FireLeft > FireRight > DoNothing
# This avoids Condorcet cycles entirely (3 binary predicates, not 6 pairwise).

{chain, default} = Synthex.Chain.solve(
  Synthex.Envs.LunarLander,
  [:fire_main, :fire_left, :fire_right],
  :do_nothing,
  depth: 0,
  max_coeff: 5,
  max_fuel: 20
)

IO.puts("\n\n=== DEPLOYABLE POLICY ===")
IO.puts("def policy(state):")

Enum.each(chain, fn {pred, action} ->
  IO.puts("  if #{inspect(pred)} -> #{inspect(action)}")
end)

IO.puts("  else -> #{inspect(default)}")
IO.puts("end")

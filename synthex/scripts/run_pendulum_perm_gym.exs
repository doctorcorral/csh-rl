# Predicate-guided action ranking synthesis for Pendulum-v1.
#
# Searches for one predicate p that partitions the state space into two
# regions, each assigned a complete action ranking (total order).
# The agent executes the top-ranked action in each region.
#
# With 3 actions there are 6 rankings and 24 non-trivial ranking pairs.
# The search is exhaustive over all predicates × pairs, then refined
# via CEGAR for counterexample-driven feature generation.
#
# max_steps: 500 — long enough for equilibrium signal.

Synthex.PermutationGym.solve(
  [:torque_neg, :no_torque, :torque_pos],
  env: :pendulum,
  max_steps: 500,
  depth: 1,
  max_coeff: 5,
  n_episodes: 200,
  top_k: 30,
  cegar_rounds: 3,
  top_pairs: 3
)

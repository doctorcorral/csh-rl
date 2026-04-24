# CSHRL-native ranking synthesis for Pendulum-v1.
#
# Generic iterative CEGAR: starts with 0 predicates (one
# default ranking) and adds predicates as needed until the
# policy is self-consistent at all anchor states.

Synthex.RankingGym.solve(
  [:torque_neg, :no_torque, :torque_pos],
  env: :pendulum,
  max_steps: 500,
  depth: 1,
  max_coeff: 5,
  lookahead: 100,
  cegar_rounds: 25,
  top_k: 30,
  n_verify: 200
)

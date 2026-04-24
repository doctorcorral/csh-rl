# Exhaustive full-ranking search for LunarLander.
#
# Fixes top actions from Phase 1 coordinate descent, then enumerates
# ALL orderings of remaining actions across all regions simultaneously.
# Each complete policy is evaluated as a whole on episodes.
#
# 4 actions, 4 regions (3 predicates + default), top fixed:
#   (3!)^4 = 6^4 = 1,296 candidate policies
#
# Predicates from Phase 1:
#   R0: 5*ω² + θ < 0  ∧  -2*x + θ < 0   → FireLeft
#   R1: -4*θ + x < 0  ∧  -5*ω + vx < 0  → FireRight
#   R2: vy < -0.1     ∧  2*vy + y < 0    → FireMain
#   Default: DoNothing

alias Synthex.PerStateRanking

chain = [
  # R0: FireLeft
  {{:and,
    {:feat, ["sq_diag", 5, 4, 5]},
    {:feat, ["diag", 0, 4, -2]}},
   :fire_left},

  # R1: FireRight
  {{:and,
    {:feat, ["diag", 4, 0, -4]},
    {:feat, ["diag", 5, 2, -5]}},
   :fire_right},

  # R2: FireMain
  {{:and,
    {:feat, ["axis", 3, -0.1]},
    {:feat, ["diag", 3, 1, 2]}},
   :fire_main},
]

PerStateRanking.exhaustive_rankings(chain, :do_nothing,
  env: :lunarlander,
  actions: [:do_nothing, :fire_left, :fire_main, :fire_right],
  seeds: Enum.to_list(0..99),
  max_steps: 1000
)

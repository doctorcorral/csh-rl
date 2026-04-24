# Per-state episode-reward ranking for LunarLander.
#
# Uses the Phase 1 chain from the best known synthesis result and
# determines full rankings via per-state profiling (CoindHomo-principled).
#
# The chain predicates (from previous coordinate descent synthesis):
#   R0: 5*w² + θ < 0  ∧  -2*x + θ < 0   → FireLeft
#   R1: -4*θ + x < 0  ∧  -5*w + vx < 0  → FireRight
#   R2: vy < -0.1     ∧  2*vy + y < 0    → FireMain
#   Default: DoNothing

alias Synthex.PerStateRanking

# The discovered predicates from coordinate descent Phase 1
chain = [
  # R0: FireLeft — 5*ω² + θ < 0 AND -2*x + θ < 0
  {{:and,
    {:feat, ["sq_diag", 5, 4, 5]},
    {:feat, ["diag", 0, 4, -2]}},
   :fire_left},

  # R1: FireRight — -4*θ + x < 0 AND -5*ω + vx < 0
  {{:and,
    {:feat, ["diag", 4, 0, -4]},
    {:feat, ["diag", 5, 2, -5]}},
   :fire_right},

  # R2: FireMain — vy < -0.1 AND 2*vy + y < 0
  {{:and,
    {:feat, ["axis", 3, -0.1]},
    {:feat, ["diag", 3, 1, 2]}},
   :fire_main},
]

PerStateRanking.determine_rankings(chain, :do_nothing,
  env: :lunarlander,
  actions: [:do_nothing, :fire_left, :fire_main, :fire_right],
  seeds: Enum.to_list(0..199),
  max_steps: 1000,
  sample_interval: 5
)

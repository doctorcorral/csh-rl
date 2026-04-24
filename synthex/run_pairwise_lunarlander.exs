# Pairwise Predicate Synthesis Phase 2 for LunarLander.
#
# Uses the Phase 1 chain from coordinate descent, collects pairwise
# oracle observations, and synthesizes predicates via CEGIS to
# determine the full ranking structurally (via Propagation Theorem).
#
# 4 actions → 6 pairs per region, 4 regions = 24 CEGIS problems.
# Cross-pair propagation may reduce this significantly.

alias Synthex.PairwisePhase2

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

PairwisePhase2.synthesize(chain, :do_nothing,
  env: :lunarlander,
  actions: [:do_nothing, :fire_left, :fire_main, :fire_right],
  seeds: Enum.to_list(0..99),
  max_steps: 1000,
  sample_interval: 10,
  depth: 1,
  max_coeff: 5
)

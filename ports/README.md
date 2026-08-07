# CSHRL Ports

Ports of the CSHRL portability kernel to proof assistants other than Agda.
The kernel — what every port must define and prove — is specified in
[`SPEC.md`](SPEC.md). The Agda development in `src/CSHRL/` is the reference
implementation and goes far beyond the kernel.

## Layout

- `rocq/` — Rocq port. Build with `make` inside `ports/rocq/` (requires
  `coqc`/`coq_makefile` on the PATH; no external libraries).
- `lean/` — Lean 4 port (planned; will use functional streams `ℕ → R` and the
  pointwise formulation as primary, per the stream isomorphism).

## Status

| Item | Agda | Rocq | Lean |
|------|------|------|------|
| D1–D4 streams and dominance | done | done | — |
| T1 stream isomorphism | done | done | — |
| D5–D11 MDP interface and the two conditions | done | done | — |
| T2 decomposition theorem | done | done | — |
| T3 BinarySacrifice separation | done | done | — |
| T4 finite-horizon subsumption | done | done | — |
| T5 learning kernel (swap, locality, demotion) | done | done | — |
| T6 Q-learning failure analysis | done | done | — |

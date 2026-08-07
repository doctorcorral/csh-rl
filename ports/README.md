# CSHRL Ports

Ports of the CSHRL portability kernel to proof assistants other than Agda.
The kernel — what every port must define and prove — is specified in
[`SPEC.md`](SPEC.md). The Agda development in `src/CSHRL/` is the reference
implementation and goes far beyond the kernel.

## Layout

- `rocq/` — Rocq port. Build with `make` inside `ports/rocq/` (requires
  `coqc`/`coq_makefile` on the PATH; no external libraries).
- `lean/` — Lean 4 port. Build with `lake build` inside `ports/lean/`
  (toolchain pinned in `lean-toolchain`; no external libraries, core only).
  Uses functional streams (`Nat → R`) with the pointwise formulation as
  primary, per the stream isomorphism.

## Status

| Item | Agda | Rocq | Lean |
|------|------|------|------|
| D1–D4 streams and dominance | done | done | done |
| T1 stream isomorphism | done | done | done (unfold + coinduction principle) |
| D5–D11 MDP interface and the two conditions | done | done | done |
| T2 decomposition theorem | done | done | done |
| T3 BinarySacrifice separation | done | done | done |
| T4 finite-horizon subsumption | done | done | done |
| T5 learning kernel (swap, locality, demotion) | done | done | done |
| T6 Q-learning failure analysis | done | done | done |

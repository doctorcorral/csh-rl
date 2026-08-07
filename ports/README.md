# CSHRL Ports

Ports of the CSHRL portability kernel to proof assistants other than Agda.
The kernel — what every port must define and prove — is specified in
[`SPEC.md`](SPEC.md). The Agda development in `src/CSHRL/` is the reference
implementation and goes beyond the kernel (with one exception: T7, the
closed convergence theorem, which the ports prove and the Agda reference
still states as an assumption record).

## Layout

- `rocq/` — Rocq port. Build with `make` inside `ports/rocq/` (requires
  `coqc`/`coq_makefile` on the PATH). The deterministic kernel (T1–T6)
  uses only Init; the stochastic milestone (T7–T12) uses the axiom-free
  Stdlib (`lia`/`nia`).
- `lean/` — Lean 4 port. Build with `lake build` inside `ports/lean/`
  (toolchain pinned in `lean-toolchain`; no external libraries, core only).
  Uses functional streams (`Nat → R`) with the pointwise formulation as
  primary, per the stream isomorphism.

Both ports are built by CI (`.github/workflows/ports.yml`), and each
contains an `AxiomCheck` module that certifies axiom-freeness on every
build.

## Status

| Item | Agda | Rocq | Lean |
|------|------|------|------|
| D1–D4 streams and dominance | done | done | done |
| T1 stream isomorphism | done | done | done (unfold + coinduction principle) |
| D5–D11 MDP interface and the two conditions | done | done | done |
| T2 decomposition theorem | done | done | done |
| T3 sacrifice separations (BinarySacrifice, SkillInvestment, PreparationDilemma) | done | done | done |
| T4 finite-horizon subsumption | done | done | done |
| T5 learning kernel (swap, locality, demotion) | done | done | done |
| T6 Q-learning failure analysis | done | done | done |
| T7 closed convergence of swap learning (violation decrease, C(n,2) bound) | assumption record | **done (closed)** | **done (closed)** |
| D12 finite distribution monad | done | done | done |
| D13/T8 lexicographic dominance, pointwise ⇒ lex | done | done | done |
| D14/T9 FOSD + SD[k] hierarchy and closure (++, scale) | done | done | done |
| T10 convolution closure (Abel summation) | done | done | done |
| D15/T11 compositional ranking algebra | done | done | done |
| D16/T12 verified state abstraction | done | done | done |

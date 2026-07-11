# FTDQE

Lean 4 formalisation of the mathematical results in the manuscript on
neighbourhood-filtered Lindbladian cooling.

## Toolchain

- Lean 4.31.0
- Mathlib 4.31.0

## Initial formalisation layer

- The grid-valued global-refresh recursion from Lemma 5 is copied from the
  supplied core-Lean file that was already machine-checked with Lean 4.31.0.
- A real-valued version of the same recursion is included for Mathlib CI.
- The algebraic core of the energy certificate from Lemma 4(b) is included.
- A corrected noisy-estimate threshold is included that both certifies the
  target overlap and is guaranteed to trigger after sufficient convergence.

The Mathlib-dependent files must pass the repository CI before they are marked
as machine-checked.

## Build

```bash
lake update
lake build
```

See `docs/formalisation-plan.md` for the planned theorem dependency graph.

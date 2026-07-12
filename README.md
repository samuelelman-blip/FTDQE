# FTDQE

Lean 4 formalisation of the mathematical results in the manuscript on
neighbourhood-filtered Lindbladian cooling.

## Toolchain

- Lean 4.31.0
- Mathlib 4.31.0

## Machine-checked modules

- `FTDQE.RefreshRecursion`: the grid-valued and real-valued global-refresh recursions underlying Lemma 5 and Eq. (31).
- `FTDQE.EnergyCertificate`: the scalar algebraic core of Lemma 4(b), including the corrected noisy-estimate threshold.
- `FTDQE.IntegralGronwall`: a continuous integral form of Grönwall's inequality.
- `FTDQE.PerturbedRelaxation`: the scalar Duhamel–Grönwall estimate of Lemma 2.
- `FTDQE.OperatorDuhamel` and `FTDQE.OperatorPerturbedRelaxation`: abstract noncommutative Duhamel and operator-norm relaxation results.
- `FTDQE.InvariantSubspaceRelaxation`: perturbed relaxation requiring the ideal mixing estimate only on an invariant class of vectors.
- `FTDQE.QuantumMatrix`, `FTDQE.QuantumGenerator`, and `FTDQE.GKLSGenerator`: finite-dimensional complex matrices, traceless-Hermitian generator plumbing, and the concrete GKLS Hermiticity/trace-preservation identities.
- `FTDQE.MatrixLindbladianRelaxation`: the finite-dimensional matrix/trace-norm bridge for Lemma 2.

## Work in progress

PR #3 formalises Lemma 3:

- compact/Cesàro stationary-state existence;
- the resolvent stability inequalities;
- uniqueness under `κ * η < rate`;
- a composed certificate theorem and finite-dimensional matrix/trace-norm wrapper.

The resolvent stability core has passed CI. The combined extension remains a draft until GitHub Actions supplies a runner and the full project build is verified.

Mathlib 4.31.0 does not bundle the Schatten-1 norm for finite complex matrices, so the matrix results use an explicit `traceNorm`/ambient-norm identification instead of rebuilding Schatten theory inside this project.

## Build

```bash
lake update
lake build
```

See `docs/formalisation-plan.md` for the theorem dependency graph and current status.

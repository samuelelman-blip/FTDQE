# FTDQE

Lean 4 formalisation of the mathematical results in the manuscript on
neighbourhood-filtered Lindbladian cooling.

## Toolchain

- Lean 4.31.0
- Mathlib 4.31.0

## Machine-checked modules

- `FTDQE.RefreshRecursion`: the grid-valued and real-valued global-refresh
  recursions underlying Lemma 5 and Eq. (31).
- `FTDQE.EnergyCertificate`: the scalar algebraic core of Lemma 4(b), including
  the corrected noisy-estimate threshold that both certifies the target overlap
  and is guaranteed to trigger after sufficient convergence.
- `FTDQE.IntegralGronwall`: a continuous integral form of Grönwall's inequality.
- `FTDQE.PerturbedRelaxation`: the scalar Duhamel--Grönwall estimate of Lemma 2,
  from the unweighted convolution inequality in Eq. (23) to the exponential
  relaxation bound in Eq. (22).

The operator-semigroup layer that derives Eq. (23) from Duhamel's formula for
finite-dimensional Lindbladian generators remains to be instantiated with
trace norms, Hermiticity and trace preservation.

## Build

```bash
lake update
lake build
```

See `docs/formalisation-plan.md` for the theorem dependency graph and current
status.

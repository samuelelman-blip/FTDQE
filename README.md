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
- `FTDQE.PerturbedRelaxation`, `FTDQE.OperatorDuhamel`, `FTDQE.OperatorPerturbedRelaxation`, and `FTDQE.InvariantSubspaceRelaxation`: the Duhamel–Grönwall proof of Lemma 2.
- `FTDQE.QuantumMatrix`, `FTDQE.QuantumGenerator`, `FTDQE.GKLSGenerator`, and `FTDQE.MatrixLindbladianRelaxation`: the finite-dimensional matrix/GKLS bridge.
- `FTDQE.StationaryStateStability`, `FTDQE.CesaroStationaryExistence`, and `FTDQE.MatrixStationaryStateStability`: Lemma 3, including existence, resolvent stability, and uniqueness.
- `FTDQE.GroundStateOverlap`: the stability-to-overlap composition in Theorem 2.
- `FTDQE.DissipatorLipschitz`: Proposition 1, the constant-`4` dissipator estimate, and Eq. (14).
- `FTDQE.GevreyTimeLocalisation`: Lemma 1 and the pointwise/tail bounds in Eqs. (8)–(9).
- `FTDQE.LiebRobinsonTruncation`: Theorem 1, including the balanced cutoff and explicit semigroup remainder.
- `FTDQE.LocalityToOverlap`: the end-to-end finite-family composition from Theorem 1 and Proposition 1 to Theorem 2.

## Validation

All merged theorem layers have passed complete local builds under the pinned toolchain. The latest merged layer completed successfully with 8577 jobs. The end-to-end composition is on PR #8 pending its local build.

## Scope boundaries

The project does not rebuild several substantial analytic libraries from first principles. In particular:

- matrix trace norms are represented by an explicit `traceNorm`/ambient-norm identification;
- the ideal-generator resolvent, concrete Cesàro GKLS trajectory, Gevrey integration-by-parts and tail estimates, Lieb–Robinson short-time approximation, and diamond-norm comparison estimates are explicit certificate interfaces;
- all scalar compositions, noncommutative matrix identities, finite-family sums, perturbative constants, stability estimates, and overlap conclusions downstream of those interfaces are proved in Lean.

## Build

```bash
lake update
lake build
```

See `docs/formalisation-plan.md` for the theorem dependency graph and precise infrastructure boundaries.

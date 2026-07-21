# FTDQE

Lean 4 formalisation of the mathematical results in the manuscript
*Neighbourhood-filtered Lindbladian cooling: locality, stability, and the cost
of global refresh*.

## Toolchain

- Lean 4.31.0
- Mathlib 4.31.0

## Formalised modules

- `FTDQE.RefreshRecursion`: Lemma 5(i) and Eqs. (30)–(32), including the integer- and real-valued refresh recursions.
- `FTDQE.EnergyCertificate`: Lemma 4(b) and Eq. (28), including the corrected noisy-estimate threshold.
- `FTDQE.StoppingRule`: Lemma 4(a), including the explicit stopping time of Eq. (27), the transient bound, and the overlap conclusion.
- `FTDQE.StrongLocalFilter`: Lemma 5(ii), including the inherited half-rate relaxation and the no-refresh accuracy regime.
- `FTDQE.IntegralGronwall`, `FTDQE.PerturbedRelaxation`, `FTDQE.OperatorDuhamel`, `FTDQE.OperatorPerturbedRelaxation`, and `FTDQE.InvariantSubspaceRelaxation`: the Duhamel–Grönwall proof of Lemma 2.
- `FTDQE.QuantumMatrix`, `FTDQE.QuantumGenerator`, `FTDQE.GKLSGenerator`, and `FTDQE.MatrixLindbladianRelaxation`: the finite-dimensional matrix/GKLS bridge.
- `FTDQE.StationaryStateStability`, `FTDQE.CesaroStationaryExistence`, and `FTDQE.MatrixStationaryStateStability`: Lemma 3, including existence, resolvent stability, and uniqueness.
- `FTDQE.GroundStateOverlap`: the stability-to-overlap composition in Theorem 2.
- `FTDQE.DissipatorLipschitz`: Proposition 1, the constant-`4` dissipator estimate, and Eq. (14).
- `FTDQE.GevreyTimeLocalisation`: Lemma 1 and the pointwise/tail bounds in Eqs. (8)–(9).
- `FTDQE.LiebRobinsonTruncation`: Theorem 1, including the balanced cutoff and explicit semigroup remainder.
- `FTDQE.LocalityToOverlap`: the end-to-end finite-family composition from Theorem 1 and Proposition 1 to Theorem 2.
- `FTDQE.MinibatchRefresh`: Lemma 6 and Eqs. (39), (43), and (46), including arbitrary-contraction geometric iteration and the half-contraction floor.
- `FTDQE.CoverageLowerBound`: Proposition 2 and Eq. (49), including the extensive sampled-coverage consequence.
- `FTDQE.ResolventLocality`: Lemma 7 and Eq. (53), including the balanced time cutoff and exponential spatial envelope.
- `FTDQE.ClusterExpansion`: Theorem 3 and Eqs. (56)–(57), (59), and (61), including the geometric resummation and global/local error consequences.

## Validation

Every module merged into `main` through the end-to-end Theorem 2 composition has passed a complete local build under the pinned toolchain. The latest validated build completed successfully with 8578 jobs. The revised-manuscript modules for Lemma 4(a), Lemma 5(ii), Lemmas 6–7, Proposition 2, and Theorem 3 are under local validation on the current pull request.

## Scope boundaries

The project does not rebuild several substantial analytic libraries from first principles. In particular:

- matrix trace norms are represented by an explicit `traceNorm`/ambient-norm identification;
- the ideal-generator resolvent, concrete Cesàro GKLS trajectory, Gevrey integration-by-parts and tail estimates, Lieb–Robinson short-time approximation, and diamond-norm comparison estimates are explicit certificate interfaces;
- the open-system Lieb–Robinson input in Lemma 7, the no-hit/light-cone witness in Proposition 2, and the connected-polymer/Kotecký–Preiss reorganisation in Theorem 3 are explicit certificate interfaces;
- all scalar compositions, noncommutative matrix identities, finite-family sums, perturbative constants, geometric recursions, coverage arithmetic, stability estimates, and global/local error consequences downstream of those interfaces are proved in Lean.

## Build

```bash
lake update
lake build
```

See `docs/formalisation-plan.md` for the theorem dependency graph and precise infrastructure boundaries.

# Formalisation plan

The theorem dependency order for the revised manuscript is:

1. ✅ Refresh recursion, Lemma 5(i), Eqs. (30)–(32).
2. ✅ Scalar energy certificate, Lemma 4(b), Eq. (28).
3. ✅ Integral Grönwall lemma.
4. ✅ Perturbed relaxation, Lemma 2, including abstract Duhamel, the invariant traceless-Hermitian formulation, the finite-dimensional matrix bridge, and concrete GKLS Hermiticity/trace-preservation algebra.
5. ✅ Stationary-state existence and stability, Lemma 3: compact/Cesàro existence, resolvent stability, uniqueness from positive perturbed decay, and the matrix trace-norm wrapper.
6. ✅ Ground-state overlap arithmetic and conditional composition, Theorem 2.
7. ✅ Dissipator Lipschitz estimate and finite-jump generator bound, Proposition 1 and Eq. (14).
8. ✅ Gevrey time localisation, Lemma 1 and Eqs. (8)–(9).
9. ✅ Lieb–Robinson jump localisation and semigroup consequence, Theorem 1.
10. ✅ End-to-end composition from Theorem 1 through Proposition 1 to Theorem 2; full local build completed with 8578 jobs.
11. 🚧 A priori stopping time and overlap conclusion, Lemma 4(a) and Eq. (27), implemented in `FTDQE.StoppingRule` pending local validation.
12. 🚧 Strong-local-filter/no-refresh regime, Lemma 5(ii), implemented in `FTDQE.StrongLocalFilter` pending local validation.
13. 🚧 Minibatched global refresh, Lemma 6 and Eqs. (39), (43), and (46), implemented in `FTDQE.MinibatchRefresh` pending local validation.
14. 🚧 Coverage lower bound, Proposition 2 and Eq. (49), implemented in `FTDQE.CoverageLowerBound` pending local validation.
15. 🚧 Resolvent quasi-locality, Lemma 7 and Eq. (53), implemented in `FTDQE.ResolventLocality` pending local validation.
16. 🚧 Convergent cluster expansion, Theorem 3 and Eqs. (56)–(57), (59), and (61), implemented in `FTDQE.ClusterExpansion` pending local validation.

## Explicit infrastructure boundaries

The formalisation is intentionally honest about reusable analytic infrastructure that Mathlib 4.31.0 does not currently provide in the required form:

- **Trace norm.** Matrix theorems use an explicit `traceNorm` and an identification with the ambient Banach-space norm rather than rebuilding Schatten-1 theory.
- **Resolvent.** Lemma 3 uses a `ResolventCertificate` recording the right inverse on the invariant subspace and the `κ / rate` norm bound. The manuscript constructs it from `J = -∫₀^∞ exp(tL) dt`.
- **Stationary-state existence.** Compact/Cesàro existence and the `O(1/(n+1))` residual implication are formalised; the concrete time-averaged GKLS trajectory remains behind an explicit certificate interface.
- **Gevrey Fourier analysis.** The integration-by-parts estimate, optimisation certificate, and one-sided improper-integral tail bounds are explicit interfaces. Their scalar composition and constants are proved in Lean.
- **Closed-system Lieb–Robinson input.** The short-time localisation estimate and stretched-exponential envelope are explicit certificates. The balanced cutoff, finite-family summation, and downstream consequences are proved in Lean.
- **Diamond-norm analysis.** Hölder, anticommutator, and induced-to-diamond comparisons are explicit theorem inputs. The noncommutative matrix identities, constant `4`, and finite-sum bound are proved internally.
- **Minibatch channel input.** Lemma 6 receives the conditional expected one-period contraction as a certificate. Its affine recursion, geometric iteration, half-contraction floor, and compounding of a one-step contraction gap are proved internally.
- **Coverage witness.** Proposition 2 receives the bounded-geometry low-mass ball and the no-hit/open-system light-cone witness through `CoverageLowerBoundCertificate`. Eq. (49) and the extensive sampled-coverage consequence are proved internally.
- **Open-system Lieb–Robinson input.** Lemma 7 receives the short-time leakage plus mixing-tail split and a scalar exponential envelope as certificates. The cutoff `t⋆ = d/(2v_L)` and the final spatial decay estimate are proved internally.
- **Polymer reorganisation.** Theorem 3 receives absolute convergence, the Kotecký–Preiss estimate, the per-cluster estimate, and the connected-walk recursion through `ClusterExpansionCertificate`. The small-denominator resummation and the global/local accuracy consequences are proved internally.

Every theorem layer merged through the end-to-end Theorem 2 composition has passed a complete local `lake build` under Lean 4.31.0 and Mathlib 4.31.0. The revised-paper extension remains unverified until the current branch passes the same full build.

# Formalisation plan

The theorem dependency order is:

1. ✅ Refresh recursion, Lemma 5, Eqs. (30)–(32).
2. ✅ Scalar energy certificate, Lemma 4(b), Eq. (28).
3. ✅ Integral Grönwall lemma.
4. ✅ Perturbed relaxation, Lemma 2, including abstract Duhamel, the invariant traceless-Hermitian formulation, the finite-dimensional matrix bridge, and concrete GKLS Hermiticity/trace-preservation algebra.
5. ✅ Stationary-state existence and stability, Lemma 3: compact/Cesàro existence, resolvent stability, uniqueness from positive perturbed decay, and the matrix trace-norm wrapper.
6. ✅ Ground-state overlap arithmetic and conditional composition, Theorem 2.
7. ✅ Dissipator Lipschitz estimate and finite-jump generator bound, Proposition 1 and Eq. (14).
8. ✅ Gevrey time localisation, Lemma 1 and Eqs. (8)–(9).
9. ✅ Lieb–Robinson jump localisation and semigroup consequence, Theorem 1.
10. 🚧 End-to-end composition from Theorem 1 through Proposition 1 to Theorem 2, implemented on PR #8 pending a full local build.

## Explicit infrastructure boundaries

The formalisation is intentionally honest about reusable analytic infrastructure that Mathlib 4.31.0 does not currently provide in the required form:

- **Trace norm.** Matrix theorems use an explicit `traceNorm` and an identification with the ambient Banach-space norm rather than rebuilding Schatten-1 theory.
- **Resolvent.** Lemma 3 uses a `ResolventCertificate` recording the right inverse on the invariant subspace and the `κ / rate` norm bound. The manuscript constructs it from `J = -∫₀^∞ exp(tL) dt`.
- **Stationary-state existence.** Compact/Cesàro existence and the `O(1/(n+1))` residual implication are formalised; the concrete time-averaged GKLS trajectory remains behind an explicit certificate interface.
- **Gevrey Fourier analysis.** The integration-by-parts estimate, optimisation certificate, and one-sided improper-integral tail bounds are explicit interfaces. Their scalar composition and constants are proved in Lean.
- **Lieb–Robinson input.** The short-time localisation estimate and stretched-exponential envelope are explicit certificates. The balanced cutoff `T = r/(2v)`, finite-family summation, and downstream consequences are proved in Lean.
- **Diamond-norm analysis.** Hölder, anticommutator, and induced-to-diamond comparisons are explicit theorem inputs. The noncommutative matrix identities, constant `4`, and finite-sum bound are proved internally.

Every merged theorem layer has passed a complete local `lake build` under Lean 4.31.0 and Mathlib 4.31.0.

# Formalisation plan

The intended dependency order is:

1. ✅ Refresh recursion, Lemma 5, Eqs. (30)–(32).
2. ✅ Scalar energy certificate, Lemma 4(b), Eq. (28).
3. ✅ Integral Grönwall lemma.
4. ✅ Perturbed relaxation, Lemma 2, including abstract Duhamel, the invariant traceless-Hermitian formulation, the finite-dimensional matrix bridge, and concrete GKLS Hermiticity/trace-preservation algebra.
5. 🚧 Stationary-state existence and stability, Lemma 3. The resolvent stability core is machine-checked; compact/Cesàro existence, uniqueness from positive perturbed decay, the composed certificate theorem, and the matrix trace-norm wrapper are implemented on PR #3 pending a full CI run.
6. Ground-state overlap, Theorem 2.
7. Dissipator Lipschitz estimate, Proposition 1.
8. Gevrey time localisation, Lemma 1.
9. Lieb–Robinson localisation and Theorem 1.

## Explicit infrastructure boundaries

Mathlib 4.31.0 does not provide a bundled Schatten-1 norm for finite complex matrices. The matrix theorems therefore use an explicit `traceNorm` together with an identification between that function and the ambient Banach-space norm.

The Lemma 3 stability theorem uses a `ResolventCertificate`, recording a right inverse of the ideal generator on the invariant subspace and the bound `κ / rate`. The manuscript constructs this certificate from

`J = -∫₀^∞ exp(tL) dt`.

The generic compactness theorem and the standard `O(1 / (n + 1))` Cesàro-residual implication are formalised. Instantiating the approximants with the concrete time-averaged GKLS trajectory remains behind an explicit certificate interface.

# Formalisation plan

The intended dependency order is:

1. ✅ Refresh recursion, Lemma 5, Eqs. (30)-(32).
2. ✅ Scalar energy certificate, Lemma 4(b), Eq. (28).
3. ✅ Integral Grönwall lemma.
4. ✅ Scalar Duhamel--Grönwall core of perturbed relaxation, Lemma 2.
5. Stationary-state existence and stability, Lemma 3.
6. Ground-state overlap, Theorem 2.
7. Dissipator Lipschitz estimate, Proposition 1.
8. Gevrey time localisation, Lemma 1.
9. Lieb--Robinson localisation and Theorem 1.
10. Concrete finite-dimensional quantum-channel instantiation.

The completed Lemma 2 layer starts from the scalar convolution inequality of
Eq. (23) and proves the decay rate `rate - κ * η`. The remaining operator layer
must derive Eq. (23) from Duhamel's formula, the ideal mixing estimate, and the
induced trace-norm bound on the perturbation, while proving that the trajectory
is continuous, nonnegative, traceless, and Hermitian where required.

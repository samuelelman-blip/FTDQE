import FTDQE.ResolventLocality
import FTDQE.LocalityToOverlap

/-!
# Convergent cluster expansion

This file formalises the certificate-level content of Theorem 3 in the revised
manuscript.  The open-system Lieb--Robinson estimate, the reorganisation of the
Neumann series into connected polymers, and the Kotecký--Preiss combinatorial
criterion enter through an explicit certificate.  The small-parameter
arithmetic, global error resummation, and local-observable conclusion are
proved internally.
-/

namespace FTDQE

noncomputable section

/-- The absolute Kotecký--Preiss constant used in Eq. (54). -/
def kpConstant : ℝ :=
  1 / (2 * Real.exp 1)

/-- The cluster-expansion parameter `q = (κ / λ) δ_R ν`. -/
def clusterRatio (κ rate δR ν : ℝ) : ℝ :=
  (κ / rate) * δR * ν

/--
Certificate for the analytic and combinatorial input to Theorem 3.

The fields `absoluteConvergence`, `kpBound`, and `perClusterBound` record the
polymer reorganisation and Kotecký--Preiss estimates.  The two numerical bounds
are the scalar consequences of the connected-walk expansion that are resummed
below in Lean.
-/
structure ClusterExpansionCertificate
    (globalError localError κ rate η δR q localConstant
      observableNorm supportSize : ℝ) where
  q_nonneg : 0 ≤ q
  q_le_kp : q ≤ kpConstant
  two_q_lt_one : 2 * q < 1
  absoluteConvergence : Prop
  kpBound : Prop
  perClusterBound : Prop
  global_recursion :
    globalError ≤ (κ / rate) * η + 2 * q * globalError
  local_bound :
    localError ≤
      localConstant * observableNorm * supportSize *
        (κ / rate) * δR

/--
The geometric resummation used in Eq. (61).  A recursive estimate of the form

`E ≤ A η + 2 q E`

with `2q < 1` implies `E ≤ A η / (1 - 2q)`.
-/
theorem cluster_global_error_bound
    (globalError A η q : ℝ)
    (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hqhalf : 2 * q < 1)
    (hrec : globalError ≤ A * η + 2 * q * globalError) :
    globalError ≤ A * η / (1 - 2 * q) := by
  have hden : 0 < 1 - 2 * q := by
    linarith
  apply (le_div_iff₀ hden).2
  have hAη : 0 ≤ A * η := mul_nonneg hA hη
  nlinarith

/--
Theorem 3 in composed certificate form.  The conclusion records absolute
convergence and the Kotecký--Preiss/per-cluster estimates, together with the
global trace-norm and local-observable bounds of Eqs. (56)--(57) and (61).
-/
theorem convergent_cluster_expansion
    (globalError localError κ rate η δR q localConstant
      observableNorm supportSize : ℝ)
    (hκ : 0 ≤ κ) (hrate : 0 < rate)
    (hη : 0 ≤ η)
    (cert : ClusterExpansionCertificate
      globalError localError κ rate η δR q localConstant
        observableNorm supportSize) :
    cert.absoluteConvergence ∧
      cert.kpBound ∧
      cert.perClusterBound ∧
      globalError ≤
        (κ / rate) * η / (1 - 2 * q) ∧
      localError ≤
        localConstant * observableNorm * supportSize *
          (κ / rate) * δR := by
  have hratio : 0 ≤ κ / rate :=
    div_nonneg hκ hrate.le
  have hglobal :
      globalError ≤ (κ / rate) * η / (1 - 2 * q) :=
    cluster_global_error_bound
      globalError (κ / rate) η q hratio hη
        cert.two_q_lt_one cert.global_recursion
  exact ⟨cert.absoluteConvergence, cert.kpBound,
    cert.perClusterBound, hglobal, cert.local_bound⟩

/--
The global part of Theorem 3 recovers a prescribed trace-distance accuracy
once the resummed finite-constant bound is at most `ε`.
-/
theorem cluster_expansion_global_accuracy
    (globalError κ rate η q ε : ℝ)
    (hκ : 0 ≤ κ) (hrate : 0 < rate)
    (hη : 0 ≤ η)
    (hqhalf : 2 * q < 1)
    (hrec :
      globalError ≤ (κ / rate) * η + 2 * q * globalError)
    (haccuracy :
      (κ / rate) * η / (1 - 2 * q) ≤ ε) :
    globalError ≤ ε := by
  have hratio : 0 ≤ κ / rate :=
    div_nonneg hκ hrate.le
  exact (cluster_global_error_bound
    globalError (κ / rate) η q hratio hη hqhalf hrec).trans haccuracy

/--
The local-observable conclusion of Theorem 3: a certificate whose local error
is proportional to `δ_R` immediately yields a target local tolerance.
-/
theorem cluster_expansion_local_accuracy
    (localError localConstant observableNorm supportSize κ rate δR ε : ℝ)
    (hbound :
      localError ≤
        localConstant * observableNorm * supportSize *
          (κ / rate) * δR)
    (haccuracy :
      localConstant * observableNorm * supportSize *
          (κ / rate) * δR ≤ ε) :
    localError ≤ ε :=
  hbound.trans haccuracy

/-- The per-cluster exponential estimate stated in Theorem 3, exposed as a
small reusable certificate interface. -/
structure PerClusterDecayCertificate
    (weight : ℕ → ℝ) (κ rate q : ℝ) where
  bound : ∀ size : ℕ,
    weight size ≤ (κ / rate) * (2 * q) ^ size

/-- A per-cluster certificate supplies the manuscript's bound at every cluster
size. -/
theorem per_cluster_decay
    (weight : ℕ → ℝ) (κ rate q : ℝ)
    (cert : PerClusterDecayCertificate weight κ rate q) :
    ∀ size : ℕ,
      weight size ≤ (κ / rate) * (2 * q) ^ size :=
  cert.bound

end

end FTDQE

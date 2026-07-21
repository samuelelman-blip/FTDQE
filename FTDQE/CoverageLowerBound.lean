import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Coverage lower bound for sampled global refreshes

This file formalises the finite counting and scalar part of Proposition 2.
The bounded-geometry averaging argument, the open-system light-cone witness,
and the quasi-locality tail enter through an explicit coverage certificate.
Lean then derives Eq. (49) and the quantitative necessity that the sampled
space-time coverage be extensive.
-/

namespace FTDQE

noncomputable section

/-- Effective radius appearing in Proposition 2. -/
def effectiveCoverageRadius
    (ρ v : ℝ) (b : ℕ) (δ ξ n ε' : ℝ) : ℝ :=
  ρ + v * (b : ℝ) * δ + ξ * Real.log (n / ε')

/--
Certificate produced by the geometric and Lieb--Robinson part of the proof of
Proposition 2.  `localMass` is the sampling mass of the low-coverage witness
ball.  The final field is the no-hit/light-cone lower bound on the expected
contraction factor.
-/
structure CoverageLowerBoundCertificate
    (q C radius n ε' : ℝ) (b D : ℕ) where
  localMass : ℝ
  localMass_nonneg : 0 ≤ localMass
  localMass_le : localMass ≤ C * radius ^ D / n
  expected_lower :
    (1 - (b : ℝ) * localMass) *
        (1 - (b : ℝ) * ε') ≤ q

/--
Proposition 2, Eq. (49), in composed certificate form:

`q_b ≥ 1 - C_D b r^D / n - b ε'`.
-/
theorem coverage_lower_bound_of_certificate
    (q C radius n ε' : ℝ) (b D : ℕ)
    (hε : 0 ≤ ε')
    (cert : CoverageLowerBoundCertificate q C radius n ε' b D) :
    1 - C * (b : ℝ) * radius ^ D / n - (b : ℝ) * ε' ≤ q := by
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hbm :
      (b : ℝ) * cert.localMass ≤
        C * (b : ℝ) * radius ^ D / n := by
    calc
      (b : ℝ) * cert.localMass ≤
          (b : ℝ) * (C * radius ^ D / n) :=
        mul_le_mul_of_nonneg_left cert.localMass_le hb
      _ = C * (b : ℝ) * radius ^ D / n := by ring
  have hcross :
      0 ≤ ((b : ℝ) * cert.localMass) * ((b : ℝ) * ε') :=
    mul_nonneg
      (mul_nonneg hb cert.localMass_nonneg)
      (mul_nonneg hb hε)
  have hproduct :
      1 - (b : ℝ) * cert.localMass - (b : ℝ) * ε' ≤
        (1 - (b : ℝ) * cert.localMass) *
          (1 - (b : ℝ) * ε') := by
    nlinarith
  calc
    1 - C * (b : ℝ) * radius ^ D / n - (b : ℝ) * ε' ≤
        1 - (b : ℝ) * cert.localMass - (b : ℝ) * ε' := by
      linarith
    _ ≤ (1 - (b : ℝ) * cert.localMass) *
          (1 - (b : ℝ) * ε') := hproduct
    _ ≤ q := cert.expected_lower

/--
Explicit finite-constant form of the statement `b r^D = Ω(n)`.  If the target
contraction is at most `1/2` and the accumulated tail is at most `1/4`, then
at least `n/(4 C_D)` units of sampled coverage are necessary.
-/
theorem half_contraction_requires_extensive_coverage
    (q C radius n ε' : ℝ) (b D : ℕ)
    (hC : 0 < C) (hn : 0 < n)
    (hqhalf : q ≤ 1 / 2)
    (htail : (b : ℝ) * ε' ≤ 1 / 4)
    (hlower :
      1 - C * (b : ℝ) * radius ^ D / n -
          (b : ℝ) * ε' ≤ q) :
    n / (4 * C) ≤ (b : ℝ) * radius ^ D := by
  have hratio :
      1 / 4 ≤ C * ((b : ℝ) * radius ^ D) / n := by
    have :
        1 - C * ((b : ℝ) * radius ^ D) / n -
            (b : ℝ) * ε' ≤ 1 / 2 := by
      calc
        1 - C * ((b : ℝ) * radius ^ D) / n -
            (b : ℝ) * ε' =
          1 - C * (b : ℝ) * radius ^ D / n -
            (b : ℝ) * ε' := by ring
        _ ≤ q := hlower
        _ ≤ 1 / 2 := hqhalf
    linarith
  have hmul :
      (1 / 4 : ℝ) * n ≤ C * ((b : ℝ) * radius ^ D) :=
    (le_div_iff₀ hn).1 hratio
  apply (div_le_iff₀ (mul_pos (by norm_num) hC)).2
  nlinarith

/-- Direct composition of the certificate with the extensive-coverage
consequence. -/
theorem coverage_lower_bound_half_contraction
    (q C radius n ε' : ℝ) (b D : ℕ)
    (hC : 0 < C) (hn : 0 < n) (hε : 0 ≤ ε')
    (hqhalf : q ≤ 1 / 2)
    (htail : (b : ℝ) * ε' ≤ 1 / 4)
    (cert : CoverageLowerBoundCertificate q C radius n ε' b D) :
    n / (4 * C) ≤ (b : ℝ) * radius ^ D := by
  apply half_contraction_requires_extensive_coverage
    q C radius n ε' b D hC hn hqhalf htail
  exact coverage_lower_bound_of_certificate
    q C radius n ε' b D hε cert

end

end FTDQE

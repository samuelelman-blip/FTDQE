import FTDQE.GevreyTimeLocalisation
import FTDQE.DissipatorLipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lieb–Robinson truncation of Gevrey-filtered jumps

This file formalises the certificate-level structure of Theorem 1.  The
short-time Lieb–Robinson approximation and the long-time Gevrey tail are
combined into the standard split estimate.  Choosing the balanced cutoff
`T = r / (2v)` is then proved internally, after which a scalar envelope
certificate yields the final stretched-exponential radius dependence.

The semigroup consequence is stated with an explicit quadratic remainder,
which is the precise finite-constant form of the manuscript's
`O(τ² exp(-2 c r^β'))` term.
-/

namespace FTDQE

noncomputable section

/-- The exponent `β' = min{1, β}` appearing in Theorem 1. -/
def lrBetaPrime (β : ℝ) : ℝ :=
  min 1 β

/-- The stretched-exponential spatial profile in Theorem 1. -/
def lrDecay (c β r : ℝ) : ℝ :=
  Real.exp (-c * r ^ β)

/--
The split estimate obtained by combining the short-time Lieb–Robinson
approximation with the long-time Gevrey tail.
-/
structure LRJumpSplitCertificate
    (jumpError : ℝ → ℝ) (C₁ C₂ μ v a β : ℝ) where
  bound : ∀ r T : ℝ, 0 ≤ r → 0 ≤ T → v * T ≤ r →
    jumpError r ≤
      C₁ * Real.exp (-μ * (r - v * T)) +
        C₂ * Real.exp (-a * T ^ β)

/--
Choosing `T = r / (2v)` in the split estimate gives the two balanced decay
terms used in the proof of Theorem 1.
-/
theorem lr_balanced_cutoff_bound
    (jumpError : ℝ → ℝ) (C₁ C₂ μ v a β r : ℝ)
    (hv : 0 < v) (hr : 0 ≤ r)
    (cert : LRJumpSplitCertificate jumpError C₁ C₂ μ v a β) :
    jumpError r ≤
      C₁ * Real.exp (-μ * (r / 2)) +
        C₂ * Real.exp (-a * (r / (2 * v)) ^ β) := by
  let T : ℝ := r / (2 * v)
  have h2v : 0 < 2 * v := mul_pos (by norm_num) hv
  have hT : 0 ≤ T := by
    exact div_nonneg hr h2v.le
  have hvT : v * T = r / 2 := by
    dsimp [T]
    field_simp [hv.ne']
    <;> ring
  have hvTle : v * T ≤ r := by
    rw [hvT]
    linarith
  have hsplit := cert.bound r T hr hT hvTle
  have hrsub : r - v * T = r / 2 := by
    rw [hvT]
    ring
  simpa [T, hrsub] using hsplit

/--
Scalar envelope certificate absorbing the balanced spatial and temporal terms
into one stretched exponential with exponent `min 1 β`.
-/
structure LRStretchedEnvelopeCertificate
    (C₁ C₂ μ v a β C c : ℝ) where
  C_pos : 0 < C
  c_pos : 0 < c
  bound : ∀ r : ℝ, 0 ≤ r →
    C₁ * Real.exp (-μ * (r / 2)) +
        C₂ * Real.exp (-a * (r / (2 * v)) ^ β) ≤
      C * lrDecay c (lrBetaPrime β) r

/--
The jump-operator part of Theorem 1 in composed certificate form.
-/
theorem lieb_robinson_jump_truncation
    (jumpError : ℝ → ℝ) (C₁ C₂ μ v a β C c : ℝ)
    (hv : 0 < v)
    (split : LRJumpSplitCertificate jumpError C₁ C₂ μ v a β)
    (envelope : LRStretchedEnvelopeCertificate C₁ C₂ μ v a β C c) :
    ∀ r : ℝ, 0 ≤ r →
      jumpError r ≤ C * lrDecay c (lrBetaPrime β) r := by
  intro r hr
  exact (lr_balanced_cutoff_bound
    jumpError C₁ C₂ μ v a β r hv hr split).trans
      (envelope.bound r hr)

/--
Explicit form of the semigroup consequence in Theorem 1.

The generator estimate is supplied by Proposition 1 after summing the
individual jump errors.  The function `quadraticRemainder` records the second
order Duhamel remainder; bounding it by the square of the radius profile is the
finite-constant version of the manuscript's big-O term.
-/
theorem semigroup_truncation_with_quadratic_remainder
    (generatorError : ℝ → ℝ)
    (semigroupError quadraticRemainder : ℝ → ℝ → ℝ)
    (C𝓛 C₂ c β : ℝ)
    (hgenerator : ∀ r : ℝ, 0 ≤ r →
      generatorError r ≤ C𝓛 * lrDecay c β r)
    (hduhamel : ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r →
      semigroupError τ r ≤
        τ * generatorError r + quadraticRemainder τ r)
    (hquadratic : ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r →
      quadraticRemainder τ r ≤
        C₂ * τ ^ 2 * (lrDecay c β r) ^ 2) :
    ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r →
      semigroupError τ r ≤
        C𝓛 * τ * lrDecay c β r +
          C₂ * τ ^ 2 * (lrDecay c β r) ^ 2 := by
  intro τ r hτ hr
  have hlinear :
      τ * generatorError r ≤ τ * (C𝓛 * lrDecay c β r) :=
    mul_le_mul_of_nonneg_left (hgenerator r hr) hτ
  calc
    semigroupError τ r ≤
        τ * generatorError r + quadraticRemainder τ r :=
      hduhamel τ r hτ hr
    _ ≤ τ * (C𝓛 * lrDecay c β r) +
          C₂ * τ ^ 2 * (lrDecay c β r) ^ 2 :=
      add_le_add hlinear (hquadratic τ r hτ hr)
    _ = C𝓛 * τ * lrDecay c β r +
          C₂ * τ ^ 2 * (lrDecay c β r) ^ 2 := by
      ring

end

end FTDQE

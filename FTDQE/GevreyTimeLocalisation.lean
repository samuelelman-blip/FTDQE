import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Time localisation of a Gevrey filter

This file formalises the certificate-level structure of Lemma 1.  The analytic
Fourier integration-by-parts estimate and its scalar optimisation are recorded
separately.  Their composition yields the stretched-exponential pointwise
bound.  A second theorem combines two one-sided tail estimates into the
manuscript's two-sided tail bound.

The remaining infrastructure boundary is explicit: constructing the Fourier
integration-by-parts certificate directly from a compactly supported Gevrey
frequency profile, and constructing the one-sided tail certificates from the
corresponding improper integrals, are separate analytic developments.
-/

namespace FTDQE

/-- The stretched-exponential profile occurring in Lemma 1. -/
def stretchedExponential (s c x : ℝ) : ℝ :=
  Real.exp (-c * x ^ (1 / s))

/-- The pointwise prefactor after optimising the integration-by-parts order. -/
def gevreyPointwiseConstant (L C₁ q : ℝ) : ℝ :=
  L * C₁ * q / (2 * Real.pi)

/--
The Fourier integration-by-parts estimate before choosing the derivative order.
Here `fAbs t` represents `|f(t)|`, `L` is the rescaled support length, and the
factor involving `m` is the Gevrey derivative estimate after `m` integrations
by parts.
-/
structure GevreyIBPCertificate
    (fAbs : ℝ → ℝ) (Δ L C₁ C₂ s : ℝ) where
  bound : ∀ (t : ℝ) (m : ℕ), 1 ≤ |Δ * t| →
    fAbs t ≤
      (Δ * L * C₁ / (2 * Real.pi)) *
        (C₂ * (m : ℝ) ^ s / |Δ * t|) ^ m

/--
Certificate for the scalar optimisation of the integration-by-parts order.
The manuscript obtains this by taking
`m = floor((x / (exp s * C₂))^(1/s))`.
-/
structure GevreyOrderOptimisationCertificate
    (C₂ s c q : ℝ) where
  optimise : ∀ x : ℝ, 1 ≤ x →
    ∃ m : ℕ,
      (C₂ * (m : ℝ) ^ s / x) ^ m ≤
        q * stretchedExponential s c x

/--
Long-time part of Eq. (8): the integration-by-parts estimate and the optimised
choice of derivative order imply stretched-exponential decay.
-/
theorem gevrey_pointwise_long_time
    (fAbs : ℝ → ℝ) (Δ L C₁ C₂ s c q : ℝ)
    (hΔ : 0 < Δ) (hL : 0 ≤ L) (hC₁ : 0 ≤ C₁)
    (hibp : GevreyIBPCertificate fAbs Δ L C₁ C₂ s)
    (hopt : GevreyOrderOptimisationCertificate C₂ s c q) :
    ∀ t : ℝ, 1 ≤ |Δ * t| →
      fAbs t ≤
        gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t| := by
  intro t ht
  rcases hopt.optimise |Δ * t| ht with ⟨m, hm⟩
  have hpref : 0 ≤ Δ * L * C₁ / (2 * Real.pi) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg hΔ.le hL) hC₁)
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  calc
    fAbs t ≤
        (Δ * L * C₁ / (2 * Real.pi)) *
          (C₂ * (m : ℝ) ^ s / |Δ * t|) ^ m :=
      hibp.bound t m ht
    _ ≤ (Δ * L * C₁ / (2 * Real.pi)) *
          (q * stretchedExponential s c |Δ * t|) :=
      mul_le_mul_of_nonneg_left hm hpref
    _ = gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t| := by
      unfold gevreyPointwiseConstant
      ring

/--
Full pointwise form of Eq. (8).  The bounded-time estimate is isolated as an
explicit input; for a normalised filter it follows from the elementary Fourier
integral bound and enlargement of the constant.
-/
theorem gevrey_pointwise_of_certificates
    (fAbs : ℝ → ℝ) (Δ L C₁ C₂ s c q : ℝ)
    (hΔ : 0 < Δ) (hL : 0 ≤ L) (hC₁ : 0 ≤ C₁)
    (hibp : GevreyIBPCertificate fAbs Δ L C₁ C₂ s)
    (hopt : GevreyOrderOptimisationCertificate C₂ s c q)
    (hshort : ∀ t : ℝ, |Δ * t| < 1 →
      fAbs t ≤
        gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t|) :
    ∀ t : ℝ,
      fAbs t ≤
        gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t| := by
  intro t
  by_cases ht : 1 ≤ |Δ * t|
  · exact gevrey_pointwise_long_time
      fAbs Δ L C₁ C₂ s c q hΔ hL hC₁ hibp hopt t ht
  · exact hshort t (lt_of_not_ge ht)

/-- The tail profile in Eq. (9), with the exponent constant halved. -/
def gevreyTailProfile (s c Δ T : ℝ) : ℝ :=
  stretchedExponential s (c / 2) (Δ * T)

/--
Two one-sided integral estimates imply the two-sided tail estimate in Eq. (9).
The functions `positiveTail`, `negativeTail`, and `totalTail` represent the
corresponding improper-integral values.
-/
theorem gevrey_two_sided_tail_bound
    (positiveTail negativeTail totalTail : ℝ → ℝ)
    (Δ s c C₃ : ℝ)
    (hdecomp : ∀ T : ℝ,
      totalTail T ≤ positiveTail T + negativeTail T)
    (hpositive : ∀ T : ℝ, 1 / Δ ≤ T →
      positiveTail T ≤ (C₃ / 2) * gevreyTailProfile s c Δ T)
    (hnegative : ∀ T : ℝ, 1 / Δ ≤ T →
      negativeTail T ≤ (C₃ / 2) * gevreyTailProfile s c Δ T) :
    ∀ T : ℝ, 1 / Δ ≤ T →
      totalTail T ≤ C₃ * gevreyTailProfile s c Δ T := by
  intro T hT
  calc
    totalTail T ≤ positiveTail T + negativeTail T := hdecomp T
    _ ≤ (C₃ / 2) * gevreyTailProfile s c Δ T +
          (C₃ / 2) * gevreyTailProfile s c Δ T :=
      add_le_add (hpositive T hT) (hnegative T hT)
    _ = C₃ * gevreyTailProfile s c Δ T := by ring

/--
Lemma 1 in composed certificate form: Eq. (8) and Eq. (9) are returned together.
-/
theorem gevrey_time_localisation_of_certificates
    (fAbs positiveTail negativeTail totalTail : ℝ → ℝ)
    (Δ L C₁ C₂ s c q C₃ : ℝ)
    (hΔ : 0 < Δ) (hL : 0 ≤ L) (hC₁ : 0 ≤ C₁)
    (hibp : GevreyIBPCertificate fAbs Δ L C₁ C₂ s)
    (hopt : GevreyOrderOptimisationCertificate C₂ s c q)
    (hshort : ∀ t : ℝ, |Δ * t| < 1 →
      fAbs t ≤
        gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t|)
    (hdecomp : ∀ T : ℝ,
      totalTail T ≤ positiveTail T + negativeTail T)
    (hpositive : ∀ T : ℝ, 1 / Δ ≤ T →
      positiveTail T ≤ (C₃ / 2) * gevreyTailProfile s c Δ T)
    (hnegative : ∀ T : ℝ, 1 / Δ ≤ T →
      negativeTail T ≤ (C₃ / 2) * gevreyTailProfile s c Δ T) :
    (∀ t : ℝ,
      fAbs t ≤
        gevreyPointwiseConstant L C₁ q * Δ *
          stretchedExponential s c |Δ * t|) ∧
    (∀ T : ℝ, 1 / Δ ≤ T →
      totalTail T ≤ C₃ * gevreyTailProfile s c Δ T) := by
  constructor
  · exact gevrey_pointwise_of_certificates
      fAbs Δ L C₁ C₂ s c q hΔ hL hC₁ hibp hopt hshort
  · exact gevrey_two_sided_tail_bound
      positiveTail negativeTail totalTail Δ s c C₃
      hdecomp hpositive hnegative

end FTDQE

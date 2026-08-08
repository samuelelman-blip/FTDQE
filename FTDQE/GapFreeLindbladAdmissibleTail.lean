import FTDQE.GapFreeLindbladAdmissibleClosure

/-!
# Derived derivative tail for admissible weights

The derivative-weighted integrability needed by the improper integration-by-parts
identity follows from the public admissibility assumptions and the already-derived
weighted boundary decay.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology Interval

noncomputable section

private theorem closure_deriv_exp_mul (lam x : ℝ) :
    deriv (fun s : ℝ => Real.exp (lam * s)) x = lam * Real.exp (lam * x) := by
  have h := (((hasDerivAt_id x).const_mul lam).exp).deriv
  simpa [mul_comm] using h

/-- The derivative-weighted exponential is integrable on the positive half-line.
This is a consequence, not an additional admissibility hypothesis. -/
theorem AdmissibleWeight.deriv_integrable
    {ε : ℝ} {m : ℝ → ℝ} (hm : AdmissibleWeight ε m) :
    IntegrableOn (fun s => deriv m s * Real.exp (-2 * ε * s)) (Ioi 0) := by
  let f : ℝ → ℝ := fun s => m s * Real.exp (-2 * ε * s)
  let g : ℝ → ℝ := fun s => deriv m s * Real.exp (-2 * ε * s)
  let R : ℝ := -m 0 + (2 * ε) * ∫ s in Ioi (0 : ℝ), f s
  have hexpAC (T : ℝ) (_hT : 0 ≤ T) :
      AbsolutelyContinuousOnInterval (fun s : ℝ => Real.exp (-2 * ε * s)) 0 T := by
    have hlin : ContDiff ℝ 1 (fun s : ℝ => (-2 * ε) * s) :=
      contDiff_const.mul contDiff_id
    exact hlin.exp.contDiffOn.absolutelyContinuousOnInterval
  have hfinite (T : ℝ) (hT : 0 ≤ T) :
      (∫ s in (0 : ℝ)..T, g s) =
        m T * Real.exp (-2 * ε * T) - m 0 +
          (2 * ε) * ∫ s in (0 : ℝ)..T, f s := by
    have hip := (hm.localAC T hT).integral_mul_deriv_eq_deriv_mul (hexpAC T hT)
    rw [show deriv (fun s : ℝ => Real.exp (-2 * ε * s)) =
      fun s => (-2 * ε) * Real.exp (-2 * ε * s) from
        funext (closure_deriv_exp_mul (-2 * ε))] at hip
    have hleft :
        (∫ s in (0 : ℝ)..T,
          m s * ((-2 * ε) * Real.exp (-2 * ε * s))) =
          (-2 * ε) * ∫ s in (0 : ℝ)..T, f s := by
      calc
        (∫ s in (0 : ℝ)..T,
          m s * ((-2 * ε) * Real.exp (-2 * ε * s))) =
            ∫ s in (0 : ℝ)..T, (-2 * ε) * f s := by
              congr 1
              funext s
              simp only [f]
              ring
        _ = (-2 * ε) * ∫ s in (0 : ℝ)..T, f s := by
              rw [intervalIntegral.integral_const_mul]
    rw [hleft] at hip
    simp only [g] at hip ⊢
    simp at hip
    have hargT : -(2 * ε * T) = -2 * ε * T := by ring
    rw [hargT] at hip
    linarith
  have hpartial_f : Tendsto
      (fun T => ∫ s in (0 : ℝ)..T, f s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), f s)) := by
    exact intervalIntegral_tendsto_integral_Ioi 0 hm.weighted_integrable tendsto_id
  have hboundary : Tendsto
      (fun T => m T * Real.exp (-2 * ε * T)) atTop (𝓝 0) :=
    hm.boundary_decay
  have hscaled : Tendsto
      (fun T => (2 * ε) * ∫ s in (0 : ℝ)..T, f s) atTop
      (𝓝 ((2 * ε) * ∫ s in Ioi (0 : ℝ), f s)) := by
    exact tendsto_const_nhds.mul hpartial_f
  have hrhs : Tendsto
      (fun T => m T * Real.exp (-2 * ε * T) - m 0 +
        (2 * ε) * ∫ s in (0 : ℝ)..T, f s) atTop (𝓝 R) := by
    simpa [R] using (hboundary.sub_const (m 0)).add hscaled
  have heq_event : ∀ᶠ T in atTop,
      (∫ s in (0 : ℝ)..T, g s) =
        m T * Real.exp (-2 * ε * T) - m 0 +
          (2 * ε) * ∫ s in (0 : ℝ)..T, f s := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hfinite T hT
  have hpartial_g : Tendsto
      (fun T => ∫ s in (0 : ℝ)..T, g s) atTop (𝓝 R) := by
    exact hrhs.congr' (heq_event.mono fun T hT => hT.symm)
  have hder_global : ∀ᵐ s ∂volume, s ∈ Ioi (0 : ℝ) → 0 ≤ deriv m s := by
    have h := hm.deriv_nonneg
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h
    exact h
  have hg_global : ∀ᵐ s ∂volume, s ∈ Ioi (0 : ℝ) → 0 ≤ g s := by
    filter_upwards [hder_global] with s hs
    intro hs0
    exact mul_nonneg (hs hs0) (Real.exp_pos _).le
  have hnorm_event : ∀ᶠ T in atTop,
      (∫ s in (0 : ℝ)..T, ‖g s‖) = ∫ s in (0 : ℝ)..T, g s := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    have hg_nonneg : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) T)), 0 ≤ g s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hg_global] with s hs
      intro hsI
      exact hs hsI.1
    exact MeasureTheory.integral_congr_ae
      (hg_nonneg.mono fun s hs => by
        change |g s| = g s
        exact abs_of_nonneg hs)
  have hnorm : Tendsto
      (fun T => ∫ s in (0 : ℝ)..T, ‖g s‖) atTop (𝓝 R) := by
    exact hpartial_g.congr' (hnorm_event.mono fun T hT => hT.symm)
  have hlocal : ∀ T : ℝ, IntegrableOn g (Ioc 0 T) := by
    intro T
    by_cases hT : 0 ≤ T
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
      have hder := (hm.localAC T hT).intervalIntegrable_deriv
      have hexpCont : ContinuousOn (fun s : ℝ => Real.exp (-2 * ε * s)) (uIcc 0 T) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      exact hder.mul_continuousOn hexpCont
    · have hTle : T ≤ 0 := le_of_not_ge hT
      have hempty : Ioc (0 : ℝ) T = ∅ := by
        ext x
        simp only [mem_Ioc, mem_empty_iff_false, iff_false]
        intro hx
        linarith [hx.1, hx.2, hTle]
      rw [hempty]
      exact integrableOn_empty
  exact integrableOn_Ioi_of_intervalIntegral_norm_tendsto
    (f := g) (b := fun T : ℝ => T) (μ := volume)
    R 0 hlocal tendsto_id hnorm

end

end GapFreeLindblad
end FTDQE

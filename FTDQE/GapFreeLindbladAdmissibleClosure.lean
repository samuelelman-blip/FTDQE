import FTDQE.GapFreeLindbladAdmissible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Closure of the admissible-weight hypotheses

This file derives the tail conditions used by the improper integration-by-parts layer
from the manuscript-level admissibility assumptions.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology Interval

noncomputable section

/-- Public admissibility assumptions for a weight on `[0,∞)`. -/
structure AdmissibleWeight (ε : ℝ) (m : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  nonneg : ∀ s, 0 ≤ s → 0 ≤ m s
  localAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval m 0 T
  deriv_nonneg : ∀ᵐ s ∂(volume.restrict (Ioi 0)), 0 ≤ deriv m s
  weighted_integrable : IntegrableOn (fun s => m s * Real.exp (-2 * ε * s)) (Ioi 0)

/-- Nonnegative a.e. derivative plus local absolute continuity makes an admissible weight
monotone on the nonnegative half-line. -/
theorem AdmissibleWeight.monotoneOn_Ici
    {ε : ℝ} {m : ℝ → ℝ} (hm : AdmissibleWeight ε m) :
    MonotoneOn m (Ici 0) := by
  intro x hx y hy hxy
  have hAC : AbsolutelyContinuousOnInterval m x y := by
    apply (hm.localAC y hy).mono
    rw [uIcc_of_le hxy, uIcc_of_le hy]
    exact Icc_subset_Icc hx le_rfl
  have hder_global : ∀ᵐ s ∂volume, s ∈ Ioi (0 : ℝ) → 0 ≤ deriv m s := by
    have h := hm.deriv_nonneg
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h
    exact h
  have hder_ioc : ∀ᵐ s ∂(volume.restrict (Ioc x y)), 0 ≤ deriv m s := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hder_global] with s hs
    intro hsxy
    exact hs (lt_of_le_of_lt hx hsxy.1)
  have hrestr : volume.restrict (Ioc x y) = volume.restrict (Icc x y) :=
    Measure.restrict_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
  have hder_icc : ∀ᵐ s ∂(volume.restrict (Icc x y)), 0 ≤ deriv m s := by
    rw [← hrestr]
    exact hder_ioc
  have hint_nonneg : 0 ≤ ∫ s in x..y, deriv m s := by
    exact intervalIntegral.integral_nonneg_of_ae_restrict hxy hder_icc
  rw [hAC.integral_deriv_eq_sub] at hint_nonneg
  linarith

/-- The weighted boundary term vanishes at infinity.  This is derived from the single
weighted-integrability hypothesis and monotonicity; it is not an additional admissibility
assumption. -/
theorem AdmissibleWeight.boundary_decay
    {ε : ℝ} {m : ℝ → ℝ} (hm : AdmissibleWeight ε m) :
    Tendsto (fun s => m s * Real.exp (-2 * ε * s)) atTop (𝓝 0) := by
  let f : ℝ → ℝ := fun s => m s * Real.exp (-2 * ε * s)
  let c : ℝ → ℝ := fun T => m T * Real.exp (-2 * ε * (T + 1))
  have hf_nonneg : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ f s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (hm.nonneg s hs.le) (Real.exp_pos _).le
  have htail : Tendsto (fun T : ℝ => ∫ s in Ioi T, f s) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (f := f) (μ := volume) tendsto_id
  have hc_nonneg : ∀ᶠ T : ℝ in atTop, 0 ≤ c T := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact mul_nonneg (hm.nonneg T hT) (Real.exp_pos _).le
  have hc_le_tail : ∀ᶠ T : ℝ in atTop, c T ≤ ∫ s in Ioi T, f s := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hT1 : T ≤ T + 1 := by linarith
    have htailInt : IntegrableOn f (Ioi T) :=
      hm.weighted_integrable.mono_set (Ioi_subset_Ioi hT)
    have hint : IntervalIntegrable f volume T (T + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT1]
      exact hm.weighted_integrable.mono_set
        (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hT))
    have hcint : IntervalIntegrable (fun _s : ℝ => c T) volume T (T + 1) :=
      intervalIntegrable_const
    have hpoint : ∀ s ∈ Icc T (T + 1), c T ≤ f s := by
      intro s hs
      have hs0 : 0 ≤ s := hT.trans hs.1
      have hmle : m T ≤ m s :=
        hm.monotoneOn_Ici hT hs0 hs.1
      have hexple : Real.exp (-2 * ε * (T + 1)) ≤ Real.exp (-2 * ε * s) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hm.eps_pos, hs.2]
      exact mul_le_mul hmle hexple (Real.exp_pos _).le (hm.nonneg s hs0)
    have hlowInt :
        (∫ s in T..T + 1, c T) ≤ ∫ s in T..T + 1, f s := by
      exact intervalIntegral.integral_mono_on hT1 hcint hint hpoint
    have hlow : c T ≤ ∫ s in T..T + 1, f s := by
      simpa using hlowInt
    have hf_tail_nonneg : ∀ᵐ s ∂(volume.restrict (Ioi T)), 0 ≤ f s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with s
      intro hs
      have hs0 : 0 ≤ s := hT.trans hs.le
      exact mul_nonneg (hm.nonneg s hs0) (Real.exp_pos _).le
    have hupper : (∫ s in T..T + 1, f s) ≤ ∫ s in Ioi T, f s := by
      rw [intervalIntegral.integral_of_le hT1]
      exact setIntegral_mono_set htailInt hf_tail_nonneg Ioc_subset_Ioi_self.eventuallyLE
    exact hlow.trans hupper
  have hc_zero : Tendsto c atTop (𝓝 0) :=
    squeeze_zero' hc_nonneg hc_le_tail htail
  have hscaled :
      Tendsto (fun T => Real.exp (2 * ε) * c T) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hc_zero)
  have hid : (fun T => Real.exp (2 * ε) * c T) = f := by
    funext T
    simp only [c, f]
    calc
      Real.exp (2 * ε) * (m T * Real.exp (-2 * ε * (T + 1))) =
          m T * (Real.exp (2 * ε) * Real.exp (-2 * ε * (T + 1))) := by ring
      _ = m T * Real.exp (2 * ε + (-2 * ε * (T + 1))) := by
          rw [Real.exp_add]
      _ = m T * Real.exp (-2 * ε * T) := by
          congr 2
          ring
  rw [hid] at hscaled
  exact hscaled

end

end GapFreeLindblad
end FTDQE

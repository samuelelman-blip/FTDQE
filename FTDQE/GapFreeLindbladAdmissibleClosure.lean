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

end

end GapFreeLindblad
end FTDQE

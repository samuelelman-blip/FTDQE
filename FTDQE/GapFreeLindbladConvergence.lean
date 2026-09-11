import FTDQE.GapFreeLindbladGKLS
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Coercive `1/t` convergence estimate

Scalar analytic layer of manuscript Theorem 2.  Once the operator calculation supplies an
instantaneous nonnegative dissipation `D` with `κ q ≤ D`, and the total available energy drop
bounds `∫ D` by `W`, the target error satisfies `q(t) ≤ W/(κ t)`.
-/

namespace FTDQE
namespace GapFreeLindblad

open Set intervalIntegral

noncomputable section

/-- Pointwise coercivity integrates to the required bound on `κ ∫ q`. -/
theorem coercivity_integral_bound
    {q D : ℝ → ℝ} {κ W t : ℝ}
    (ht : 0 ≤ t) (hκ : 0 ≤ κ)
    (hq_int : IntervalIntegrable q MeasureTheory.volume 0 t)
    (hD_int : IntervalIntegrable D MeasureTheory.volume 0 t)
    (hcoerc : ∀ s ∈ Icc (0 : ℝ) t, κ * q s ≤ D s)
    (henergy : ∫ s in (0 : ℝ)..t, D s ≤ W) :
    κ * ∫ s in (0 : ℝ)..t, q s ≤ W := by
  have hκq_int : IntervalIntegrable (fun s => κ * q s) MeasureTheory.volume 0 t :=
    hq_int.const_mul κ
  have hmono :
      ∫ s in (0 : ℝ)..t, κ * q s ≤ ∫ s in (0 : ℝ)..t, D s := by
    apply intervalIntegral.integral_mono_on ht hκq_int hD_int
    exact hcoerc
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono.trans henergy

/-- Manuscript Theorem 2, scalar analytic core.

No spectral gap occurs in the statement.  `κ` is only the explicit coercivity constant and
`W` is the available energy-width bound. -/
theorem gapFree_one_over_t
    {q D : ℝ → ℝ} {κ W t : ℝ}
    (hκ : 0 < κ) (ht : 0 < t)
    (hq_nonneg : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ q s)
    (hq_anti : Antitone q)
    (hq_int : IntervalIntegrable q MeasureTheory.volume 0 t)
    (hD_int : IntervalIntegrable D MeasureTheory.volume 0 t)
    (hcoerc : ∀ s ∈ Icc (0 : ℝ) t, κ * q s ≤ D s)
    (henergy : ∫ s in (0 : ℝ)..t, D s ≤ W) :
    q t ≤ W / (κ * t) := by
  apply antitone_endpoint_le_of_integral_bound hκ ht hq_nonneg hq_anti hq_int
  exact coercivity_integral_bound ht.le hκ.le hq_int hD_int hcoerc henergy

end

end GapFreeLindblad
end FTDQE

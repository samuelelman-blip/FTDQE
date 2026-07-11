import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral Grönwall inequality

A scalar integral form of Grönwall's inequality used in the proof of the
perturbed-relaxation lemma.
-/

namespace FTDQE

open Set intervalIntegral

/-- If a continuous nonnegative function satisfies

`u(x) ≤ A + B ∫₀ˣ u(s) ds`

on `[0,t]`, then `u(t) ≤ A exp(Bt)`.
-/
theorem integral_gronwall
    (u : ℝ → ℝ) (A B t : ℝ)
    (hu : Continuous u)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hu_nonneg : ∀ x ∈ Icc (0 : ℝ) t, 0 ≤ u x)
    (hineq : ∀ x ∈ Icc (0 : ℝ) t,
      u x ≤ A + B * ∫ s in (0 : ℝ)..x, u s) :
    u t ≤ A * Real.exp (B * t) := by
  let F : ℝ → ℝ := fun x => A + B * ∫ s in (0 : ℝ)..x, u s
  have hFderiv : ∀ x : ℝ, HasDerivAt F (B * u x) x := by
    intro x
    dsimp [F]
    convert ((hu.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul B).const_add A using 1 <;>
      ring
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hFderiv x).continuousAt
  have hF0 : ‖F 0‖ ≤ A := by
    simp [F, Real.norm_eq_abs, abs_of_nonneg hA]
  have hbound : ∀ x ∈ Ico (0 : ℝ) t, ‖B * u x‖ ≤ B * ‖F x‖ + 0 := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) t := ⟨hx.1, le_of_lt hx.2⟩
    have hux : 0 ≤ u x := hu_nonneg x hx'
    have hle : u x ≤ F x := by simpa [F] using hineq x hx'
    have hFx : 0 ≤ F x := hux.trans hle
    rw [add_zero, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB hux),
      abs_of_nonneg hFx]
    exact mul_le_mul_of_nonneg_left hle hB
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    hFcont.continuousOn
    (fun x hx => (hFderiv x).hasDerivWithinAt)
    hF0 hbound t ⟨ht, le_rfl⟩
  have hut : u t ≤ F t := by
    simpa [F] using hineq t ⟨ht, le_rfl⟩
  have hut0 : 0 ≤ u t := hu_nonneg t ⟨ht, le_rfl⟩
  have hFt0 : 0 ≤ F t := hut0.trans hut
  calc
    u t ≤ F t := hut
    _ = ‖F t‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hFt0]
    _ ≤ A * Real.exp (B * t) := by
      simpa [gronwallBound_ε0, sub_zero] using hG

end FTDQE

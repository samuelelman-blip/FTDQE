import FTDQE.StationaryStateStability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cesàro stationary-state existence

This file supplies the quantitative `O(1 / T)` residual bridge used in the
Cesàro proof of Lemma 3(i).
-/

namespace FTDQE

open Filter
open scoped Topology

/-- A norm bound of order `C / (n + 1)` forces a sequence to converge to zero. -/
theorem tendsto_zero_of_norm_le_const_div_add_one
    {X : Type*} [NormedAddCommGroup X]
    (f : ℕ → X) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ C / ((n : ℝ) + 1)) :
    Tendsto f atTop (𝓝 0) := by
  apply squeeze_zero_norm hbound
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/--
A compact sequence of Cesàro approximants with the standard inverse-time
generator residual has a stationary cluster point.
-/
theorem exists_stationary_of_compact_cesaro_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (stateSpace : Set X)
    (hcompact : IsCompact stateSpace)
    (approximants : ℕ → X)
    (hmem : ∀ n : ℕ, approximants n ∈ stateSpace)
    (C : ℝ)
    (hresidualBound : ∀ n : ℕ,
      ‖L (approximants n)‖ ≤ C / ((n : ℝ) + 1)) :
    ∃ σ' ∈ stateSpace, IsStationary L σ' := by
  apply exists_stationary_of_compact_approximants
    L stateSpace hcompact approximants hmem
  exact tendsto_zero_of_norm_le_const_div_add_one
    (fun n : ℕ => L (approximants n)) C hresidualBound

end FTDQE

import FTDQE.GapFreeLindbladDarkness
import Mathlib.Analysis.Matrix.Order

/-!
# Exact Lyapunov identity for the constant Cauchy kernel

This file specializes the general cross-frequency identity to the manuscript's constant
weight `m₀ = 2 ε`.  The resulting drift is exactly `-ε B†B`, so negativity is proved as
an operator statement with no frequency-separation assumption.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- Sum of all frequency components in a finite downward family. -/
def componentSum (A : ι → QMatrix d) : QMatrix d := ∑ i, A i

/-- Expanding the square of the summed component produces the full double Gram sum. -/
theorem doubleGramSum_eq
    (A : ι → QMatrix d) :
    (∑ i, ∑ j, (A j)ᴴ * A i) = (componentSum A)ᴴ * componentSum A := by
  classical
  simp [componentSum, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_comm]

/-- Complex-cast version of the constant-kernel drift coefficient. -/
theorem constantKernel_drift_factor_complex
    {ε ω ω' : ℝ}
    (hε : 0 < ε) (hω : ω ≤ -ε) (hω' : ω' ≤ -ε) :
    ((constantKernel ε ω ω' : ℝ) : ℂ) *
        (((ω : ℂ) + (ω' : ℂ)) / 2) = (-(ε : ℝ) : ℂ) := by
  norm_cast
  exact constantKernel_drift_factor hε hω hω'

/-- Exact operator identity `L†(H) = -ε B†B` for the constant Cauchy kernel.

This is the constant-weight instance of the manuscript's kernel--Lyapunov theorem. -/
theorem constantKernel_correlatedAdjoint_energy
    {H : QMatrix d} {ε : ℝ} {ω : ι → ℝ} {A : ι → QMatrix d}
    (hε : 0 < ε)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε) :
    correlatedAdjoint
        (fun i j => ((constantKernel ε (ω i) (ω j) : ℝ) : ℂ)) A H =
      (-(ε : ℝ) : ℂ) • ((componentSum A)ᴴ * componentSum A) := by
  rw [correlatedAdjoint_energy
    (fun i j => ((constantKernel ε (ω i) (ω j) : ℝ) : ℂ)) hH hA]
  simp_rw [constantKernel_drift_factor_complex hε (hdown _) (hdown _)]
  rw [← Finset.smul_sum]
  congr 1
  rw [doubleGramSum_eq]

/-- The positive operator whose negative is the constant-kernel energy drift. -/
def constantLyapunovOperator (ε : ℝ) (A : ι → QMatrix d) : QMatrix d :=
  (ε : ℂ) • ((componentSum A)ᴴ * componentSum A)

/-- `K₀ = ε B†B` is positive semidefinite for `ε ≥ 0`. -/
theorem constantLyapunovOperator_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (A : ι → QMatrix d) :
    (constantLyapunovOperator ε A).PosSemidef := by
  have hgram : ((componentSum A)ᴴ * componentSum A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (componentSum A)
  have hεc : (0 : ℂ) ≤ (ε : ℂ) := by exact_mod_cast hε
  exact hgram.smul hεc

/-- The constant-kernel energy drift is negative semidefinite. -/
theorem constantKernel_energy_nonpos
    {H : QMatrix d} {ε : ℝ} {ω : ι → ℝ} {A : ι → QMatrix d}
    (hε : 0 < ε)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε) :
    correlatedAdjoint
        (fun i j => ((constantKernel ε (ω i) (ω j) : ℝ) : ℂ)) A H ≤ 0 := by
  rw [constantKernel_correlatedAdjoint_energy hε hH hA hdown]
  have hK := constantLyapunovOperator_posSemidef hε.le A
  have hnonneg : 0 ≤ constantLyapunovOperator ε A := hK.nonneg
  simpa [constantLyapunovOperator] using (neg_nonpos.mpr hnonneg)

end

end GapFreeLindblad
end FTDQE

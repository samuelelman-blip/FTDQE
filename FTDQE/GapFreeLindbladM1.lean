import FTDQE.GapFreeLindbladCauchyPSD
import FTDQE.GapFreeLindbladAbstractLyapunov

/-!
# The concrete linear-weight (`m₁`) gap-free generator

This file packages the manuscript's preferred nonconstant weight
`m₁(s)=4 ε² s`. For downward frequencies, its Kossakowski matrix is the Hadamard square
of the base Cauchy kernel and its energy-drift kernel is a positive multiple of the base
Cauchy matrix. Hence both GKLS validity and exact Lyapunov monotonicity follow without any
frequency-separation lower bound.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

def m1DriftKernel (ε : ℝ) (ω : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((2 * ε^2 / (-(ω i + ω j)) : ℝ) : ℂ)

theorem m1DriftKernel_eq_smul_cauchy
    (ε : ℝ) (ω : ι → ℝ) :
    m1DriftKernel ε ω =
      ((2 * ε^2 : ℝ) : ℂ) • cauchyFrequencyMatrix ω := by
  ext i j
  simp [m1DriftKernel, cauchyFrequencyMatrix, Matrix.smul_apply, div_eq_mul_inv]
  ring

theorem m1DriftKernel_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (ω : ι → ℝ) (hωneg : ∀ i, ω i < 0) :
    (m1DriftKernel ε ω).PosSemidef := by
  rw [m1DriftKernel_eq_smul_cauchy]
  have hC := cauchyFrequencyMatrix_posSemidef ω hωneg
  have hs : (0 : ℂ) ≤ ((2 * ε^2 : ℝ) : ℂ) := by
    exact_mod_cast mul_nonneg (by norm_num) (sq_nonneg ε)
  exact hC.smul hs

theorem linearKernel_weighted_eq_neg_m1Drift
    {ε : ℝ} (hε : 0 < ε) {ω ω' : ℝ}
    (hω : ω ≤ -ε) (hω' : ω' ≤ -ε) :
    ((linearKernel ε ω ω' : ℝ) : ℂ) *
        (((ω : ℂ) + (ω' : ℂ)) / 2) =
      -(((2 * ε^2 / (-(ω + ω')) : ℝ) : ℂ)) := by
  norm_cast
  exact linearKernel_drift_factor hε hω hω'

theorem m1Kossakowski_posSemidef
    {ε : ℝ} (hε : 0 < ε) (ω : ι → ℝ) (hdown : ∀ i, ω i ≤ -ε) :
    (linearKernelMatrix ε ω).PosSemidef := by
  apply linearKernelMatrix_posSemidef hε.le ω
  intro i
  linarith [hdown i]

theorem m1_exists_GKLS_jumps
    {ε : ℝ} (hε : 0 < ε) (ω : ι → ℝ) (A : ι → QMatrix d)
    (hdown : ∀ i, ω i ≤ -ε) :
    ∃ J : ι → QMatrix d, ∀ ρ,
      correlatedDissipator (linearKernelMatrix ε ω) A ρ =
        ∑ r, lindbladDissipator (J r) ρ :=
  exists_jumps_of_kossakowski_posSemidef
    (linearKernelMatrix ε ω) A (m1Kossakowski_posSemidef hε ω hdown)

theorem m1_energy_nonpos
    {H : QMatrix d} {ε : ℝ} {ω : ι → ℝ} {A : ι → QMatrix d}
    (hε : 0 < ε)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε) :
    correlatedAdjoint
        (fun i j => ((linearKernel ε (ω i) (ω j) : ℝ) : ℂ)) A H ≤ 0 := by
  let C : Matrix ι ι ℂ := linearKernelMatrix ε ω
  let D : Matrix ι ι ℂ := m1DriftKernel ε ω
  apply correlatedAdjoint_nonpos_of_driftKernel_posSemidef C D hH hA
  · intro i j
    exact linearKernel_weighted_eq_neg_m1Drift hε (hdown i) (hdown j)
  · apply m1DriftKernel_posSemidef hε.le ω
    intro i
    linarith [hdown i]

end

end GapFreeLindblad
end FTDQE

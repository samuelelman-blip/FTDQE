import FTDQE.GapFreeLindbladKernelGram
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positivity of the downward Cauchy Kossakowski kernel

For frequencies `ωᵢ < 0`, the matrix `1 / (-(ωᵢ+ωⱼ))` is the Gram matrix of the
functions `s ↦ exp (ωᵢ s)` in `L²((0,∞))`.  This gives a direct Lean proof of the
positive-semidefiniteness used by the constant kernel, and hence by the Hadamard-power
normalized family.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder MeasureTheory

noncomputable section

/-- The scalar exponential on the positive half-line, viewed as a complex-valued function. -/
def halfLineExp (ω : ℝ) : ℝ → ℂ := fun s => (Real.exp (ω * s) : ℂ)

/-- Negative exponential rates define square-integrable functions on `(0,∞)`. -/
theorem halfLineExp_memLp_two {ω : ℝ} (hω : ω < 0) :
    MemLp (halfLineExp ω) 2 (Measure.restrict volume (Ioi 0)) := by
  have hcont : Continuous (halfLineExp ω) := by
    unfold halfLineExp
    fun_prop
  have hmeas :
      AEStronglyMeasurable (halfLineExp ω) (Measure.restrict volume (Ioi 0)) :=
    hcont.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  change IntegrableOn (fun s : ℝ => ‖halfLineExp ω s‖ ^ 2) (Ioi 0)
  have hfun :
      (fun s : ℝ => ‖halfLineExp ω s‖ ^ 2) =
        (fun s : ℝ => Real.exp ((2 * ω) * s)) := by
    funext s
    simp only [halfLineExp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

/-- The corresponding `L²` vector. -/
def halfLineExpLp (ω : ℝ) (hω : ω < 0) :
    ℝ →₂[(Measure.restrict volume (Ioi 0))] ℂ :=
  (halfLineExp_memLp_two hω).toLp (halfLineExp ω)

/-- Pointwise scalar inner product of the real exponential embeddings. -/
theorem inner_halfLineExp_pointwise (ω ω' s : ℝ) :
    ⟪halfLineExp ω s, halfLineExp ω' s⟫_ℂ =
      Complex.exp (((ω + ω' : ℝ) : ℂ) * (s : ℂ)) := by
  change star ((Real.exp (ω * s) : ℂ)) * (Real.exp (ω' * s) : ℂ) = _
  rw [show star ((Real.exp (ω * s) : ℂ)) = (Real.exp (ω * s) : ℂ) by simp]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have harg :
      (((ω + ω' : ℝ) : ℂ) * (s : ℂ)) = (((ω + ω') * s : ℝ) : ℂ) := by
    norm_num
  rw [harg, ← Complex.ofReal_exp]
  norm_cast
  congr 1
  ring

/-- Inner products of the exponential `L²` vectors give the Cauchy denominator exactly. -/
theorem inner_halfLineExpLp {ω ω' : ℝ} (hω : ω < 0) (hω' : ω' < 0) :
    ⟪halfLineExpLp ω hω, halfLineExpLp ω' hω'⟫_ℂ =
      ((1 / (-(ω + ω')) : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hcoeω :
      ((halfLineExpLp ω hω : ℝ → ℂ)) =ᵐ[
        Measure.restrict volume (Ioi 0)] halfLineExp ω := by
    simpa [halfLineExpLp] using MemLp.coeFn_toLp (halfLineExp_memLp_two hω)
  have hcoeω' :
      ((halfLineExpLp ω' hω' : ℝ → ℂ)) =ᵐ[
        Measure.restrict volume (Ioi 0)] halfLineExp ω' := by
    simpa [halfLineExpLp] using MemLp.coeFn_toLp (halfLineExp_memLp_two hω')
  have hcongr :
      (fun s : ℝ =>
        ⟪(halfLineExpLp ω hω : ℝ → ℂ) s,
          (halfLineExpLp ω' hω' : ℝ → ℂ) s⟫_ℂ) =ᵐ[
            Measure.restrict volume (Ioi 0)]
        (fun s : ℝ => Complex.exp (((ω + ω' : ℝ) : ℂ) * (s : ℂ))) := by
    filter_upwards [hcoeω, hcoeω'] with s hs hs'
    rw [hs, hs']
    exact inner_halfLineExp_pointwise ω ω' s
  rw [integral_congr_ae hcongr]
  rw [MeasureTheory.integral_restrict measurableSet_Ioi]
  have hsum : ω + ω' < 0 := by linarith
  rw [integral_exp_mul_complex_Ioi (a := ((ω + ω' : ℝ) : ℂ)) (by simpa using hsum) 0]
  simp only [mul_zero, Complex.exp_zero]
  have hne : ω + ω' ≠ 0 := ne_of_lt hsum
  rw [show -((1 : ℂ) / ((ω + ω' : ℝ) : ℂ)) =
      (((1 / (-(ω + ω')) : ℝ) : ℂ)) by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]
    field_simp]

section Finite

variable {ι : Type*} [Finite ι]

/-- Unscaled Cauchy matrix of a negative frequency family. -/
def cauchyFrequencyMatrix (ω : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((1 / (-(ω i + ω j)) : ℝ) : ℂ)

/-- The negative-frequency Cauchy matrix is positive semidefinite, with no lower bound on
pairwise frequency separations. -/
theorem cauchyFrequencyMatrix_posSemidef
    (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (cauchyFrequencyMatrix ω).PosSemidef := by
  let v : ι → (ℝ →₂[(Measure.restrict volume (Ioi 0))] ℂ) :=
    fun i => halfLineExpLp (ω i) (hω i)
  apply posSemidef_of_gram_entries (cauchyFrequencyMatrix ω) v
  intro i j
  exact (inner_halfLineExpLp (hω i) (hω j)).symm

/-- The manuscript's constant kernel `2 ε / (-(ωᵢ+ωⱼ))` is positive semidefinite for
`ε ≥ 0` and strictly downward frequencies. -/
theorem constantKernelMatrix_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (constantKernelMatrix ε ω).PosSemidef := by
  have hC := cauchyFrequencyMatrix_posSemidef ω hω
  have hscale : (0 : ℂ) ≤ ((2 * ε : ℝ) : ℂ) := by
    exact_mod_cast (mul_nonneg (by norm_num) hε)
  have hs := hC.smul hscale
  convert hs using 1
  ext i j
  simp [constantKernelMatrix, constantKernel, cauchyFrequencyMatrix, Matrix.smul_apply,
    div_eq_mul_inv, mul_assoc]

/-- Therefore the linear-weight kernel `m₁` is positive semidefinite as well. -/
theorem linearKernelMatrix_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (linearKernelMatrix ε ω).PosSemidef :=
  linearKernelMatrix_posSemidef_of_constant
    (constantKernelMatrix_posSemidef hε ω hω)

end Finite

end

end GapFreeLindblad
end FTDQE

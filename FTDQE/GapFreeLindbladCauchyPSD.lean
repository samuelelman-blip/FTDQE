import FTDQE.GapFreeLindbladKernelGram
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder MeasureTheory

noncomputable section

def halfLineExp (ω : ℝ) : ℝ → ℂ := fun s => (Real.exp (ω * s) : ℂ)

theorem complex_inner_ofReal (x y : ℝ) :
    ⟪(x : ℂ), (y : ℂ)⟫_ℂ = ((x * y : ℝ) : ℂ) := by
  calc
    ⟪(x : ℂ), (y : ℂ)⟫_ℂ =
        ⟪(x : ℂ) • (1 : ℂ), (y : ℂ) • (1 : ℂ)⟫_ℂ := by simp
    _ = (starRingEnd ℂ) (x : ℂ) *
        ⟪(1 : ℂ), (y : ℂ) • (1 : ℂ)⟫_ℂ := by
      rw [inner_smul_left]
    _ = (starRingEnd ℂ) (x : ℂ) *
        ((y : ℂ) * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
      rw [inner_smul_right]
    _ = ((x * y : ℝ) : ℂ) := by simp

theorem halfLineExp_memLp_two {ω : ℝ} (hω : ω < 0) :
    MemLp (halfLineExp ω) 2 (Measure.restrict volume (Ioi 0)) := by
  have hcont : Continuous (halfLineExp ω) := by
    unfold halfLineExp
    fun_prop
  have hmeas : AEStronglyMeasurable (halfLineExp ω)
      (Measure.restrict volume (Ioi 0)) := hcont.aestronglyMeasurable
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

def halfLineExpLp (ω : ℝ) (hω : ω < 0) :
    ℝ →₂[(Measure.restrict volume (Ioi 0))] ℂ :=
  (halfLineExp_memLp_two hω).toLp (halfLineExp ω)

theorem inner_halfLineExp_pointwise (ω ω' s : ℝ) :
    ⟪halfLineExp ω s, halfLineExp ω' s⟫_ℂ =
      Complex.exp (((ω + ω' : ℝ) : ℂ) * (s : ℂ)) := by
  rw [halfLineExp, halfLineExp, complex_inner_ofReal]
  rw [← Real.exp_add]
  have harg :
      (((ω + ω' : ℝ) : ℂ) * (s : ℂ)) =
        (((ω + ω') * s : ℝ) : ℂ) := by
    norm_num
  rw [harg, ← Complex.ofReal_exp]
  congr 2
  ring

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
  have hsum : ω + ω' < 0 := by linarith
  have hne : ω + ω' ≠ 0 := ne_of_lt hsum
  have hformula := integral_exp_mul_complex_Ioi
    (a := ((ω + ω' : ℝ) : ℂ)) (by simpa using hsum) 0
  rw [hformula]
  simp only [mul_zero, Complex.exp_zero]
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]
  have hnec : ((ω + ω' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  field_simp [hnec]

section Finite

variable {ι : Type*} [Finite ι]

def cauchyFrequencyMatrix (ω : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((1 / (-(ω i + ω j)) : ℝ) : ℂ)

theorem cauchyFrequencyMatrix_posSemidef
    (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (cauchyFrequencyMatrix ω).PosSemidef := by
  let v : ι → (ℝ →₂[(Measure.restrict volume (Ioi 0))] ℂ) :=
    fun i => halfLineExpLp (ω i) (hω i)
  apply posSemidef_of_gram_entries (cauchyFrequencyMatrix ω) v
  intro i j
  exact (inner_halfLineExpLp (hω i) (hω j)).symm

theorem constantKernelMatrix_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (constantKernelMatrix ε ω).PosSemidef := by
  have hC := cauchyFrequencyMatrix_posSemidef ω hω
  have hscale : (0 : ℂ) ≤ ((2 * ε : ℝ) : ℂ) := by
    exact_mod_cast (mul_nonneg (by norm_num) hε)
  have hs := hC.smul hscale
  convert hs using 1
  ext i j
  simp [constantKernelMatrix, constantKernel, cauchyFrequencyMatrix,
    Matrix.smul_apply, div_eq_mul_inv, mul_assoc]

theorem linearKernelMatrix_posSemidef
    {ε : ℝ} (hε : 0 ≤ ε) (ω : ι → ℝ) (hω : ∀ i, ω i < 0) :
    (linearKernelMatrix ε ω).PosSemidef :=
  linearKernelMatrix_posSemidef_of_constant
    (constantKernelMatrix_posSemidef hε ω hω)

end Finite

end

end GapFreeLindblad
end FTDQE

import FTDQE.GapFreeLindbladAbstractLyapunov
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Normalized Cauchy kernel family

Algebraic relations among the concrete kernels `m₀,m₁,...` from the manuscript.  In particular,
the linear-weight kernel is the Hadamard square of the constant-weight kernel, so Schur positivity
propagates automatically once the base Cauchy kernel is positive semidefinite.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {ι : Type*}

/-- Complex constant-weight Cauchy kernel matrix. -/
def constantKernelMatrix (ε : ℝ) (ω : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((constantKernel ε (ω i) (ω j) : ℝ) : ℂ)

/-- Complex linear-weight kernel matrix. -/
def linearKernelMatrix (ε : ℝ) (ω : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((linearKernel ε (ω i) (ω j) : ℝ) : ℂ)

/-- The `m₁` kernel is the entrywise square of the `m₀` kernel. -/
theorem linearKernelMatrix_eq_hadamard
    (ε : ℝ) (ω : ι → ℝ) :
    linearKernelMatrix ε ω =
      constantKernelMatrix ε ω ⊙ constantKernelMatrix ε ω := by
  ext i j
  simp [linearKernelMatrix, constantKernelMatrix, linearKernel, constantKernel, Matrix.hadamard]
  ring

/-- Schur product theorem: positivity of the base Cauchy kernel implies positivity of `m₁`. -/
theorem linearKernelMatrix_posSemidef_of_constant
    {ε : ℝ} {ω : ι → ℝ}
    (h0 : (constantKernelMatrix ε ω).PosSemidef) :
    (linearKernelMatrix ε ω).PosSemidef := by
  rw [linearKernelMatrix_eq_hadamard]
  exact h0.hadamard h0

/-- Positive integer Hadamard powers, indexed so `0` means exponent one. -/
def kernelHadamardPow (C : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => C
  | n + 1 => kernelHadamardPow C n ⊙ C

/-- Positive semidefiniteness is preserved by every positive Hadamard power. -/
theorem kernelHadamardPow_posSemidef
    [Finite ι]
    (C : Matrix ι ι ℂ) (hC : C.PosSemidef) :
    ∀ n : ℕ, (kernelHadamardPow C n).PosSemidef
  | 0 => by simpa [kernelHadamardPow] using hC
  | n + 1 => by
      rw [kernelHadamardPow]
      exact (kernelHadamardPow_posSemidef C hC n).hadamard hC

end

end GapFreeLindblad
end FTDQE

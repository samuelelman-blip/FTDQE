import FTDQE.GapFreeLindbladKernelFamily
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gram representation of Kossakowski kernels

This isolates the functional-analytic content of manuscript Lemma 2.  Any kernel represented as
inner products of vectors in a complex inner-product space is positive semidefinite.  The
Laplace-integral kernel is obtained by taking the vectors to be exponential functions in a weighted
`L²` space.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder

noncomputable section

variable {ι E : Type*} [Finite ι]
variable [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A matrix identified entrywise with a Gram matrix is positive semidefinite. -/
theorem posSemidef_of_eq_gram
    (C : Matrix ι ι ℂ) (v : ι → E)
    (hC : C = Matrix.gram ℂ v) :
    C.PosSemidef := by
  rw [hC]
  exact Matrix.posSemidef_gram ℂ v

/-- Pointwise formulation of the same result. -/
theorem posSemidef_of_gram_entries
    (C : Matrix ι ι ℂ) (v : ι → E)
    (hC : ∀ i j, C i j = ⟪v i, v j⟫_ℂ) :
    C.PosSemidef := by
  apply posSemidef_of_eq_gram C v
  ext i j
  exact hC i j

/-- Specialization to `L²`: this is the exact abstract mechanism behind the manuscript's
statement that `C_m` is a Gram matrix of the functions `s ↦ exp(ω s)`. -/
theorem l2Kernel_posSemidef
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (v : ι → MeasureTheory.Lp ℂ 2 μ) :
    (Matrix.gram ℂ v).PosSemidef :=
  Matrix.posSemidef_gram ℂ v

end

end GapFreeLindblad
end FTDQE

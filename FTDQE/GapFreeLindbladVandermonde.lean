import FTDQE.GapFreeLindblad
import Mathlib.LinearAlgebra.Vandermonde

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators

noncomputable section

variable {d n : ℕ}

theorem complex_ofReal_injective_comp {ω : Fin n → ℝ}
    (hω : Function.Injective ω) :
    Function.Injective (fun i => (ω i : ℂ)) := by
  intro i j hij
  apply hω
  exact Complex.ofReal_injective hij

/-- Evaluation of a matrix entry as a complex-linear functional. -/
def matrixEntryLinear (p q : Fin d) : QMatrix d →ₗ[ℂ] ℂ where
  toFun M := M p q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Distinct frequencies separate matrix-valued moments.  Only injectivity is required;
there is no lower bound on frequency separation. -/
theorem matrix_eq_zero_of_vandermonde_moments
    {ω : Fin n → ℝ} (hω : Function.Injective ω)
    (V : Fin n → QMatrix d)
    (hmom : ∀ k : Fin n,
      (∑ j : Fin n, ((ω j : ℂ) ^ (k : ℕ)) • V j) = 0) :
    ∀ j, V j = 0 := by
  intro j
  ext p q
  let coeff : Fin n → ℂ := fun r => V r p q
  have hscalar : ∀ k : Fin n,
      (∑ r : Fin n, coeff r * ((ω r : ℂ) ^ (k : ℕ))) = 0 := by
    intro k
    have hentry := congrArg (matrixEntryLinear (d := d) p q) (hmom k)
    have hpowCoeff :
        (∑ r : Fin n, ((ω r : ℂ) ^ (k : ℕ)) * coeff r) = 0 := by
      simpa [matrixEntryLinear, coeff] using hentry
    calc
      (∑ r : Fin n, coeff r * ((ω r : ℂ) ^ (k : ℕ))) =
          ∑ r : Fin n, ((ω r : ℂ) ^ (k : ℕ)) * coeff r := by
            apply Finset.sum_congr rfl
            intro r hr
            exact mul_comm _ _
      _ = 0 := hpowCoeff
  have hz : coeff = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (complex_ofReal_injective_comp hω) hscalar
  exact congrFun hz j

end

end GapFreeLindblad
end FTDQE

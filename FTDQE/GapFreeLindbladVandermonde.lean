import FTDQE.GapFreeLindblad
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Vandermonde separation of distinct Bohr components

Finite-dimensional terminal step of the manuscript's jointly-dark argument.  If the exponential
profile has all of its first `n` moments equal to zero and the `n` frequencies are distinct, then
each matrix-valued frequency component vanishes separately.  Only injectivity is assumed; no
quantitative lower bound on frequency separation occurs.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators

noncomputable section

variable {d n : ℕ}

/-- Injectivity of real frequencies is preserved by the embedding into `ℂ`. -/
theorem complex_ofReal_injective_comp {ω : Fin n → ℝ}
    (hω : Function.Injective ω) :
    Function.Injective (fun i => (ω i : ℂ)) := by
  intro i j hij
  apply hω
  exact Complex.ofReal_injective hij

/-- Matrix-valued Vandermonde separation.

This is the exact algebraic conclusion used after differentiating
`∑_j exp(ω_j s) V_j = 0` at `s=0`. -/
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
    have hentry := congrArg (fun M : QMatrix d => M p q) (hmom k)
    simp only [Finset.sum_apply, Matrix.smul_apply, Pi.zero_apply] at hentry
    simpa [coeff, mul_comm] using hentry
  have hz : coeff = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (complex_ofReal_injective_comp hω) hscalar
  exact congrFun hz j

end

end GapFreeLindblad
end FTDQE

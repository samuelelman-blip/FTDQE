import FTDQE.GapFreeLindbladAdmissibleClosed
import FTDQE.GapFreeLindbladCoercivity

/-!
# End-to-end gap-free bridge

This file closes the final algebraic hand-off between darkness of the low-energy target
and the excited-sector hypotheses used by the restricted-coercivity `1/t` theorem.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- The Heisenberg Lindblad dissipator is unital. -/
theorem heisenbergDissipator_one (J : QMatrix d) :
    heisenbergDissipator J (1 : QMatrix d) = 0 := by
  simp [heisenbergDissipator]
  module

/-- Heisenberg dissipators are linear over subtraction in the observable. -/
theorem heisenbergDissipator_sub (J X Y : QMatrix d) :
    heisenbergDissipator J (X - Y) =
      heisenbergDissipator J X - heisenbergDissipator J Y := by
  simp [heisenbergDissipator, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  module

/-- The finite dissipative adjoint is unital. -/
theorem finiteDissipativeAdjoint_one (J : ι → QMatrix d) :
    finiteDissipativeAdjoint J (1 : QMatrix d) = 0 := by
  simp [finiteDissipativeAdjoint, heisenbergDissipator_one]

/-- Drift of the complement is the negative drift of the target. -/
theorem finiteDissipativeAdjoint_one_sub
    (J : ι → QMatrix d) (P : QMatrix d) :
    finiteDissipativeAdjoint J ((1 : QMatrix d) - P) =
      -finiteDissipativeAdjoint J P := by
  simp [finiteDissipativeAdjoint, heisenbergDissipator_sub,
    heisenbergDissipator_one]

/-- Darkness of a positive target implies nonpositive drift of its complement. -/
theorem complement_drift_nonpos_of_dark
    (J : ι → QMatrix d) {P : QMatrix d}
    (hP : P.PosSemidef) (hdark : ∀ r, J r * P = 0) :
    finiteDissipativeAdjoint J ((1 : QMatrix d) - P) ≤ 0 := by
  rw [finiteDissipativeAdjoint_one_sub]
  exact neg_nonpos.mpr
    (finiteDissipativeAdjoint_posSemidef_of_dark J hP hdark).nonneg

/-- A kernel Gram operator annihilates a target on the right when every component does. -/
theorem kernelGramOperator_mul_eq_zero_of_components_dark
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) (P : QMatrix d)
    (hdark : ∀ i, A i * P = 0) :
    kernelGramOperator D A * P = 0 := by
  rw [kernelGramOperator, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Matrix.mul_assoc, hdark]

/-- For a positive Gram kernel, darkness also gives left annihilation. -/
theorem mul_kernelGramOperator_eq_zero_of_components_dark
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) {P : QMatrix d}
    (hD : D.PosSemidef) (hP : P.IsHermitian)
    (hdark : ∀ i, A i * P = 0) :
    P * kernelGramOperator D A = 0 := by
  let K := kernelGramOperator D A
  have hK : K.PosSemidef := kernelGramOperator_posSemidef D A hD
  have hright : K * P = 0 :=
    kernelGramOperator_mul_eq_zero_of_components_dark D A P hdark
  have hstar := congrArg Matrix.conjTranspose hright
  simpa [K, hK.isHermitian.eq, hP.eq, Matrix.conjTranspose_mul] using hstar

/-- The Lyapunov operator is entirely supported on the complement of a dark target. -/
theorem complement_mul_kernelGramOperator_mul_complement
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) {P : QMatrix d}
    (hD : D.PosSemidef) (hP : P.IsHermitian)
    (hdark : ∀ i, A i * P = 0) :
    ((1 : QMatrix d) - P) * kernelGramOperator D A * ((1 : QMatrix d) - P) =
      kernelGramOperator D A := by
  have hright := kernelGramOperator_mul_eq_zero_of_components_dark D A P hdark
  have hleft := mul_kernelGramOperator_eq_zero_of_components_dark D A hD hP hdark
  rw [Matrix.sub_mul, Matrix.one_mul, hleft, sub_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, hright, sub_zero]

end

end GapFreeLindblad
end FTDQE

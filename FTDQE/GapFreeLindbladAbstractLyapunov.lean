import FTDQE.GapFreeLindbladGKLS
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Abstract kernel--Lyapunov criterion

The manuscript's integration-by-parts step has a clean finite-dimensional algebraic core:
if the Hadamard product of the Kossakowski kernel with `(ωᵢ+ωⱼ)/2` is the negative of a
positive semidefinite coefficient kernel `D`, then the energy drift is the negative of a
positive semidefinite operator.  This file proves that statement without any spectral-gap
or frequency-separation hypothesis.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- Operator-valued Gram form induced by a coefficient kernel. -/
def kernelGramOperator (D : Matrix ι ι ℂ) (A : ι → QMatrix d) : QMatrix d :=
  ∑ i, ∑ j, D i j • ((A j)ᴴ * A i)

/-- Factorization of the operator-valued Gram form for `D=BᴴB`. -/
theorem kernelGramOperator_factor
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) :
    kernelGramOperator (Bᴴ * B) A =
      ∑ r, (factorJump B A r)ᴴ * factorJump B A r := by
  classical
  rw [kernelGramOperator]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_smul]
  rw [triple_sum_cycle]
  apply Finset.sum_congr rfl
  intro r hr
  rw [factorJump]
  simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [smul_smul, Matrix.mul_assoc, mul_comm]

/-- Positive coefficient kernels produce positive operator-valued Gram forms. -/
theorem kernelGramOperator_posSemidef
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d)
    (hD : D.PosSemidef) :
    (kernelGramOperator D A).PosSemidef := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  rw [hB]
  change (kernelGramOperator (Bᴴ * B) A).PosSemidef
  rw [kernelGramOperator_factor]
  exact Matrix.posSemidef_sum (Finset.univ : Finset ι)
    (fun r _ => Matrix.posSemidef_conjTranspose_mul_self (factorJump B A r))

/-- If the frequency-weighted Kossakowski coefficients equal `-D`, the exact energy drift
is `- kernelGramOperator D A`. -/
theorem correlatedAdjoint_eq_neg_kernelGramOperator
    {H : QMatrix d} {ω : ι → ℝ} {A : ι → QMatrix d}
    (C D : Matrix ι ι ℂ)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hcoeff : ∀ i j,
      C i j * (((ω i : ℂ) + (ω j : ℂ)) / 2) = -D i j) :
    correlatedAdjoint (fun i j => C i j) A H = - kernelGramOperator D A := by
  rw [correlatedAdjoint_energy (fun i j => C i j) hH hA]
  simp_rw [hcoeff]
  rw [kernelGramOperator]
  simp_rw [neg_smul]
  simp only [Finset.sum_neg_distrib]

/-- Abstract exact Lyapunov theorem. -/
theorem correlatedAdjoint_nonpos_of_driftKernel_posSemidef
    {H : QMatrix d} {ω : ι → ℝ} {A : ι → QMatrix d}
    (C D : Matrix ι ι ℂ)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hcoeff : ∀ i j,
      C i j * (((ω i : ℂ) + (ω j : ℂ)) / 2) = -D i j)
    (hD : D.PosSemidef) :
    correlatedAdjoint (fun i j => C i j) A H ≤ 0 := by
  rw [correlatedAdjoint_eq_neg_kernelGramOperator C D hH hA hcoeff]
  exact neg_nonpos.mpr (kernelGramOperator_posSemidef D A hD).nonneg

end

end GapFreeLindblad
end FTDQE

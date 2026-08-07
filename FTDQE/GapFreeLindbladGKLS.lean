import FTDQE.GapFreeLindbladLyapunov
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Kossakowski factorization and GKLS validity

This file verifies the finite-dimensional algebra behind Proposition 1 of the manuscript.
A positive semidefinite Kossakowski matrix factors as `Bᴴ * B`; taking the conjugated rows
of `B` as coefficients of the Bohr components gives ordinary Lindblad jump operators.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- One cross term in a correlated Schrödinger-picture dissipator. -/
def crossDissipator (A B ρ : QMatrix d) : QMatrix d :=
  A * ρ * Bᴴ -
    (1 / 2 : ℂ) • ((Bᴴ * A) * ρ + ρ * (Bᴴ * A))

/-- Kossakowski-form dissipator with component family `A` and coefficient matrix `C`. -/
def correlatedDissipator
    (C : Matrix ι ι ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) : QMatrix d :=
  ∑ i, ∑ j, C i j • crossDissipator (A i) (A j) ρ

/-- Jump formed from one row of a Kossakowski factor.  The conjugation is chosen so that
`Bᴴ * B` appears with the same `(i,j)` convention as `correlatedDissipator`. -/
def factorJump (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (r : ι) : QMatrix d :=
  ∑ i, star (B r i) • A i

/-- A Lindblad dissipator is the diagonal cross dissipator. -/
theorem crossDissipator_self (J ρ : QMatrix d) :
    crossDissipator J J ρ = lindbladDissipator J ρ := by
  rfl

/-- Expansion of a cross dissipator in each argument. -/
theorem crossDissipator_sum_smul
    (c e : ι → ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) :
    crossDissipator (∑ i, c i • A i) (∑ j, e j • A j) ρ =
      ∑ i, ∑ j, (c i * star (e j)) • crossDissipator (A i) (A j) ρ := by
  classical
  simp [crossDissipator, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, Finset.smul_sum,
    smul_sub, smul_add, smul_smul, Matrix.mul_assoc]

/-- Expanding the jump associated with one factor row. -/
theorem lindbladDissipator_factorJump
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) (r : ι) :
    lindbladDissipator (factorJump B A r) ρ =
      ∑ i, ∑ j, (star (B r i) * B r j) • crossDissipator (A i) (A j) ρ := by
  rw [← crossDissipator_self]
  rw [factorJump, crossDissipator_sum_smul]
  simp

/-- Summing factor jumps reconstructs the correlated dissipator for `Bᴴ * B`. -/
theorem correlatedDissipator_eq_sum_factorJumps
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) :
    correlatedDissipator (Bᴴ * B) A ρ =
      ∑ r, lindbladDissipator (factorJump B A r) ρ := by
  classical
  rw [correlatedDissipator]
  simp_rw [lindbladDissipator_factorJump]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, star_star]
  simp [Finset.smul_sum, Finset.sum_smul, Finset.sum_comm, mul_comm, mul_left_comm,
    mul_assoc]

/-- Every positive-semidefinite Kossakowski matrix admits an explicit ordinary-GKLS
representation of its correlated dissipator. -/
theorem exists_jumps_of_kossakowski_posSemidef
    (C : Matrix ι ι ℂ) (A : ι → QMatrix d)
    (hC : C.PosSemidef) :
    ∃ J : ι → QMatrix d, ∀ ρ,
      correlatedDissipator C A ρ = ∑ r, lindbladDissipator (J r) ρ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  refine ⟨factorJump B A, ?_⟩
  intro ρ
  rw [hB]
  simpa only [star_eq_conjTranspose] using correlatedDissipator_eq_sum_factorJumps B A ρ

end

end GapFreeLindblad
end FTDQE

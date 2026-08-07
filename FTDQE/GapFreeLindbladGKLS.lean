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

/-- `crossDissipator` is linear in its first jump argument. -/
theorem crossDissipator_smul_left
    (c : ℂ) (A B ρ : QMatrix d) :
    crossDissipator (c • A) B ρ = c • crossDissipator A B ρ := by
  simp [crossDissipator, Matrix.mul_assoc, smul_sub, smul_add, smul_smul]

/-- `crossDissipator` is conjugate-linear in its second jump argument. -/
theorem crossDissipator_smul_right
    (c : ℂ) (A B ρ : QMatrix d) :
    crossDissipator A (c • B) ρ = star c • crossDissipator A B ρ := by
  simp [crossDissipator, Matrix.mul_assoc, smul_sub, smul_add, smul_smul]

/-- `crossDissipator` preserves finite sums in its first argument. -/
theorem crossDissipator_sum_left
    (F : ι → QMatrix d) (B ρ : QMatrix d) :
    crossDissipator (∑ i, F i) B ρ = ∑ i, crossDissipator (F i) B ρ := by
  classical
  simp [crossDissipator, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.smul_sum, Matrix.mul_assoc]

/-- `crossDissipator` preserves finite sums in its second argument. -/
theorem crossDissipator_sum_right
    (A : QMatrix d) (F : ι → QMatrix d) (ρ : QMatrix d) :
    crossDissipator A (∑ j, F j) ρ = ∑ j, crossDissipator A (F j) ρ := by
  classical
  simp [crossDissipator, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.smul_sum, Matrix.mul_assoc]

/-- Full sesquilinear expansion of the correlated cross dissipator. -/
theorem crossDissipator_sum_smul
    (c e : ι → ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) :
    crossDissipator (∑ i, c i • A i) (∑ j, e j • A j) ρ =
      ∑ i, ∑ j, (c i * star (e j)) • crossDissipator (A i) (A j) ρ := by
  rw [crossDissipator_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [crossDissipator_smul_left, crossDissipator_sum_right]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [crossDissipator_smul_right, smul_smul]

/-- Expanding the jump associated with one factor row. -/
theorem lindbladDissipator_factorJump
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) (r : ι) :
    lindbladDissipator (factorJump B A r) ρ =
      ∑ i, ∑ j, (star (B r i) * B r j) • crossDissipator (A i) (A j) ρ := by
  rw [← crossDissipator_self]
  rw [factorJump, crossDissipator_sum_smul]
  simp only [star_star]

/-- Cyclic reordering of three finite sums. -/
theorem triple_sum_cycle {M : Type*} [AddCommMonoid M]
    (f : ι → ι → ι → M) :
    (∑ i, ∑ j, ∑ r, f i j r) = ∑ r, ∑ i, ∑ j, f i j r := by
  calc
    (∑ i, ∑ j, ∑ r, f i j r) = ∑ i, ∑ r, ∑ j, f i j r := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, f i j r := Finset.sum_comm

/-- Summing factor jumps reconstructs the correlated dissipator for `Bᴴ * B`. -/
theorem correlatedDissipator_eq_sum_factorJumps
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (ρ : QMatrix d) :
    correlatedDissipator (Bᴴ * B) A ρ =
      ∑ r, lindbladDissipator (factorJump B A r) ρ := by
  classical
  rw [correlatedDissipator]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_smul]
  simp_rw [lindbladDissipator_factorJump]
  exact triple_sum_cycle
    (fun i j r => (star (B r i) * B r j) • crossDissipator (A i) (A j) ρ)

/-- Every positive-semidefinite Kossakowski matrix admits an explicit ordinary-GKLS
representation of its correlated dissipator. -/
theorem exists_jumps_of_kossakowski_posSemidef
    (C : Matrix ι ι ℂ) (A : ι → QMatrix d)
    (hC : C.PosSemidef) :
    ∃ J : ι → QMatrix d, ∀ ρ,
      correlatedDissipator C A ρ = ∑ r, lindbladDissipator (J r) ρ := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  refine ⟨factorJump B A, ?_⟩
  intro ρ
  rw [hB]
  simpa only [star_eq_conjTranspose] using correlatedDissipator_eq_sum_factorJumps B A ρ

end

end GapFreeLindblad
end FTDQE

import FTDQE.GapFreeLindbladGKLS
import FTDQE.GapFreeLindbladDarkness

/-!
# Adjoint factorization of correlated GKLS kernels

This file closes the bridge between the Kossakowski-factorized Schrödinger generator
and the correlated Heisenberg generator used in the Lyapunov calculation.  The same
ordinary Lindblad jumps realize both pictures and inherit darkness from the underlying
Bohr components.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- A diagonal cross-energy term is the usual Heisenberg Lindblad dissipator. -/
theorem crossEnergyDrift_self (J X : QMatrix d) :
    crossEnergyDrift X J J = heisenbergDissipator J X := by
  simp [crossEnergyDrift, heisenbergDissipator, add_comm]

/-- `crossEnergyDrift` is linear in its first jump component. -/
theorem crossEnergyDrift_smul_left
    (c : ℂ) (X A B : QMatrix d) :
    crossEnergyDrift X (c • A) B = c • crossEnergyDrift X A B := by
  simp [crossEnergyDrift, Matrix.mul_assoc, smul_sub, smul_add, smul_smul]
  module

/-- `crossEnergyDrift` is conjugate-linear in its second jump component. -/
theorem crossEnergyDrift_smul_right
    (c : ℂ) (X A B : QMatrix d) :
    crossEnergyDrift X A (c • B) = star c • crossEnergyDrift X A B := by
  simp [crossEnergyDrift, Matrix.mul_assoc, smul_sub, smul_add, smul_smul]
  module

/-- `crossEnergyDrift` preserves finite sums in its first jump component. -/
theorem crossEnergyDrift_sum_left
    (X : QMatrix d) (F : ι → QMatrix d) (B : QMatrix d) :
    crossEnergyDrift X (∑ i, F i) B = ∑ i, crossEnergyDrift X (F i) B := by
  classical
  simp [crossEnergyDrift, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum, Matrix.mul_assoc]

/-- `crossEnergyDrift` preserves finite sums in its second jump component. -/
theorem crossEnergyDrift_sum_right
    (X A : QMatrix d) (F : ι → QMatrix d) :
    crossEnergyDrift X A (∑ j, F j) = ∑ j, crossEnergyDrift X A (F j) := by
  classical
  simp [crossEnergyDrift, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum, Matrix.mul_assoc]

/-- Full sesquilinear expansion of a cross-energy term. -/
theorem crossEnergyDrift_sum_smul
    (X : QMatrix d) (c e : ι → ℂ) (A : ι → QMatrix d) :
    crossEnergyDrift X (∑ i, c i • A i) (∑ j, e j • A j) =
      ∑ i, ∑ j, (c i * star (e j)) • crossEnergyDrift X (A i) (A j) := by
  rw [crossEnergyDrift_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [crossEnergyDrift_smul_left, crossEnergyDrift_sum_right]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [crossEnergyDrift_smul_right, smul_smul]

/-- One factor jump expands into the Kossakowski row contribution in the Heisenberg picture. -/
theorem heisenbergDissipator_factorJump
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (X : QMatrix d) (r : ι) :
    heisenbergDissipator (factorJump B A r) X =
      ∑ i, ∑ j, (star (B r i) * B r j) • crossEnergyDrift X (A i) (A j) := by
  rw [← crossEnergyDrift_self]
  rw [factorJump, crossEnergyDrift_sum_smul]
  simp only [star_star]

/-- The same factor jumps that realize the Schrödinger Kossakowski dissipator also realize
its correlated Heisenberg adjoint. -/
theorem correlatedAdjoint_eq_sum_factorJumps
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (X : QMatrix d) :
    correlatedAdjoint (fun i j => (Bᴴ * B) i j) A X =
      ∑ r, heisenbergDissipator (factorJump B A r) X := by
  classical
  rw [correlatedAdjoint]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_smul]
  simp_rw [heisenbergDissipator_factorJump]
  exact triple_sum_cycle
    (fun i j r => (star (B r i) * B r j) • crossEnergyDrift X (A i) (A j))

/-- Factorized jumps inherit darkness from every component in the family. -/
theorem factorJump_mul_eq_zero_of_components_dark
    (B : Matrix ι ι ℂ) (A : ι → QMatrix d) (P : QMatrix d)
    (hdark : ∀ i, A i * P = 0) :
    ∀ r, factorJump B A r * P = 0 := by
  intro r
  exact sum_smul_mul_eq_zero A (fun i => star (B r i)) P hdark

/-- A positive Kossakowski matrix has one ordinary jump family that simultaneously realizes
both the Schrödinger dissipator and the correlated Heisenberg adjoint. -/
theorem exists_jumps_of_kossakowski_posSemidef_both_pictures
    (C : Matrix ι ι ℂ) (A : ι → QMatrix d)
    (hC : C.PosSemidef) :
    ∃ J : ι → QMatrix d,
      (∀ ρ, correlatedDissipator C A ρ = ∑ r, lindbladDissipator (J r) ρ) ∧
      (∀ X, correlatedAdjoint (fun i j => C i j) A X =
        finiteDissipativeAdjoint J X) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  refine ⟨factorJump B A, ?_, ?_⟩
  · intro ρ
    rw [hB]
    simpa only [star_eq_conjTranspose] using
      correlatedDissipator_eq_sum_factorJumps B A ρ
  · intro X
    rw [finiteDissipativeAdjoint]
    rw [hB]
    simpa only [star_eq_conjTranspose] using
      correlatedAdjoint_eq_sum_factorJumps B A X

/-- If the component family is dark, the simultaneous factorized GKLS realization can be
chosen dark on the same target. -/
theorem exists_dark_jumps_of_kossakowski_posSemidef
    (C : Matrix ι ι ℂ) (A : ι → QMatrix d) (P : QMatrix d)
    (hC : C.PosSemidef) (hdark : ∀ i, A i * P = 0) :
    ∃ J : ι → QMatrix d,
      (∀ r, J r * P = 0) ∧
      (∀ ρ, correlatedDissipator C A ρ = ∑ r, lindbladDissipator (J r) ρ) ∧
      (∀ X, correlatedAdjoint (fun i j => C i j) A X =
        finiteDissipativeAdjoint J X) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  refine ⟨factorJump B A, factorJump_mul_eq_zero_of_components_dark B A P hdark, ?_, ?_⟩
  · intro ρ
    rw [hB]
    simpa only [star_eq_conjTranspose] using
      correlatedDissipator_eq_sum_factorJumps B A ρ
  · intro X
    rw [finiteDissipativeAdjoint]
    rw [hB]
    simpa only [star_eq_conjTranspose] using
      correlatedAdjoint_eq_sum_factorJumps B A X

end

end GapFreeLindblad
end FTDQE

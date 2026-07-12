import FTDQE.QuantumGenerator
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Finite-dimensional GKLS generators

Concrete Hamiltonian and dissipative terms, together with Hermiticity and trace
preservation identities used in Lemma 2.
-/

namespace FTDQE

open Matrix

noncomputable section

variable {d : ℕ}

/-- Hamiltonian contribution `-i[H,X]`. -/
def hamiltonianPart (H X : QMatrix d) : QMatrix d :=
  (-Complex.I) • (H * X - X * H)

/-- One Lindblad dissipator `A X A† - 1/2 {A†A,X}`. -/
def lindbladDissipator (A X : QMatrix d) : QMatrix d :=
  A * X * Aᴴ -
    (1 / 2 : ℂ) • ((Aᴴ * A) * X + X * (Aᴴ * A))

/-- Finite-dimensional GKLS generator with Hamiltonian `H` and jumps `J`. -/
def gklsApply {ι : Type*} [Fintype ι]
    (H : QMatrix d) (J : ι → QMatrix d) (X : QMatrix d) : QMatrix d :=
  hamiltonianPart H X + ∑ a, lindbladDissipator (J a) X

theorem hamiltonianPart_isHermitian
    {H X : QMatrix d} (hH : H.IsHermitian) (hX : X.IsHermitian) :
    (hamiltonianPart H X).IsHermitian := by
  have hcomm : (H * X - X * H)ᴴ = -(H * X - X * H) := by
    simp [hH.eq, hX.eq, Matrix.conjTranspose_mul]
  rw [Matrix.IsHermitian, hamiltonianPart, Matrix.conjTranspose_smul, hcomm]
  simp

theorem trace_hamiltonianPart (H X : QMatrix d) :
    Matrix.trace (hamiltonianPart H X) = 0 := by
  simp [hamiltonianPart, Matrix.trace_mul_comm H X]

theorem lindbladDissipator_isHermitian
    (A : QMatrix d) {X : QMatrix d} (hX : X.IsHermitian) :
    (lindbladDissipator A X).IsHermitian := by
  rw [Matrix.IsHermitian, lindbladDissipator]
  simp [hX.eq, Matrix.conjTranspose_mul]
  noncomm_ring

theorem trace_lindbladDissipator (A X : QMatrix d) :
    Matrix.trace (lindbladDissipator A X) = 0 := by
  rw [lindbladDissipator, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add]
  have hcycle : Matrix.trace (A * X * Aᴴ) = Matrix.trace ((Aᴴ * A) * X) := by
    simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle A X Aᴴ
  have hcomm : Matrix.trace (X * (Aᴴ * A)) = Matrix.trace ((Aᴴ * A) * X) :=
    Matrix.trace_mul_comm X (Aᴴ * A)
  rw [hcycle, hcomm]
  ring

theorem gklsApply_isHermitian {ι : Type*} [Fintype ι]
    {H : QMatrix d} (J : ι → QMatrix d) {X : QMatrix d}
    (hH : H.IsHermitian) (hX : X.IsHermitian) :
    (gklsApply H J X).IsHermitian := by
  rw [Matrix.IsHermitian, gklsApply, Matrix.conjTranspose_add]
  rw [(hamiltonianPart_isHermitian hH hX).eq]
  congr 1
  simp_rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (lindbladDissipator_isHermitian (J a) hX).eq

theorem trace_gklsApply {ι : Type*} [Fintype ι]
    (H : QMatrix d) (J : ι → QMatrix d) (X : QMatrix d) :
    Matrix.trace (gklsApply H J X) = 0 := by
  simp [gklsApply, trace_hamiltonianPart, trace_lindbladDissipator]

end

end FTDQE

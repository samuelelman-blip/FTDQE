import FTDQE.GapFreeLindblad
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Gap-free Lindblad target darkness

Operator-level formalization of the target-darkness and monotone-population mechanism.
The target projector is represented abstractly by a positive semidefinite matrix `P`; the
spectral argument in the manuscript supplies `J r * P = 0` for every downward jump.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Heisenberg adjoint of one Lindblad dissipator. -/
def heisenbergDissipator (J X : QMatrix d) : QMatrix d :=
  Jᴴ * X * J -
    (1 / 2 : ℂ) • ((Jᴴ * J) * X + X * (Jᴴ * J))

/-- If a jump annihilates a Hermitian target operator on the right, its Heisenberg
dissipator on that target is the positive sandwich `J† P J`. -/
theorem heisenbergDissipator_of_dark
    {J P : QMatrix d}
    (hP : P.IsHermitian)
    (hdark : J * P = 0) :
    heisenbergDissipator J P = Jᴴ * P * J := by
  have hleft : P * Jᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hdark
    simpa [hP.eq, Matrix.conjTranspose_mul] using h
  have hrightGram : (Jᴴ * J) * P = 0 := by
    rw [Matrix.mul_assoc, hdark, Matrix.mul_zero]
  have hleftGram : P * (Jᴴ * J) = 0 := by
    rw [← Matrix.mul_assoc, hleft, Matrix.zero_mul]
  simp [heisenbergDissipator, hrightGram, hleftGram]

/-- For a positive target operator, the dark-jump contribution to target population
is positive semidefinite. -/
theorem heisenbergDissipator_posSemidef_of_dark
    {J P : QMatrix d}
    (hP : P.PosSemidef)
    (hdark : J * P = 0) :
    (heisenbergDissipator J P).PosSemidef := by
  rw [heisenbergDissipator_of_dark hP.isHermitian hdark]
  exact hP.conjTranspose_mul_mul_same J

section FiniteJumps

variable {ι : Type*} [Fintype ι]

/-- Dissipative Heisenberg adjoint for a finite family of jumps. -/
def finiteDissipativeAdjoint (J : ι → QMatrix d) (X : QMatrix d) : QMatrix d :=
  ∑ r, heisenbergDissipator (J r) X

/-- A family of jumps dark on `P` produces exactly the sum of positive sandwiches. -/
theorem finiteDissipativeAdjoint_of_dark
    (J : ι → QMatrix d) {P : QMatrix d}
    (hP : P.IsHermitian)
    (hdark : ∀ r, J r * P = 0) :
    finiteDissipativeAdjoint J P = ∑ r, (J r)ᴴ * P * J r := by
  rw [finiteDissipativeAdjoint]
  apply Finset.sum_congr rfl
  intro r hr
  exact heisenbergDissipator_of_dark hP (hdark r)

/-- Operator form of monotone target population: the Heisenberg derivative of a
positive dark target is positive semidefinite. -/
theorem finiteDissipativeAdjoint_posSemidef_of_dark
    (J : ι → QMatrix d) {P : QMatrix d}
    (hP : P.PosSemidef)
    (hdark : ∀ r, J r * P = 0) :
    (finiteDissipativeAdjoint J P).PosSemidef := by
  rw [finiteDissipativeAdjoint_of_dark J hP.isHermitian hdark]
  simpa using Matrix.posSemidef_sum (Finset.univ : Finset ι)
    (fun r _ => hP.conjTranspose_mul_mul_same (J r))

/-- Coherent Heisenberg contribution `i[G,X]`. -/
def coherentAdjoint (G X : QMatrix d) : QMatrix d :=
  Complex.I • (G * X - X * G)

/-- A coherent term commuting with the target projector does not change target population. -/
theorem coherentAdjoint_eq_zero_of_commute
    {G P : QMatrix d} (hcomm : G * P = P * G) :
    coherentAdjoint G P = 0 := by
  simp [coherentAdjoint, hcomm]

/-- Full operator-level monotonicity statement corresponding to manuscript Lemma 5. -/
theorem fullAdjoint_target_posSemidef
    (J : ι → QMatrix d) {G P : QMatrix d}
    (hP : P.PosSemidef)
    (hdark : ∀ r, J r * P = 0)
    (hcomm : G * P = P * G) :
    (coherentAdjoint G P + finiteDissipativeAdjoint J P).PosSemidef := by
  rw [coherentAdjoint_eq_zero_of_commute hcomm, zero_add]
  exact finiteDissipativeAdjoint_posSemidef_of_dark J hP hdark

end FiniteJumps

end

end GapFreeLindblad
end FTDQE

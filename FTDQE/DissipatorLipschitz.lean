import FTDQE.GKLSGenerator

/-!
# Lipschitz continuity of the dissipator

This file formalises Proposition 1 and Eq. (14) at the certificate level.
The noncommutative matrix identities are proved directly.  The analytic
trace-norm/diamond-norm input is isolated into the standard Hölder bounds, and
the constant `4` and finite-jump summation are then derived internally.
-/

namespace FTDQE

open Matrix

noncomputable section

variable {d : ℕ}

/-- The completely positive sandwich term in a Lindblad dissipator. -/
def sandwichTerm (K X : QMatrix d) : QMatrix d :=
  K * X * Kᴴ

/-- The positive quadratic coefficient appearing in the anticommutator. -/
def gramTerm (K : QMatrix d) : QMatrix d :=
  Kᴴ * K

/-- Difference identity used for the sandwich contribution. -/
theorem sandwichTerm_sub_identity (K K' X : QMatrix d) :
    sandwichTerm K X - sandwichTerm K' X =
      K * X * (K - K')ᴴ + (K - K') * X * K'ᴴ := by
  simp [sandwichTerm, Matrix.conjTranspose_sub]
  noncomm_ring

/-- Difference identity used for the anticommutator coefficient. -/
theorem gramTerm_sub_identity (K K' : QMatrix d) :
    gramTerm K - gramTerm K' =
      Kᴴ * (K - K') + (K - K')ᴴ * K' := by
  simp [gramTerm, Matrix.conjTranspose_sub]
  noncomm_ring

/--
The scalar norm bookkeeping in Proposition 1.

The hypotheses correspond respectively to:

* the two-term Hölder bound for the sandwich difference;
* the two-term operator-norm bound for `K†K - K'†K'`;
* the anticommutator estimate;
* the triangle inequality for the full dissipator difference.
-/
theorem dissipator_lipschitz_from_holder
    (jumpError stateNorm sandwichError gramError antiError totalError : ℝ)
    (hstate : 0 ≤ stateNorm)
    (hsandwich : sandwichError ≤ 2 * jumpError * stateNorm)
    (hgram : gramError ≤ 2 * jumpError)
    (hanti : antiError ≤ gramError * stateNorm)
    (htotal : totalError ≤ sandwichError + antiError) :
    totalError ≤ 4 * jumpError * stateNorm := by
  calc
    totalError ≤ sandwichError + antiError := htotal
    _ ≤ sandwichError + gramError * stateNorm := add_le_add_left hanti sandwichError
    _ ≤ 2 * jumpError * stateNorm + gramError * stateNorm :=
      add_le_add_right hsandwich (gramError * stateNorm)
    _ ≤ 2 * jumpError * stateNorm + (2 * jumpError) * stateNorm := by
      exact add_le_add_left (mul_le_mul_of_nonneg_right hgram hstate)
        (2 * jumpError * stateNorm)
    _ = 4 * jumpError * stateNorm := by ring

/-- Unit-trace-norm form of the pointwise dissipator estimate. -/
theorem dissipator_lipschitz_unit_state
    (jumpError sandwichError gramError antiError totalError : ℝ)
    (hsandwich : sandwichError ≤ 2 * jumpError)
    (hgram : gramError ≤ 2 * jumpError)
    (hanti : antiError ≤ gramError)
    (htotal : totalError ≤ sandwichError + antiError) :
    totalError ≤ 4 * jumpError := by
  have h := dissipator_lipschitz_from_holder
    jumpError 1 sandwichError gramError antiError totalError
    (by positivity)
    (by simpa using hsandwich)
    hgram
    (by simpa using hanti)
    htotal
  simpa using h

/--
Finite-jump summation in Eq. (14): if each dissipator error is at most four
times the corresponding jump error, then the full generator error is at most
four times the sum of jump errors.
-/
theorem finite_sum_dissipator_lipschitz
    {ι : Type*} [Fintype ι]
    (jumpError dissipatorError : ι → ℝ)
    (totalError : ℝ)
    (hjump : ∀ a, 0 ≤ jumpError a)
    (hperJump : ∀ a, dissipatorError a ≤ 4 * jumpError a)
    (htotal : totalError ≤ ∑ a, dissipatorError a) :
    totalError ≤ 4 * ∑ a, jumpError a := by
  calc
    totalError ≤ ∑ a, dissipatorError a := htotal
    _ ≤ ∑ a, 4 * jumpError a := by
      exact Finset.sum_le_sum fun a _ => hperJump a
    _ = 4 * ∑ a, jumpError a := by
      rw [Finset.mul_sum]

/--
Eq. (14) including the standard induced-norm-to-diamond-norm comparison.
-/
theorem generator_perturbation_bound
    {ι : Type*} [Fintype ι]
    (jumpError dissipatorError : ι → ℝ)
    (inducedError diamondError : ℝ)
    (hjump : ∀ a, 0 ≤ jumpError a)
    (hperJump : ∀ a, dissipatorError a ≤ 4 * jumpError a)
    (hinducedDiamond : inducedError ≤ diamondError)
    (hdiamondSum : diamondError ≤ ∑ a, dissipatorError a) :
    inducedError ≤ 4 * ∑ a, jumpError a := by
  apply finite_sum_dissipator_lipschitz
    jumpError dissipatorError inducedError hjump hperJump
  exact hinducedDiamond.trans hdiamondSum

end

end FTDQE

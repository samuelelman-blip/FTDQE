import FTDQE.InvariantSubspaceRelaxation
import FTDQE.QuantumMatrix

/-!
# Matrix/Lindbladian instantiation of perturbed relaxation

This file transports the invariant-subspace theorem to a normed matrix model.
The function `traceNorm` is explicit because Mathlib 4.31 does not yet bundle
the Schatten-1 norm on finite complex matrices.
-/

namespace FTDQE

/-- Matrix-model form of Lemma 2.

`toMatrix` identifies the Banach space with finite complex matrices, and
`hnorm` states that its norm is the chosen matrix trace norm.  The flow and
perturbation preservation hypotheses are then exactly Hermiticity and trace
preservation for the Lindbladian data.
-/
theorem matrix_lindbladian_perturbed_relaxation
    {d : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (toMatrix : X ≃ₗ[ℝ] QMatrix d)
    (traceNorm : QMatrix d → ℝ)
    (hnorm : ∀ y : X, ‖y‖ = traceNorm (toMatrix y))
    (ideal perturbed : ℝ → X →L[ℝ] X) (error : X →L[ℝ] X)
    (x : X) (κ rate η : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (htraj : Continuous (fun t : ℝ => perturbed t x))
    (hintegrand : ∀ t : ℝ,
      Continuous (fun s : ℝ => ideal (t - s) (error (perturbed s x))))
    (hduhamel : ∀ t : ℝ, 0 ≤ t →
      perturbed t x = ideal t x +
        ∫ s in (0 : ℝ)..t, ideal (t - s) (error (perturbed s x)))
    (hmix : ∀ t : ℝ, 0 ≤ t → ∀ y : X,
      IsTracelessHermitian (toMatrix y) →
      ‖ideal t y‖ ≤ κ * Real.exp (-rate * t) * ‖y‖)
    (herror : ∀ y : X, ‖error y‖ ≤ η * ‖y‖)
    (hx : IsTracelessHermitian (toMatrix x))
    (hflowPres : ∀ s : ℝ, 0 ≤ s →
      IsTracelessHermitian (toMatrix (perturbed s x)))
    (herrorPres : ∀ y : X, IsTracelessHermitian (toMatrix y) →
      IsTracelessHermitian (toMatrix (error y))) :
    ∀ t : ℝ, 0 ≤ t →
      traceNorm (toMatrix (perturbed t x)) ≤
        κ * Real.exp (-(rate - κ * η) * t) * traceNorm (toMatrix x) := by
  have hbound := perturbed_relaxation_on_invariant_subspace
    ideal perturbed error
    (fun y : X => IsTracelessHermitian (toMatrix y))
    x κ rate η hκ hη htraj hintegrand hduhamel hmix herror hx
    (fun s hs => herrorPres (perturbed s x) (hflowPres s hs))
  intro t ht
  simpa [hnorm] using hbound t ht

end FTDQE

import FTDQE.MatrixLindbladianRelaxation
import FTDQE.StationaryStateStability

/-!
# Matrix form of stationary-state stability

This file transports Lemma 3 through the explicit finite-dimensional matrix
and trace-norm model introduced for Lemma 2.
-/

namespace FTDQE

/--
Matrix/trace-norm form of Lemma 3.  The only norm infrastructure assumed is
the same explicit identification used in `matrix_lindbladian_perturbed_relaxation`.
-/
theorem matrix_stationary_state_existence_stability_and_uniqueness
    {d : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (toMatrix : X ≃ₗ[ℝ] QMatrix d)
    (traceNorm : QMatrix d → ℝ)
    (hnorm : ∀ y : X, ‖y‖ = traceNorm (toMatrix y))
    (L E : X →L[ℝ] X)
    (flow : ℝ → X →L[ℝ] X)
    (stateSpace : Set X)
    (κ rate η : ℝ)
    (C : ResolventCertificate L
      (fun y : X => IsTracelessHermitian (toMatrix y)) κ rate)
    (σ : X)
    (hσ : IsStationary L σ)
    (hκ : 0 < κ)
    (hcompact : IsCompact stateSpace)
    (approximants : ℕ → X)
    (hmem : ∀ n : ℕ, approximants n ∈ stateSpace)
    (hresidual : Filter.Tendsto
      (fun n : ℕ => (L + E) (approximants n))
      Filter.atTop (nhds 0))
    (hPdiff : ∀ x ∈ stateSpace,
      IsTracelessHermitian (toMatrix (x - σ)))
    (hPsub : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace,
      IsTracelessHermitian (toMatrix (x - y)))
    (hPerror : ∀ x ∈ stateSpace,
      IsTracelessHermitian (toMatrix (E x)))
    (herror : ∀ x ∈ stateSpace,
      traceNorm (toMatrix (E x)) ≤ η * traceNorm (toMatrix x))
    (hstateNorm : ∀ x ∈ stateSpace,
      traceNorm (toMatrix x) = 1)
    (hgeneratorFlow : ∀ x ∈ stateSpace,
      IsStationary (L + E) x → IsFlowStationary flow x)
    (hrelax : ∀ t : ℝ, 0 ≤ t → ∀ y : X,
      IsTracelessHermitian (toMatrix y) →
      traceNorm (toMatrix (flow t y)) ≤
        κ * Real.exp (-(rate - κ * η) * t) *
          traceNorm (toMatrix y)) :
    ∃ σ' ∈ stateSpace,
      IsStationary (L + E) σ' ∧
      traceNorm (toMatrix (σ' - σ)) ≤
        (κ / rate) * traceNorm (toMatrix (E σ')) ∧
      traceNorm (toMatrix (σ' - σ)) ≤ κ * η / rate ∧
      (0 < rate - κ * η →
        ∀ τ ∈ stateSpace, IsStationary (L + E) τ → τ = σ') := by
  have herror' : ∀ x ∈ stateSpace, ‖E x‖ ≤ η * ‖x‖ := by
    intro x hx
    simpa only [hnorm] using herror x hx
  have hstateNorm' : ∀ x ∈ stateSpace, ‖x‖ = 1 := by
    intro x hx
    simpa only [hnorm] using hstateNorm x hx
  have hrelax' : ∀ t : ℝ, 0 ≤ t → ∀ y : X,
      IsTracelessHermitian (toMatrix y) →
      ‖flow t y‖ ≤
        κ * Real.exp (-(rate - κ * η) * t) * ‖y‖ := by
    intro t ht y hy
    simpa only [hnorm] using hrelax t ht y hy
  rcases stationary_state_existence_stability_and_uniqueness
      L E flow stateSpace
      (fun y : X => IsTracelessHermitian (toMatrix y))
      κ rate η C σ hσ hκ hcompact approximants hmem hresidual
      hPdiff hPsub hPerror herror' hstateNorm'
      hgeneratorFlow hrelax' with
    ⟨σ', hσ'mem, hσ'stationary, hfirst, hsecond, hunique⟩
  refine ⟨σ', hσ'mem, hσ'stationary, ?_, ?_, hunique⟩
  · simpa only [hnorm] using hfirst
  · simpa only [hnorm] using hsecond

end FTDQE

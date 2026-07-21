import FTDQE.GroundStateOverlap

/-!
# Strong local-filter regime

This file formalises Lemma 5(ii) from the revised manuscript.  A perturbation
smaller than `rate / (2κ)` leaves at least half of the ideal relaxation rate,
and the stronger overlap-scale bound makes the global refresh unnecessary for
the stated accuracy guarantee.
-/

namespace FTDQE

/-- The perturbative decay rate is at least half the ideal rate. -/
theorem strong_local_filter_decay_margin
    (κ rate η : ℝ)
    (hκ : 0 < κ) (hrate : 0 < rate)
    (hη : η ≤ rate / (2 * κ)) :
    rate / 2 ≤ rate - κ * η ∧ 0 < rate - κ * η := by
  have hmul : κ * η ≤ κ * (rate / (2 * κ)) :=
    mul_le_mul_of_nonneg_left hη hκ.le
  have hhalf : κ * (rate / (2 * κ)) = rate / 2 := by
    field_simp [hκ.ne']
  rw [hhalf] at hmul
  constructor <;> linarith

/--
If Lemma 2 gives relaxation at rate `rate - κη`, then the strong-local-filter
condition upgrades it to the simpler rate `rate / 2` used in Lemma 5(ii).
-/
theorem strong_local_filter_relaxation
    {X : Type*} [NormedAddCommGroup X]
    (flow : ℝ → X → X)
    (κ rate η : ℝ)
    (hκ : 0 < κ) (hrate : 0 < rate)
    (hη : η ≤ rate / (2 * κ))
    (hrelax : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      ‖flow t x‖ ≤ κ * Real.exp (-(rate - κ * η) * t) * ‖x‖) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      ‖flow t x‖ ≤ κ * Real.exp (-(rate / 2) * t) * ‖x‖ := by
  intro t ht x
  have hmargin := (strong_local_filter_decay_margin
    κ rate η hκ hrate hη).1
  have hmul : (rate / 2) * t ≤ (rate - κ * η) * t :=
    mul_le_mul_of_nonneg_right hmargin ht
  have harg : -(rate - κ * η) * t ≤ -(rate / 2) * t := by
    nlinarith
  have hexp : Real.exp (-(rate - κ * η) * t) ≤
      Real.exp (-(rate / 2) * t) :=
    Real.exp_le_exp.mpr harg
  calc
    ‖flow t x‖ ≤ κ * Real.exp (-(rate - κ * η) * t) * ‖x‖ :=
      hrelax t ht x
    _ ≤ κ * Real.exp (-(rate / 2) * t) * ‖x‖ := by
      gcongr

/--
Accuracy part of Lemma 5(ii).  Under the overlap-scale perturbation bound, the
stationary state of the neighbourhood dynamics already has the conclusion of
Theorem 2, so no global step is needed for the accuracy guarantee.
-/
theorem strong_local_filter_accuracy
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L' : X →L[ℝ] X)
    (stateSpace : Set X)
    (σ : X)
    (overlap : X → ℝ)
    (ε κ rate η : ℝ)
    (hκ : 0 < κ)
    (hrate : 0 < rate)
    (hε0 : 0 < ε)
    (hε1 : ε ≤ 1)
    (hη : η ≤ rate * ε / (2 * κ))
    (hlemma3 :
      ∃ σR ∈ stateSpace,
        IsStationary L' σR ∧
        ‖σR - σ‖ ≤ κ * η / rate ∧
        (0 < rate - κ * η →
          ∀ τ ∈ stateSpace, IsStationary L' τ → τ = σR))
    (hoverlap : ∀ x ∈ stateSpace,
      1 - overlap x ≤ ‖x - σ‖) :
    ∃ σR ∈ stateSpace,
      IsStationary L' σR ∧
      ‖σR - σ‖ ≤ ε / 2 ∧
      1 - ε / 2 ≤ overlap σR ∧
      (∀ τ ∈ stateSpace, IsStationary L' τ → τ = σR) := by
  exact ground_state_overlap_of_lemma3
    L' stateSpace σ overlap ε κ rate η
    hκ hrate hε0 hε1 hη hlemma3 hoverlap

end FTDQE
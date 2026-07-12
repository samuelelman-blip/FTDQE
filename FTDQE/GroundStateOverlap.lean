import FTDQE.StationaryStateStability

/-!
# Ground-state overlap certificate

This file formalises the final composition step in Theorem 2.  The locality
analysis supplies the perturbation estimate

`η ≤ rate * ε / (2 * κ)`;

Lemma 3 supplies existence, stationary-state stability, and conditional
uniqueness.  The remaining argument is scalar arithmetic together with the
standard bound that the ground-state population deficit is at most the trace
distance from the ground-state projector.
-/

namespace FTDQE

/--
The scalar arithmetic at the heart of Theorem 2.

If the generator perturbation is at most `rate * ε / (2 * κ)`, the stationary
state stability estimate improves to `distance ≤ ε / 2`, the perturbed decay
rate stays positive, and any overlap deficit bounded by `distance` is at most
`ε / 2`.
-/
theorem ground_state_overlap_arithmetic
    (ε κ rate η distance overlap : ℝ)
    (hκ : 0 < κ)
    (hrate : 0 < rate)
    (hε0 : 0 < ε)
    (hε1 : ε ≤ 1)
    (hη : η ≤ rate * ε / (2 * κ))
    (hdistance : distance ≤ κ * η / rate)
    (hoverlap : 1 - overlap ≤ distance) :
    κ * η < rate ∧
      distance ≤ ε / 2 ∧
      1 - ε / 2 ≤ overlap := by
  have hεnonneg : 0 ≤ ε := hε0.le
  have hκη : κ * η ≤ rate * ε / 2 := by
    calc
      κ * η ≤ κ * (rate * ε / (2 * κ)) :=
        mul_le_mul_of_nonneg_left hη hκ.le
      _ = rate * ε / 2 := by
        field_simp [hκ.ne']
        <;> ring
  have hratehalf : rate * ε / 2 ≤ rate / 2 := by
    have hmul : rate * ε ≤ rate * 1 :=
      mul_le_mul_of_nonneg_left hε1 hrate.le
    nlinarith
  have hsmall : κ * η < rate := by
    nlinarith
  have hdistance' : distance ≤ ε / 2 := by
    calc
      distance ≤ κ * η / rate := hdistance
      _ ≤ (rate * ε / 2) / rate :=
        (div_le_div_iff_of_pos_right hrate).2 hκη
      _ = ε / 2 := by
        field_simp [hrate.ne']
        <;> ring
  have hoverlap' : 1 - ε / 2 ≤ overlap := by
    linarith
  exact ⟨hsmall, hdistance', hoverlap'⟩

/--
Theorem 2 in certificate form.

The input `hlemma3` is precisely the existence/stability/conditional-uniqueness
conclusion supplied by Lemma 3.  The function `overlap` is the ground-state
population, and `hoverlap` is the standard trace-distance estimate

`1 - overlap x ≤ ‖x - σ‖`.
-/
theorem ground_state_overlap_of_lemma3
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
  rcases hlemma3 with
    ⟨σR, hσRmem, hσRstationary, hstable, hunique⟩
  have hcert := ground_state_overlap_arithmetic
    ε κ rate η ‖σR - σ‖ (overlap σR)
    hκ hrate hε0 hε1 hη hstable (hoverlap σR hσRmem)
  have hdecay : 0 < rate - κ * η := sub_pos.mpr hcert.1
  refine ⟨σR, hσRmem, hσRstationary,
    hcert.2.1, hcert.2.2, ?_⟩
  exact hunique hdecay

end FTDQE

import FTDQE.InvariantSubspaceRelaxation

/-!
# Stationary-state stability

This file begins the formalisation of Lemma 3.  It isolates the resolvent
argument on the invariant traceless-Hermitian subspace from the separate
finite-dimensional compactness argument that supplies existence.
-/

namespace FTDQE

/-- A vector is stationary for a continuous linear generator. -/
def IsStationary
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (x : X) : Prop :=
  L x = 0

/--
A certified inverse of `L` on the invariant subspace selected by `P`.
For Lemma 3 this is the resolvent
`J = -∫₀^∞ exp(tL) dt`, whose norm is at most `κ / rate`.
-/
structure ResolventCertificate
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (P : X → Prop) (κ rate : ℝ) where
  resolvent : X →L[ℝ] X
  rate_pos : 0 < rate
  rightInverse : ∀ y : X, P y → resolvent (L y) = y
  norm_le : ∀ y : X, P y →
    ‖resolvent y‖ ≤ (κ / rate) * ‖y‖

/--
Lemma 3(ii), abstract resolvent form.  If `σ` is stationary for `L` and
`σ'` is stationary for `L + E`, then the resolvent identity gives

`‖σ' - σ‖ ≤ (κ / rate) ‖E σ'‖ ≤ κ η / rate`.
-/
theorem stationary_state_stability_of_resolvent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L E : X →L[ℝ] X) (P : X → Prop)
    (κ rate η : ℝ)
    (C : ResolventCertificate L P κ rate)
    (σ σ' : X)
    (hσ : IsStationary L σ)
    (hσ' : IsStationary (L + E) σ')
    (hdiff : P (σ' - σ))
    (herrorImage : P (E σ'))
    (herror : ‖E σ'‖ ≤ η * ‖σ'‖)
    (hσ'norm : ‖σ'‖ = 1)
    (hκ : 0 ≤ κ) :
    ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ ∧
      ‖σ' - σ‖ ≤ κ * η / rate := by
  have hσ0 : L σ = 0 := hσ
  have hσ'0 : L σ' + E σ' = 0 := by
    simpa [IsStationary] using hσ'
  have hLσ' : L σ' = -(E σ') := by
    calc
      L σ' = L σ' + E σ' - E σ' := by abel
      _ = 0 - E σ' := by rw [hσ'0]
      _ = -(E σ') := by simp
  have hLdiff : L (σ' - σ) = -(E σ') := by
    calc
      L (σ' - σ) = L σ' - L σ := by simp
      _ = -(E σ') - 0 := by rw [hLσ', hσ0]
      _ = -(E σ') := by simp
  have hfirst : ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ := by
    calc
      ‖σ' - σ‖ = ‖C.resolvent (L (σ' - σ))‖ := by
        exact congrArg norm (C.rightInverse (σ' - σ) hdiff).symm
      _ = ‖C.resolvent (E σ')‖ := by
        rw [hLdiff]
        simp
      _ ≤ (κ / rate) * ‖E σ'‖ := C.norm_le (E σ') herrorImage
  have hratio : 0 ≤ κ / rate :=
    div_nonneg hκ C.rate_pos.le
  have hsecond : ‖σ' - σ‖ ≤ κ * η / rate := by
    calc
      ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ := hfirst
      _ ≤ (κ / rate) * (η * ‖σ'‖) :=
        mul_le_mul_of_nonneg_left herror hratio
      _ = κ * η / rate := by rw [hσ'norm]; ring
  exact ⟨hfirst, hsecond⟩

end FTDQE

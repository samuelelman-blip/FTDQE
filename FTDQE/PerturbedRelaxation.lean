import FTDQE.IntegralGronwall

/-!
# Perturbed relaxation

This file formalises the Duhamel--Grönwall core of Lemma 2. The trajectory
`h(t)` represents the trace norm of the perturbed evolution applied to a
traceless Hermitian input. The weighted Duhamel inequality is exactly the
scalar inequality obtained from Eq. (23) after multiplying by `exp (λ t)`.
-/

namespace FTDQE

open Set intervalIntegral

/-- Abstract Duhamel--Grönwall relaxation estimate.

If the exponentially weighted norm trajectory satisfies

`e^(λt) h(t) ≤ κ ‖X‖ + κη ∫₀ᵗ e^(λs) h(s) ds`,

then

`h(t) ≤ κ e^{-(λ-κη)t} ‖X‖`.
-/
theorem perturbed_relaxation_of_weighted_duhamel
    (h : ℝ → ℝ) (κ rate η xnorm : ℝ)
    (hh : Continuous h)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η) (hxnorm : 0 ≤ xnorm)
    (h_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ h t)
    (hduhamel : ∀ t : ℝ, 0 ≤ t →
      Real.exp (rate * t) * h t ≤
        κ * xnorm + κ * η * ∫ s in (0 : ℝ)..t, Real.exp (rate * s) * h s) :
    ∀ t : ℝ, 0 ≤ t →
      h t ≤ κ * Real.exp (-(rate - κ * η) * t) * xnorm := by
  intro t ht
  let u : ℝ → ℝ := fun s => Real.exp (rate * s) * h s
  have hu : Continuous u := by
    dsimp [u]
    fun_prop
  have hu_nonneg : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ u s := by
    intro s hs
    exact mul_nonneg (Real.exp_nonneg _) (h_nonneg s hs.1)
  have hweighted : ∀ s ∈ Icc (0 : ℝ) t,
      u s ≤ κ * xnorm + (κ * η) * ∫ r in (0 : ℝ)..s, u r := by
    intro s hs
    simpa [u, mul_assoc] using hduhamel s hs.1
  have hu_bound := integral_gronwall u (κ * xnorm) (κ * η) t hu
    (mul_nonneg hκ hxnorm) (mul_nonneg hκ hη) ht hu_nonneg hweighted
  have hexp : 0 < Real.exp (rate * t) := Real.exp_pos _
  have hdiv : h t ≤
      ((κ * xnorm) * Real.exp ((κ * η) * t)) / Real.exp (rate * t) := by
    apply (le_div_iff₀ hexp).2
    simpa [u] using hu_bound
  calc
    h t ≤ ((κ * xnorm) * Real.exp ((κ * η) * t)) / Real.exp (rate * t) := hdiv
    _ = κ * Real.exp (-(rate - κ * η) * t) * xnorm := by
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1 <;> ring

end FTDQE

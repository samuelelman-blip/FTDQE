import FTDQE.OperatorDuhamel
import FTDQE.PerturbedRelaxation

/-!
# Operator-norm perturbed relaxation

This file combines the Banach-algebra Duhamel identity with the scalar
Duhamel--Grönwall theorem. It gives the operator-level analytic statement of
Lemma 2 on any invariant real Banach space.
-/

namespace FTDQE

open Set intervalIntegral
open NormedSpace

/-- Operator-norm form of Lemma 2 in a real Banach algebra.

The ideal semigroup has decay bound `κ exp (-rate t)`, and the perturbation has
norm at most `η`. Then the perturbed semigroup decays with rate
`rate - κ * η`.
-/
theorem perturbed_relaxation_banach_algebra
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L E : A) (κ rate η : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hmix : ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • L)‖ ≤ κ * Real.exp (-rate * t))
    (hpert : ‖E‖ ≤ η) :
    ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • (L + E))‖ ≤
        κ * Real.exp (-(rate - κ * η) * t) := by
  let h : ℝ → ℝ := fun s => ‖exp (s • (L + E))‖
  have hflowcont : Continuous (fun s : ℝ => exp (s • (L + E))) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_exp_smul_const (L + E) s).continuousAt
  have hh : Continuous h := by
    exact continuous_norm.comp hflowcont
  have h_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ h t := by
    intro t _
    exact norm_nonneg _
  have hduhamel : ∀ t : ℝ, 0 ≤ t →
      h t ≤ κ * Real.exp (-rate * t) * 1 +
        κ * η * ∫ s in (0 : ℝ)..t,
          Real.exp (-rate * (t - s)) * h s := by
    intro t ht
    let V : ℝ → A := fun s =>
      exp ((t - s) • L) * E * exp (s • (L + E))
    let g : ℝ → ℝ := fun s =>
      κ * η * (Real.exp (-rate * (t - s)) * h s)
    have hpoint : ∀ s ∈ Ioc (0 : ℝ) t, ‖V s‖ ≤ g s := by
      intro s hs
      have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
      have hm := hmix (t - s) hts
      dsimp [V, g, h]
      calc
        ‖exp ((t - s) • L) * E * exp (s • (L + E))‖
            ≤ ‖exp ((t - s) • L) * E‖ * ‖exp (s • (L + E))‖ :=
          norm_mul_le _ _
        _ ≤ (‖exp ((t - s) • L)‖ * ‖E‖) * ‖exp (s • (L + E))‖ := by
          gcongr
          exact norm_mul_le _ _
        _ ≤ ((κ * Real.exp (-rate * (t - s))) * η) *
              ‖exp (s • (L + E))‖ := by
          gcongr
        _ = κ * η *
              (Real.exp (-rate * (t - s)) * ‖exp (s • (L + E))‖) := by
          ring
    have hgcont : Continuous g := by
      dsimp [g, h]
      fun_prop
    have hnormint :
        ‖∫ s in (0 : ℝ)..t, V s‖ ≤
          κ * η * ∫ s in (0 : ℝ)..t,
            Real.exp (-rate * (t - s)) * h s := by
      calc
        ‖∫ s in (0 : ℝ)..t, V s‖ ≤ ∫ s in (0 : ℝ)..t, g s := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht
          · exact Filter.Eventually.of_forall fun s hs => hpoint s hs
          · exact hgcont.intervalIntegrable _ _
        _ = κ * η * ∫ s in (0 : ℝ)..t,
            Real.exp (-rate * (t - s)) * h s := by
          simp [g, mul_assoc]
    change ‖exp (t • (L + E))‖ ≤
      κ * Real.exp (-rate * t) * 1 +
        κ * η * ∫ s in (0 : ℝ)..t,
          Real.exp (-rate * (t - s)) * h s
    rw [duhamel_exp_add L E t]
    calc
      ‖exp (t • L) + ∫ s in (0 : ℝ)..t, V s‖
          ≤ ‖exp (t • L)‖ + ‖∫ s in (0 : ℝ)..t, V s‖ := norm_add_le _ _
      _ ≤ κ * Real.exp (-rate * t) +
            κ * η * ∫ s in (0 : ℝ)..t,
              Real.exp (-rate * (t - s)) * h s :=
        add_le_add (hmix t ht) hnormint
      _ = κ * Real.exp (-rate * t) * 1 +
            κ * η * ∫ s in (0 : ℝ)..t,
              Real.exp (-rate * (t - s)) * h s := by ring
  have result := perturbed_relaxation_of_duhamel
    h κ rate η 1 hh hκ hη zero_le_one h_nonneg hduhamel
  intro t ht
  simpa [h] using result t ht

end FTDQE

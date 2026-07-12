import FTDQE.PerturbedRelaxation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Perturbed relaxation on an invariant subspace

This file gives the vector-level form of Lemma 2.  The ideal mixing estimate is
assumed only for vectors satisfying a predicate `P`; in the quantum
instantiation, `P` will express that an operator is traceless and Hermitian.
-/

namespace FTDQE

open Set intervalIntegral

/-- Perturbed relaxation when the ideal mixing estimate is available only on
an invariant class of vectors.

The hypothesis `hduhamel` is the vector-valued Duhamel formula.  The conditions
`hPx` and `hPintegrand` ensure that the ideal mixing bound is invoked only on
the invariant subspace, rather than on the full ambient operator space.
-/
theorem perturbed_relaxation_on_invariant_subspace
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (ideal perturbed : ℝ → X →L[ℝ] X) (error : X →L[ℝ] X)
    (P : X → Prop) (x : X) (κ rate η : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (htraj : Continuous (fun t : ℝ => perturbed t x))
    (hintegrand : ∀ t : ℝ,
      Continuous (fun s : ℝ => ideal (t - s) (error (perturbed s x))))
    (hduhamel : ∀ t : ℝ, 0 ≤ t →
      perturbed t x = ideal t x +
        ∫ s in (0 : ℝ)..t, ideal (t - s) (error (perturbed s x)))
    (hmix : ∀ t : ℝ, 0 ≤ t → ∀ y : X, P y →
      ‖ideal t y‖ ≤ κ * Real.exp (-rate * t) * ‖y‖)
    (herror : ∀ y : X, ‖error y‖ ≤ η * ‖y‖)
    (hPx : P x)
    (hPintegrand : ∀ s : ℝ, 0 ≤ s → P (error (perturbed s x))) :
    ∀ t : ℝ, 0 ≤ t →
      ‖perturbed t x‖ ≤
        κ * Real.exp (-(rate - κ * η) * t) * ‖x‖ := by
  let h : ℝ → ℝ := fun s => ‖perturbed s x‖
  have hh : Continuous h := continuous_norm.comp htraj
  have h_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ h t := by
    intro t _
    exact norm_nonneg _
  have hscalar : ∀ t : ℝ, 0 ≤ t →
      h t ≤ κ * Real.exp (-rate * t) * ‖x‖ +
        κ * η * ∫ s in (0 : ℝ)..t,
          Real.exp (-rate * (t - s)) * h s := by
    intro t ht
    let V : ℝ → X := fun s => ideal (t - s) (error (perturbed s x))
    let g : ℝ → ℝ := fun s =>
      κ * η * (Real.exp (-rate * (t - s)) * h s)
    have hpoint : ∀ s ∈ Ioc (0 : ℝ) t, ‖V s‖ ≤ g s := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1.le
      have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
      have hm := hmix (t - s) hts (error (perturbed s x))
        (hPintegrand s hs0)
      have he := herror (perturbed s x)
      dsimp [V, g, h]
      calc
        ‖ideal (t - s) (error (perturbed s x))‖
            ≤ κ * Real.exp (-rate * (t - s)) * ‖error (perturbed s x)‖ := hm
        _ ≤ κ * Real.exp (-rate * (t - s)) *
              (η * ‖perturbed s x‖) := by
          gcongr
        _ = κ * η *
              (Real.exp (-rate * (t - s)) * ‖perturbed s x‖) := by
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
    change ‖perturbed t x‖ ≤
      κ * Real.exp (-rate * t) * ‖x‖ +
        κ * η * ∫ s in (0 : ℝ)..t,
          Real.exp (-rate * (t - s)) * h s
    rw [hduhamel t ht]
    calc
      ‖ideal t x + ∫ s in (0 : ℝ)..t, V s‖
          ≤ ‖ideal t x‖ + ‖∫ s in (0 : ℝ)..t, V s‖ := norm_add_le _ _
      _ ≤ κ * Real.exp (-rate * t) * ‖x‖ +
            κ * η * ∫ s in (0 : ℝ)..t,
              Real.exp (-rate * (t - s)) * h s :=
        add_le_add (hmix t ht x hPx) hnormint
  exact perturbed_relaxation_of_duhamel
    h κ rate η ‖x‖ hh hκ hη (norm_nonneg x) h_nonneg hscalar

end FTDQE
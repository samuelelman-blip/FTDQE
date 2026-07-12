import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Operator Duhamel identity

This file proves the Duhamel identity for exponentials in an arbitrary real
Banach algebra. Taking the Banach algebra to be the algebra of bounded linear
endomorphisms gives the operator identity used in Lemma 2.
-/

namespace FTDQE

open Set intervalIntegral
open NormedSpace

/-- Duhamel's formula for two elements of a real Banach algebra:

`exp (t(L+E)) = exp (tL) + ∫₀ᵗ exp ((t-s)L) E exp (s(L+E)) ds`.
-/
theorem duhamel_exp_add
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L E : A) (t : ℝ) :
    exp (t • (L + E)) =
      exp (t • L) +
        ∫ s in (0 : ℝ)..t,
          exp ((t - s) • L) * E * exp (s • (L + E)) := by
  let q : ℝ → ℝ := (fun _ : ℝ => t) - id
  let left : ℝ → A := (fun u : ℝ => exp (u • L)) ∘ q
  let right : ℝ → A := fun s => exp (s • (L + E))
  let F : ℝ → A := fun s => left s * right s
  let G : ℝ → A := fun s => left s * E * right s
  have hinner (s : ℝ) : HasDerivAt q (-1) s := by
    dsimp [q]
    simpa using (hasDerivAt_const (x := s) t).sub (hasDerivAt_id s)
  have hleft (s : ℝ) :
      HasDerivAt left (-(exp (q s • L) * L)) s := by
    have h := (hasDerivAt_exp_smul_const L (q s)).scomp s (hinner s)
    simpa only [left, Function.comp_apply, neg_smul, one_smul] using h
  have hright (s : ℝ) :
      HasDerivAt right ((L + E) * exp (s • (L + E))) s := by
    simpa only [right] using hasDerivAt_exp_smul_const' (L + E) s
  have hFderiv (s : ℝ) : HasDerivAt F (G s) s := by
    dsimp [F, G]
    have h := (hleft s).mul (hright s)
    dsimp [left, right] at h ⊢
    convert h using 1
    · ext r
      rfl
    · noncomm_ring
  have hleftcont : Continuous left := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hleft s).continuousAt
  have hrightcont : Continuous right := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hright s).continuousAt
  have hGcont : Continuous G := by
    dsimp [G]
    exact (hleftcont.mul continuous_const).mul hrightcont
  have hFTC : (∫ s in (0 : ℝ)..t, G s) = F t - F 0 :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hFderiv s)
      (hGcont.intervalIntegrable _ _)
  calc
    exp (t • (L + E)) = F t := by simp [F, left, right, q]
    _ = F 0 + ∫ s in (0 : ℝ)..t, G s := by rw [hFTC]; abel
    _ = exp (t • L) +
        ∫ s in (0 : ℝ)..t,
          exp ((t - s) • L) * E * exp (s • (L + E)) := by
      simp [F, G, left, right, q]

end FTDQE

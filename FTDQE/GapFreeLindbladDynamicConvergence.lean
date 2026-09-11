import FTDQE.GapFreeLindbladDynamics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Dynamical `1/t` convergence theorem

This file discharges the scalar dynamical hypotheses in `gapFree_one_over_t` from an actual
finite-dimensional GKLS master-equation trajectory and operator inequalities.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set intervalIntegral
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Pairing with a positive state preserves the Loewner order on observables. -/
theorem realTracePair_mono_of_le
    {A B ρ : QMatrix d} (hAB : A ≤ B) (hρ : ρ.PosSemidef) :
    realTracePair A ρ ≤ realTracePair B ρ := by
  have hdiff : (B - A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)
  have hp := realTracePair_nonneg_of_posSemidef hdiff hρ
  have hlin : realTracePair (B - A) ρ =
      realTracePair B ρ - realTracePair A ρ := by
    simp [realTracePair, complexTracePair, Matrix.sub_mul]
  rw [hlin] at hp
  linarith

/-- Real scalar multiplication pulls through the real trace pairing. -/
theorem realTracePair_ofReal_smul (κ : ℝ) (A ρ : QMatrix d) :
    realTracePair ((κ : ℂ) • A) ρ = κ * realTracePair A ρ := by
  simp [realTracePair, complexTracePair, Matrix.smul_mul, Complex.real_smul]

/-- The operator coercivity inequality `κ P ≤ K` implies the pointwise scalar inequality
`κ Tr(Pρ) ≤ Tr(Kρ)` for every positive state. -/
theorem realTracePair_coercivity
    {P K ρ : QMatrix d} {κ : ℝ}
    (hPK : ((κ : ℂ) • P) ≤ K)
    (hρ : ρ.PosSemidef) :
    κ * realTracePair P ρ ≤ realTracePair K ρ := by
  have hmono := realTracePair_mono_of_le hPK hρ
  rw [realTracePair_ofReal_smul] at hmono
  exact hmono

/-- If the energy Heisenberg derivative equals `-K`, the energy expectation has derivative
`-Tr(Kρ_t)` along the actual GKLS trajectory. -/
theorem energy_hasDerivAt_of_adjoint_eq_neg
    {ι : Type*} [Fintype ι]
    {G H K : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hH : fullHeisenbergAdjoint G J H = -K)
    (t : ℝ) :
    HasDerivAt (fun s => realTracePair H (ρ s))
      (-realTracePair K (ρ t)) t := by
  have h := realTracePair_hasDerivAt htraj H t
  rw [hH] at h
  simpa [realTracePair, complexTracePair] using h

/-- Fundamental-theorem-of-calculus form of the energy budget. -/
theorem dissipation_integral_eq_energy_drop
    {ι : Type*} [Fintype ι]
    {G H K : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hH : fullHeisenbergAdjoint G J H = -K)
    (a b : ℝ) :
    ∫ s in a..b, realTracePair K (ρ s) =
      realTracePair H (ρ a) - realTracePair H (ρ b) := by
  have hDcont : Continuous (fun s => realTracePair K (ρ s)) :=
    continuous_realTracePair_trajectory htraj
  have hDint : IntervalIntegrable (fun s => -realTracePair K (ρ s))
      MeasureTheory.volume a b := hDcont.neg.intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun s => realTracePair H (ρ s))
    (f' := fun s => -realTracePair K (ρ s))
    (fun s _hs => energy_hasDerivAt_of_adjoint_eq_neg htraj hH s)
    hDint
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

/-- Dynamical version of the paper's `1/t` convergence theorem.

Unlike `gapFree_one_over_t`, this theorem does not assume that `q` is antitone, does not assume
pointwise scalar coercivity, and does not assume an integrated dissipation budget. These are all
derived from the GKLS ODE and operator inequalities. -/
theorem gapFree_one_over_t_of_gkls
    {ι : Type*} [Fintype ι]
    {G H P K : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    {κ W Emin t : ℝ}
    (hκ : 0 < κ) (ht : 0 < t)
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hP : P.PosSemidef)
    (hPadj : fullHeisenbergAdjoint G J P ≤ 0)
    (hcoerc : ((κ : ℂ) • P) ≤ K)
    (hHadj : fullHeisenbergAdjoint G J H = -K)
    (hfloor : Emin ≤ realTracePair H (ρ t))
    (hwidth : realTracePair H (ρ 0) - Emin ≤ W) :
    realTracePair P (ρ t) ≤ W / (κ * t) := by
  let q : ℝ → ℝ := fun s => realTracePair P (ρ s)
  let D : ℝ → ℝ := fun s => realTracePair K (ρ s)
  have hq_nonneg : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ q s := by
    intro s hs
    exact realTracePair_nonneg_of_posSemidef hP (hpos s)
  have hq_anti : Antitone q :=
    antitone_realTracePair_of_adjoint_nonpos htraj hpos hPadj
  have hq_cont : Continuous q := continuous_realTracePair_trajectory htraj
  have hD_cont : Continuous D := continuous_realTracePair_trajectory htraj
  have hq_int : IntervalIntegrable q MeasureTheory.volume 0 t :=
    hq_cont.intervalIntegrable 0 t
  have hD_int : IntervalIntegrable D MeasureTheory.volume 0 t :=
    hD_cont.intervalIntegrable 0 t
  have hcoerc_scalar : ∀ s ∈ Icc (0 : ℝ) t, κ * q s ≤ D s := by
    intro s hs
    exact realTracePair_coercivity hcoerc (hpos s)
  have hdrop :
      ∫ s in (0 : ℝ)..t, D s =
        realTracePair H (ρ 0) - realTracePair H (ρ t) := by
    exact dissipation_integral_eq_energy_drop htraj hHadj 0 t
  have henergy : ∫ s in (0 : ℝ)..t, D s ≤ W := by
    rw [hdrop]
    linarith
  exact gapFree_one_over_t hκ ht hq_nonneg hq_anti hq_int hD_int
    hcoerc_scalar henergy

end

end GapFreeLindblad
end FTDQE

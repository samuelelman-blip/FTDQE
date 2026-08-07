import FTDQE.GKLSGenerator
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Gap-free Lindblad kernel formalization

Finite-dimensional algebraic core of the working note
"Gap-Free Convergence of Dissipative Lindblad Dynamics to a Low-Energy Subspace".

The first layer deliberately treats the Bohr components abstractly through their defining
commutation relation. This avoids importing any spectral-gap hypothesis: the only frequency
assumption used below is the exact relation `H A_ω = A_ω H + ω A_ω`.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- `A` is a Bohr component of frequency `ω` for `H` when
`H A = A H + ω A`.  This convention agrees with the manuscript: negative `ω`
lowers energy. -/
def IsBohrComponent (H A : QMatrix d) (ω : ℝ) : Prop :=
  H * A = A * H + (ω : ℂ) • A

/-- Taking the adjoint of a Bohr relation reverses the frequency. -/
theorem IsBohrComponent.adjoint_left
    {H A : QMatrix d} {ω : ℝ}
    (hH : H.IsHermitian) (hA : IsBohrComponent H A ω) :
    H * Aᴴ = Aᴴ * H - (ω : ℂ) • Aᴴ := by
  have hstar : Aᴴ * H = H * Aᴴ + (ω : ℂ) • Aᴴ := by
    calc
      Aᴴ * H = (H * A)ᴴ := by
        simp [hH.eq, Matrix.conjTranspose_mul]
      _ = (A * H + (ω : ℂ) • A)ᴴ := by rw [hA]
      _ = H * Aᴴ + (ω : ℂ) • Aᴴ := by
        simp [hH.eq, Matrix.conjTranspose_mul]
  exact (eq_sub_iff_add_eq).2 hstar.symm

/-- The contribution of one pair of jump components to the Heisenberg energy drift. -/
def crossEnergyDrift (H A B : QMatrix d) : QMatrix d :=
  Bᴴ * H * A -
    (1 / 2 : ℂ) • (H * (Bᴴ * A) + (Bᴴ * A) * H)

/-- Exact cross-frequency drift identity, manuscript Eq. (24).

No assumption involving `|ω-ω'|` occurs. -/
theorem crossEnergyDrift_eq
    {H A B : QMatrix d} {ω ω' : ℝ}
    (hH : H.IsHermitian)
    (hA : IsBohrComponent H A ω)
    (hB : IsBohrComponent H B ω') :
    crossEnergyDrift H A B =
      (((ω : ℂ) + (ω' : ℂ)) / 2) • (Bᴴ * A) := by
  have hBadj : H * Bᴴ = Bᴴ * H - (ω' : ℂ) • Bᴴ :=
    hB.adjoint_left hH
  have h1 :
      Bᴴ * H * A = Bᴴ * A * H + (ω : ℂ) • (Bᴴ * A) := by
    calc
      Bᴴ * H * A = Bᴴ * (H * A) := by simp [Matrix.mul_assoc]
      _ = Bᴴ * (A * H + (ω : ℂ) • A) := by rw [hA]
      _ = Bᴴ * A * H + (ω : ℂ) • (Bᴴ * A) := by
        simp [Matrix.mul_add, Matrix.mul_assoc]
  have h2 :
      H * (Bᴴ * A) =
        Bᴴ * A * H + ((ω : ℂ) - (ω' : ℂ)) • (Bᴴ * A) := by
    calc
      H * (Bᴴ * A) = (H * Bᴴ) * A := by simp [Matrix.mul_assoc]
      _ = (Bᴴ * H - (ω' : ℂ) • Bᴴ) * A := by rw [hBadj]
      _ = Bᴴ * (H * A) - (ω' : ℂ) • (Bᴴ * A) := by
        simp [Matrix.sub_mul, Matrix.mul_assoc]
      _ = Bᴴ * (A * H + (ω : ℂ) • A) - (ω' : ℂ) • (Bᴴ * A) := by rw [hA]
      _ = Bᴴ * A * H + ((ω : ℂ) - (ω' : ℂ)) • (Bᴴ * A) := by
        simp [Matrix.mul_add, Matrix.mul_assoc]
        module
  rw [crossEnergyDrift, h1, h2]
  module

section Correlated

variable {ι : Type*} [Fintype ι]

/-- Heisenberg dissipative action associated with a Kossakowski kernel `C`. -/
def correlatedAdjoint
    (C : ι → ι → ℂ) (A : ι → QMatrix d) (X : QMatrix d) : QMatrix d :=
  ∑ i, ∑ j, C i j • crossEnergyDrift X (A i) (A j)

/-- Summing the pairwise identity gives the full cross-frequency energy-drift formula. -/
theorem correlatedAdjoint_energy
    {H : QMatrix d} {ω : ι → ℝ} {A : ι → QMatrix d}
    (C : ι → ι → ℂ)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i)) :
    correlatedAdjoint C A H =
      ∑ i, ∑ j,
        (C i j * (((ω i : ℂ) + (ω j : ℂ)) / 2)) • ((A j)ᴴ * A i) := by
  rw [correlatedAdjoint]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [crossEnergyDrift_eq hH (hA i) (hA j)]
  simp [smul_smul]

/-- The constant-weight Cauchy kernel used in the first running example. -/
def constantKernel (ε : ℝ) (ω ω' : ℝ) : ℝ :=
  (2 * ε) / (-(ω + ω'))

/-- The linear-weight kernel `m₁(s)=4 ε² s`. -/
def linearKernel (ε : ℝ) (ω ω' : ℝ) : ℝ :=
  (2 * ε / (-(ω + ω'))) ^ 2

/-- For downward frequencies the constant kernel times the drift factor is exactly `-ε`. -/
theorem constantKernel_drift_factor
    {ε ω ω' : ℝ}
    (hε : 0 < ε) (hω : ω ≤ -ε) (hω' : ω' ≤ -ε) :
    constantKernel ε ω ω' * ((ω + ω') / 2) = -ε := by
  have hsum : ω + ω' ≠ 0 := by linarith
  rw [constantKernel]
  field_simp
  ring

/-- For the linear weight the drift coefficient has the expected negative Cauchy form. -/
theorem linearKernel_drift_factor
    {ε ω ω' : ℝ}
    (hε : 0 < ε) (hω : ω ≤ -ε) (hω' : ω' ≤ -ε) :
    linearKernel ε ω ω' * ((ω + ω') / 2) =
      -(2 * ε^2 / (-(ω + ω'))) := by
  have hsum : ω + ω' ≠ 0 := by linarith
  rw [linearKernel]
  field_simp
  ring

/-- A linear combination of downward components is dark on `P` whenever every component is. -/
theorem sum_smul_mul_eq_zero
    (A : ι → QMatrix d) (c : ι → ℂ) (P : QMatrix d)
    (hP : ∀ i, A i * P = 0) :
    (∑ i, c i • A i) * P = 0 := by
  rw [Finset.sum_mul]
  simp [hP]

end Correlated

section ConvergenceScalar

open intervalIntegral

/-- Scalar endpoint estimate used in Theorem 2.

This is the last step of the paper's `1/t` argument: a nonincreasing nonnegative target error
whose time integral is bounded by `W/κ` obeys the advertised endpoint bound. -/
theorem antitone_endpoint_le_of_integral_bound
    {q : ℝ → ℝ} {κ W t : ℝ}
    (hκ : 0 < κ) (ht : 0 < t)
    (hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ q s)
    (hq_anti : Antitone q)
    (hq_int : IntervalIntegrable q volume 0 t)
    (hbound : κ * ∫ s in (0 : ℝ)..t, q s ≤ W) :
    q t ≤ W / (κ * t) := by
  have hconst_int :
      ∫ _s in (0 : ℝ)..t, q t = t * q t := by
    simp [ht.ne']
  have hmono :
      ∫ s in (0 : ℝ)..t, q t ≤ ∫ s in (0 : ℝ)..t, q s := by
    apply intervalIntegral.integral_mono_on
    · exact intervalIntegrable_const
    · exact hq_int
    · exact hq_nonneg
    · intro s hs
      exact hq_anti hs.2
  rw [hconst_int] at hmono
  have hprod : κ * (t * q t) ≤ W := le_trans (mul_le_mul_of_nonneg_left hmono hκ.le) hbound
  have hkt : 0 < κ * t := mul_pos hκ ht
  apply (le_div_iff₀ hkt).2
  nlinarith

end ConvergenceScalar

end

end GapFreeLindblad
end FTDQE

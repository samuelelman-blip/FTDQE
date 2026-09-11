import FTDQE.GapFreeLindblad

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem ofReal_smul_qMatrix (r : ℝ) (X : QMatrix d) :
    (r : ℂ) • X = r • X := by
  ext i j
  simp [Complex.real_smul]

def HasEnergy (H P : QMatrix d) (E : ℝ) : Prop :=
  H * P = (E : ℂ) • P

def NoSpectrumBelow (H : QMatrix d) (E₀ : ℝ) : Prop :=
  ∀ E : ℝ, E < E₀ → ∀ X : QMatrix d,
    H * X = (E : ℂ) • X → X = 0

theorem bohr_mul_hasEnergy
    {H A P : QMatrix d} {ω E : ℝ}
    (hA : IsBohrComponent H A ω)
    (hP : HasEnergy H P E) :
    H * (A * P) = ((E + ω : ℝ) : ℂ) • (A * P) := by
  calc
    H * (A * P) = (H * A) * P := by simp [Matrix.mul_assoc]
    _ = (A * H + (ω : ℂ) • A) * P := by rw [hA]
    _ = A * (H * P) + (ω : ℂ) • (A * P) := by
      simp [Matrix.add_mul, Matrix.mul_assoc]
    _ = A * ((E : ℂ) • P) + (ω : ℂ) • (A * P) := by rw [hP]
    _ = (E : ℂ) • (A * P) + (ω : ℂ) • (A * P) := by
      rw [Matrix.mul_smul]
    _ = ((E : ℂ) + (ω : ℂ)) • (A * P) := by
      rw [add_smul]
    _ = ((E + ω : ℝ) : ℂ) • (A * P) := by
      rw [Complex.ofReal_add]

theorem bohr_mul_eq_zero_below_target
    {H A P : QMatrix d} {ω E E₀ ε : ℝ}
    (hbelow : NoSpectrumBelow H E₀)
    (hA : IsBohrComponent H A ω)
    (hP : HasEnergy H P E)
    (hE : E < E₀ + ε)
    (hω : ω ≤ -ε) :
    A * P = 0 := by
  have hsum : E + ω < E₀ := by linarith
  apply hbelow (E + ω) hsum (A * P)
  exact bohr_mul_hasEnergy hA hP

section FiniteTarget

variable {ι : Type*} [Fintype ι]

theorem bohr_mul_target_sum_eq_zero
    {H A : QMatrix d} {ω E₀ ε : ℝ}
    (P : ι → QMatrix d) (E : ι → ℝ)
    (hbelow : NoSpectrumBelow H E₀)
    (hA : IsBohrComponent H A ω)
    (hP : ∀ i, HasEnergy H (P i) (E i))
    (hE : ∀ i, E i < E₀ + ε)
    (hω : ω ≤ -ε) :
    A * (∑ i, P i) = 0 := by
  rw [Matrix.mul_sum]
  simp [bohr_mul_eq_zero_below_target hbelow hA (hP _) (hE _) hω]

end FiniteTarget

theorem isBohrComponent_shift_iff
    (H A : QMatrix d) (ω c : ℝ) :
    IsBohrComponent (H + (c : ℂ) • (1 : QMatrix d)) A ω ↔
      IsBohrComponent H A ω := by
  constructor
  · intro h
    have hexp : H * A + c • A = A * H + c • A + ω • A := by
      simpa [IsBohrComponent, Matrix.add_mul, Matrix.mul_add,
        ofReal_smul_qMatrix] using h
    have hcancel : H * A + c • A = (A * H + ω • A) + c • A := by
      calc
        H * A + c • A = A * H + c • A + ω • A := hexp
        _ = (A * H + ω • A) + c • A := by abel
    have hreal : H * A = A * H + ω • A := add_right_cancel hcancel
    simpa [IsBohrComponent, ofReal_smul_qMatrix] using hreal
  · intro h
    have hreal : H * A = A * H + ω • A := by
      simpa [IsBohrComponent, ofReal_smul_qMatrix] using h
    have hexp : H * A + c • A = A * H + c • A + ω • A := by
      calc
        H * A + c • A = (A * H + ω • A) + c • A := by rw [hreal]
        _ = A * H + c • A + ω • A := by abel
    simpa [IsBohrComponent, Matrix.add_mul, Matrix.mul_add,
      ofReal_smul_qMatrix] using hexp

end

end GapFreeLindblad
end FTDQE

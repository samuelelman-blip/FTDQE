import FTDQE.GapFreeLindbladAdmissibleClosed
import FTDQE.GapFreeLindbladCoercivity

/-!
# End-to-end gap-free theorem

This file closes the final algebraic hand-off between darkness of the low-energy target,
the excited-sector restricted coercivity constant, and the concrete GKLS `1/t` theorem.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- The Heisenberg Lindblad dissipator is unital. -/
theorem heisenbergDissipator_one (J : QMatrix d) :
    heisenbergDissipator J (1 : QMatrix d) = 0 := by
  simp [heisenbergDissipator]
  module

/-- Heisenberg dissipators are linear over subtraction in the observable. -/
theorem heisenbergDissipator_sub (J X Y : QMatrix d) :
    heisenbergDissipator J (X - Y) =
      heisenbergDissipator J X - heisenbergDissipator J Y := by
  simp [heisenbergDissipator, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  module

/-- The finite dissipative adjoint is unital. -/
theorem finiteDissipativeAdjoint_one (J : ι → QMatrix d) :
    finiteDissipativeAdjoint J (1 : QMatrix d) = 0 := by
  simp [finiteDissipativeAdjoint, heisenbergDissipator_one]

/-- Drift of the complement is the negative drift of the target. -/
theorem finiteDissipativeAdjoint_one_sub
    (J : ι → QMatrix d) (P : QMatrix d) :
    finiteDissipativeAdjoint J ((1 : QMatrix d) - P) =
      -finiteDissipativeAdjoint J P := by
  simp [finiteDissipativeAdjoint, heisenbergDissipator_sub,
    heisenbergDissipator_one]

/-- Darkness of a positive target implies nonpositive drift of its complement. -/
theorem complement_drift_nonpos_of_dark
    (J : ι → QMatrix d) {P : QMatrix d}
    (hP : P.PosSemidef) (hdark : ∀ r, J r * P = 0) :
    finiteDissipativeAdjoint J ((1 : QMatrix d) - P) ≤ 0 := by
  rw [finiteDissipativeAdjoint_one_sub]
  exact neg_nonpos.mpr
    (finiteDissipativeAdjoint_posSemidef_of_dark J hP hdark).nonneg

/-- A kernel Gram operator annihilates a target on the right when every component does. -/
theorem kernelGramOperator_mul_eq_zero_of_components_dark
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) (P : QMatrix d)
    (hdark : ∀ i, A i * P = 0) :
    kernelGramOperator D A * P = 0 := by
  rw [kernelGramOperator, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Matrix.mul_assoc, hdark]

/-- For a positive Gram kernel, darkness also gives left annihilation. -/
theorem mul_kernelGramOperator_eq_zero_of_components_dark
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) {P : QMatrix d}
    (hD : D.PosSemidef) (hP : P.IsHermitian)
    (hdark : ∀ i, A i * P = 0) :
    P * kernelGramOperator D A = 0 := by
  let K := kernelGramOperator D A
  have hK : K.PosSemidef := kernelGramOperator_posSemidef D A hD
  have hright : K * P = 0 :=
    kernelGramOperator_mul_eq_zero_of_components_dark D A P hdark
  have hstar := congrArg Matrix.conjTranspose hright
  simpa [K, hK.isHermitian.eq, hP.eq, Matrix.conjTranspose_mul] using hstar

/-- The Lyapunov operator is entirely supported on the complement of a dark target. -/
theorem complement_mul_kernelGramOperator_mul_complement
    (D : Matrix ι ι ℂ) (A : ι → QMatrix d) {P : QMatrix d}
    (hD : D.PosSemidef) (hP : P.IsHermitian)
    (hdark : ∀ i, A i * P = 0) :
    ((1 : QMatrix d) - P) * kernelGramOperator D A * ((1 : QMatrix d) - P) =
      kernelGramOperator D A := by
  have hright := kernelGramOperator_mul_eq_zero_of_components_dark D A P hdark
  have hleft := mul_kernelGramOperator_eq_zero_of_components_dark D A hD hP hdark
  rw [Matrix.sub_mul, Matrix.one_mul, hleft, sub_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, hright, sub_zero]

/-- The operational coercivity constant for an admissible-weight Lyapunov operator,
compressed to an explicitly supplied orthonormal frame for the excited sector. -/
def admissibleKappaRestricted
    {r : ℕ} {ε : ℝ} {m : ℝ → ℝ} {ω : ι → ℝ}
    (hm : AdmissibleWeight ε m) (hdown : ∀ i, ω i ≤ -ε)
    (A : ι → QMatrix d) (U : Matrix (Fin d) (Fin (r + 1)) ℂ) : ℝ :=
  let D := admissibleDriftKernelMatrix m ω
  let K := kernelGramOperator D A
  kappaRestricted K U
    (kernelGramOperator_posSemidef D A
      (admissibleWeight_driftKernelMatrix_posSemidef hm hdown)).isHermitian

/-- Fully closed finite-dimensional gap-free preparation theorem.

For a public admissible weight, a downward Bohr family dark on the low-energy target,
and an orthonormal frame spanning the complementary excited sector, positive restricted
coercivity implies existence of ordinary dark GKLS jumps whose every positive trajectory
obeys the explicit `W/(κ_m t)` excited-population bound. No Hamiltonian gap, Liouvillian
gap, or minimum Bohr-frequency separation appears in the assumptions. -/
theorem admissibleWeight_exists_dark_GKLS_gapFree_one_over_t
    {r : ℕ}
    {H P₀ : QMatrix d} {ε : ℝ} {m : ℝ → ℝ}
    {ω : ι → ℝ} {A : ι → QMatrix d}
    (U : Matrix (Fin d) (Fin (r + 1)) ℂ)
    (hm : AdmissibleWeight ε m)
    (hH : H.PosSemidef)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε)
    (hP₀ : P₀.PosSemidef)
    (hP₀le : P₀ ≤ (1 : QMatrix d))
    (hdark : ∀ i, A i * P₀ = 0)
    (hUstarU : Uᴴ * U = 1)
    (hUUstar : U * Uᴴ = (1 : QMatrix d) - P₀)
    (hκ : 0 < admissibleKappaRestricted hm hdown A U) :
    ∃ J : ι → QMatrix d,
      (∀ j, J j * P₀ = 0) ∧
      (∀ ρ, correlatedDissipator (admissibleKernelMatrix m ω) A ρ =
        ∑ j, lindbladDissipator (J j) ρ) ∧
      ∀ {ρ : ℝ → QMatrix d} {W t : ℝ},
        0 < t →
        IsGKLSTrajectory (0 : QMatrix d) J ρ →
        IsPositiveTrajectory ρ →
        realTracePair H (ρ 0) ≤ W →
        realTracePair ((1 : QMatrix d) - P₀) (ρ t) ≤
          W / (admissibleKappaRestricted hm hdown A U * t) := by
  let D := admissibleDriftKernelMatrix m ω
  let K := kernelGramOperator D A
  let Q : QMatrix d := (1 : QMatrix d) - P₀
  have hD : D.PosSemidef := by
    simpa [D] using admissibleWeight_driftKernelMatrix_posSemidef hm hdown
  have hKpos : K.PosSemidef := by
    exact kernelGramOperator_posSemidef D A hD
  have hKherm : K.IsHermitian := hKpos.isHermitian
  have hQ : Q.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hP₀le)
  have hKU : Q * K * Q = K := by
    simpa [Q, K, D] using
      complement_mul_kernelGramOperator_mul_complement
        D A hD hP₀.isHermitian hdark
  obtain ⟨J, hJdark, hsch, henergy⟩ :=
    admissibleWeight_exists_dark_GKLS_jumps_with_energy_drift
      hm hH.isHermitian hA hdown hdark
  refine ⟨J, hJdark, hsch, ?_⟩
  intro ρ W t ht htraj hpos hW
  have hQadjD : finiteDissipativeAdjoint J Q ≤ 0 := by
    simpa [Q] using complement_drift_nonpos_of_dark J hP₀ hJdark
  have hQadj : fullHeisenbergAdjoint (0 : QMatrix d) J Q ≤ 0 := by
    simpa [fullHeisenbergAdjoint, coherentAdjoint] using hQadjD
  have hHadj : fullHeisenbergAdjoint (0 : QMatrix d) J H = -K := by
    simpa [fullHeisenbergAdjoint, coherentAdjoint, K, D] using henergy
  have hfloor : (0 : ℝ) ≤ realTracePair H (ρ t) :=
    realTracePair_nonneg_of_posSemidef hH (hpos t)
  have hwidth : realTracePair H (ρ 0) - (0 : ℝ) ≤ W := by
    simpa using hW
  have hκ' : 0 < kappaRestricted K U hKherm := by
    simpa [admissibleKappaRestricted, K, D] using hκ
  have hbound := gapFree_one_over_t_of_gkls_kappaRestricted
    (d := d) (r := r) (G := (0 : QMatrix d)) (H := H)
    (P := Q) (K := K) (J := J) (ρ := ρ) U
    hKherm hUstarU (by simpa [Q] using hUUstar) hKU hκ' ht
    htraj hpos hQ hQadj hHadj hfloor hwidth
  simpa [Q, admissibleKappaRestricted, K, D] using hbound

end

end GapFreeLindblad
end FTDQE

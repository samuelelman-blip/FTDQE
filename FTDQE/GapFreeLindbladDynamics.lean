import FTDQE.GapFreeLindbladDarkness
import FTDQE.GapFreeLindbladConvergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Gap-free Lindblad dynamics

The finite-dimensional master equation is stated entrywise.  This is equivalent to the matrix
ODE and avoids introducing any auxiliary norm on matrix space.  Observable derivatives are then
proved by finite sums of scalar derivatives.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Function
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Complex trace pairing before taking the physical real part. -/
def complexTracePair (O ρ : QMatrix d) : ℂ := Matrix.trace (O * ρ)

/-- Real expectation pairing. -/
def realTracePair (O ρ : QMatrix d) : ℝ := (complexTracePair O ρ).re

/-- A curve solves the concrete GKLS master equation when every matrix entry satisfies the
corresponding scalar ODE.  In finite dimension this is exactly the matrix equation
`ρ'(t) = gklsApply G J (ρ t)`. -/
def IsGKLSTrajectory {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (ρ : ℝ → QMatrix d) : Prop :=
  ∀ p q t,
    HasDerivAt (fun s : ℝ => ρ s p q)
      (gklsApply G J (ρ t) p q) t

/-- The full Heisenberg adjoint associated with the same Hamiltonian and jump family. -/
def fullHeisenbergAdjoint {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (O : QMatrix d) : QMatrix d :=
  coherentAdjoint G O + finiteDissipativeAdjoint J O

/-- Trace duality for the coherent part. -/
theorem trace_hamiltonian_duality
    (G O ρ : QMatrix d) :
    Matrix.trace (O * hamiltonianPart G ρ) =
      Matrix.trace (coherentAdjoint G O * ρ) := by
  rw [hamiltonianPart, coherentAdjoint]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_smul, Matrix.trace_sub]
  have h1 : Matrix.trace (O * (G * ρ)) = Matrix.trace ((O * G) * ρ) := by
    simp [Matrix.mul_assoc]
  have h2 : Matrix.trace (O * (ρ * G)) = Matrix.trace ((G * O) * ρ) := by
    calc
      Matrix.trace (O * (ρ * G)) = Matrix.trace ((O * ρ) * G) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (G * (O * ρ)) := Matrix.trace_mul_comm (O * ρ) G
      _ = Matrix.trace ((G * O) * ρ) := by simp [Matrix.mul_assoc]
  rw [h1, h2]
  ring

/-- Trace duality for one Lindblad dissipator. -/
theorem trace_lindblad_duality
    (J O ρ : QMatrix d) :
    Matrix.trace (O * lindbladDissipator J ρ) =
      Matrix.trace (heisenbergDissipator J O * ρ) := by
  rw [lindbladDissipator, heisenbergDissipator]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul]
  have hsandwich :
      Matrix.trace (O * (J * ρ * Jᴴ)) = Matrix.trace ((Jᴴ * O * J) * ρ) := by
    calc
      Matrix.trace (O * (J * ρ * Jᴴ)) =
          Matrix.trace ((O * J) * (ρ * Jᴴ)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * Jᴴ) * (O * J)) :=
        Matrix.trace_mul_comm (O * J) (ρ * Jᴴ)
      _ = Matrix.trace (ρ * (Jᴴ * O * J)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Jᴴ * O * J) * ρ) :=
        Matrix.trace_mul_comm ρ (Jᴴ * O * J)
  have hleft :
      Matrix.trace (O * ((Jᴴ * J) * ρ)) =
        Matrix.trace ((O * (Jᴴ * J)) * ρ) := by simp [Matrix.mul_assoc]
  have hright :
      Matrix.trace (O * (ρ * (Jᴴ * J))) =
        Matrix.trace (((Jᴴ * J) * O) * ρ) := by
    calc
      Matrix.trace (O * (ρ * (Jᴴ * J))) =
          Matrix.trace ((O * ρ) * (Jᴴ * J)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Jᴴ * J) * (O * ρ)) :=
        Matrix.trace_mul_comm (O * ρ) (Jᴴ * J)
      _ = Matrix.trace (((Jᴴ * J) * O) * ρ) := by simp [Matrix.mul_assoc]
  rw [hsandwich, hleft, hright]
  ring

/-- Exact Schrödinger--Heisenberg trace duality for the finite GKLS generator. -/
theorem trace_gkls_duality {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (O ρ : QMatrix d) :
    Matrix.trace (O * gklsApply G J ρ) =
      Matrix.trace (fullHeisenbergAdjoint G J O * ρ) := by
  calc
    Matrix.trace (O * gklsApply G J ρ) =
        Matrix.trace (O * hamiltonianPart G ρ) +
          ∑ r, Matrix.trace (O * lindbladDissipator (J r) ρ) := by
      simp [gklsApply, Matrix.mul_add, Matrix.mul_sum]
    _ = Matrix.trace (coherentAdjoint G O * ρ) +
          ∑ r, Matrix.trace (heisenbergDissipator (J r) O * ρ) := by
      rw [trace_hamiltonian_duality]
      apply congrArg (fun z => Matrix.trace (coherentAdjoint G O * ρ) + z)
      apply Finset.sum_congr rfl
      intro r hr
      exact trace_lindblad_duality (J r) O ρ
    _ = Matrix.trace (fullHeisenbergAdjoint G J O * ρ) := by
      simp [fullHeisenbergAdjoint, finiteDissipativeAdjoint,
        Matrix.add_mul, Finset.sum_mul]

/-- The complex trace pairing differentiates along the actual entrywise GKLS master equation. -/
theorem complexTracePair_hasDerivAt {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (hρ : IsGKLSTrajectory G J ρ) (O : QMatrix d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => complexTracePair O (ρ s))
      (complexTracePair O (gklsApply G J (ρ t))) t := by
  have hsum :
      HasDerivAt
        (fun s : ℝ => ∑ i : Fin d, ∑ j : Fin d, O i j * ρ s j i)
        (∑ i : Fin d, ∑ j : Fin d,
          O i j * gklsApply G J (ρ t) j i) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hρ j i t).const_mul (O i j)
  simpa [complexTracePair, Matrix.trace, Matrix.mul_apply] using hsum

/-- Taking the real part gives the physical expectation derivative. -/
theorem realTracePair_hasDerivAt {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (hρ : IsGKLSTrajectory G J ρ) (O : QMatrix d) (t : ℝ) :
    HasDerivAt (fun s => realTracePair O (ρ s))
      (realTracePair (fullHeisenbergAdjoint G J O) (ρ t)) t := by
  have hc := complexTracePair_hasDerivAt hρ O t
  have hre :
      HasDerivAt (fun s : ℝ => (complexTracePair O (ρ s)).re)
        (complexTracePair O (gklsApply G J (ρ t))).re t := by
    have houter :
        HasFDerivAt (RCLike.reCLM : ℂ →L[ℝ] ℝ)
          (RCLike.reCLM : ℂ →L[ℝ] ℝ) (complexTracePair O (ρ t)) :=
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt
    simpa [Function.comp_def] using houter.comp_hasDerivAt t hc
  have hduality :
      complexTracePair O (gklsApply G J (ρ t)) =
        complexTracePair (fullHeisenbergAdjoint G J O) (ρ t) := by
    exact trace_gkls_duality G J O (ρ t)
  simpa [realTracePair, hduality] using hre

/-- Positive matrices have nonnegative real trace pairing. -/
theorem realTracePair_nonneg_of_posSemidef
    {A ρ : QMatrix d} (hA : A.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ realTracePair A ρ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  have hB' : ρ = Bᴴ * B := by simpa only [star_eq_conjTranspose] using hB
  rw [hB']
  have hBA : (B * A * Bᴴ).PosSemidef := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      hA.conjTranspose_mul_mul_same Bᴴ
  have htrace : 0 ≤ Matrix.trace (B * A * Bᴴ) := hBA.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (B * A * Bᴴ)).re :=
    RCLike.nonneg_iff.mp htrace |>.1
  unfold realTracePair complexTracePair
  have hcycle :
      Matrix.trace (A * (Bᴴ * B)) = Matrix.trace (B * A * Bᴴ) := by
    calc
      Matrix.trace (A * (Bᴴ * B)) = Matrix.trace ((A * Bᴴ) * B) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (B * (A * Bᴴ)) := Matrix.trace_mul_comm (A * Bᴴ) B
      _ = Matrix.trace (B * A * Bᴴ) := by simp [Matrix.mul_assoc]
  rw [hcycle]
  exact hre

/-- A positive density trajectory.  Positivity preservation by the GKLS semigroup is formalized
separately from the observable calculus. -/
def IsPositiveTrajectory (ρ : ℝ → QMatrix d) : Prop :=
  ∀ t, (ρ t).PosSemidef

/-- Observable expectations along an actual GKLS trajectory are continuous. -/
theorem continuous_realTracePair_trajectory {ι : Type*} [Fintype ι]
    {G O : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (hρ : IsGKLSTrajectory G J ρ) :
    Continuous (fun t => realTracePair O (ρ t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (realTracePair_hasDerivAt hρ O t).continuousAt

/-- If the Heisenberg derivative is positive semidefinite, expectation is monotone. -/
theorem monotone_realTracePair_of_adjoint_posSemidef
    {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d} {O : QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hO : (fullHeisenbergAdjoint G J O).PosSemidef) :
    Monotone (fun t => realTracePair O (ρ t)) := by
  refine monotone_of_hasDerivAt_nonneg
    (f' := fun t => realTracePair (fullHeisenbergAdjoint G J O) (ρ t))
    (fun t => realTracePair_hasDerivAt htraj O t) ?_
  intro t
  exact realTracePair_nonneg_of_posSemidef hO (hpos t)

/-- If the Heisenberg derivative is negative semidefinite, expectation is antitone. -/
theorem antitone_realTracePair_of_adjoint_nonpos
    {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d} {O : QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hO : fullHeisenbergAdjoint G J O ≤ 0) :
    Antitone (fun t => realTracePair O (ρ t)) := by
  have hneg : (-fullHeisenbergAdjoint G J O).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr hO)
  refine antitone_of_hasDerivAt_nonpos
    (f' := fun t => realTracePair (fullHeisenbergAdjoint G J O) (ρ t))
    (fun t => realTracePair_hasDerivAt htraj O t) ?_
  intro t
  have hp := realTracePair_nonneg_of_posSemidef hneg (hpos t)
  have hp' : 0 ≤ -realTracePair (fullHeisenbergAdjoint G J O) (ρ t) := by
    simpa [realTracePair, complexTracePair] using hp
  exact neg_nonneg.mp hp'

/-- For a dark target commuting with the coherent term, target population is monotone along the
actual GKLS master equation. -/
theorem target_population_monotone {ι : Type*} [Fintype ι]
    {G P : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hP : P.PosSemidef)
    (hdark : ∀ r, J r * P = 0)
    (hcomm : G * P = P * G) :
    Monotone (fun t => realTracePair P (ρ t)) := by
  apply monotone_realTracePair_of_adjoint_posSemidef htraj hpos
  simpa [fullHeisenbergAdjoint] using
    fullAdjoint_target_posSemidef J hP hdark hcomm

end

end GapFreeLindblad
end FTDQE

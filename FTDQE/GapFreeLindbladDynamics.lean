import FTDQE.GapFreeLindbladDarkness
import FTDQE.GapFreeLindbladConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Order

/-!
# Gap-free Lindblad dynamics

This file closes the ODE layer between the operator inequalities and the scalar convergence
argument.  A trajectory is required to solve the actual finite-dimensional GKLS master equation
`ρ' = L(ρ)`.  From that equation we derive the Heisenberg expectation derivative, rather than
assuming monotonicity of the scalar observables.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Function
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Real expectation pairing.  For Hermitian `O` and positive `ρ` this is the usual real
expectation value `Tr(Oρ)`. -/
def realTracePair (O ρ : QMatrix d) : ℝ :=
  (Matrix.trace (O * ρ)).re

/-- The real expectation pairing with fixed observable is real-linear in the state. -/
def realTracePairLinear (O : QMatrix d) : QMatrix d →ₗ[ℝ] ℝ where
  toFun := realTracePair O
  map_add' X Y := by
    simp [realTracePair, Matrix.mul_add]
  map_smul' r X := by
    simp [realTracePair, Matrix.mul_smul, Complex.real_smul]

/-- In finite dimension the real expectation functional is automatically continuous. -/
noncomputable def realTracePairCLM (O : QMatrix d) : QMatrix d →L[ℝ] ℝ :=
  { realTracePairLinear O with
    cont := (realTracePairLinear O).continuous_of_finiteDimensional }

@[simp]
theorem realTracePairCLM_apply (O ρ : QMatrix d) :
    realTracePairCLM O ρ = realTracePair O ρ := rfl

/-- A differentiable curve solving the concrete GKLS master equation. -/
def IsGKLSTrajectory {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (ρ : ℝ → QMatrix d) : Prop :=
  ∀ t, HasDerivAt ρ (gklsApply G J (ρ t)) t

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
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_smul]
  have h1 : Matrix.trace (O * (G * ρ)) = Matrix.trace ((O * G) * ρ) := by
    simp [Matrix.mul_assoc]
  have h2 : Matrix.trace (O * (ρ * G)) = Matrix.trace ((G * O) * ρ) := by
    calc
      Matrix.trace (O * (ρ * G)) = Matrix.trace ((O * ρ) * G) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (G * (O * ρ)) := Matrix.trace_mul_comm (O * ρ) G
      _ = Matrix.trace ((G * O) * ρ) := by simp [Matrix.mul_assoc]
  rw [h1, h2]
  module

/-- Trace duality for one Lindblad dissipator. -/
theorem trace_lindblad_duality
    (J O ρ : QMatrix d) :
    Matrix.trace (O * lindbladDissipator J ρ) =
      Matrix.trace (heisenbergDissipator J O * ρ) := by
  rw [lindbladDissipator, heisenbergDissipator]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul]
  have hsandwich :
      Matrix.trace (O * (J * ρ * Jᴴ)) =
        Matrix.trace ((Jᴴ * O * J) * ρ) := by
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
  module

/-- Exact Schrödinger--Heisenberg trace duality for the finite GKLS generator. -/
theorem trace_gkls_duality {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (O ρ : QMatrix d) :
    Matrix.trace (O * gklsApply G J ρ) =
      Matrix.trace (fullHeisenbergAdjoint G J O * ρ) := by
  rw [gklsApply, fullHeisenbergAdjoint]
  simp only [Matrix.mul_add, Matrix.trace_add]
  rw [trace_hamiltonian_duality]
  simp only [finiteDissipativeAdjoint, Matrix.add_mul, Matrix.trace_add,
    Finset.sum_mul, Matrix.trace_sum]
  apply congrArg (fun z => Matrix.trace (coherentAdjoint G O * ρ) + z)
  apply Finset.sum_congr rfl
  intro r hr
  exact trace_lindblad_duality (J r) O ρ

/-- Along an actual GKLS ODE trajectory, every observable expectation has derivative given by
the Heisenberg adjoint. -/
theorem realTracePair_hasDerivAt {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (hρ : IsGKLSTrajectory G J ρ) (O : QMatrix d) (t : ℝ) :
    HasDerivAt (fun s => realTracePair O (ρ s))
      (realTracePair (fullHeisenbergAdjoint G J O) (ρ t)) t := by
  have hcomp := (realTracePairCLM O).hasFDerivAt.comp t (hρ t).hasFDerivAt
  have hderiv :
      HasDerivAt (fun s => realTracePair O (ρ s))
        (realTracePair O (gklsApply G J (ρ t))) t := by
    simpa [realTracePairCLM_apply] using hcomp.hasDerivAt
  convert hderiv using 1
  unfold realTracePair
  rw [trace_gkls_duality]

/-- Positive matrices have nonnegative real trace pairing. -/
theorem realTracePair_nonneg_of_posSemidef
    {A ρ : QMatrix d} (hA : A.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ realTracePair A ρ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [hB]
  have hBA : (B * A * Bᴴ).PosSemidef := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      hA.conjTranspose_mul_mul_same Bᴴ
  have htrace : 0 ≤ Matrix.trace (B * A * Bᴴ) := hBA.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (B * A * Bᴴ)).re :=
    RCLike.nonneg_iff.mp htrace |>.1
  unfold realTracePair
  have hcycle :
      Matrix.trace (A * (Bᴴ * B)) = Matrix.trace (B * A * Bᴴ) := by
    calc
      Matrix.trace (A * (Bᴴ * B)) = Matrix.trace ((A * Bᴴ) * B) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (B * (A * Bᴴ)) := Matrix.trace_mul_comm (A * Bᴴ) B
      _ = Matrix.trace (B * A * Bᴴ) := by simp [Matrix.mul_assoc]
  rw [hcycle]
  exact hre

/-- A positive density trajectory pairs nonnegatively with every positive observable. -/
def IsPositiveTrajectory (ρ : ℝ → QMatrix d) : Prop :=
  ∀ t, (ρ t).PosSemidef

/-- If the Heisenberg derivative of `O` is positive semidefinite, its expectation is monotone
along every positive solution of the GKLS ODE. -/
theorem monotone_realTracePair_of_adjoint_posSemidef
    {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d} {O : QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hO : (fullHeisenbergAdjoint G J O).PosSemidef) :
    Monotone (fun t => realTracePair O (ρ t)) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun t => realTracePair_hasDerivAt htraj O t)
  intro t
  exact realTracePair_nonneg_of_posSemidef hO (hpos t)

/-- If the Heisenberg derivative of `O` is negative semidefinite, its expectation is antitone
along every positive solution of the GKLS ODE. -/
theorem antitone_realTracePair_of_adjoint_nonpos
    {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d} {O : QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hO : fullHeisenbergAdjoint G J O ≤ 0) :
    Antitone (fun t => realTracePair O (ρ t)) := by
  have hneg : (-fullHeisenbergAdjoint G J O).PosSemidef := by
    simpa [Matrix.nonneg_iff_posSemidef] using neg_nonneg.mpr hO
  apply antitone_of_hasDerivAt_nonpos
    (fun t => realTracePair_hasDerivAt htraj O t)
  intro t
  have hp := realTracePair_nonneg_of_posSemidef hneg (hpos t)
  have hlin : realTracePair (-fullHeisenbergAdjoint G J O) (ρ t) =
      -realTracePair (fullHeisenbergAdjoint G J O) (ρ t) := by
    simp [realTracePair]
  rw [hlin] at hp
  linarith

/-- For a dark target projector commuting with the coherent Hamiltonian, the target population is
monotone along the actual GKLS master equation.  Thus monotonicity is no longer a scalar
hypothesis. -/
theorem target_population_monotone {ι : Type*} [Fintype ι]
    {G P : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hP : P.PosSemidef)
    (hdark : ∀ r, J r * P = 0)
    (hcomm : G * P = P * G) :
    Monotone (fun t => realTracePair P (ρ t)) := by
  apply monotone_realTracePair_of_adjoint_posSemidef htraj hpos
  simpa [fullHeisenbergAdjoint] using fullAdjoint_target_posSemidef J hP hdark hcomm

end

end GapFreeLindblad
end FTDQE

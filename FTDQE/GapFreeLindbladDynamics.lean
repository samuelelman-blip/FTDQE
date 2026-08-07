import FTDQE.GapFreeLindbladDarkness
import FTDQE.GapFreeLindbladConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Order

namespace FTDQE
namespace GapFreeLindblad

open Matrix Function
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}

def realTracePair (O ρ : QMatrix d) : ℝ :=
  (Matrix.trace (O * ρ)).re

def realTracePairLinear (O : QMatrix d) : QMatrix d →ₗ[ℝ] ℝ where
  toFun := realTracePair O
  map_add' X Y := by simp [realTracePair, Matrix.mul_add]
  map_smul' r X := by simp [realTracePair, Complex.real_smul]

noncomputable def realTracePairCLM (O : QMatrix d) : QMatrix d →L[ℝ] ℝ :=
  { realTracePairLinear O with
    cont := (realTracePairLinear O).continuous_of_finiteDimensional }

@[simp]
theorem realTracePairCLM_apply (O ρ : QMatrix d) :
    realTracePairCLM O ρ = realTracePair O ρ := rfl

def IsGKLSTrajectory {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (ρ : ℝ → QMatrix d) : Prop :=
  ∀ t, HasDerivAt ρ (gklsApply G J (ρ t)) t

def fullHeisenbergAdjoint {ι : Type*} [Fintype ι]
    (G : QMatrix d) (J : ι → QMatrix d) (O : QMatrix d) : QMatrix d :=
  coherentAdjoint G O + finiteDissipativeAdjoint J O

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
      Matrix.trace (O * (ρ * G)) = Matrix.trace ((O * ρ) * G) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (G * (O * ρ)) := Matrix.trace_mul_comm (O * ρ) G
      _ = Matrix.trace ((G * O) * ρ) := by simp [Matrix.mul_assoc]
  rw [h1, h2]
  ring

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
      Matrix.trace (O * (J * ρ * Jᴴ)) = Matrix.trace ((O * J) * (ρ * Jᴴ)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * Jᴴ) * (O * J)) := Matrix.trace_mul_comm (O * J) (ρ * Jᴴ)
      _ = Matrix.trace (ρ * (Jᴴ * O * J)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Jᴴ * O * J) * ρ) := Matrix.trace_mul_comm ρ (Jᴴ * O * J)
  have hleft :
      Matrix.trace (O * ((Jᴴ * J) * ρ)) = Matrix.trace ((O * (Jᴴ * J)) * ρ) := by
    simp [Matrix.mul_assoc]
  have hright :
      Matrix.trace (O * (ρ * (Jᴴ * J))) = Matrix.trace (((Jᴴ * J) * O) * ρ) := by
    calc
      Matrix.trace (O * (ρ * (Jᴴ * J))) = Matrix.trace ((O * ρ) * (Jᴴ * J)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Jᴴ * J) * (O * ρ)) := Matrix.trace_mul_comm (O * ρ) (Jᴴ * J)
      _ = Matrix.trace (((Jᴴ * J) * O) * ρ) := by simp [Matrix.mul_assoc]
  rw [hsandwich, hleft, hright]
  ring

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

theorem realTracePair_hasDerivAt {ι : Type*} [Fintype ι]
    {G : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (hρ : IsGKLSTrajectory G J ρ) (O : QMatrix d) (t : ℝ) :
    HasDerivAt (fun s => realTracePair O (ρ s))
      (realTracePair (fullHeisenbergAdjoint G J O) (ρ t)) t := by
  have houter :
      HasFDerivAt (realTracePairCLM O) (realTracePairCLM O) (ρ t) :=
    (realTracePairCLM O).hasFDerivAt
  have hcomp :
      HasDerivAt ((realTracePairCLM O) ∘ ρ)
        (realTracePairCLM O (gklsApply G J (ρ t))) t :=
    houter.comp_hasDerivAt t (hρ t)
  have hderiv :
      HasDerivAt (fun s => realTracePair O (ρ s))
        (realTracePair O (gklsApply G J (ρ t))) t := by
    simpa [Function.comp_def] using hcomp
  convert hderiv using 1
  unfold realTracePair
  rw [trace_gkls_duality]

theorem realTracePair_nonneg_of_posSemidef
    {A ρ : QMatrix d} (hA : A.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ realTracePair A ρ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  have hB' : ρ = Bᴴ * B := by simpa only [star_eq_conjTranspose] using hB
  rw [hB']
  have hBA : (B * A * Bᴴ).PosSemidef := by
    simpa [Matrix.conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ
  have htrace : 0 ≤ Matrix.trace (B * A * Bᴴ) := hBA.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (B * A * Bᴴ)).re := RCLike.nonneg_iff.mp htrace |>.1
  unfold realTracePair
  have hcycle : Matrix.trace (A * (Bᴴ * B)) = Matrix.trace (B * A * Bᴴ) := by
    calc
      Matrix.trace (A * (Bᴴ * B)) = Matrix.trace ((A * Bᴴ) * B) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (B * (A * Bᴴ)) := Matrix.trace_mul_comm (A * Bᴴ) B
      _ = Matrix.trace (B * A * Bᴴ) := by simp [Matrix.mul_assoc]
  rw [hcycle]
  exact hre

def IsPositiveTrajectory (ρ : ℝ → QMatrix d) : Prop :=
  ∀ t, (ρ t).PosSemidef

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
    simpa [realTracePair] using hp
  exact neg_nonneg.mp hp'

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

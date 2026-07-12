import FTDQE.QuantumMatrix

/-!
# Matrix-generator preservation properties

This file records the concrete preservation hypotheses used for finite-
dimensional Lindbladian generators and their perturbations.
-/

namespace FTDQE

open Matrix

variable {d : ℕ}

/-- A real-linear matrix map preserves Hermiticity. -/
def HermiticityPreserving (T : QMatrix d →L[ℝ] QMatrix d) : Prop :=
  ∀ X : QMatrix d, X.IsHermitian → (T X).IsHermitian

/-- A generator annihilates the trace. -/
def TraceAnnihilating (T : QMatrix d →L[ℝ] QMatrix d) : Prop :=
  ∀ X : QMatrix d, Matrix.trace (T X) = 0

/-- A map preserves the traceless Hermitian subspace. -/
def PreservesTracelessHermitian (T : QMatrix d →L[ℝ] QMatrix d) : Prop :=
  ∀ X : QMatrix d, IsTracelessHermitian X → IsTracelessHermitian (T X)

 theorem preservesTracelessHermitian_of_properties
    {T : QMatrix d →L[ℝ] QMatrix d}
    (hH : HermiticityPreserving T) (htr : TraceAnnihilating T) :
    PreservesTracelessHermitian T := by
  intro X hX
  exact ⟨hH X hX.1, htr X⟩

 theorem hermiticityPreserving_sub
    {L L' : QMatrix d →L[ℝ] QMatrix d}
    (hL : HermiticityPreserving L) (hL' : HermiticityPreserving L') :
    HermiticityPreserving (L' - L) := by
  intro X hX
  simpa using (hL' X hX).sub (hL X hX)

 theorem traceAnnihilating_sub
    {L L' : QMatrix d →L[ℝ] QMatrix d}
    (hL : TraceAnnihilating L) (hL' : TraceAnnihilating L') :
    TraceAnnihilating (L' - L) := by
  intro X
  simp [hL X, hL' X]

/-- The difference of two Hermiticity-preserving, trace-annihilating generators
preserves the traceless Hermitian subspace. -/
theorem perturbation_preserves_tracelessHermitian
    {L L' : QMatrix d →L[ℝ] QMatrix d}
    (hLH : HermiticityPreserving L) (hLtr : TraceAnnihilating L)
    (hL'H : HermiticityPreserving L') (hL'tr : TraceAnnihilating L') :
    PreservesTracelessHermitian (L' - L) :=
  preservesTracelessHermitian_of_properties
    (hermiticityPreserving_sub hLH hL'H)
    (traceAnnihilating_sub hLtr hL'tr)

end FTDQE

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-dimensional quantum matrices

Concrete matrix space and the traceless Hermitian predicate used in Lemma 2.
-/

namespace FTDQE

open Matrix

/-- Complex `d × d` matrices. -/
abbrev QMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- The real invariant subspace relevant for mixing of density-matrix differences. -/
def IsTracelessHermitian {d : ℕ} (X : QMatrix d) : Prop :=
  X.IsHermitian ∧ Matrix.trace X = 0

@[simp] theorem isTracelessHermitian_zero (d : ℕ) :
    IsTracelessHermitian (0 : QMatrix d) := by
  constructor
  · exact Matrix.isHermitian_zero
  · simp [IsTracelessHermitian]

 theorem IsTracelessHermitian.add {d : ℕ} {X Y : QMatrix d}
    (hX : IsTracelessHermitian X) (hY : IsTracelessHermitian Y) :
    IsTracelessHermitian (X + Y) := by
  constructor
  · exact hX.1.add hY.1
  · simp [hX.2, hY.2]

 theorem IsTracelessHermitian.neg {d : ℕ} {X : QMatrix d}
    (hX : IsTracelessHermitian X) : IsTracelessHermitian (-X) := by
  constructor
  · exact hX.1.neg
  · simp [hX.2]

 theorem IsTracelessHermitian.sub {d : ℕ} {X Y : QMatrix d}
    (hX : IsTracelessHermitian X) (hY : IsTracelessHermitian Y) :
    IsTracelessHermitian (X - Y) := by
  constructor
  · exact hX.1.sub hY.1
  · simp [hX.2, hY.2]

end FTDQE

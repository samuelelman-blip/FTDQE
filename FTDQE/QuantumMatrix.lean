import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-dimensional quantum matrices

This file fixes the concrete matrix space used for the quantum instantiation of
Lemma 2 and records the elementary algebra of the traceless Hermitian subspace.
-/

namespace FTDQE

open Matrix

/-- Complex `d × d` matrices, regarded as
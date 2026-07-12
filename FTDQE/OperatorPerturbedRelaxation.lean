import FTDQE.OperatorDuhamel
import FTDQE.PerturbedRelaxation

/-!
# Operator-norm perturbed relaxation

This file combines the Banach-algebra Duhamel identity with the scalar
Duhamel--Grönwall theorem. It gives both a full operator-norm statement and the
pointwise invariant-subspace statement needed for Lemma 2.
-/

namespace FTDQE

open Set intervalIntegral
open NormedSpace

/
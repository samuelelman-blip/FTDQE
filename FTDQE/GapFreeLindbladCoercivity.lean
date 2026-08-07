import FTDQE.GapFreeLindbladDynamicConvergence

/-!
# Operator coercivity constant

The manuscript defines `κ_m(ε)` as the minimum eigenvalue of the Lyapunov operator
`K_m` restricted to the above-threshold subspace.  Once target darkness has made `K_m`
block diagonal with respect to the target/complement decomposition, this is equivalently the
largest real scalar `κ` for which the Loewner inequality `κ P_> ≤ K_m` holds.

This file formalizes that equivalent operator characterization and wires it directly into the
GKLS `1/t` theorem.  Thus the runtime theorem no longer accepts an unrelated scalar `κ`: it
accepts a coercivity constant certified to be the greatest Loewner lower bound for the actual
pair `(K_m,P_>)`.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set intervalIntegral
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {d : ℕ}

/-- `κ` is the operator coercivity constant of `K` on the positive target-complement
operator `P` when it is the greatest scalar satisfying `κ P ≤ K` in Loewner order.

For an orthogonal projector `P=P_>` and a Hermitian `K` annihilating the complementary
subspace, finite-dimensional spectral theory identifies this greatest scalar with
`λ_min(K|_{Ran P_>})`, which is the manuscript definition of `κ_m(ε)`. -/
def IsKappaM (K P : QMatrix d) (κ : ℝ) : Prop :=
  IsGreatest {μ : ℝ | ((μ : ℂ) • P) ≤ K} κ

/-- The defining operator inequality supplied by `κ_m`. -/
theorem IsKappaM.coercivity
    {K P : QMatrix d} {κ : ℝ}
    (hκm : IsKappaM K P κ) :
    ((κ : ℂ) • P) ≤ K :=
  hκm.1

/-- Maximality of the operator coercivity constant. -/
theorem IsKappaM.maximal
    {K P : QMatrix d} {κ μ : ℝ}
    (hκm : IsKappaM K P κ)
    (hμ : ((μ : ℂ) • P) ≤ K) :
    μ ≤ κ :=
  hκm.2 hμ

/-- The operator coercivity constant, if it exists, is unique. -/
theorem IsKappaM.unique
    {K P : QMatrix d} {κ κ' : ℝ}
    (hκ : IsKappaM K P κ)
    (hκ' : IsKappaM K P κ') :
    κ = κ' := by
  exact le_antisymm (hκ'.maximal hκ.coercivity) (hκ.maximal hκ'.coercivity)

/-- Pointwise trace coercivity using the actual operator coercivity constant. -/
theorem realTracePair_kappaM
    {K P ρ : QMatrix d} {κm : ℝ}
    (hκm : IsKappaM K P κm)
    (hρ : ρ.PosSemidef) :
    κm * realTracePair P ρ ≤ realTracePair K ρ :=
  realTracePair_coercivity hκm.coercivity hρ

/-- Dynamical `1/t` theorem with the manuscript coercivity constant wired into the
operator statement.

Compared with `gapFree_one_over_t_of_gkls`, the scalar rate is no longer accompanied by an
independent coercivity hypothesis.  `hκm : IsKappaM K P κm` says precisely that `κm` is the
greatest Loewner lower bound of the actual Lyapunov operator `K` on `P`.
-/
theorem gapFree_one_over_t_of_gkls_kappaM
    {ι : Type*} [Fintype ι]
    {G H P K : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    {κm W Emin t : ℝ}
    (hκm_pos : 0 < κm) (ht : 0 < t)
    (hκm : IsKappaM K P κm)
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hP : P.PosSemidef)
    (hPadj : fullHeisenbergAdjoint G J P ≤ 0)
    (hHadj : fullHeisenbergAdjoint G J H = -K)
    (hfloor : Emin ≤ realTracePair H (ρ t))
    (hwidth : realTracePair H (ρ 0) - Emin ≤ W) :
    realTracePair P (ρ t) ≤ W / (κm * t) := by
  exact gapFree_one_over_t_of_gkls hκm_pos ht htraj hpos hP hPadj
    hκm.coercivity hHadj hfloor hwidth

end

end GapFreeLindblad
end FTDQE

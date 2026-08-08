import FTDQE.GapFreeLindbladAdmissibleTail

/-!
# Closed public theorem for arbitrary admissible weights

This file exposes the arbitrary-weight construction using only the manuscript-level
admissibility assumptions.  The boundary decay and derivative-weighted integrability
needed by the internal integration-by-parts proof are derived, not assumed.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology Interval

noncomputable section

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-- Package the two derived tail facts into the internal integration-by-parts record. -/
def AdmissibleWeight.toData
    {ε : ℝ} {m : ℝ → ℝ} (hm : AdmissibleWeight ε m) :
    AdmissibleWeightData ε m where
  eps_pos := hm.eps_pos
  nonneg := hm.nonneg
  localAC := hm.localAC
  deriv_nonneg := hm.deriv_nonneg
  weighted_integrable := hm.weighted_integrable
  boundary_decay := hm.boundary_decay
  deriv_integrable := hm.deriv_integrable

/-- The Kossakowski kernel for every public admissible weight is positive semidefinite. -/
theorem admissibleWeight_kernelMatrix_posSemidef
    {ε : ℝ} {m : ℝ → ℝ} {ω : ι → ℝ}
    (hm : AdmissibleWeight ε m) (hdown : ∀ i, ω i ≤ -ε) :
    (admissibleKernelMatrix m ω).PosSemidef := by
  change (laplaceGramMatrix m ω).PosSemidef
  apply laplaceGramMatrix_posSemidef
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hm.nonneg s hs.le
  · intro i j
    apply admissible_kernel_integrable hm.toData
    linarith [hdown i, hdown j]

/-- Hence every public admissible weight has an ordinary finite GKLS jump representation. -/
theorem admissibleWeight_exists_GKLS_jumps
    {ε : ℝ} {m : ℝ → ℝ} (ω : ι → ℝ) (A : ι → QMatrix d)
    (hm : AdmissibleWeight ε m) (hdown : ∀ i, ω i ≤ -ε) :
    ∃ J : ι → QMatrix d, ∀ ρ,
      correlatedDissipator (admissibleKernelMatrix m ω) A ρ =
        ∑ r, lindbladDissipator (J r) ρ :=
  exists_jumps_of_kossakowski_posSemidef
    (admissibleKernelMatrix m ω) A
    (admissibleWeight_kernelMatrix_posSemidef hm hdown)

/-- Public scalar integration-by-parts identity. -/
theorem admissibleWeight_scalar_drift_identity
    {ε lam : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleWeight ε m) (hlam : lam ≤ -2 * ε) :
    -(admissibleScalarKernel m lam) * (lam / 2) =
      admissibleScalarDriftKernel m lam :=
  admissible_scalar_drift_identity hm.toData hlam

/-- The public arbitrary-weight drift kernel is positive semidefinite. -/
theorem admissibleWeight_driftKernelMatrix_posSemidef
    {ε : ℝ} {m : ℝ → ℝ} {ω : ι → ℝ}
    (hm : AdmissibleWeight ε m) (hdown : ∀ i, ω i ≤ -ε) :
    (admissibleDriftKernelMatrix m ω).PosSemidef :=
  admissibleDriftKernelMatrix_posSemidef hm.toData hdown

/-- Exact public arbitrary-weight Lyapunov identity. -/
theorem admissibleWeight_correlatedAdjoint_energy
    {H : QMatrix d} {ε : ℝ} {m : ℝ → ℝ} {ω : ι → ℝ} {A : ι → QMatrix d}
    (hm : AdmissibleWeight ε m)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε) :
    correlatedAdjoint (fun i j => admissibleKernelMatrix m ω i j) A H =
      -kernelGramOperator (admissibleDriftKernelMatrix m ω) A :=
  admissibleKernel_correlatedAdjoint_energy hm.toData hH hA hdown

/-- Closed arbitrary-admissible-weight energy monotonicity theorem. -/
theorem admissibleWeight_correlatedAdjoint_energy_nonpos
    {H : QMatrix d} {ε : ℝ} {m : ℝ → ℝ} {ω : ι → ℝ} {A : ι → QMatrix d}
    (hm : AdmissibleWeight ε m)
    (hH : H.IsHermitian)
    (hA : ∀ i, IsBohrComponent H (A i) (ω i))
    (hdown : ∀ i, ω i ≤ -ε) :
    correlatedAdjoint (fun i j => admissibleKernelMatrix m ω i j) A H ≤ 0 :=
  admissibleKernel_correlatedAdjoint_energy_nonpos hm.toData hH hA hdown

end

end GapFreeLindblad
end FTDQE

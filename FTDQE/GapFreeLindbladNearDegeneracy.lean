import FTDQE.GapFreeLindbladM1

/-!
# Near-degenerate frequency scaling

Exact scalar identity behind manuscript Eq. (43): for two downward frequencies
`-Ω` and `-(Ω+δ)`, the determinant of the `m₁` drift matrix is proportional to `δ²`.
This makes explicit that no separation is assumed even though the achieved coercivity can
vanish continuously as frequencies coalesce.
-/

namespace FTDQE
namespace GapFreeLindblad

noncomputable section

/-- Entries of the two-frequency `m₁` drift matrix, without the common factor
`2 γ ε²`. -/
def nearDegA (Ω : ℝ) : ℝ := 1 / (2 * Ω)
def nearDegB (Ω δ : ℝ) : ℝ := 1 / (2 * Ω + δ)
def nearDegD (Ω δ : ℝ) : ℝ := 1 / (2 * Ω + 2 * δ)

/-- Exact Cauchy determinant identity. -/
theorem nearDeg_cauchy_det
    {Ω δ : ℝ}
    (hΩ : Ω ≠ 0) (hΩδ : Ω + δ ≠ 0) (hmid : 2 * Ω + δ ≠ 0) :
    nearDegA Ω * nearDegD Ω δ - nearDegB Ω δ ^ 2 =
      δ ^ 2 / (4 * Ω * (Ω + δ) * (2 * Ω + δ) ^ 2) := by
  simp [nearDegA, nearDegB, nearDegD]
  field_simp
  ring

/-- Including the common factor `2 γ ε²` reproduces the manuscript determinant exactly. -/
theorem nearDeg_m1_det
    {γ ε Ω δ : ℝ}
    (hΩ : Ω ≠ 0) (hΩδ : Ω + δ ≠ 0) (hmid : 2 * Ω + δ ≠ 0) :
    (2 * γ * ε^2 * nearDegA Ω) * (2 * γ * ε^2 * nearDegD Ω δ) -
      (2 * γ * ε^2 * nearDegB Ω δ) ^ 2 =
      γ^2 * ε^4 * δ^2 /
        (Ω * (Ω + δ) * (2 * Ω + δ)^2) := by
  rw [show
    (2 * γ * ε^2 * nearDegA Ω) * (2 * γ * ε^2 * nearDegD Ω δ) -
        (2 * γ * ε^2 * nearDegB Ω δ) ^ 2 =
      (2 * γ * ε^2)^2 *
        (nearDegA Ω * nearDegD Ω δ - nearDegB Ω δ ^ 2) by ring]
  rw [nearDeg_cauchy_det hΩ hΩδ hmid]
  field_simp
  ring

end

end GapFreeLindblad
end FTDQE

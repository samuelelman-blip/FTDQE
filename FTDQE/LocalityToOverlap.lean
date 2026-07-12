import FTDQE.LiebRobinsonTruncation
import FTDQE.GroundStateOverlap

/-!
# From local jump truncation to ground-state overlap

This file closes the main dependency chain in Theorem 2:

1. Theorem 1 bounds each truncated jump error by a common
   stretched-exponential spatial profile.
2. Proposition 1 converts the finite family of jump errors into a generator
   perturbation bound with the factor `4`.
3. A radius condition makes that perturbation at most
   `rate * ε / (2 * κ)`.
4. Theorem 2 then gives existence, uniqueness, trace-distance control, and
   ground-state overlap.

For a family of `n` jumps, the resulting generator estimate is

`η ≤ 4 n C exp(-c r^β')`.
-/

namespace FTDQE

noncomputable section

/--
Theorem 1 plus Proposition 1 for a finite family of jumps.

Every jump uses the same Lieb–Robinson/Gevrey constants, so summing over the
finite index type produces the manuscript's linear factor in the number of
jumps.
-/
theorem finite_family_generator_locality
    {ι : Type*} [Fintype ι]
    (jumpError : ι → ℝ → ℝ)
    (dissipatorError : ι → ℝ)
    (η diamondError : ℝ)
    (C₁ C₂ μ v g β C c r : ℝ)
    (hv : 0 < v)
    (hr : 0 ≤ r)
    (hjump : ∀ i, 0 ≤ jumpError i r)
    (hperJump : ∀ i, dissipatorError i ≤ 4 * jumpError i r)
    (hinducedDiamond : η ≤ diamondError)
    (hdiamondSum : diamondError ≤ ∑ i, dissipatorError i)
    (split : ∀ i,
      LRJumpSplitCertificate (jumpError i) C₁ C₂ μ v g β)
    (envelope :
      LRStretchedEnvelopeCertificate C₁ C₂ μ v g β C c) :
    η ≤
      4 * (Fintype.card ι : ℝ) * C *
        lrDecay c (lrBetaPrime β) r := by
  have hgenerator : η ≤ 4 * ∑ i, jumpError i r :=
    generator_perturbation_bound
      (fun i => jumpError i r) dissipatorError η diamondError
      hjump hperJump hinducedDiamond hdiamondSum
  have hper : ∀ i,
      jumpError i r ≤ C * lrDecay c (lrBetaPrime β) r := by
    intro i
    exact lieb_robinson_jump_truncation
      (jumpError i) C₁ C₂ μ v g β C c hv (split i) envelope r hr
  have hsum :
      (∑ i, jumpError i r) ≤
        ∑ _i : ι, C * lrDecay c (lrBetaPrime β) r := by
    exact Finset.sum_le_sum fun i _ => hper i
  calc
    η ≤ 4 * ∑ i, jumpError i r := hgenerator
    _ ≤ 4 * ∑ _i : ι, C * lrDecay c (lrBetaPrime β) r :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * (Fintype.card ι : ℝ) * C *
          lrDecay c (lrBetaPrime β) r := by
      simp
      ring

/--
End-to-end certificate form of Theorem 2.

The hypothesis `hradius` is the explicit finite-constant version of the radius
choice in Eq. (25):

`4 n C exp(-c r^β') ≤ rate * ε / (2κ)`.

All remaining hypotheses are exactly the certificate interfaces supplied by
Theorem 1, Proposition 1, and Lemma 3.
-/
theorem ground_state_overlap_from_locality
    {ι X : Type*}
    [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L' : X →L[ℝ] X)
    (stateSpace : Set X)
    (σ : X)
    (overlap : X → ℝ)
    (jumpError : ι → ℝ → ℝ)
    (dissipatorError : ι → ℝ)
    (η diamondError : ℝ)
    (ε κ rate C₁ C₂ μ v g β C c r : ℝ)
    (hκ : 0 < κ)
    (hrate : 0 < rate)
    (hε0 : 0 < ε)
    (hε1 : ε ≤ 1)
    (hv : 0 < v)
    (hr : 0 ≤ r)
    (hjump : ∀ i, 0 ≤ jumpError i r)
    (hperJump : ∀ i, dissipatorError i ≤ 4 * jumpError i r)
    (hinducedDiamond : η ≤ diamondError)
    (hdiamondSum : diamondError ≤ ∑ i, dissipatorError i)
    (split : ∀ i,
      LRJumpSplitCertificate (jumpError i) C₁ C₂ μ v g β)
    (envelope :
      LRStretchedEnvelopeCertificate C₁ C₂ μ v g β C c)
    (hradius :
      4 * (Fintype.card ι : ℝ) * C *
          lrDecay c (lrBetaPrime β) r ≤
        rate * ε / (2 * κ))
    (hlemma3 :
      ∃ σR ∈ stateSpace,
        IsStationary L' σR ∧
        ‖σR - σ‖ ≤ κ * η / rate ∧
        (0 < rate - κ * η →
          ∀ τ ∈ stateSpace, IsStationary L' τ → τ = σR))
    (hoverlap : ∀ x ∈ stateSpace,
      1 - overlap x ≤ ‖x - σ‖) :
    ∃ σR ∈ stateSpace,
      IsStationary L' σR ∧
      ‖σR - σ‖ ≤ ε / 2 ∧
      1 - ε / 2 ≤ overlap σR ∧
      (∀ τ ∈ stateSpace, IsStationary L' τ → τ = σR) := by
  have hlocal :
      η ≤ 4 * (Fintype.card ι : ℝ) * C *
        lrDecay c (lrBetaPrime β) r :=
    finite_family_generator_locality
      jumpError dissipatorError η diamondError
      C₁ C₂ μ v g β C c r hv hr
      hjump hperJump hinducedDiamond hdiamondSum split envelope
  have hη : η ≤ rate * ε / (2 * κ) := hlocal.trans hradius
  exact ground_state_overlap_of_lemma3
    L' stateSpace σ overlap ε κ rate η
    hκ hrate hε0 hε1 hη hlemma3 hoverlap

end

end FTDQE

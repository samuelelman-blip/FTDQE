/-
Copyright (c) 2026 Samuel J. Elman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel J. Elman
-/
import FTDQE.RefreshRecursion

/-!
# Minibatched global refresh

This file formalises Lemma 6 and Eqs. (39), (43), and (46) of the revised
manuscript.  The probabilistic channel argument enters only through the
one-period scalar recurrence; all geometric iteration and contraction-floor
estimates are proved here.
-/

namespace FTDQE

/--
General affine geometric recursion used in Lemma 6.  If
`d_{k+1} ≤ q (d_k + c)` with `0 ≤ q < 1`, then Eq. (39) holds.
-/
theorem minibatch_refresh_geometric_bound
    (d : ℕ → ℝ) (q c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ k, d (k + 1) ≤ q * (d k + c)) :
    ∀ k,
      d k ≤ q ^ k * d 0 +
        q * (1 - q ^ k) / (1 - q) * c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hdenpos : 0 < 1 - q := sub_pos.mpr hq1
      have hsum :
          d k + c ≤
            q ^ k * d 0 +
              q * (1 - q ^ k) / (1 - q) * c + c := by
        exact add_le_add ih (le_refl c)
      have hmono :
          q * (d k + c) ≤
            q *
              (q ^ k * d 0 +
                q * (1 - q ^ k) / (1 - q) * c + c) :=
        mul_le_mul_of_nonneg_left hsum hq0
      calc
        d (k + 1) ≤ q * (d k + c) := hrec k
        _ ≤ q *
              (q ^ k * d 0 +
                q * (1 - q ^ k) / (1 - q) * c + c) := hmono
        _ = q ^ (k + 1) * d 0 +
              q * (1 - q ^ (k + 1)) / (1 - q) * c := by
          rw [pow_succ]
          field_simp [hdenpos.ne']
          <;> ring

/--
Lemma 6 in scalar certificate form.  The first hypothesis is the conditional
expectation estimate from the sampled channel construction; the conclusion is
the finite-period bound of Eq. (39).
-/
theorem minibatched_global_refresh
    (expectedDistance : ℕ → ℝ) (q_b c : ℝ)
    (hq0 : 0 ≤ q_b) (hq1 : q_b < 1)
    (honePeriod : ∀ k,
      expectedDistance (k + 1) ≤
        q_b * (expectedDistance k + c)) :
    ∀ k,
      expectedDistance k ≤
        q_b ^ k * expectedDistance 0 +
          q_b * (1 - q_b ^ k) / (1 - q_b) * c := by
  exact minibatch_refresh_geometric_bound
    expectedDistance q_b c hq0 hq1 honePeriod

/--
When `q_b ≤ 1/2`, the minibatch recursion is dominated by the deterministic
half-contraction recursion of Lemma 5.
-/
theorem minibatch_refresh_half_bound
    (d : ℕ → ℝ) (q_b c : ℝ)
    (_hq0 : 0 ≤ q_b) (hqhalf : q_b ≤ 1 / 2)
    (hc : 0 ≤ c) (hd : ∀ k, 0 ≤ d k)
    (hrec : ∀ k, d (k + 1) ≤ q_b * (d k + c)) :
    ∀ k, d k ≤ d 0 / (2 : ℝ) ^ k + c := by
  have hhalfrec : ∀ k, 2 * d (k + 1) ≤ d k + c := by
    intro k
    have hsum : 0 ≤ d k + c := add_nonneg (hd k) hc
    have hqmul : q_b * (d k + c) ≤ (1 / 2 : ℝ) * (d k + c) :=
      mul_le_mul_of_nonneg_right hqhalf hsum
    have hstep := hrec k
    nlinarith
  exact contraction_bound_real_div d c hc hhalfrec

/--
Finite form of the `limsup ≤ c` conclusion in Lemma 6: once the geometric
transient is at most `ε`, the distance is at most `c + ε`.
-/
theorem minibatch_refresh_eventual_floor
    (d : ℕ → ℝ) (q_b c ε : ℝ) (k : ℕ)
    (hq0 : 0 ≤ q_b) (hqhalf : q_b ≤ 1 / 2)
    (hc : 0 ≤ c) (hd : ∀ j, 0 ≤ d j)
    (hrec : ∀ j, d (j + 1) ≤ q_b * (d j + c))
    (htransient : d 0 / (2 : ℝ) ^ k ≤ ε) :
    d k ≤ c + ε := by
  have hbound := minibatch_refresh_half_bound
    d q_b c hq0 hqhalf hc hd hrec k
  linarith

/--
Eq. (46): a uniform one-microstep contraction gap compounds
multiplicatively across a minibatch.
-/
theorem iterated_microstep_contraction
    (q : ℕ → ℝ) (γ : ℝ)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hq0 : q 0 ≤ 1)
    (hstep : ∀ b, q (b + 1) ≤ (1 - γ) * q b) :
    ∀ b, q b ≤ (1 - γ) ^ b := by
  intro b
  induction b with
  | zero => simpa using hq0
  | succ b ih =>
      calc
        q (b + 1) ≤ (1 - γ) * q b := hstep b
        _ ≤ (1 - γ) * (1 - γ) ^ b :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγ1)
        _ = (1 - γ) ^ (b + 1) := by
          rw [pow_succ]
          ring

/-- Any certified batch size whose geometric factor is at most `1/2` gives the
contraction threshold required by Lemma 6. -/
theorem microstep_gap_gives_half_contraction
    (q : ℕ → ℝ) (γ : ℝ) (b : ℕ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hq0 : q 0 ≤ 1)
    (hstep : ∀ j, q (j + 1) ≤ (1 - γ) * q j)
    (hbatch : (1 - γ) ^ b ≤ 1 / 2) :
    q b ≤ 1 / 2 := by
  exact (iterated_microstep_contraction
    q γ hγ0 hγ1 hq0 hstep b).trans hbatch

end FTDQE

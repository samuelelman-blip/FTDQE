import Mathlib

/-!
# Periodic global-refresh recursion

Arithmetic core of Lemma 5. The analytic channel estimates enter through
`hrec`; this file proves the geometric recursion and residual drift floor.
-/

namespace FTDQE

/-- `pow2 k = 2^k`, retained in the natural-number proof to match the original
core-Lean ancillary formalisation. -/
def pow2 : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * pow2 k

theorem pow2_pos : ∀ k, 0 < pow2 k
  | 0 => Nat.one_pos
  | k + 1 => by
      have ih := pow2_pos k
      simp only [pow2]
      omega

private theorem mul_two_shift (a b : ℕ) : a * (2 * b) = 2 * (a * b) := by
  calc
    a * (2 * b) = (a * 2) * b := (Nat.mul_assoc a 2 b).symm
    _ = (2 * a) * b := by rw [Nat.mul_comm a 2]
    _ = 2 * (a * b) := Nat.mul_assoc 2 a b

/-- Grid-valued version of the one-period contraction bound. -/
theorem contraction_bound_nat (d : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ k, 2 * d (k + 1) ≤ d k + c) :
    ∀ k, pow2 k * d k + c ≤ d 0 + pow2 k * c := by
  intro k
  induction k with
  | zero =>
      simp only [pow2, Nat.one_mul]
      omega
  | succ k ih =>
      have h1 : pow2 k * (2 * d (k + 1)) ≤ pow2 k * (d k + c) :=
        Nat.mul_le_mul_left _ (hrec k)
      have h2 : pow2 k * (2 * d (k + 1)) =
          2 * (pow2 k * d (k + 1)) :=
        mul_two_shift _ _
      have h3 : pow2 k * (d k + c) = pow2 k * d k + pow2 k * c :=
        Nat.mul_add _ _ _
      have h4 : pow2 (k + 1) * d (k + 1) =
          2 * (pow2 k * d (k + 1)) := by
        show 2 * pow2 k * d (k + 1) = 2 * (pow2 k * d (k + 1))
        exact Nat.mul_assoc 2 (pow2 k) (d (k + 1))
      have h5 : pow2 (k + 1) * c = 2 * (pow2 k * c) := by
        show 2 * pow2 k * c = 2 * (pow2 k * c)
        exact Nat.mul_assoc 2 (pow2 k) c
      omega

/-- Once `2^k` exceeds the initial grid-valued distance, the sequence is at
most the drift floor. -/
theorem reaches_floor_nat (d : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ k, 2 * d (k + 1) ≤ d k + c) {k : ℕ}
    (hk : d 0 < pow2 k) :
    d k ≤ c := by
  have h := contraction_bound_nat d c hrec k
  have hp := pow2_pos k
  have h6 : pow2 k * (1 + c) = pow2 k + pow2 k * c := by
    rw [Nat.mul_add, Nat.mul_one]
  have h7 : pow2 k * d k < pow2 k * (1 + c) := by omega
  have h8 : d k < 1 + c := Nat.lt_of_mul_lt_mul_left h7
  omega

/-- Real-valued form matching Eq. (31):

`2^k d_k ≤ d_0 + (2^k - 1)c`.
-/
theorem contraction_bound_real (d : ℕ → ℝ) (c : ℝ)
    (hrec : ∀ k, 2 * d (k + 1) ≤ d k + c) :
    ∀ k, (2 : ℝ) ^ k * d k ≤ d 0 + ((2 : ℝ) ^ k - 1) * c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) k
      have hstep := mul_le_mul_of_nonneg_left (hrec k) hpow
      rw [pow_succ]
      nlinarith

/-- The manuscript's convenient weaker form
`d_k ≤ 2^{-k} d_0 + c`, assuming a nonnegative drift floor. -/
theorem contraction_bound_real_div (d : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hrec : ∀ k, 2 * d (k + 1) ≤ d k + c) (k : ℕ) :
    d k ≤ d 0 / (2 : ℝ) ^ k + c := by
  have h := contraction_bound_real d c hrec k
  have hp : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hmul :
      d k * (2 : ℝ) ^ k ≤
        (d 0 / (2 : ℝ) ^ k + c) * (2 : ℝ) ^ k := by
    calc
      d k * (2 : ℝ) ^ k = (2 : ℝ) ^ k * d k := by ring
      _ ≤ d 0 + ((2 : ℝ) ^ k - 1) * c := h
      _ ≤ d 0 + (2 : ℝ) ^ k * c := by nlinarith
      _ = (d 0 / (2 : ℝ) ^ k + c) * (2 : ℝ) ^ k := by
        field_simp [ne_of_gt hp]
  exact (mul_le_mul_iff_right₀ hp).mp (by simpa [mul_comm] using hmul)

end FTDQE

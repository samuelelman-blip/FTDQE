import FTDQE.GroundStateOverlap
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A priori stopping rule

This file adds the scalar and compositional part of Lemma 4(a) from the revised
manuscript.  The operator relaxation estimate is supplied by Lemma 2; the
proof here verifies the explicit stopping time and combines the transient and
stationary-state errors.
-/

namespace FTDQE

noncomputable section

/-- The stopping time appearing in Eq. (27). -/
def stoppingTime (κ rate ε : ℝ) : ℝ :=
  (2 / rate) * Real.log (4 * κ / ε)

/-- The stopping time is nonnegative under the manuscript assumptions. -/
theorem stoppingTime_nonneg
    (κ rate ε : ℝ)
    (hκ : 1 ≤ κ) (hrate : 0 < rate)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ stoppingTime κ rate ε := by
  have hratio : 1 ≤ 4 * κ / ε := by
    apply (le_div_iff₀ hε0).2
    nlinarith
  exact mul_nonneg
    (div_nonneg (by norm_num) hrate.le)
    (Real.log_nonneg hratio)

/--
At the stopping time of Eq. (27), a transient bounded by
`2 κ exp (-(rate - κ η)t)` is at most `ε / 2` whenever
`κ η ≤ rate / 2`.
-/
theorem stoppingTime_exponential_bound
    (κ rate η ε : ℝ)
    (hκ : 1 ≤ κ) (hrate : 0 < rate)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : κ * η ≤ rate / 2) :
    2 * κ * Real.exp
        (-(rate - κ * η) * stoppingTime κ rate ε) ≤ ε / 2 := by
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have ht : 0 ≤ stoppingTime κ rate ε :=
    stoppingTime_nonneg κ rate ε hκ hrate hε0 hε1
  have hdecay : rate / 2 ≤ rate - κ * η := by
    linarith
  have hmul_pos :
      (rate / 2) * stoppingTime κ rate ε ≤
        (rate - κ * η) * stoppingTime κ rate ε :=
    mul_le_mul_of_nonneg_right hdecay ht
  have hmul :
      -(rate - κ * η) * stoppingTime κ rate ε ≤
        -(rate / 2) * stoppingTime κ rate ε := by
    nlinarith
  have heq :
      -(rate / 2) * stoppingTime κ rate ε =
        -Real.log (4 * κ / ε) := by
    dsimp [stoppingTime]
    field_simp [hrate.ne']
    <;> ring
  have harg :
      -(rate - κ * η) * stoppingTime κ rate ε ≤
        -Real.log (4 * κ / ε) := by
    calc
      -(rate - κ * η) * stoppingTime κ rate ε ≤
          -(rate / 2) * stoppingTime κ rate ε := hmul
      _ = -Real.log (4 * κ / ε) := heq
  have hratio_pos : 0 < 4 * κ / ε :=
    div_pos (mul_pos (by norm_num) hκ0) hε0
  have hexp_eq :
      Real.exp (-Real.log (4 * κ / ε)) = ε / (4 * κ) := by
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    field_simp [hκ0.ne', hε0.ne']
    <;> ring
  have hexp :
      Real.exp (-(rate - κ * η) * stoppingTime κ rate ε) ≤
        ε / (4 * κ) := by
    calc
      Real.exp (-(rate - κ * η) * stoppingTime κ rate ε) ≤
          Real.exp (-Real.log (4 * κ / ε)) :=
        Real.exp_le_exp.mpr harg
      _ = ε / (4 * κ) := hexp_eq
  calc
    2 * κ * Real.exp
        (-(rate - κ * η) * stoppingTime κ rate ε) ≤
      2 * κ * (ε / (4 * κ)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (by norm_num) hκ0.le)
    _ = ε / 2 := by
      field_simp [hκ0.ne']
      <;> ring

/--
Lemma 4(a) in scalar certificate form.  Lemma 2 supplies `htransient`, while
Theorem 2 supplies `hstationary`.  The triangle inequality then gives total
trace distance at most `ε` at the explicit stopping time.
-/
theorem stopping_rule_apriori
    (κ rate η ε transient stationaryDistance totalDistance : ℝ)
    (hκ : 1 ≤ κ) (hrate : 0 < rate)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : κ * η ≤ rate / 2)
    (htransient : transient ≤
      2 * κ * Real.exp
        (-(rate - κ * η) * stoppingTime κ rate ε))
    (hstationary : stationaryDistance ≤ ε / 2)
    (htotal : totalDistance ≤ transient + stationaryDistance) :
    totalDistance ≤ ε := by
  have hdecay := stoppingTime_exponential_bound
    κ rate η ε hκ hrate hε0 hε1 hsmall
  linarith

/-- The trace-distance conclusion of Lemma 4(a) implies overlap at least
`1 - ε`. -/
theorem stopping_rule_overlap
    (κ rate η ε transient stationaryDistance totalDistance overlap : ℝ)
    (hκ : 1 ≤ κ) (hrate : 0 < rate)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : κ * η ≤ rate / 2)
    (htransient : transient ≤
      2 * κ * Real.exp
        (-(rate - κ * η) * stoppingTime κ rate ε))
    (hstationary : stationaryDistance ≤ ε / 2)
    (htotal : totalDistance ≤ transient + stationaryDistance)
    (hoverlap : 1 - overlap ≤ totalDistance) :
    1 - ε ≤ overlap := by
  have hdist := stopping_rule_apriori
    κ rate η ε transient stationaryDistance totalDistance
    hκ hrate hε0 hε1 hsmall htransient hstationary htotal
  linarith

end

end FTDQE
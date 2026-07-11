import Mathlib

/-!
# Energy certificate

This file formalises the scalar core of Lemma 4(b) from the FTDQE manuscript.
The finite-dimensional spectral argument will later provide the hypothesis

`0 ≤ energy - groundEnergy - gap * (1 - groundPopulation)`.

The result here converts that hypothesis into the quoted population bound.
-/

namespace FTDQE

/-- Algebraic core of the energy certificate.

`H - E₀ I ⪰ Δ (I - P)` paired with a positive state `ρ` gives the hypothesis
`hremainder`. This theorem performs the final scalar rearrangement.
-/
theorem energy_certificate_of_gap_remainder_nonneg
    {energy groundEnergy gap groundPopulation : ℝ}
    (hgap : 0 < gap)
    (hremainder :
      0 ≤ energy - groundEnergy - gap * (1 - groundPopulation)) :
    1 - groundPopulation ≤ (energy - groundEnergy) / gap := by
  apply (le_div_iff₀ hgap).2
  linarith

/-- Division-free form of the energy certificate. -/
theorem gap_mul_population_error_le_energy_error
    {energy groundEnergy gap groundPopulation : ℝ}
    (hremainder :
      0 ≤ energy - groundEnergy - gap * (1 - groundPopulation)) :
    gap * (1 - groundPopulation) ≤ energy - groundEnergy := by
  linarith

/-- A certified noisy energy estimate implies the target population bound.

The constants are deliberately asymmetric. An estimate with error at most
`gap * ε / 4`, accepted below `groundEnergy + 3 * gap * ε / 4`, certifies an
energy error at most `gap * ε`. This threshold is also guaranteed to trigger
once the true energy error is at most `gap * ε / 2`.
-/
theorem population_certificate_of_noisy_energy_estimate
    {energy estimate groundEnergy gap ε groundPopulation : ℝ}
    (hgap : 0 < gap)
    (hε : 0 ≤ ε)
    (hestimate_error : |estimate - energy| ≤ gap * ε / 4)
    (haccept : estimate ≤ groundEnergy + 3 * gap * ε / 4)
    (hremainder :
      0 ≤ energy - groundEnergy - gap * (1 - groundPopulation)) :
    1 - groundPopulation ≤ ε := by
  have henergy : energy - groundEnergy ≤ gap * ε := by
    have hlower : energy - estimate ≤ gap * ε / 4 := by
      have := (abs_le.mp hestimate_error).1
      linarith
    linarith
  have hpopulation :=
    gap_mul_population_error_le_energy_error hremainder
  nlinarith

/-- The corrected noisy test is guaranteed to fire once the true energy is
within `gap * ε / 2` of the ground energy. -/
theorem noisy_energy_test_eventually_accepts
    {energy estimate groundEnergy gap ε : ℝ}
    (hgap : 0 < gap)
    (hε : 0 ≤ ε)
    (henergy : energy ≤ groundEnergy + gap * ε / 2)
    (hestimate_error : |estimate - energy| ≤ gap * ε / 4) :
    estimate ≤ groundEnergy + 3 * gap * ε / 4 := by
  have hupper : estimate - energy ≤ gap * ε / 4 :=
    (abs_le.mp hestimate_error).2
  linarith

end FTDQE

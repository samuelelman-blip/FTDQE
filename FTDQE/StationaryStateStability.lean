import FTDQE.InvariantSubspaceRelaxation
import Mathlib.Topology.Sequences

/-!
# Stationary-state stability

This file formalises the three structural ingredients of Lemma 3: existence
from compact approximate stationary states, the resolvent stability estimate,
and uniqueness from perturbed exponential relaxation.
-/

namespace FTDQE

open Filter
open scoped Topology

/-- A vector is stationary for a continuous linear generator. -/
def IsStationary
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (x : X) : Prop :=
  L x = 0

/-- A vector is fixed by a continuous-time flow at every nonnegative time. -/
def IsFlowStationary
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (flow : ℝ → X →L[ℝ] X) (x : X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → flow t x = x

/--
Compactness form of the Cesàro existence argument in Lemma 3(i).
A sequence of states in a compact state space whose generator residual tends
to zero has a stationary cluster point in that state space.
-/
theorem exists_stationary_of_compact_approximants
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (stateSpace : Set X)
    (hcompact : IsCompact stateSpace)
    (approximants : ℕ → X)
    (hmem : ∀ n : ℕ, approximants n ∈ stateSpace)
    (hresidual :
      Tendsto (fun n : ℕ => L (approximants n)) atTop (𝓝 0)) :
    ∃ σ' ∈ stateSpace, IsStationary L σ' := by
  rcases hcompact.isSeqCompact hmem with
    ⟨σ', hσ'mem, φ, hφmono, hφlim⟩
  refine ⟨σ', hσ'mem, ?_⟩
  unfold IsStationary
  have hLlim :
      Tendsto (fun n : ℕ => L (approximants (φ n))) atTop (𝓝 (L σ')) := by
    simpa [Function.comp_def] using
      (L.continuous.tendsto σ').comp hφlim
  have hzero :
      Tendsto (fun n : ℕ => L (approximants (φ n))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      hresidual.comp hφmono.tendsto_atTop
  exact tendsto_nhds_unique hLlim hzero

/--
A certified inverse of `L` on the invariant subspace selected by `P`.
For Lemma 3 this is the resolvent
`J = -∫₀^∞ exp(tL) dt`, whose norm is at most `κ / rate`.
-/
structure ResolventCertificate
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] X) (P : X → Prop) (κ rate : ℝ) where
  resolvent : X →L[ℝ] X
  rate_pos : 0 < rate
  rightInverse : ∀ y : X, P y → resolvent (L y) = y
  norm_le : ∀ y : X, P y →
    ‖resolvent y‖ ≤ (κ / rate) * ‖y‖

/--
Lemma 3(ii), abstract resolvent form.  If `σ` is stationary for `L` and
`σ'` is stationary for `L + E`, then the resolvent identity gives

`‖σ' - σ‖ ≤ (κ / rate) ‖E σ'‖ ≤ κ η / rate`.
-/
theorem stationary_state_stability_of_resolvent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L E : X →L[ℝ] X) (P : X → Prop)
    (κ rate η : ℝ)
    (C : ResolventCertificate L P κ rate)
    (σ σ' : X)
    (hσ : IsStationary L σ)
    (hσ' : IsStationary (L + E) σ')
    (hdiff : P (σ' - σ))
    (herrorImage : P (E σ'))
    (herror : ‖E σ'‖ ≤ η * ‖σ'‖)
    (hσ'norm : ‖σ'‖ = 1)
    (hκ : 0 ≤ κ) :
    ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ ∧
      ‖σ' - σ‖ ≤ κ * η / rate := by
  have hσ0 : L σ = 0 := hσ
  have hσ'0 : L σ' + E σ' = 0 := by
    simpa [IsStationary] using hσ'
  have hLσ' : L σ' = -(E σ') := by
    calc
      L σ' = L σ' + E σ' - E σ' := by abel
      _ = 0 - E σ' := by rw [hσ'0]
      _ = -(E σ') := by simp
  have hLdiff : L (σ' - σ) = -(E σ') := by
    calc
      L (σ' - σ) = L σ' - L σ := by simp
      _ = -(E σ') - 0 := by rw [hLσ', hσ0]
      _ = -(E σ') := by simp
  have hfirst : ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ := by
    calc
      ‖σ' - σ‖ = ‖C.resolvent (L (σ' - σ))‖ := by
        exact congrArg norm (C.rightInverse (σ' - σ) hdiff).symm
      _ = ‖C.resolvent (E σ')‖ := by
        rw [hLdiff]
        simp
      _ ≤ (κ / rate) * ‖E σ'‖ := C.norm_le (E σ') herrorImage
  have hratio : 0 ≤ κ / rate :=
    div_nonneg hκ C.rate_pos.le
  have hsecond : ‖σ' - σ‖ ≤ κ * η / rate := by
    calc
      ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ := hfirst
      _ ≤ (κ / rate) * (η * ‖σ'‖) :=
        mul_le_mul_of_nonneg_left herror hratio
      _ = κ * η / rate := by rw [hσ'norm]; ring
  exact ⟨hfirst, hsecond⟩

/--
Lemma 3(iii): exponential relaxation makes a stationary state unique whenever
the perturbed decay rate `rate - κ * η` is positive.
-/
theorem flow_stationary_unique_of_perturbed_relaxation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (flow : ℝ → X →L[ℝ] X) (P : X → Prop)
    (κ rate η : ℝ)
    (hκ : 0 < κ)
    (hdecay : 0 < rate - κ * η)
    (hrelax : ∀ t : ℝ, 0 ≤ t → ∀ y : X, P y →
      ‖flow t y‖ ≤
        κ * Real.exp (-(rate - κ * η) * t) * ‖y‖)
    (σ₁ σ₂ : X)
    (hσ₁ : IsFlowStationary flow σ₁)
    (hσ₂ : IsFlowStationary flow σ₂)
    (hdiff : P (σ₁ - σ₂)) :
    σ₁ = σ₂ := by
  let decay : ℝ := rate - κ * η
  let t : ℝ := Real.log (κ + 1) / decay
  have hdecay' : 0 < decay := hdecay
  have hkone : 0 < κ + 1 := by linarith
  have ht : 0 ≤ t := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hdecay'.le
  have harg : -decay * t = -Real.log (κ + 1) := by
    dsimp [t]
    field_simp [hdecay'.ne']
  have hexp : Real.exp (-decay * t) = 1 / (κ + 1) := by
    rw [harg, Real.exp_neg, Real.exp_log hkone]
    rfl
  have hfactor : κ * Real.exp (-decay * t) < 1 := by
    rw [hexp]
    have hlt : κ / (κ + 1) < 1 :=
      (div_lt_one hkone).2 (by linarith)
    simpa [div_eq_mul_inv] using hlt
  have hfixed : flow t (σ₁ - σ₂) = σ₁ - σ₂ := by
    rw [map_sub, hσ₁ t ht, hσ₂ t ht]
  have hbound := hrelax t ht (σ₁ - σ₂) hdiff
  change ‖flow t (σ₁ - σ₂)‖ ≤
    κ * Real.exp (-decay * t) * ‖σ₁ - σ₂‖ at hbound
  rw [hfixed] at hbound
  have hnormzero : ‖σ₁ - σ₂‖ = 0 := by
    nlinarith [norm_nonneg (σ₁ - σ₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)

/--
Lemma 3 in composed certificate form.  Compact approximate stationary states
supply existence, the ideal resolvent supplies the unconditional stability
bound, and positive perturbed decay supplies uniqueness.
-/
theorem stationary_state_existence_stability_and_uniqueness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L E : X →L[ℝ] X)
    (flow : ℝ → X →L[ℝ] X)
    (stateSpace : Set X) (P : X → Prop)
    (κ rate η : ℝ)
    (C : ResolventCertificate L P κ rate)
    (σ : X)
    (hσ : IsStationary L σ)
    (hκ : 0 < κ)
    (hcompact : IsCompact stateSpace)
    (approximants : ℕ → X)
    (hmem : ∀ n : ℕ, approximants n ∈ stateSpace)
    (hresidual : Tendsto
      (fun n : ℕ => (L + E) (approximants n)) atTop (𝓝 0))
    (hPdiff : ∀ x ∈ stateSpace, P (x - σ))
    (hPsub : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, P (x - y))
    (hPerror : ∀ x ∈ stateSpace, P (E x))
    (herror : ∀ x ∈ stateSpace, ‖E x‖ ≤ η * ‖x‖)
    (hnorm : ∀ x ∈ stateSpace, ‖x‖ = 1)
    (hgeneratorFlow : ∀ x ∈ stateSpace,
      IsStationary (L + E) x → IsFlowStationary flow x)
    (hrelax : ∀ t : ℝ, 0 ≤ t → ∀ y : X, P y →
      ‖flow t y‖ ≤
        κ * Real.exp (-(rate - κ * η) * t) * ‖y‖) :
    ∃ σ' ∈ stateSpace,
      IsStationary (L + E) σ' ∧
      ‖σ' - σ‖ ≤ (κ / rate) * ‖E σ'‖ ∧
      ‖σ' - σ‖ ≤ κ * η / rate ∧
      (0 < rate - κ * η →
        ∀ τ ∈ stateSpace, IsStationary (L + E) τ → τ = σ') := by
  rcases exists_stationary_of_compact_approximants
      (L + E) stateSpace hcompact approximants hmem hresidual with
    ⟨σ', hσ'mem, hσ'stationary⟩
  have hstable := stationary_state_stability_of_resolvent
    L E P κ rate η C σ σ' hσ hσ'stationary
    (hPdiff σ' hσ'mem) (hPerror σ' hσ'mem)
    (herror σ' hσ'mem) (hnorm σ' hσ'mem) hκ.le
  refine ⟨σ', hσ'mem, hσ'stationary, hstable.1, hstable.2, ?_⟩
  intro hdecay τ hτmem hτstationary
  have hunique := flow_stationary_unique_of_perturbed_relaxation
    flow P κ rate η hκ hdecay hrelax σ' τ
    (hgeneratorFlow σ' hσ'mem hσ'stationary)
    (hgeneratorFlow τ hτmem hτstationary)
    (hPsub σ' hσ'mem τ hτmem)
  exact hunique.symm

end FTDQE

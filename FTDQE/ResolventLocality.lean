import FTDQE.StationaryStateStability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quasi-locality of the reduced resolvent

This file formalises the certificate-level content of Lemma 7.  The
open-system Lieb--Robinson estimate and the trace-norm mixing tail are combined
through the manuscript's split at `t⋆ = d/(2v)`.  The final absorption of the
short-time polynomial prefactor into one exponential is isolated as an
explicit envelope certificate, in the same style as Theorem 1.
-/

namespace FTDQE

noncomputable section

/-- The resolvent localisation length `ξ_J`. -/
def resolventLength (v rate μ : ℝ) : ℝ :=
  max (2 * v / rate) (2 / μ)

/-- Exponential spatial profile used in Lemma 7. -/
def resolventDecay (ξ d : ℝ) : ℝ :=
  Real.exp (-d / ξ)

/--
Split-integral certificate before choosing the cutoff time.  The first term is
the open-system Lieb--Robinson leakage and the second is the mixing tail.
-/
structure ResolventTimeSplitCertificate
    (error : ℝ → ℝ) (C κ v μ rate : ℝ) where
  bound : ∀ d T : ℝ, 0 ≤ d → 0 ≤ T → v * T ≤ d / 2 →
    error d ≤
      C * T * Real.exp (-μ * (d - v * T)) +
        (κ / rate) * Real.exp (-rate * T)

/-- Choosing `t⋆ = d/(2v)` gives the two terms appearing in the proof of
Lemma 7. -/
theorem resolvent_balanced_cutoff_bound
    (error : ℝ → ℝ) (C κ v μ rate d : ℝ)
    (hv : 0 < v) (hd : 0 ≤ d)
    (cert : ResolventTimeSplitCertificate error C κ v μ rate) :
    error d ≤
      C * (d / (2 * v)) * Real.exp (-μ * (d / 2)) +
        (κ / rate) * Real.exp (-rate * (d / (2 * v))) := by
  let T : ℝ := d / (2 * v)
  have h2v : 0 < 2 * v := mul_pos (by norm_num) hv
  have hT : 0 ≤ T := div_nonneg hd h2v.le
  have hvT : v * T = d / 2 := by
    dsimp [T]
    field_simp [hv.ne']
    <;> ring
  have hsplit := cert.bound d T hd hT (by rw [hvT])
  have hdsub : d - v * T = d / 2 := by
    rw [hvT]
    ring
  simpa [T, hdsub] using hsplit

/--
Envelope certificate absorbing the two balanced terms into the single spatial
profile with length `max {2v/rate, 2/μ}`.
-/
structure ResolventEnvelopeCertificate
    (C κ v μ rate C_J : ℝ) where
  length_pos : 0 < resolventLength v rate μ
  bound : ∀ d : ℝ, 0 ≤ d →
    C * (d / (2 * v)) * Real.exp (-μ * (d / 2)) +
        (κ / rate) * Real.exp (-rate * (d / (2 * v))) ≤
      C_J * (κ / rate) *
        resolventDecay (resolventLength v rate μ) d

/--
Lemma 7 in composed certificate form.  For a local traceless-Hermitian input,
`error d` is the trace norm of the part of the reduced resolvent reaching a
region at distance `d`.
-/
theorem resolvent_quasilocality
    (error : ℝ → ℝ) (C κ v μ rate C_J : ℝ)
    (hv : 0 < v)
    (split : ResolventTimeSplitCertificate error C κ v μ rate)
    (envelope : ResolventEnvelopeCertificate C κ v μ rate C_J) :
    ∀ d : ℝ, 0 ≤ d →
      error d ≤
        C_J * (κ / rate) *
          resolventDecay (resolventLength v rate μ) d := by
  intro d hd
  exact (resolvent_balanced_cutoff_bound
    error C κ v μ rate d hv hd split).trans
      (envelope.bound d hd)

end

end FTDQE

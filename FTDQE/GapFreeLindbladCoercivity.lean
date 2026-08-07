import FTDQE.GapFreeLindbladDynamicConvergence
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Finset.Max

/-!
# Spectral coercivity constant

This file identifies the scalar coercivity parameter used by the dynamical `1/t`
theorem with the minimum eigenvalue of the Lyapunov operator compressed to the
excited sector.
-/

namespace FTDQE
namespace GapFreeLindblad

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

variable {d r : ℕ}

/-- Minimum eigenvalue of a nonempty finite-dimensional Hermitian matrix. -/
def hermitianMinEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  Finset.min' (Finset.univ.image hA.eigenvalues) (by simp)

/-- The chosen minimum is below every eigenvalue. -/
theorem hermitianMinEigenvalue_le_eigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (i : n) :
    hermitianMinEigenvalue A hA ≤ hA.eigenvalues i := by
  classical
  unfold hermitianMinEigenvalue
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- A Hermitian matrix dominates its smallest eigenvalue times the identity. -/
theorem hermitianMinEigenvalue_smul_one_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ((hermitianMinEigenvalue A hA : ℂ) • (1 : Matrix n n ℂ)) ≤ A := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let κ : ℝ := hermitianMinEigenvalue A hA
  let Λ : Matrix n n ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i - κ : ℝ) : ℂ))
  have hdiag : Λ.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((hA.eigenvalues i - κ : ℝ) : ℂ)
    exact Complex.ofReal_nonneg.mpr <|
      sub_nonneg.mpr (by simpa [κ] using hermitianMinEigenvalue_le_eigenvalue A hA i)
  have hconj : (U * Λ * Uᴴ).PosSemidef := hdiag.mul_mul_conjTranspose_same U
  have hunit : U * Uᴴ = (1 : Matrix n n ℂ) := by
    change (hA.eigenvectorUnitary : Matrix n n ℂ) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hscalar : U * ((κ : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ =
      (κ : ℂ) • (1 : Matrix n n ℂ) := by
    calc
      U * ((κ : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ =
          (κ : ℂ) • (U * Uᴴ) := by simp [Matrix.mul_assoc]
      _ = (κ : ℂ) • (1 : Matrix n n ℂ) := by rw [hunit]
  have hspec : A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    change A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_apply] using hA.spectral_theorem
  have hdiagsub :
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) -
          ((κ : ℂ) • (1 : Matrix n n ℂ)) = Λ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Λ, κ]
    · simp [Λ, hij]
  have hfirst :
      A - ((κ : ℂ) • (1 : Matrix n n ℂ)) =
        (U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ) -
          ((κ : ℂ) • (1 : Matrix n n ℂ)) :=
    congrArg (fun X : Matrix n n ℂ => X - ((κ : ℂ) • (1 : Matrix n n ℂ))) hspec
  have heq : A - ((κ : ℂ) • (1 : Matrix n n ℂ)) = U * Λ * Uᴴ := by
    calc
      A - ((κ : ℂ) • (1 : Matrix n n ℂ)) =
          (U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ) -
            ((κ : ℂ) • (1 : Matrix n n ℂ)) := hfirst
      _ = (U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ) -
            U * ((κ : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ := by rw [hscalar]
      _ = (U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) -
            U * ((κ : ℂ) • (1 : Matrix n n ℂ))) * Uᴴ := by
              rw [Matrix.sub_mul]
      _ = U * (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) -
            ((κ : ℂ) • (1 : Matrix n n ℂ))) * Uᴴ := by
              rw [Matrix.mul_sub]
      _ = U * Λ * Uᴴ := by rw [hdiagsub]
  rw [heq]
  exact hconj

/-- Compression of a Lyapunov operator to an explicitly supplied orthonormal frame for
`Ran P`. -/
def restrictedLyapunov
    (K : QMatrix d) (U : Matrix (Fin d) (Fin (r + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Uᴴ * K * U

/-- Manuscript coercivity constant `κ_m`: the minimum eigenvalue of the compression
of `K_m` to the excited sector. -/
def kappaRestricted
    (K : QMatrix d) (U : Matrix (Fin d) (Fin (r + 1)) ℂ)
    (hK : K.IsHermitian) : ℝ :=
  hermitianMinEigenvalue (restrictedLyapunov K U)
    (Matrix.isHermitian_conjTranspose_mul_mul U hK)

/-- The minimum-eigenvalue definition gives the exact Loewner coercivity inequality
`K ≥ κ_m P` whenever the columns of `U` span `Ran P` and `K` is supported there. -/
theorem kappaRestricted_smul_projector_le
    (P K : QMatrix d) (U : Matrix (Fin d) (Fin (r + 1)) ℂ)
    (hK : K.IsHermitian)
    (_hUstarU : Uᴴ * U = 1)
    (hUUstar : U * Uᴴ = P)
    (hKU : P * K * P = K) :
    ((kappaRestricted K U hK : ℂ) • P) ≤ K := by
  classical
  let Kc := restrictedLyapunov K U
  have hKc : Kc.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U hK
  have hc : ((kappaRestricted K U hK : ℂ) •
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)) ≤ Kc := by
    simpa [kappaRestricted, Kc] using hermitianMinEigenvalue_smul_one_le Kc hKc
  rw [Matrix.le_iff] at hc ⊢
  have hconj :
      (U * (Kc - ((kappaRestricted K U hK : ℂ) •
        (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ).PosSemidef :=
    hc.mul_mul_conjTranspose_same U
  have hleft :
      U * (((kappaRestricted K U hK : ℂ) •
        (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ =
        (kappaRestricted K U hK : ℂ) • P := by
    calc
      U * (((kappaRestricted K U hK : ℂ) •
          (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ =
          (kappaRestricted K U hK : ℂ) • (U * Uᴴ) := by simp [Matrix.mul_assoc]
      _ = (kappaRestricted K U hK : ℂ) • P := by rw [hUUstar]
  have hright : U * Kc * Uᴴ = K := by
    simp only [Kc, restrictedLyapunov]
    calc
      U * (Uᴴ * K * U) * Uᴴ = (U * Uᴴ) * K * (U * Uᴴ) := by
        simp [Matrix.mul_assoc]
      _ = P * K * P := by rw [hUUstar]
      _ = K := hKU
  have heq :
      U * (Kc - ((kappaRestricted K U hK : ℂ) •
        (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ =
        K - (kappaRestricted K U hK : ℂ) • P := by
    calc
      U * (Kc - ((kappaRestricted K U hK : ℂ) •
          (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ =
          (U * Kc - U * ((kappaRestricted K U hK : ℂ) •
            (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ := by
              rw [Matrix.mul_sub]
      _ = U * Kc * Uᴴ -
          U * (((kappaRestricted K U hK : ℂ) •
            (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))) * Uᴴ := by
              rw [Matrix.sub_mul]
      _ = K - (kappaRestricted K U hK : ℂ) • P := by rw [hright, hleft]
  rw [← heq]
  exact hconj

/-- End-to-end `1/t` bound with the abstract scalar `κ` replaced by the actual minimum
eigenvalue of `K` on the excited sector. -/
theorem gapFree_one_over_t_of_gkls_kappaRestricted
    {ι : Type*} [Fintype ι]
    {G H P K : QMatrix d} {J : ι → QMatrix d} {ρ : ℝ → QMatrix d}
    (U : Matrix (Fin d) (Fin (r + 1)) ℂ)
    {W Emin t : ℝ}
    (hK : K.IsHermitian)
    (hUstarU : Uᴴ * U = 1)
    (hUUstar : U * Uᴴ = P)
    (hKU : P * K * P = K)
    (hκ : 0 < kappaRestricted K U hK)
    (ht : 0 < t)
    (htraj : IsGKLSTrajectory G J ρ)
    (hpos : IsPositiveTrajectory ρ)
    (hP : P.PosSemidef)
    (hPadj : fullHeisenbergAdjoint G J P ≤ 0)
    (hHadj : fullHeisenbergAdjoint G J H = -K)
    (hfloor : Emin ≤ realTracePair H (ρ t))
    (hwidth : realTracePair H (ρ 0) - Emin ≤ W) :
    realTracePair P (ρ t) ≤ W / (kappaRestricted K U hK * t) := by
  exact gapFree_one_over_t_of_gkls hκ ht htraj hpos hP hPadj
    (kappaRestricted_smul_projector_le P K U hK hUstarU hUUstar hKU)
    hHadj hfloor hwidth

end

end GapFreeLindblad
end FTDQE
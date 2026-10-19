import Dressed.TrialResidual
import Dressed.NumberThermalTail

/-!
# Actual finite-matrix trial certificates

The lower certificate uses a derived first-excited threshold, the actual
Rayleigh quotient and actual centered variance. The reference energy need not
be the Rayleigh quotient. Concrete trial/residual estimates remain separate.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every unsorted matrix eigenvalue is the corresponding permuted sorted one. -/
theorem eigenvalue_eq_ascending {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (i : ι) :
    hH.eigenvalues i = ascendingEigenvalue hH
      (((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i).rev) := by
  simp [ascendingEigenvalue, Matrix.IsHermitian.eigenvalues]

/-- Temple for actual ground energy with a threshold on the actual nonlowest
ordered spectrum. The threshold is not identified with the physical gap. -/
theorem groundEnergy_temple (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℝ ι) (hψ : ‖ψ‖=1) (threshold : ℝ)
    (hnext : ∀ k : Fin (Fintype.card ι), k≠0 → threshold≤ascendingEigenvalue hH k)
    (hmean : ⟪ψ,H.toEuclideanLin ψ⟫<threshold) :
    ⟪ψ,H.toEuclideanLin ψ⟫-
      ‖H.toEuclideanLin ψ-⟪ψ,H.toEuclideanLin ψ⟫ • ψ‖^2 /
        (threshold-⟪ψ,H.toEuclideanLin ψ⟫) ≤ groundEnergy hH := by
  apply hermitian_matrix_temple H hH ψ hψ (groundEnergy hH) threshold
  · intro i
    rw [eigenvalue_eq_ascending hH i]
    let k : Fin (Fintype.card ι) :=
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i).rev
    by_cases hk : k=0
    · left
      change ascendingEigenvalue hH k=groundEnergy hH
      rw [hk]
      rfl
    · right
      exact hnext k hk
  · intro i
    rw [eigenvalue_eq_ascending hH i]
    exact ascendingEigenvalue_monotone hH (Fin.zero_le _)
  · exact hmean

/-- The exact normalized trial provides a variational upper energy bound. -/
theorem dressed_trial_energy_upper (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ vacuum : EuclideanSpace ℝ ι) (hnorm : 1≤‖ψ‖)
    (reference η ε : ℝ) (hzero : ⟪vacuum,H.toEuclideanLin ψ-reference • ψ⟫=0)
    (heta : ‖ψ-vacuum‖≤η) (heps : ‖H.toEuclideanLin ψ-reference • ψ‖≤ε) :
    groundEnergy hH≤reference+η*ε := by
  have h := normalized_rayleigh_error_bound H.toEuclideanLin ψ vacuum
    hnorm reference η ε hzero heta heps
  have hu := (abs_le.mp h).2
  have hv := groundEnergy_le_rayleigh H hH (‖ψ‖⁻¹ • ψ)
    (norm_normalized_trial ψ (by linarith))
  linarith

/-- A half-unit Temple denominator turns actual residual estimates into a
true lower bound on the matrix's actual ground energy. -/
theorem dressed_trial_energy_lower (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ vacuum : EuclideanSpace ℝ ι) (hnorm : 1≤‖ψ‖)
    (reference η ε threshold : ℝ)
    (hzero : ⟪vacuum,H.toEuclideanLin ψ-reference • ψ⟫=0)
    (heta : ‖ψ-vacuum‖≤η) (heps : ‖H.toEuclideanLin ψ-reference • ψ‖≤ε)
    (hnext : ∀ k : Fin (Fintype.card ι), k≠0 → threshold≤ascendingEigenvalue hH k)
    (hden : (1/2 : ℝ)≤threshold-(reference+η*ε)) :
    reference-η*ε-2*ε^2≤groundEnergy hH := by
  let φ := ‖ψ‖⁻¹ • ψ
  let μ := ⟪φ,H.toEuclideanLin φ⟫
  have hnormφ : ‖φ‖=1 := norm_normalized_trial ψ (by linarith)
  have herror : |μ-reference|≤η*ε :=
    normalized_rayleigh_error_bound H.toEuclideanLin ψ vacuum
      hnorm reference η ε hzero heta heps
  have hmhi := (abs_le.mp herror).2
  have hmlo := (abs_le.mp herror).1
  have hd : (1/2 : ℝ)≤threshold-μ := by linarith
  have hdp : 0<threshold-μ := by linarith
  have hv : ‖H.toEuclideanLin φ-μ • φ‖^2≤ε^2 :=
    normalized_variance_bound H.toEuclideanLin ψ hnorm reference ε heps
  have hquot : ‖H.toEuclideanLin φ-μ • φ‖^2/(threshold-μ)≤2*ε^2 := by
    apply (div_le_iff₀ hdp).2
    nlinarith [sq_nonneg ε]
  have ht := groundEnergy_temple H hH φ hnormφ threshold hnext (by linarith)
  change μ-‖H.toEuclideanLin φ-μ • φ‖^2/(threshold-μ)≤groundEnergy hH at ht
  linarith

end BilayerDressed

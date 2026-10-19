import Dressed.MatrixTrialCertificate

/-! Actual normalized trial certificates from a directly controlled signed
residual expectation. The reference energy is never substituted for the true
Rayleigh quotient, and Temple uses an absolute nonlowest-energy threshold. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Direct unnormalized expectation control yields a normalized Rayleigh bound
because the true dressed trial norm is at least one. -/
theorem normalized_rayleigh_bound_of_mean
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (ψ : EuclideanSpace ℝ ι) (hnorm : 1 ≤ ‖ψ‖) (reference m : ℝ)
    (hmean : |⟪ψ,T ψ-reference • ψ⟫|  ≤  m) :
    |⟪‖ψ‖⁻¹ • ψ,T (‖ψ‖⁻¹ • ψ)⟫ - reference|  ≤  m := by
  rw [normalized_rayleigh_shift T ψ (by linarith) reference,abs_div,abs_of_nonneg (sq_nonneg ‖ψ‖)]
  have hm : 0 ≤ m := (abs_nonneg _).trans hmean
  have hn : 1 ≤ ‖ψ‖^2 := by nlinarith
  exact (div_le_iff₀ (by nlinarith : 0 < ‖ψ‖^2)).2
    (hmean.trans (le_mul_of_one_le_right hm hn))

/-- Variational upper bound from the actual signed residual mean. -/
theorem mean_trial_energy_upper (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℝ ι) (hnorm : 1 ≤ ‖ψ‖) (reference m : ℝ)
    (hmean : |⟪ψ,H.toEuclideanLin ψ-reference • ψ⟫|  ≤  m) :
    groundEnergy hH ≤ reference+m := by
  have he := normalized_rayleigh_bound_of_mean H.toEuclideanLin ψ hnorm reference m hmean
  have hv := groundEnergy_le_rayleigh H hH (‖ψ‖⁻¹ • ψ)
    (norm_normalized_trial ψ (by linarith))
  linarith [(abs_le.mp he).2]

/-- Temple lower bound with an arbitrary certified positive denominator d.
Both the signed mean and residual norm are measured on the actual trial. -/
theorem mean_trial_energy_lower (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℝ ι) (hnorm : 1 ≤ ‖ψ‖) (reference m ε threshold d : ℝ)
    (hmean : |⟪ψ,H.toEuclideanLin ψ-reference • ψ⟫|  ≤  m)
    (heps : ‖H.toEuclideanLin ψ-reference • ψ‖ ≤ ε)
    (hnext : ∀ k : Fin (Fintype.card ι), k≠0 → threshold ≤ ascendingEigenvalue hH k)
    (hd : 0 < d) (hden : d ≤ threshold-(reference+m)) :
    reference-m-ε^2/d ≤ groundEnergy hH := by
  let φ := ‖ψ‖⁻¹ • ψ
  let μ := ⟪φ,H.toEuclideanLin φ⟫
  have hnormφ : ‖φ‖=1 := norm_normalized_trial ψ (by linarith)
  have he : |μ-reference|  ≤  m :=
    normalized_rayleigh_bound_of_mean H.toEuclideanLin ψ hnorm reference m hmean
  have hmhi := (abs_le.mp he).2
  have hmlo := (abs_le.mp he).1
  have hdμ : d ≤ threshold-μ := by linarith
  have hpμ : 0 < threshold-μ := hd.trans_le hdμ
  have hv : ‖H.toEuclideanLin φ-μ • φ‖^2 ≤ ε^2 :=
    normalized_variance_bound H.toEuclideanLin ψ hnorm reference ε heps
  have hquot : ‖H.toEuclideanLin φ-μ • φ‖^2/(threshold-μ) ≤ ε^2/d :=
    div_le_div₀ (sq_nonneg _) hv hd hdμ
  have ht := groundEnergy_temple H hH φ hnormφ threshold hnext (by linarith)
  change μ-‖H.toEuclideanLin φ-μ • φ‖^2/(threshold-μ) ≤ groundEnergy hH at ht
  linarith

end BilayerDressed

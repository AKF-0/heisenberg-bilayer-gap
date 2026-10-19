import Dressed.FiniteTemple

/-! Actual Rayleigh and residual forms of finite-dimensional Temple's inequality.
The eigenbasis is related to the linear operator by explicit eigenvector equations;
neither the mean nor the variance is an unrelated scalar input. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BilayerDressed

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eigenbasis_coefficient (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i) (ψ : E) (i : ι) :
    ⟪b i, T ψ⟫ = energy i * ⟪b i, ψ⟫ := by
  rw [← hT (b i) ψ, heig i]
  exact real_inner_smul_left (b i) ψ (energy i)

theorem rayleigh_eq_spectralMean (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i) (ψ : E) :
    spectralMean (fun i => ⟪b i, ψ⟫^2) energy = ⟪ψ, T ψ⟫ := by
  unfold spectralMean
  calc
    (∑ i, ⟪b i, ψ⟫^2 * energy i) =
        ∑ i, ⟪ψ, b i⟫ * ⟪b i, T ψ⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [eigenbasis_coefficient T hT b energy heig ψ i, real_inner_comm ψ (b i)]
      ring
    _ = ⟪ψ, T ψ⟫ := b.sum_inner_mul_inner ψ (T ψ)

theorem residual_norm_eq_spectralVariance (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i) (ψ : E) :
    spectralVariance (fun i => ⟪b i, ψ⟫^2) energy =
      ‖T ψ - ⟪ψ,T ψ⟫ • ψ‖^2 := by
  unfold spectralVariance
  rw [rayleigh_eq_spectralMean T hT b energy heig ψ]
  calc
    (∑ i, ⟪b i,ψ⟫^2 * (energy i-⟪ψ,T ψ⟫)^2) =
        ∑ i, ⟪b i,T ψ-⟪ψ,T ψ⟫ • ψ⟫^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sub_right, inner_smul_right,
        eigenbasis_coefficient T hT b energy heig ψ i]
      ring
    _ = ‖T ψ-⟪ψ,T ψ⟫ • ψ‖^2 := b.sum_sq_inner_right _

/-- Temple's inequality for an actual symmetric linear operator, its unit trial
vector, actual Rayleigh quotient, and actual residual norm. -/
theorem operator_temple (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (energy : ι → ℝ)
    (heig : ∀ i, T (b i) = energy i • b i)
    (ψ : E) (hψ : ‖ψ‖ = 1) (ground threshold : ℝ)
    (hspectrum : ∀ i, energy i = ground ∨ threshold ≤ energy i)
    (hground : ∀ i, ground ≤ energy i)
    (hmean : ⟪ψ,T ψ⟫ < threshold) :
    ⟪ψ,T ψ⟫ - ‖T ψ-⟪ψ,T ψ⟫ • ψ‖^2 / (threshold-⟪ψ,T ψ⟫) ≤ ground := by
  have hsum : ∑ i, ⟪b i,ψ⟫^2 = 1 := by rw [b.sum_sq_inner_right ψ, hψ]; norm_num
  have h := finite_temple (fun i => ⟪b i,ψ⟫^2) energy ground threshold
    (fun _ => sq_nonneg _) hsum hspectrum hground
    (by simpa only [rayleigh_eq_spectralMean T hT b energy heig ψ] using hmean)
  simpa only [rayleigh_eq_spectralMean T hT b energy heig ψ,
    residual_norm_eq_spectralVariance T hT b energy heig ψ] using h

end BilayerDressed

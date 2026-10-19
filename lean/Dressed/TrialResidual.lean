import Dressed.ResidualGeometry
import Dressed.MatrixTemple

/-! Actual normalized trial vectors, Rayleigh quotients and residual variance.
No approximate energy is silently substituted for the true Rayleigh quotient. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Subtracting the component parallel to a unit trial vector cannot increase the residual. -/
theorem centered_residual_sq_le (ψ r : E) (hψ : ‖ψ‖=1) :
    ‖r-⟪ψ,r⟫ • ψ‖^2 ≤ ‖r‖^2 := by
  rw [norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hψ, mul_one]
  rw [sq_abs, real_inner_comm r ψ]
  nlinarith [sq_nonneg ⟪ψ,r⟫]

/-- The centered operator residual is bounded by the residual around any reference energy. -/
theorem operator_variance_le_reference (T : E →ₗ[ℝ] E) (ψ : E)
    (hψ : ‖ψ‖=1) (reference : ℝ) :
    ‖T ψ-⟪ψ,T ψ⟫ • ψ‖^2 ≤ ‖T ψ-reference • ψ‖^2 := by
  have hi : ⟪ψ,T ψ-reference • ψ⟫ = ⟪ψ,T ψ⟫-reference := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hψ]
    ring
  have he : T ψ-reference • ψ-⟪ψ,T ψ-reference • ψ⟫ • ψ =
      T ψ-⟪ψ,T ψ⟫ • ψ := by
    rw [hi, sub_smul]
    abel
  have h := centered_residual_sq_le ψ (T ψ-reference • ψ) hψ
  rwa [he] at h

/-- A nonzero vector is normalized by its real norm, not an assumed scalar factor. -/
theorem norm_normalized_trial (ψ : E) (hψ : 0<‖ψ‖) :
    ‖‖ψ‖⁻¹ • ψ‖=1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hψ)]
  exact inv_mul_cancel₀ (ne_of_gt hψ)

/-- Rescaling the actual operator residual rescales its norm exactly. -/
theorem normalized_reference_residual (T : E →ₗ[ℝ] E) (ψ : E)
    (hψ : 0<‖ψ‖) (reference : ℝ) :
    ‖T (‖ψ‖⁻¹ • ψ)-reference • (‖ψ‖⁻¹ • ψ)‖ =
      ‖T ψ-reference • ψ‖/‖ψ‖ := by
  have he : T (‖ψ‖⁻¹ • ψ)-reference • (‖ψ‖⁻¹ • ψ) =
      ‖ψ‖⁻¹ • (T ψ-reference • ψ) := by
    rw [map_smul, smul_sub, smul_smul, smul_smul, mul_comm reference]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hψ)]
  ring

/-- A lower bound one on the unnormalized trial norm means the variance does
not acquire an adverse normalization factor. -/
theorem normalized_variance_bound (T : E →ₗ[ℝ] E) (ψ : E)
    (hψ : 1≤‖ψ‖) (reference ε : ℝ)
    (hr : ‖T ψ-reference • ψ‖≤ε) :
    ‖T (‖ψ‖⁻¹ • ψ)-⟪‖ψ‖⁻¹ • ψ,T (‖ψ‖⁻¹ • ψ)⟫ • (‖ψ‖⁻¹ • ψ)‖^2 ≤ ε^2 := by
  have hp : 0<‖ψ‖ := by linarith
  have he : 0≤ε := (norm_nonneg _).trans hr
  have h := operator_variance_le_reference T (‖ψ‖⁻¹ • ψ)
    (norm_normalized_trial ψ hp) reference
  rw [normalized_reference_residual T ψ hp reference] at h
  have hq : ‖T ψ-reference • ψ‖/‖ψ‖≤ε := by
    apply (div_le_iff₀ hp).2
    exact hr.trans (le_mul_of_one_le_right he hψ)
  exact h.trans (sq_le_sq₀ (div_nonneg (norm_nonneg _) hp.le) he |>.2 hq)

/-- The true normalized Rayleigh shift is the normalized inner product with
the unnormalized reference residual. -/
theorem normalized_rayleigh_shift (T : E →ₗ[ℝ] E) (ψ : E)
    (hψ : 0<‖ψ‖) (reference : ℝ) :
    ⟪‖ψ‖⁻¹ • ψ,T (‖ψ‖⁻¹ • ψ)⟫-reference =
      ⟪ψ,T ψ-reference • ψ⟫/‖ψ‖^2 := by
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right,
    inner_sub_right, real_inner_self_eq_norm_sq]
  field_simp
  <;> ring

/-- Zero vacuum overlap improves the actual Rayleigh error by the non-vacuum
trial distance, even though the trial is not initially normalized. -/
theorem normalized_rayleigh_error_bound (T : E →ₗ[ℝ] E) (ψ vacuum : E)
    (hnorm : 1≤‖ψ‖) (reference η ε : ℝ)
    (hzero : ⟪vacuum,T ψ-reference • ψ⟫=0)
    (heta : ‖ψ-vacuum‖≤η) (heps : ‖T ψ-reference • ψ‖≤ε) :
    |⟪‖ψ‖⁻¹ • ψ,T (‖ψ‖⁻¹ • ψ)⟫-reference|≤η*ε := by
  rw [normalized_rayleigh_shift T ψ (by linarith) reference]
  exact normalized_mean_residual_bound ψ vacuum (T ψ-reference • ψ)
    hzero hnorm η ε heta heps

end BilayerDressed

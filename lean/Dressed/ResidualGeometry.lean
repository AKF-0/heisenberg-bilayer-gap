import Mathlib

/-! The zero-vacuum residual improvement in a real Hilbert space. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BilayerDressed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_residual_vacuum_bound (ψ vacuum residual : E)
    (hzero : ⟪vacuum,residual⟫ = 0) :
    |⟪ψ,residual⟫| ≤ ‖ψ-vacuum‖ * ‖residual‖ := by
  have h := abs_real_inner_le_norm (ψ-vacuum) residual
  simpa only [inner_sub_left, hzero, sub_zero] using h

/-- The mean error retains the non-vacuum factor instead of losing it to a
generic residual estimate. The vector need not already be normalized. -/
theorem normalized_mean_residual_bound (ψ vacuum residual : E)
    (hzero : ⟪vacuum,residual⟫ = 0) (hnorm : 1 ≤ ‖ψ‖)
    (η ε : ℝ) (heta : ‖ψ-vacuum‖ ≤ η) (heps : ‖residual‖ ≤ ε) :
    |⟪ψ,residual⟫ / ‖ψ‖^2| ≤ η*ε := by
  have hη : 0 ≤ η := le_trans (norm_nonneg _) heta
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) heps
  have hden : 1 ≤ ‖ψ‖^2 := by nlinarith [norm_nonneg ψ]
  have hprod : |⟪ψ,residual⟫| ≤ η*ε :=
    (inner_residual_vacuum_bound ψ vacuum residual hzero).trans
      (mul_le_mul heta heps (norm_nonneg _) hη)
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖ψ‖)]
  apply (div_le_iff₀ (by linarith : 0 < ‖ψ‖^2)).2
  exact hprod.trans (le_mul_of_one_le_right (mul_nonneg hη hε) hden)

end BilayerDressed

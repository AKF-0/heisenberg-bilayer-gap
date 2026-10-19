import Mathlib

/-! Finite tensor-factor quadratic forms and positivity, without spectral input. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace BilayerDressed

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem kronecker_identity_quadratic (A : Matrix ι ι ℝ) (v : ι × κ → ℝ) :
    dotProduct v ((A ⊗ₖ (1 : Matrix κ κ ℝ)).mulVec v) =
      ∑ k : κ, dotProduct (fun i => v (i,k)) (A.mulVec (fun i => v (i,k))) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

/-- Positivity of a genuine tensor identity extension follows from slice positivity. -/
theorem kronecker_identity_quadratic_nonneg (A : Matrix ι ι ℝ)
    (hA : ∀ v : ι → ℝ, 0 ≤ dotProduct v (A.mulVec v)) (v : ι × κ → ℝ) :
    0 ≤ dotProduct v ((A ⊗ₖ (1 : Matrix κ κ ℝ)).mulVec v) := by
  rw [kronecker_identity_quadratic]
  exact Finset.sum_nonneg fun k _ => hA _

/-- Matrix reindexing preserves the actual quadratic form with the same vector permutation. -/
theorem reindex_quadratic {τ : Type*} [Fintype τ]
    (e : ι ≃ τ) (A : Matrix ι ι ℝ) (v : τ → ℝ) :
    dotProduct v ((Matrix.reindex e e A).mulVec v) =
      dotProduct (v ∘ e) (A.mulVec (v ∘ e)) := by
  simp only [dotProduct, mulVec, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  simp only [e.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← e.sum_comp]
  simp

end BilayerDressed

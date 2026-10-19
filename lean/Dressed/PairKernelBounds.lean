import Dressed.PairVacuumNorm
import Dressed.MatrixRowBounds

/-!
# Concrete pair-kernel bounds from actual coefficient estimates

`κ` bounds the absolute row sum of K; `a` bounds each absolute entry. The site
count is always `Fintype.card V`, not a freely supplied scaling parameter.
All operator norms below are genuine Euclidean Hilbert-space operator norms.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual ordered pair kernel is bounded by its absolute coefficient sum. -/
theorem pairKernelOperator_opNorm_le (K : V → V → ℝ) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairKernelOperator K)‖ ≤
      Real.sqrt 3 * ∑ u, ∑ v, |K u v| := by
  classical
  unfold pairKernelOperator
  simp only [map_sum, map_smul]
  calc
    _ ≤ ∑ u, ∑ v, ‖K u v •
        Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate u v)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun u _ => norm_sum_le _ _
    _ ≤ ∑ u, ∑ v, |K u v| * Real.sqrt 3 := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pairCreate_opNorm_le_sqrt_three u v) (abs_nonneg _)
    _ = _ := by simp only [Finset.mul_sum, mul_comm]

/-- Absolute row bounds control the total actual coefficient mass. -/
theorem sum_abs_le_card_row (K : Matrix V V ℝ) (κ : ℝ) (hrow : HasAbsRowBound K κ) :
    (∑ u, ∑ v, |K u v|) ≤ (Fintype.card V : ℝ) * κ := by
  calc
    _ ≤ ∑ _u : V, κ := Finset.sum_le_sum fun u _ => hrow u
    _ = _ := by simp

/-- Half of the ordered sum gives the physical S and the factor √3/2. -/
theorem pairKernelS_opNorm_le_of_row (K : Matrix V V ℝ) (κ : ℝ)
    (hrow : HasAbsRowBound K κ) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairKernelS K)‖ ≤
      (Real.sqrt 3 / 2) * (Fintype.card V : ℝ) * κ := by
  have hmass : (∑ u, ∑ v, |K u v / 2|) ≤ (Fintype.card V : ℝ) * κ / 2 := by
    calc
      _ = (∑ u, ∑ v, |K u v|) / 2 := by
        simp only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (sum_abs_le_card_row K κ hrow) (by norm_num)
  calc
    _ ≤ Real.sqrt 3 * ∑ u, ∑ v, |K u v / 2| :=
      pairKernelOperator_opNorm_le (fun u v => K u v / 2)
    _ ≤ Real.sqrt 3 * ((Fintype.card V : ℝ) * κ / 2) :=
      mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Vacuum amplification from symmetry, zero diagonal, an entry bound a, and a row bound κ. -/
theorem pairKernelS_vacuum_norm_sq_le_entry_row (K : Matrix V V ℝ) (a κ : ℝ)
    (hK : ∀ u v, K u v = K v u) (hdiag : ∀ u, K u u = 0)
    (hentry : ∀ u v, |K u v| ≤ a) (hrow : HasAbsRowBound K κ) (ha : 0 ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (pairKernelS K) vacuumVector‖ ^ 2 ≤
      (3 / 2 : ℝ) * (Fintype.card V : ℝ) * a * κ := by
  rw [pairKernelS_vacuum_norm_sq K hK hdiag]
  calc
    _ ≤ (3 / 2 : ℝ) * ((Fintype.card V : ℝ) * a * κ) :=
      mul_le_mul_of_nonneg_left (sum_sq_le_entry_row K a κ hentry hrow ha) (by norm_num)
    _ = _ := by ring

end BilayerDressed

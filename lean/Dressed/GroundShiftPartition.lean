import Dressed.NumberThermalTail
import Gap.TraceConvexity

/-! Exact actual matrix partition ratios from correlated ground-energy defects
and the shifted thermal tail. Exactly one lowest state contributes the unit
term; no nondegeneracy or spectral-gap assumption is introduced. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
open BilayerGap
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem relativePartition_ge_one {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) :
    1 ≤ relativePartition hH β := by
  have h := excitedPartition_nonneg hH β
  rw [←relativePartition_sub_one_eq_excited] at h
  linarith

theorem relativePartition_pos {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) :
    0 < relativePartition hH β := lt_of_lt_of_le (by norm_num) (relativePartition_ge_one hH β)

/-- Exact spectral shift of the genuine trace exponential partition function. -/
theorem partition_eq_ground_shift {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) :
    TraceConvexity.partition H β =
      Real.exp (-β*groundEnergy hH)*relativePartition hH β := by
  rw [TraceConvexity.partition_eq_sum hH β,←sum_ascendingEigenvalue hH (fun x => Real.exp (-β*x))]
  unfold relativePartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [←Real.exp_add]
  congr 1
  ring

/-- Exact spatial ratio, retaining the correlated energy defect. -/
theorem partition_spatial_ratio_eq {H0 : Matrix ι ι ℝ} {H1 : Matrix κ κ ℝ}
    (h0 : H0.IsHermitian) (h1 : H1.IsHermitian) (β : ℝ) :
    TraceConvexity.partition H1 β/(TraceConvexity.partition H0 β)^2 =
      Real.exp (-β*(groundEnergy h1-2*groundEnergy h0))*
        relativePartition h1 β/(relativePartition h0 β)^2 := by
  rw [partition_eq_ground_shift h0,partition_eq_ground_shift h1]
  have he : Real.exp (-β*groundEnergy h1)=
      Real.exp (-β*(groundEnergy h1-2*groundEnergy h0))*(Real.exp (-β*groundEnergy h0))^2 := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [Real.exp_ne_zero,ne_of_gt (relativePartition_pos h0 β)]

/-- A certified defect upper bound and a genuine small-box thermal upper bound
imply the physical spatial-purity lower bound. -/
theorem partition_spatial_ratio_lower {H0 : Matrix ι ι ℝ} {H1 : Matrix κ κ ℝ}
    (h0 : H0.IsHermitian) (h1 : H1.IsHermitian) (β d Q : ℝ)
    (hβ : 0 ≤ β) (hdef : groundEnergy h1-2*groundEnergy h0 ≤ d)
    (hQ : relativePartition h0 β ≤ Q) :
    Real.exp (-β*d)/Q^2 ≤
      TraceConvexity.partition H1 β/(TraceConvexity.partition H0 β)^2 := by
  rw [partition_spatial_ratio_eq h0 h1]
  have hQ0 := relativePartition_pos h0 β
  have hQp : 0 < Q := hQ0.trans_le hQ
  have he : Real.exp (-β*d) ≤ Real.exp (-β*(groundEnergy h1-2*groundEnergy h0)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq1 := relativePartition_ge_one h1 β
  apply div_le_div₀ (by positivity)
  · exact he.trans (le_mul_of_one_le_right (Real.exp_nonneg _) hq1)
  · exact sq_pos_of_pos hQ0
  · exact pow_le_pow_left₀ hQ0.le hQ 2

/-- The physical thermal ratio cancels the ground energy exactly. -/
theorem partition_thermal_ratio_eq {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (β : ℝ) :
    TraceConvexity.partition H (2*β)/(TraceConvexity.partition H β)^2 =
      relativePartition hH (2*β)/(relativePartition hH β)^2 := by
  rw [partition_eq_ground_shift hH,partition_eq_ground_shift hH]
  have he : Real.exp (-(2*β)*groundEnergy hH)=(Real.exp (-β*groundEnergy hH))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [Real.exp_ne_zero,ne_of_gt (relativePartition_pos hH β)]

theorem partition_thermal_ratio_lower {H : Matrix ι ι ℝ} (hH : H.IsHermitian)
    (β Q : ℝ) (hQ : relativePartition hH β ≤ Q) :
    1/Q^2 ≤ TraceConvexity.partition H (2*β)/(TraceConvexity.partition H β)^2 := by
  rw [partition_thermal_ratio_eq hH]
  have hQ0 := relativePartition_pos hH β
  apply div_le_div₀ (relativePartition_pos hH (2*β)).le (relativePartition_ge_one hH (2*β))
    (sq_pos_of_pos hQ0) (pow_le_pow_left₀ hQ0.le hQ 2)

end BilayerDressed

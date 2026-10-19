import Gap.Staircase
import Gap.Seeds

/-! The three actual staircase seed defects from finite partition bounds.
The denominators correspond to areas 16, 32 and 64, and the numerator lower
bounds come from the common product-singlet state, not from an assumed gap. -/
noncomputable section
namespace BilayerGap.PartitionSeed

/-- A partition upper bound and a separate numerator lower bound control purity. -/
theorem ratio_lower {X Y U : ℝ} (hX : 0 < X) (hU : X ≤ U) (hY : 1 ≤ Y) :
    1 / U ^ 2 ≤ Y / X ^ 2 := by
  have hU0 : 0 < U := hX.trans_le hU
  apply le_trans (one_div_le_one_div_of_le (sq_pos_of_pos hX)
    (pow_le_pow_left₀ hX.le hU 2))
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hX)).2 hY

/-- The exact rational certificate applies to the real denominator bound. -/
theorem narrow_ratio {X Y : ℝ} (hX : 0 < X) (hY : 1 ≤ Y)
    (k : ℕ) (hk : k = 8 ∨ k = 16 ∨ k = 32)
    (hXupper : X ≤ (10001/10000 : ℝ)^k) :
    1-Y/X^2 ≤ 1/100 := by
  have h := ratio_lower hX hXupper hY
  have hrat : (99/100 : ℝ) ≤ 1 / ((10001/10000 : ℝ)^k)^2 := by
    rcases hk with rfl | rfl | rfl <;> norm_num
  linarith

/-- All three seed defects at the concrete volume (4,4,14). -/
theorem narrow_staircase (Z : Volume → ℝ)
    (hpos : ∀ v, 0 < Z v)
    (h44 : Z ⟨4,4,14⟩ ≤ (10001/10000 : ℝ)^8)
    (h84 : Z ⟨8,4,14⟩ ≤ (10001/10000 : ℝ)^16)
    (h88 : Z ⟨8,8,14⟩ ≤ (10001/10000 : ℝ)^32)
    (h84lo : 1 ≤ Z ⟨8,4,14⟩)
    (h88lo : 1 ≤ Z ⟨8,8,14⟩)
    (h88tlo : 1 ≤ Z ⟨8,8,28⟩) :
    1-staircaseA Z ⟨4,4,14⟩ ≤ 1/100 ∧
    1-staircaseB Z ⟨4,4,14⟩ ≤ 1/100 ∧
    1-staircaseC Z ⟨4,4,14⟩ ≤ 1/100 := by
  constructor
  · exact narrow_ratio (hpos ⟨4,4,14⟩) h84lo 8 (by simp) h44
  constructor
  · exact narrow_ratio (hpos ⟨8,4,14⟩) h88lo 16 (by simp) h84
  · have hh := narrow_ratio (hpos ⟨8,8,14⟩) h88tlo 32 (by simp) h88
    norm_num only [staircaseC, partitionRatio, doubleCoord, show (2:ℝ)*14 = 28 by norm_num]
    exact hh

#print axioms narrow_staircase
end BilayerGap.PartitionSeed

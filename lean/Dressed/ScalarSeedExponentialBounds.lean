import Dressed.ScalarExponentialBridge
import Dressed.CubicExponentialLower

/-! Genuine scalar exponential seed inequalities. Physical energy and thermal
comparison hypotheses are not introduced by this file. -/
noncomputable section
namespace BilayerDressed.ScalarThermal

theorem lowerExp3_cast_le_exp (z : ℚ) (hz : 0≤z) :
    (ScalarWarmup.lowerExp3 z : ℝ) ≤ Real.exp (-(z:ℝ)) := by
  simpa [ScalarWarmup.lowerExp3] using
    ScalarAnalytic.cubic_exp_neg_lower (z:ℝ) (by exact_mod_cast hz)

theorem thermal_exponential_tail16 :
    (48:ℝ)*Real.exp (-((16*den16:ℚ):ℝ)) /
      (1-Real.exp (-((16*a:ℚ):ℝ)))^49 < 305/1000000 := by
  have hq := suppression_a
  have ht := suppression_16
  have hq0 := Real.exp_pos (-((16*a:ℚ):ℝ))
  have ht0 := Real.exp_pos (-((16*den16:ℚ):ℝ))
  have hd : (0:ℝ)<1-Real.exp (-((16*a:ℚ):ℝ)) := by linarith
  calc
    _ ≤ (48:ℝ)*(1/157894)/(1-1/238947)^49 := by
      gcongr
    _ < 305/1000000 := by norm_num

theorem thermal_exponential_tail32 :
    (96:ℝ)*Real.exp (-((16*den32:ℚ):ℝ)) /
      (1-Real.exp (-((16*a:ℚ):ℝ)))^97 < 927/1000000 := by
  have hq := suppression_a
  have ht := suppression_32
  have hq0 := Real.exp_pos (-((16*a:ℚ):ℝ))
  have ht0 := Real.exp_pos (-((16*den32:ℚ):ℝ))
  have hd : (0:ℝ)<1-Real.exp (-((16*a:ℚ):ℝ)) := by linarith
  calc
    _ ≤ (96:ℝ)*(1/103691)/(1-1/238947)^97 := by
      gcongr
    _ < 927/1000000 := by norm_num

theorem thermal_exponential_tail64 :
    (192:ℝ)*Real.exp (-((16*den64:ℚ):ℝ)) /
      (1-Real.exp (-((16*a:ℚ):ℝ)))^193 < 4331/1000000 := by
  have hq := suppression_a
  have ht := suppression_64
  have hq0 := Real.exp_pos (-((16*a:ℚ):ℝ))
  have ht0 := Real.exp_pos (-((16*den64:ℚ):ℝ))
  have hd : (0:ℝ)<1-Real.exp (-((16*a:ℚ):ℝ)) := by linarith
  calc
    _ ≤ (192:ℝ)*(1/44383)/(1-1/238947)^193 := by
      gcongr
    _ < 4331/1000000 := by norm_num

theorem initial_a_exponential :
    1-Real.exp (-((16*ScalarWarmup.dx:ℚ):ℝ))/(ScalarWarmup.Q0:ℝ)^2 <
      (ScalarWarmup.a0:ℝ) := by
  have hp := lowerExp3_cast_le_exp (16*ScalarWarmup.dx)
    (by norm_num [ScalarWarmup.dx])
  have hd := div_le_div_of_nonneg_right hp (sq_nonneg (ScalarWarmup.Q0:ℝ))
  have hn : 1-(ScalarWarmup.lowerExp3 (16*ScalarWarmup.dx):ℝ)/
      (ScalarWarmup.Q0:ℝ)^2 < (ScalarWarmup.a0:ℝ) := by
    exact_mod_cast ScalarWarmup.initial_a
  linarith

theorem initial_b_exponential :
    1-Real.exp (-((16*ScalarWarmup.dy:ℚ):ℝ))/(ScalarWarmup.Q1:ℝ)^2 <
      (ScalarWarmup.b0:ℝ) := by
  have hp := lowerExp3_cast_le_exp (16*ScalarWarmup.dy)
    (by norm_num [ScalarWarmup.dy])
  have hd := div_le_div_of_nonneg_right hp (sq_nonneg (ScalarWarmup.Q1:ℝ))
  have hn : 1-(ScalarWarmup.lowerExp3 (16*ScalarWarmup.dy):ℝ)/
      (ScalarWarmup.Q1:ℝ)^2 < (ScalarWarmup.b0:ℝ) := by
    exact_mod_cast ScalarWarmup.initial_b
  linarith

end BilayerDressed.ScalarThermal

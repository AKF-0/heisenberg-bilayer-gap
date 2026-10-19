import Dressed.ScalarThermalCertificate
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Connect fixed rational Taylor certificates to the genuine real exponential.
No physical spectral estimate is assumed or asserted by this scalar file. -/
noncomputable section
namespace BilayerDressed.ScalarThermal
open scoped BigOperators

theorem taylor50_le_exp (x : ℚ) (hx : 0≤x) :
    (taylor50 x : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold taylor50
  push_cast
  exact Real.sum_le_exp_of_nonneg (x := (x : ℝ)) (by exact_mod_cast hx) 51

theorem exp_floor_of_taylor {x C : ℚ} (hx : 0≤x) (h : C<taylor50 x) :
    (C : ℝ)<Real.exp (x : ℝ) :=
  (by exact_mod_cast h : (C : ℝ)<(taylor50 x : ℝ)).trans_le (taylor50_le_exp x hx)

theorem exp_a_floor : (238947:ℝ)<Real.exp ((16*a:ℚ):ℝ) :=
  exp_floor_of_taylor (by norm_num [a]) taylor_a

theorem exp_16_floor : (157894:ℝ)<Real.exp ((16*den16:ℚ):ℝ) :=
  exp_floor_of_taylor (by norm_num [den16]) taylor_16

theorem exp_32_floor : (103691:ℝ)<Real.exp ((16*den32:ℚ):ℝ) :=
  exp_floor_of_taylor (by norm_num [den32]) taylor_32

theorem exp_64_floor : (44383:ℝ)<Real.exp ((16*den64:ℚ):ℝ) :=
  exp_floor_of_taylor (by norm_num [den64]) taylor_64

theorem exp_neg_lt_inverse {x C : ℝ} (hC : 0<C) (h : C<Real.exp x) :
    Real.exp (-x)<1/C := by
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos x) hC).2 h

theorem suppression_a : Real.exp (-((16*a:ℚ):ℝ)) < 1/238947 :=
  exp_neg_lt_inverse (by norm_num) exp_a_floor

theorem suppression_16 : Real.exp (-((16*den16:ℚ):ℝ)) < 1/157894 :=
  exp_neg_lt_inverse (by norm_num) exp_16_floor

theorem suppression_32 : Real.exp (-((16*den32:ℚ):ℝ)) < 1/103691 :=
  exp_neg_lt_inverse (by norm_num) exp_32_floor

theorem suppression_64 : Real.exp (-((16*den64:ℚ):ℝ)) < 1/44383 :=
  exp_neg_lt_inverse (by norm_num) exp_64_floor
end BilayerDressed.ScalarThermal

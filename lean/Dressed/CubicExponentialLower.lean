import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Scalar lower cubic Taylor bound, proved by two monotonicity arguments.
This is a bound for all nonnegative real arguments, not a sampled check. -/
noncomputable section
namespace BilayerDressed.ScalarAnalytic

theorem quadratic_exp_neg_upper (x : ℝ) (hx : 0≤x) :
    Real.exp (-x) ≤ 1-x+x^2/2 := by
  let f : ℝ → ℝ := fun y => 1-y+y^2/2-Real.exp (-y)
  have hd (y : ℝ) : HasDerivAt f (-1+y+Real.exp (-y)) y := by
    dsimp [f]
    convert (((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      ((hasDerivAt_id y).neg.exp) using 1 <;> simp only [id_eq, Pi.neg_apply] <;> ring
  have hm : Monotone f := monotone_of_hasDerivAt_nonneg hd (by
    intro y
    change 0 ≤ -1+y+Real.exp (-y)
    have h := Real.add_one_le_exp (-y)
    linarith)
  have h := hm hx
  dsimp [f] at h
  simp only [neg_zero, Real.exp_zero, zero_pow (by decide : 2≠0)] at h
  linarith

theorem cubic_exp_neg_lower (x : ℝ) (hx : 0≤x) :
    1-x+x^2/2-x^3/6 ≤ Real.exp (-x) := by
  let f : ℝ → ℝ := fun y => Real.exp (-y)-1+y-y^2/2+y^3/6
  have hd (y : ℝ) : HasDerivAt f (-Real.exp (-y)+1-y+y^2/2) y := by
    dsimp [f]
    convert (((((hasDerivAt_id y).neg.exp).sub (hasDerivAt_const y (1:ℝ))).add
      (hasDerivAt_id y)).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;> simp only [id_eq, Pi.neg_apply] <;> ring
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [f]; fun_prop)
      (fun y _ => (hd y).hasDerivWithinAt) (by
        intro y hy
        have hy0 : 0≤y := le_of_lt (by simpa only [interior_Ici, Set.mem_Ioi] using hy)
        have h := quadratic_exp_neg_upper y hy0
        linarith)
  have h := hm (by simp : (0:ℝ)∈Set.Ici 0) hx hx
  dsimp [f] at h
  norm_num at h
  linarith
end BilayerDressed.ScalarAnalytic

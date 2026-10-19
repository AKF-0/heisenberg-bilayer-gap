import Gap.Seeds

/-!
# Actual exponential bounds behind the rational seed certificates

The exact rational Taylor sums are connected to `Real.exp` using its proved
positive-series lower bound. The geometric upper bound is derived from
`1-x ≤ exp(-x)`. These are scalar analytic facts, not assumptions about a
Hamiltonian, its spectrum, matrix log-trace convexity, or a torus seed.
-/

noncomputable section
namespace BilayerGap
namespace SeedAnalytic

/-- The rational Taylor polynomial is a certified lower bound for the actual
real exponential at every nonnegative rational argument. -/
theorem taylorSum_cast_le_exp (x : ℚ) (hx : 0 ≤ x) (n : ℕ) :
    (SeedCertificate.taylorSum x n : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold SeedCertificate.taylorSum
  push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) (n + 1)

/-- The exact degree-18 rational certificate implies the actual exponential bound. -/
theorem exp_fourteen_gt : (1000000 : ℝ) < Real.exp 14 := by
  have h : (1000000 : ℝ) < (SeedCertificate.taylorSum 14 18 : ℝ) := by
    exact_mod_cast SeedCertificate.narrow_taylor_gt
  exact h.trans_le (by simpa using taylorSum_cast_le_exp 14 (by norm_num) 18)

/-- The exact degree-29 rational certificate at `13.93`, with no floating-point premise. -/
theorem exp_wide_threshold_gt : (1000000 : ℝ) < Real.exp (1393 / 100) := by
  have h : (1000000 : ℝ) < (SeedCertificate.taylorSum (1393 / 100) 29 : ℝ) := by
    exact_mod_cast SeedCertificate.wide_taylor_gt
  exact h.trans_le (by simpa using taylorSum_cast_le_exp (1393 / 100) (by norm_num) 29)

/-- A positive lower bound for an exponential gives an inverse upper bound. -/
theorem exp_neg_lt_inverse {x C : ℝ} (hC : 0 < C) (h : C < Real.exp x) :
    Real.exp (-x) < 1 / C := by
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos x) hC).2 h

theorem exp_neg_fourteen_lt : Real.exp (-14) < (1 / 1000000 : ℝ) :=
  exp_neg_lt_inverse (by norm_num) exp_fourteen_gt

theorem exp_neg_wide_threshold_lt : Real.exp (-(1393 / 100)) < (1 / 1000000 : ℝ) :=
  exp_neg_lt_inverse (by norm_num) exp_wide_threshold_gt

/-- Doubling a suppression exponent squares its bound. -/
theorem exp_neg_double_lt {x C : ℝ} (hC : 0 < C) (h : C < Real.exp x) :
    Real.exp (-(2 * x)) < (1 / C) ^ 2 := by
  have hi := exp_neg_lt_inverse hC h
  have hp := Real.exp_pos (-x)
  have heq : Real.exp (-(2 * x)) = Real.exp (-x) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq]
  nlinarith

theorem exp_neg_twenty_eight_lt : Real.exp (-28) < (1 / 1000000000000 : ℝ) := by
  have h := exp_neg_double_lt (by norm_num : (0 : ℝ) < 1000000) exp_fourteen_gt
  norm_num at h ⊢
  exact h

theorem exp_neg_wide_double_lt : Real.exp (-(1393 / 50)) < (1 / 1000000000000 : ℝ) := by
  have h := exp_neg_double_lt (by norm_num : (0 : ℝ) < 1000000) exp_wide_threshold_gt
  norm_num at h ⊢
  exact h

/-- A geometric upper bound for the actual exponential. In particular it
applies throughout `0 ≤ x < 1`, but no lower bound on x is needed. -/
theorem exp_le_geometric {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h := (inv_le_inv₀ (Real.exp_pos (-x)) (sub_pos.mpr hx)).2
    (Real.one_sub_le_exp_neg x)
  simpa only [Real.exp_neg, inv_inv, one_div] using h

/-- Exact rational upper bound for the narrow ground-energy contribution. -/
theorem narrow_ground_exponential_bound :
    Real.exp (14 * (3 / 499000 : ℝ)) ≤ 499000 / 498958 := by
  have h := exp_le_geometric (x := 14 * (3 / 499000 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

theorem narrow_low_correction_bound :
    Real.exp (14 * (1 / 250 : ℝ) / 2) ≤ 250 / 243 := by
  have h := exp_le_geometric (x := 14 * (1 / 250 : ℝ) / 2) (by norm_num)
  norm_num at h ⊢
  exact h

theorem narrow_high_correction_bound :
    Real.exp (14 * (1 / 250 : ℝ)) ≤ 125 / 118 := by
  have h := exp_le_geometric (x := 14 * (1 / 250 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The exponential comparison needed for the wider endpoint ground shift. -/
theorem wide_ground_exponential_bound :
    Real.exp (112 * (1 / 400 : ℝ) ^ 2) ≤ 1 / (1 - 112 * (1 / 400 : ℝ) ^ 2) :=
  exp_le_geometric (by norm_num)

#print axioms taylorSum_cast_le_exp
#print axioms exp_fourteen_gt
#print axioms exp_wide_threshold_gt
#print axioms exp_le_geometric
#print axioms exp_neg_double_lt

end SeedAnalytic
end BilayerGap

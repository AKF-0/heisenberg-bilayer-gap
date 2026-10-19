import Mathlib

/-!
# Scalar staircase contraction and the dyadic majorant

This file proves the scalar part of Sections 3–4 of the analytic gap argument.
It does not assert a spatial moment representation, identify partition functions,
or assume the final gap theorem as an axiom. The transport-product and squaring
inequalities are explicit hypotheses wherever physical purities are used.
-/

namespace BilayerGap

noncomputable section

/-- The defect bound after squaring and renormalizing a probability distribution. -/
def purityStep (u : ℝ) : ℝ := u ^ 2 / (2 * (1 - u) ^ 2)

/-- Defect associated with the staircase transfer product of degrees `4,2,1`. -/
def stairDefect (a b c : ℝ) : ℝ := 1 - (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c)

/-- The dimension-two common-defect coefficient. -/
def G7 (u : ℝ) : ℝ :=
  ((∑ k ∈ Finset.range 7, ((1 - u) ^ (k + 1))⁻¹) ^ 2) / 2

/-- The exact dyadic scalar majorant. -/
def dyadicBound (K r : ℝ) (j : ℕ) : ℝ := r ^ (2 ^ j) / K

theorem purityStep_nonneg (u : ℝ) : 0 ≤ purityStep u := by
  unfold purityStep
  positivity

/-- The squaring defect map is increasing on `[0,1)`. -/
theorem purityStep_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    purityStep a ≤ purityStep b := by
  have hbpos : 0 < 1 - b := sub_pos.mpr hb
  have hden : 0 < 2 * (1 - b) ^ 2 := by positivity
  have hnum : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have hsq : (1 - b) ^ 2 ≤ (1 - a) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact div_le_div₀ (sq_nonneg b) hnum hden (by nlinarith)

/-- Valid input defects give a valid transported defect. -/
theorem stairDefect_bounds {a b c : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ stairDefect a b c ∧ stairDefect a b c < 1 := by
  have hapos : 0 < 1 - a := sub_pos.mpr ha1
  have hbpos : 0 < 1 - b := sub_pos.mpr hb1
  have hcpos : 0 < 1 - c := sub_pos.mpr hc1
  have hp0 : 0 < (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c) := by positivity
  have hp1 : (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c) ≤ 1 := by
    calc
      (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c) ≤ 1 ^ 4 * 1 ^ 2 * 1 := by
        gcongr <;> linarith
      _ = 1 := by norm_num
  unfold stairDefect
  constructor <;> linarith

theorem stairDefect_same (u : ℝ) : stairDefect u u u = 1 - (1 - u) ^ 7 := by
  unfold stairDefect
  ring

/-- Exact geometric-series identity behind the quadratic coefficient. -/
theorem common_step_eq_G7 {u : ℝ} (hu : u < 1) :
    purityStep (stairDefect u u u) = G7 u * u ^ 2 := by
  have hne : 1 - u ≠ 0 := by linarith
  rw [stairDefect_same]
  unfold purityStep G7
  simp only [sub_sub_cancel, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  field_simp [hne]
  ring

/-- The dimension-two small-defect coefficient is exactly `49/2`. -/
theorem G7_zero : G7 0 = 49 / 2 := by
  norm_num [G7, Finset.sum_range_succ]

/-- The coefficient is increasing throughout the physical defect interval. -/
theorem G7_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) : G7 a ≤ G7 b := by
  have ha : a < 1 := hab.trans_lt hb
  have hapos : 0 < 1 - a := sub_pos.mpr ha
  have hbpos : 0 < 1 - b := sub_pos.mpr hb
  have hsa : 0 ≤ ∑ k ∈ Finset.range 7, ((1 - a) ^ (k + 1))⁻¹ := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hs : (∑ k ∈ Finset.range 7, ((1 - a) ^ (k + 1))⁻¹) ≤
      ∑ k ∈ Finset.range 7, ((1 - b) ^ (k + 1))⁻¹ := by
    apply Finset.sum_le_sum
    intro k hk
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact pow_le_pow_left₀ (by linarith) (by linarith) (k + 1)
  unfold G7
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hsa hs 2) (by norm_num)

/-- One endpoint coefficient certificate controls the whole initial interval. -/
theorem common_step_le_of_endpoint {u u0 K : ℝ} (hu : u ≤ u0) (hu0 : u0 < 1)
    (hG : G7 u0 ≤ K) : purityStep (stairDefect u u u) ≤ K * u ^ 2 := by
  rw [common_step_eq_G7 (hu.trans_lt hu0)]
  exact mul_le_mul_of_nonneg_right ((G7_mono hu hu0).trans hG) (sq_nonneg u)

/-- Replacing all three valid defects by a common upper bound is sound. -/
theorem stairDefect_le_common {a b c u : ℝ}
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u) (hu : u < 1) :
    stairDefect a b c ≤ stairDefect u u u := by
  have hp : (1 - u) ^ 4 * (1 - u) ^ 2 * (1 - u) ≤
      (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c) := by
    gcongr <;> linarith
  unfold stairDefect
  linarith

/-- Bernoulli's inequality supplies the seven-defect loss used after spatial
interpolation. This is scalar only; spatial interpolation is a separate input. -/
theorem seven_factor_lower {u : ℝ} (hu : u ≤ 1) :
    1 - 7 * u ≤ (1 - u) ^ 7 := by
  have h := one_add_mul_le_pow (a := -u) (by linarith) 7
  simpa only [Nat.cast_ofNat, mul_neg, sub_eq_add_neg] using h

/-- Two commuting-square transport bounds yield the `4,2,1` product. -/
theorem two_transports_product {A B C X Y : ℝ}
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hX : A ^ 2 * B ≤ X) (hY : X ^ 2 * C ≤ Y) :
    A ^ 4 * B ^ 2 * C ≤ Y := by
  calc
    A ^ 4 * B ^ 2 * C = (A ^ 2 * B) ^ 2 * C := by ring
    _ ≤ X ^ 2 * C := by gcongr
    _ ≤ Y := hY

/-- Convert actual purity bounds and a transport/squaring inequality into the
closed scalar staircase update. The probability-squaring theorem is a separate
input, not an axiom asserting a contraction or a spectral gap. -/
theorem transport_then_square_bound {A B C p d a b c : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hA : 1 - a ≤ A) (hB : 1 - b ≤ B) (hC : 1 - c ≤ C)
    (hp1 : p ≤ 1) (hp : A ^ 4 * B ^ 2 * C ≤ p)
    (hsquare : d ≤ purityStep (1 - p)) :
    d ≤ purityStep (stairDefect a b c) := by
  have hproduct : (1 - a) ^ 4 * (1 - b) ^ 2 * (1 - c) ≤ p := by
    apply le_trans _ hp
    gcongr <;> linarith
  have hdef : 1 - p ≤ stairDefect a b c := by
    unfold stairDefect
    linarith
  have hvalid := stairDefect_bounds ha0 ha1 hb0 hb1 hc0 hc1
  exact hsquare.trans (purityStep_mono (by linarith) hdef hvalid.2)

/-- A common scalar bound controls any one closed staircase update. -/
theorem one_component_contraction {a b c u K : ℝ}
    (ha0 : 0 ≤ a) (hau : a ≤ u) (hb0 : 0 ≤ b) (hbu : b ≤ u)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu : u < 1)
    (hcommon : purityStep (stairDefect u u u) ≤ K * u ^ 2) :
    purityStep (stairDefect a b c) ≤ K * u ^ 2 := by
  have habc := stairDefect_bounds ha0 (lt_of_le_of_lt hau hu)
    hb0 (lt_of_le_of_lt hbu hu) hc0 (lt_of_le_of_lt hcu hu)
  have huu := stairDefect_bounds (ha0.trans hau) hu
    (ha0.trans hau) hu (ha0.trans hau) hu
  exact (purityStep_mono habc.1 (stairDefect_le_common hau hbu hcu hu) huu.2).trans hcommon

/-- The sequential staircase closes: the second update uses the new first
component, and the third uses both new components. -/
theorem staircase_contraction {a b c a' b' c' u K : ℝ}
    (ha0 : 0 ≤ a) (hau : a ≤ u) (hb0 : 0 ≤ b) (hbu : b ≤ u)
    (hc0 : 0 ≤ c) (hcu : c ≤ u)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (_hc'0 : 0 ≤ c')
    (hu : u < 1) (hsmall : K * u ^ 2 ≤ u)
    (hcommon : purityStep (stairDefect u u u) ≤ K * u ^ 2)
    (hfirst : a' ≤ purityStep (stairDefect a b c))
    (hsecond : b' ≤ purityStep (stairDefect b c a'))
    (hthird : c' ≤ purityStep (stairDefect c a' b')) :
    a' ≤ K * u ^ 2 ∧ b' ≤ K * u ^ 2 ∧ c' ≤ K * u ^ 2 := by
  have ha' := hfirst.trans (one_component_contraction ha0 hau hb0 hbu hc0 hcu hu hcommon)
  have hb' := hsecond.trans (one_component_contraction hb0 hbu hc0 hcu ha'0
    (ha'.trans hsmall) hu hcommon)
  have hc' := hthird.trans (one_component_contraction hc0 hcu ha'0
    (ha'.trans hsmall) hb'0 (hb'.trans hsmall) hu hcommon)
  exact ⟨ha', hb', hc'⟩

theorem dyadicBound_zero (K r : ℝ) : dyadicBound K r 0 = r / K := by
  simp [dyadicBound]

/-- The doubly exponential closed form solves the exact quadratic recurrence. -/
theorem dyadicBound_succ {K r : ℝ} (hK : K ≠ 0) (j : ℕ) :
    dyadicBound K r (j + 1) = K * dyadicBound K r j ^ 2 := by
  unfold dyadicBound
  rw [pow_succ, pow_mul]
  field_simp [hK]

theorem dyadicBound_pos {K r : ℝ} (hK : 0 < K) (hr : 0 < r) (j : ℕ) :
    0 < dyadicBound K r j := by
  unfold dyadicBound
  positivity

/-- The rescaled bound remains strictly below one. -/
theorem mul_dyadicBound_lt_one {K r : ℝ} (hK : 0 < K)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    K * dyadicBound K r j < 1 := by
  have hp : r ^ (2 ^ j) < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
  unfold dyadicBound
  calc
    K * (r ^ (2 ^ j) / K) = r ^ (2 ^ j) := by field_simp [hK.ne']
    _ < 1 := hp

theorem dyadicBound_strict_decrease {K r : ℝ} (hK : 0 < K)
    (hr0 : 0 < r) (hr1 : r < 1) (j : ℕ) :
    dyadicBound K r (j + 1) < dyadicBound K r j := by
  rw [dyadicBound_succ hK.ne']
  have hp := dyadicBound_pos hK hr0 j
  have hs := mul_dyadicBound_lt_one hK hr0.le hr1 j
  calc
    K * dyadicBound K r j ^ 2 = (K * dyadicBound K r j) * dyadicBound K r j := by ring
    _ < 1 * dyadicBound K r j := mul_lt_mul_of_pos_right hs hp
    _ = dyadicBound K r j := one_mul _

/-- All dyadic bounds lie below the initial one. -/
theorem dyadicBound_le_initial {K r : ℝ} (hK : 0 < K)
    (hr0 : 0 < r) (hr1 : r < 1) (j : ℕ) :
    dyadicBound K r j ≤ r / K := by
  induction j with
  | zero => simp [dyadicBound]
  | succ j ih => exact (dyadicBound_strict_decrease hK hr0 hr1 j).le.trans ih

/-- The coefficient condition converts the seven-defect purity loss into the
strict exponential ratio required by the thermal gap argument. -/
theorem dyadic_seven_ratio_lt {K r : ℝ} (hK : 0 < K)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hmargin : 7 < K * (1 - 7 * (r / K))) (j : ℕ) :
    7 * dyadicBound K r j / (1 - 7 * dyadicBound K r j) < r ^ (2 ^ j) := by
  have hu := dyadicBound_le_initial hK hr0 hr1 j
  have hmarginj : 7 < K * (1 - 7 * dyadicBound K r j) := by nlinarith
  have hden : 0 < 1 - 7 * dyadicBound K r j :=
    (mul_pos_iff_of_pos_left hK).1 (lt_trans (by norm_num) hmarginj)
  have hp : 0 < r ^ (2 ^ j) := by positivity
  have hfactor : 7 / (K * (1 - 7 * dyadicBound K r j)) < 1 :=
    (div_lt_one (mul_pos hK hden)).2 hmarginj
  calc
    7 * dyadicBound K r j / (1 - 7 * dyadicBound K r j) =
        r ^ (2 ^ j) * (7 / (K * (1 - 7 * dyadicBound K r j))) := by
      unfold dyadicBound
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ < r ^ (2 ^ j) * 1 := mul_lt_mul_of_pos_left hfactor hp
    _ = r ^ (2 ^ j) := mul_one _

/-- The scalar bootstrap is valid at every scale, provided the common scalar
estimate holds throughout the initial interval. The three sequence values are
actual input defects, constrained by the explicitly stated staircase updates. -/
theorem dyadic_staircase_bound {a b c : ℕ → ℝ} {K r : ℝ}
    (hK : 0 < K) (hr0 : 0 < r) (hr1 : r < 1) (hu0 : r / K < 1)
    (hnonneg : ∀ j, 0 ≤ a j ∧ 0 ≤ b j ∧ 0 ≤ c j)
    (hseed : a 0 ≤ r / K ∧ b 0 ≤ r / K ∧ c 0 ≤ r / K)
    (hcommon : ∀ u : ℝ, 0 ≤ u → u ≤ r / K →
      purityStep (stairDefect u u u) ≤ K * u ^ 2)
    (hfirst : ∀ j, a (j + 1) ≤ purityStep (stairDefect (a j) (b j) (c j)))
    (hsecond : ∀ j, b (j + 1) ≤ purityStep (stairDefect (b j) (c j) (a (j + 1))))
    (hthird : ∀ j, c (j + 1) ≤ purityStep (stairDefect (c j) (a (j + 1)) (b (j + 1)))) :
    ∀ j, a j ≤ dyadicBound K r j ∧ b j ≤ dyadicBound K r j ∧
      c j ≤ dyadicBound K r j := by
  intro j
  induction j with
  | zero => simpa only [dyadicBound_zero] using hseed
  | succ j ih =>
    have hj0 := (dyadicBound_pos hK hr0 j).le
    have hjle := dyadicBound_le_initial hK hr0 hr1 j
    have hsmall : K * dyadicBound K r j ^ 2 ≤ dyadicBound K r j := by
      rw [← dyadicBound_succ hK.ne']
      exact (dyadicBound_strict_decrease hK hr0 hr1 j).le
    have hstep := staircase_contraction (hnonneg j).1 ih.1
      (hnonneg j).2.1 ih.2.1 (hnonneg j).2.2 ih.2.2
      (hnonneg (j + 1)).1 (hnonneg (j + 1)).2.1 (hnonneg (j + 1)).2.2
      (hjle.trans_lt hu0) hsmall (hcommon _ hj0 hjle)
      (hfirst j) (hsecond j) (hthird j)
    simpa only [dyadicBound_succ hK.ne'] using hstep

/-- The finite-seed scalar theorem with only the single endpoint `G₇` estimate. -/
theorem dyadic_staircase_bound_of_G7 {a b c : ℕ → ℝ} {K r : ℝ}
    (hK : 0 < K) (hr0 : 0 < r) (hr1 : r < 1) (hu0 : r / K < 1)
    (hG : G7 (r / K) ≤ K)
    (hnonneg : ∀ j, 0 ≤ a j ∧ 0 ≤ b j ∧ 0 ≤ c j)
    (hseed : a 0 ≤ r / K ∧ b 0 ≤ r / K ∧ c 0 ≤ r / K)
    (hfirst : ∀ j, a (j + 1) ≤ purityStep (stairDefect (a j) (b j) (c j)))
    (hsecond : ∀ j, b (j + 1) ≤ purityStep (stairDefect (b j) (c j) (a (j + 1))))
    (hthird : ∀ j, c (j + 1) ≤ purityStep (stairDefect (c j) (a (j + 1)) (b (j + 1)))) :
    ∀ j, a j ≤ dyadicBound K r j ∧ b j ≤ dyadicBound K r j ∧
      c j ≤ dyadicBound K r j := by
  apply dyadic_staircase_bound hK hr0 hr1 hu0 hnonneg hseed
  · intro u _ huu0
    exact common_step_le_of_endpoint huu0 hu0 hG
  · exact hfirst
  · exact hsecond
  · exact hthird

#print axioms common_step_eq_G7
#print axioms G7_mono
#print axioms transport_then_square_bound
#print axioms dyadicBound_succ
#print axioms dyadic_seven_ratio_lt
#print axioms dyadic_staircase_bound_of_G7

end

end BilayerGap

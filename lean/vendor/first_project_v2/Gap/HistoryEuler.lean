import Mathlib

/-!
# First-order product approximation in a real Banach algebra

This is the analytic ingredient for a discrete history transfer construction.
No convergence of partition functions is an assumption: a one-step derivative
at the identity suffices. The algebra is allowed to be noncommutative.
-/

noncomputable section
namespace BilayerGap.History
open Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

/-- A noncommutative telescoping estimate. No commutation premise is needed. -/
theorem norm_pow_sub_pow_le (x y : A) (R : ℝ) (hR : 1 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (n : ℕ) :
    ‖x^n-y^n‖ ≤ (n:ℝ)*R^n*‖x-y‖ := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x^(n+1)-y^(n+1) = (x^n-y^n)*x+y^n*(x-y) := by
      simp only [pow_succ, sub_mul, mul_sub]
      abel
    have hyn : ‖y^n‖ ≤ R^n :=
      (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg _) hy n)
    calc
      ‖x^(n+1)-y^(n+1)‖ ≤ ‖(x^n-y^n)*x‖+‖y^n*(x-y)‖ := by
        rw [heq]; exact norm_add_le _ _
      _ ≤ ‖x^n-y^n‖*‖x‖+‖y^n‖*‖x-y‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((n:ℝ)*R^n*‖x-y‖)*R+R^n*‖x-y‖ :=
        add_le_add (mul_le_mul ih hx (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right hyn (norm_nonneg _))
      _ ≤ ((n+1:ℕ):ℝ)*R^(n+1)*‖x-y‖ := by
        have hh := mul_le_mul_of_nonneg_right hR (show 0 ≤ R^n*‖x-y‖ by positivity)
        push_cast
        rw [pow_succ]
        nlinarith

/-- Uniform scalar power bound for a step whose norm grows only linearly. -/
theorem step_norm_power_bound (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    (1+C/((n:ℝ)+1))^(n+1) ≤ Real.exp C := by
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  calc
    (1+C/((n:ℝ)+1))^(n+1) ≤ (Real.exp (C/((n:ℝ)+1)))^(n+1) := by
      apply pow_le_pow_left₀ (by positivity)
      simpa [add_comm] using Real.add_one_le_exp (C/((n:ℝ)+1))
    _ = Real.exp C := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp

/-- Local consistency plus a linear stability bound implies convergence of
iterated steps to the exact exponential. The hypotheses concern one step,
not a power or a partition function. -/
theorem tendsto_pow_of_local_error (F : ℕ → A) (H : A) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ᶠ n in atTop, ‖F n‖ ≤ 1+C/((n:ℝ)+1))
    (hE : ∀ᶠ n : ℕ in atTop,
      ‖NormedSpace.exp ℝ ((1/((n:ℝ)+1)) • H)‖ ≤ 1+C/((n:ℝ)+1))
    (herr : Tendsto (fun (n : ℕ) => ((n:ℝ)+1)*
      ‖F n-NormedSpace.exp ℝ ((1/((n:ℝ)+1)) • H)‖) atTop (𝓝 0)) :
    Tendsto (fun n => (F n)^(n+1)) atTop (𝓝 (NormedSpace.exp ℝ H)) := by
  have hexact (n : ℕ) :
      (NormedSpace.exp ℝ ((1/((n:ℝ)+1)) • H))^(n+1) = NormedSpace.exp ℝ H := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    simp [Nat.cast_add, Nat.cast_one, hn]
  have hbound : ∀ᶠ n in atTop,
      ‖(F n)^(n+1)-NormedSpace.exp ℝ H‖ ≤ Real.exp C *
        (((n:ℝ)+1)*‖F n-NormedSpace.exp ℝ ((1/((n:ℝ)+1)) • H)‖) := by
    filter_upwards [hF, hE] with n hnF hnE
    rw [← hexact n]
    have hnR : 1 ≤ 1+C/((n:ℝ)+1) := le_add_of_nonneg_right (by positivity)
    refine (norm_pow_sub_pow_le (F n) _ _ hnR hnF hnE (n+1)).trans ?_
    have hp := step_norm_power_bound C hC n
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ ((n:ℝ)+1)*‖F n-NormedSpace.exp ℝ ((1/((n:ℝ)+1)) • H)‖ by positivity)
    simpa [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hbound ?_
  simpa using tendsto_const_nhds.mul herr

/-- Differentiability supplies the rescaled one-step slopes at reciprocal times. -/
theorem tendsto_discrete_slope (F : ℝ → A) (H : A)
    (hF : HasDerivAt F H 0) (h0 : F 0 = 1) :
    Tendsto (fun (n : ℕ) => ((n:ℝ)+1) • (F (1/((n:ℝ)+1))-1))
      atTop (𝓝 H) := by
  have ht : Tendsto (fun (n : ℕ) => (1/((n:ℝ)+1))) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun n => by change 0 < 1/((n:ℝ)+1); positivity)⟩
  simpa [h0, one_div, Function.comp_def] using hF.tendsto_slope_zero_right.comp ht

/-- A derivative at the identity supplies the linear stability estimate needed
for taking arbitrarily many steps. -/
theorem eventually_norm_step_le (F : ℝ → A) (H : A)
    (hF : HasDerivAt F H 0) (h0 : F 0 = 1) :
    ∀ᶠ n : ℕ in atTop, ‖F (1/((n:ℝ)+1))‖ ≤ 1+(‖H‖+1)/((n:ℝ)+1) := by
  have hb := (tendsto_discrete_slope F H hF h0).norm.eventually_le_const
    (show ‖H‖ < ‖H‖+1 by linarith)
  filter_upwards [hb] with n hn
  have hnpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have he : ‖F (1/((n:ℝ)+1))-1‖ ≤ (‖H‖+1)/((n:ℝ)+1) := by
    rw [norm_smul, Real.norm_of_nonneg hnpos.le] at hn
    exact (le_div_iff₀ hnpos).mpr (by simpa [mul_comm] using hn)
  calc
    ‖F (1/((n:ℝ)+1))‖ = ‖(F (1/((n:ℝ)+1))-1)+1‖ := by congr 1; abel
    _ ≤ ‖F (1/((n:ℝ)+1))-1‖+‖(1:A)‖ := norm_add_le _ _
    _ ≤ 1+(‖H‖+1)/((n:ℝ)+1) := by rw [norm_one]; linarith

/-- The Euler/Chernoff limit for any differentiable one-step map at the
identity in a real Banach algebra. In particular this applies to an explicitly
constructed matching polynomial, rather than assuming a transfer limit. -/
theorem tendsto_pow_of_hasDerivAt (F : ℝ → A) (H : A)
    (h0 : F 0 = 1) (hF : HasDerivAt F H 0) :
    Tendsto (fun (n : ℕ) => (F (1/((n:ℝ)+1)))^(n+1))
      atTop (𝓝 (NormedSpace.exp ℝ H)) := by
  let E : ℝ → A := fun t => NormedSpace.exp ℝ (t • H)
  have hE0 : E 0 = 1 := by simp [E]
  have hE : HasDerivAt E H 0 := by
    simpa [E] using hasDerivAt_exp_smul_const H (0:ℝ)
  apply tendsto_pow_of_local_error (fun n => F (1/((n:ℝ)+1))) H (‖H‖+1)
    (by positivity) (eventually_norm_step_le F H hF h0)
    (eventually_norm_step_le E H hE hE0)
  have hs := ((tendsto_discrete_slope F H hF h0).sub
    (tendsto_discrete_slope E H hE hE0)).norm
  convert hs using 1
  · ext n
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul]
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)]
  · simp

#print axioms tendsto_pow_of_hasDerivAt

end BilayerGap.History

import Mathlib

/-!
# Finite Taylor operators with actual operator-norm bounds

Hard-core creation sums are nilpotent, so finite Taylor operators suffice for
the dressed trial. No normalizable infinite Fock vector is needed here.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- The first `m` Taylor terms as a bounded linear operator. -/
def taylorOperator (S : E →L[ℝ] E) (m : ℕ) : E →L[ℝ] E :=
  ∑ k ∈ Finset.range m, ((k.factorial : ℝ)⁻¹) • S^k

/-- The operator norm is bounded by the scalar exponential for every cutoff. -/
theorem norm_taylorOperator_le (S : E →L[ℝ] E) (m : ℕ) :
    ‖taylorOperator S m‖ ≤ Real.exp ‖S‖ := by
  unfold taylorOperator
  calc
    ‖∑ k ∈ Finset.range m, ((k.factorial : ℝ)⁻¹) • S^k‖ ≤
        ∑ k ∈ Finset.range m, ‖((k.factorial : ℝ)⁻¹) • S^k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, ‖S‖^k/(k.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h := mul_le_mul_of_nonneg_left (norm_pow_le S k)
        (by positivity : 0 ≤ (k.factorial : ℝ)⁻¹)
      simpa only [div_eq_mul_inv, mul_comm] using h
    _ ≤ Real.exp ‖S‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) m

/-- Isolating the vacuum term retains the norm of `S vacuum`, not just `S`. -/
theorem taylorOperator_sub_identity (S : E →L[ℝ] E) (m : ℕ) (x : E) :
    taylorOperator S (m+1) x-x =
      ∑ k ∈ Finset.range m, (((k+1).factorial : ℝ)⁻¹) • ((S^k) (S x)) := by
  simp [taylorOperator, Finset.sum_range_succ', ContinuousLinearMap.sum_apply,
    pow_succ, ContinuousLinearMap.mul_apply]

/-- A finite dressed vector stays close to its vacuum by the first-created
vector norm, which is substantially sharper than a bare operator norm. -/
theorem norm_taylorOperator_sub_le (S : E →L[ℝ] E) (m : ℕ) (x : E) :
    ‖taylorOperator S (m+1) x-x‖ ≤ Real.exp ‖S‖*‖S x‖ := by
  rw [taylorOperator_sub_identity]
  calc
    ‖∑ k ∈ Finset.range m, (((k+1).factorial : ℝ)⁻¹) • ((S^k) (S x))‖ ≤
        ∑ k ∈ Finset.range m, ‖(((k+1).factorial : ℝ)⁻¹) • ((S^k) (S x))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (‖S‖^k/(k.factorial : ℝ))*‖S x‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hp := (S^k).le_opNorm (S x)
      have hpow := mul_le_mul_of_nonneg_right (norm_pow_le S k) (norm_nonneg (S x))
      have hf : (k.factorial : ℝ) ≤ ((k+1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (Nat.le_succ k)
      have hinv : (((k+1).factorial : ℝ)⁻¹) ≤ (k.factorial : ℝ)⁻¹ :=
        inv_anti₀ (by positivity) hf
      calc
        _ ≤ (((k+1).factorial : ℝ)⁻¹)*(‖S‖^k*‖S x‖) :=
          mul_le_mul_of_nonneg_left (hp.trans hpow) (by positivity)
        _ ≤ ((k.factorial : ℝ)⁻¹)*(‖S‖^k*‖S x‖) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
        _ = _ := by ring
    _ = (∑ k ∈ Finset.range m, ‖S‖^k/(k.factorial : ℝ))*‖S x‖ := by
      rw [Finset.sum_mul]
    _ ≤ Real.exp ‖S‖*‖S x‖ :=
      mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (norm_nonneg _) m) (norm_nonneg _)

/-- A fixed rational amplification constant, proved from an explicit finite
Taylor remainder estimate rather than floating point. -/
theorem exp_nine_tenths_lt : Real.exp (9/10 : ℝ) < 5/2 := by
  have h := Real.exp_bound' (x := (9/10 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The usable finite-operator amplification bound in the smaller checkpoint. -/
theorem norm_taylorOperator_le_five_halves (S : E →L[ℝ] E)
    (hS : ‖S‖≤9/10) (m : ℕ) : ‖taylorOperator S m‖ ≤ 5/2 :=
  (norm_taylorOperator_le S m).trans ((Real.exp_le_exp.mpr hS).trans exp_nine_tenths_lt.le)

local instance : Module ℚ (E →L[ℝ] E) :=
  Module.compHom (E →L[ℝ] E) (Rat.castHom ℝ)

/-- The algebraic nilpotent exponential is exactly the finite operator polynomial. -/
theorem nilpotent_exp_eq_taylor (S : E →L[ℝ] E) (m : ℕ) (hS : S^m=0) :
    IsNilpotent.exp S = taylorOperator S m := by
  rw [IsNilpotent.exp_eq_sum hS, taylorOperator]
  apply Finset.sum_congr rfl
  intro k _
  simpa using ratCast_smul_eq ℚ ℝ ((k.factorial : ℚ)⁻¹) (S^k)

/-- No cutoff-dependent loss appears for the exact finite nilpotent exponential. -/
theorem norm_nilpotent_exp_le (S : E →L[ℝ] E) (hS : IsNilpotent S) :
    ‖IsNilpotent.exp S‖ ≤ Real.exp ‖S‖ := by
  obtain ⟨m,hm⟩ := hS
  rw [nilpotent_exp_eq_taylor S m hm]
  exact norm_taylorOperator_le S m

/-- The vacuum improvement also holds for the exact algebraic exponential. -/
theorem norm_nilpotent_exp_sub_le (S : E →L[ℝ] E) (hS : IsNilpotent S) (x : E) :
    ‖(IsNilpotent.exp S) x-x‖ ≤ Real.exp ‖S‖*‖S x‖ := by
  obtain ⟨m,hm⟩ := hS
  have hm1 : S^(m+1)=0 := by rw [pow_succ, hm, zero_mul]
  rw [nilpotent_exp_eq_taylor S (m+1) hm1]
  exact norm_taylorOperator_sub_le S m x

end BilayerDressed

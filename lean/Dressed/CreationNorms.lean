import Dressed.GlobalCreation

/-!
# Genuine Euclidean operator norm of finite hard-core creation

The norm in this file is the norm of `Matrix.toEuclideanCLM`, hence the Hilbert
space operator norm, not the default entrywise matrix norm.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Matrix
namespace BilayerDressed
set_option maxHeartbeats 1000000
open BilayerGap.Torus
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev ConfigurationHilbert (V : Type*) [Fintype V] := EuclideanSpace ℝ (Configuration V)

/-- The exact nonzero entry in a hard-core creation row. -/
theorem globalCreate_entry (v : V) (α : Fin 3) (s t : Configuration V) :
    globalCreate v α s t =
      if s v = α.succ then if t = Function.update s v 0 then 1 else 0 else 0 := by
  classical
  have he : ((∀ w, w ≠ v → s w = t w) ∧ t v = 0) ↔
      t = Function.update s v 0 := by
    constructor
    · rintro ⟨hout, hv⟩
      funext w
      by_cases hw : w = v
      · subst w; simpa using hv
      · simpa [Function.update_of_ne hw] using (hout w hw).symm
    · intro ht
      subst t
      exact ⟨fun w hw => by simp [Function.update_of_ne hw], by simp⟩
  simp only [globalCreate, siteLift, rungCreate, Matrix.single, Matrix.of_apply]
  have hc : ((∀ w, w ≠ v → s w = t w) ∧ (α.succ = s v ∧ 0 = t v)) ↔
      (s v = α.succ ∧ t = Function.update s v 0) := by
    constructor
    · rintro ⟨ho, ha, hb⟩
      exact ⟨ha.symm, he.mp ⟨ho, hb.symm⟩⟩
    · rintro ⟨ha, hb⟩
      have hh := he.mpr hb
      exact ⟨hh.1, ha.symm, hh.2.symm⟩
  rw [← ite_and]
  simp only [hc, ite_and]

/-- Exact action: erase the triplet at the output site to find its input coefficient. -/
theorem globalCreate_mulVec (v : V) (α : Fin 3) (x : Configuration V → ℝ)
    (s : Configuration V) :
    (globalCreate v α *ᵥ x) s =
      if s v = α.succ then x (Function.update s v 0) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, globalCreate_entry]
  by_cases hs : s v = α.succ <;> simp [hs]

/-- Swap the vacuum and the chosen triplet at one site, a true configuration permutation. -/
def creationSwap (v : V) (α : Fin 3) : Configuration V ≃ Configuration V :=
  Equiv.piCongrRight fun w => if w = v then Equiv.swap 0 α.succ else Equiv.refl _

theorem creationSwap_of_occupied (v : V) (α : Fin 3) (s : Configuration V)
    (hs : s v = α.succ) : creationSwap v α s = Function.update s v 0 := by
  classical
  funext w
  by_cases hw : w = v
  · subst w
    simp [creationSwap, Equiv.piCongrRight, hs]
  · simp [creationSwap, Equiv.piCongrRight, hw, Function.update_of_ne hw]

/-- The actual creation matrix is a contraction on the finite configuration Hilbert space. -/
theorem globalCreate_norm_apply_le (v : V) (α : Fin 3) (x : ConfigurationHilbert V) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x‖ ≤ ‖x‖ := by
  classical
  have hsq : ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ s : Configuration V, ‖x (creationSwap v α s)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro s _
        change ‖(globalCreate v α *ᵥ (fun t => x t)) s‖ ^ 2 ≤ _
        rw [globalCreate_mulVec]
        by_cases hs : s v = α.succ
        · rw [if_pos hs, creationSwap_of_occupied v α s hs]
        · simp [hs, sq_nonneg]
      _ = _ := (creationSwap v α).sum_comp (fun s => ‖x s‖ ^ 2)
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x), norm_nonneg x]

/-- Uniform dimension-independent bound in the genuine Hilbert operator norm. -/
theorem globalCreate_opNorm_le_one (v : V) (α : Fin 3) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using globalCreate_norm_apply_le v α x

/-- Different triplet colors at the same output site have orthogonal ranges. -/
theorem globalCreate_inner_zero_of_color_ne (v : V) (α β : Fin 3) (hαβ : α ≠ β)
    (x y : ConfigurationHilbert V) :
    ⟪Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x,
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v β) y⟫ = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro s _
  change ⟪(globalCreate v α *ᵥ (fun t => x t)) s,
    (globalCreate v β *ᵥ (fun t => y t)) s⟫ = 0
  rw [globalCreate_mulVec, globalCreate_mulVec]
  by_cases hs : s v = α.succ
  · have ht : s v ≠ β.succ := by
      intro ht
      exact hαβ (Fin.succ_injective _ (hs.symm.trans ht))
    simp [hs, hαβ]
  · simp [hs]

/-- Pythagoras for the three actual color channels of a pair creation. -/
theorem pairCreate_norm_sq_eq_sum (u v : V) (x : ConfigurationHilbert V) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate u v) x‖ ^ 2 =
      ∑ α : Fin 3, ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
          (globalCreate u α)
        (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x)‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  unfold pairCreate
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_mul,
    ContinuousLinearMap.mul_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_eq_single α]
  · exact real_inner_self_eq_norm_sq _
  · intro β _ hβα
    exact globalCreate_inner_zero_of_color_ne u β α hβα
      (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v β) x)
      (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x)
  · simp

/-- The true pair-creation norm is at most √3, uniformly in the site count. -/
theorem pairCreate_norm_apply_le_sqrt_three (u v : V) (x : ConfigurationHilbert V) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate u v) x‖ ≤
      Real.sqrt 3 * ‖x‖ := by
  have hsq : ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (pairCreate u v) x‖ ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
    rw [pairCreate_norm_sq_eq_sum]
    calc
      _ ≤ ∑ _α : Fin 3, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro α _
        have h1 := globalCreate_norm_apply_le u α
          (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v α) x)
        have h2 := globalCreate_norm_apply_le v α x
        exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = _ := by simp
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hrhs : 0 ≤ Real.sqrt 3 * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).mp
  simpa only [mul_pow, hsqrt] using hsq

/-- Genuine Hilbert operator norm, not the default matrix norm. -/
theorem pairCreate_opNorm_le_sqrt_three (u v : V) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairCreate u v)‖ ≤ Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact pairCreate_norm_apply_le_sqrt_three u v

end BilayerDressed

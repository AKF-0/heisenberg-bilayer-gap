import Dressed.CreationNorms

/-!
# Orthogonal-color bounds in the actual finite hard-core Hilbert space

The output color sectors are orthogonal for the concrete creation matrices.
The coefficient vectors may be arbitrary and correlated. No Gaussian state,
Wick rule, independence assumption, or entrywise matrix norm is used.
-/
noncomputable section
namespace BilayerDressed.ColorSector
open Matrix
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pythagoras for any finite family of genuinely orthogonal Hilbert vectors. -/
theorem orthogonal_sum_norm_sq {I : Type*} [Fintype I]
    (y : I → ConfigurationHilbert V)
    (hy : ∀ i j, i ≠ j → ⟪y i,y j⟫ = 0) :
    ‖∑ i,y i‖^2 = ∑ i,‖y i‖^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hji
    apply hy
    aesop
  · simp

/-- A same-site creation channel acting on a genuine Hilbert vector. -/
def singleAction (u : V) (α : Fin 3) (x : ConfigurationHilbert V) :
    ConfigurationHilbert V :=
  Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate u α) x

/-- The two-color output of two concrete creation operators. -/
def pairAction (u v : V) (p : Fin 3 × Fin 3) (x : ConfigurationHilbert V) :
    ConfigurationHilbert V := singleAction u p.1 (singleAction v p.2 x)

/-- Exact interchange of the two physical creation factors. -/
theorem pairAction_swap (u v : V) (p : Fin 3 × Fin 3) (x : ConfigurationHilbert V) :
    pairAction u v p x = pairAction v u (p.2,p.1) x := by
  have hh := congrArg
    (fun A : ConfigurationMatrix V =>
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) A x)
    (global_creation_commute u v p.1 p.2).eq
  simpa only [map_mul, ContinuousLinearMap.mul_apply, pairAction, singleAction] using hh

/-- Different output colors at one site are orthogonal for arbitrary inputs. -/
theorem singleAction_orthogonal (u : V) (α β : Fin 3) (hαβ : α ≠ β)
    (x y : ConfigurationHilbert V) :
    ⟪singleAction u α x,singleAction u β y⟫ = 0 :=
  globalCreate_inner_zero_of_color_ne u α β hαβ x y

/-- Different output color pairs are orthogonal, even for correlated coefficient vectors. -/
theorem pairAction_orthogonal (u v : V) (p q : Fin 3 × Fin 3) (hpq : p ≠ q)
    (x y : ConfigurationHilbert V) :
    ⟪pairAction u v p x,pairAction u v q y⟫ = 0 := by
  by_cases h₁ : p.1 = q.1
  · have h₂ : p.2 ≠ q.2 := fun h₂ => hpq (Prod.ext h₁ h₂)
    rw [pairAction_swap u v p x, pairAction_swap u v q y]
    exact singleAction_orthogonal v p.2 q.2 h₂ _ _
  · exact singleAction_orthogonal u p.1 q.1 h₁ _ _

theorem singleAction_norm_le (u : V) (α : Fin 3) (x : ConfigurationHilbert V) :
    ‖singleAction u α x‖ ≤ ‖x‖ := globalCreate_norm_apply_le u α x

theorem pairAction_norm_le (u v : V) (p : Fin 3 × Fin 3) (x : ConfigurationHilbert V) :
    ‖pairAction u v p x‖ ≤ ‖x‖ :=
  (singleAction_norm_le u p.1 _).trans (singleAction_norm_le v p.2 x)

/-- Exact one-site Pythagoras, with arbitrary color-dependent input vectors. -/
theorem single_sum_norm_sq (u : V) (x : Fin 3 → ConfigurationHilbert V) :
    ‖∑ α,singleAction u α (x α)‖^2 = ∑ α,‖singleAction u α (x α)‖^2 :=
  orthogonal_sum_norm_sq _ (fun α β hαβ => singleAction_orthogonal u α β hαβ _ _)

/-- Exact two-site Pythagoras for all nine output colors. No distinct-site assumption is needed:
when the two endpoints coincide every hard-core two-creation product is zero. -/
theorem pair_sum_norm_sq (u v : V) (x : (Fin 3 × Fin 3) → ConfigurationHilbert V) :
    ‖∑ p,pairAction u v p (x p)‖^2 = ∑ p,‖pairAction u v p (x p)‖^2 :=
  orthogonal_sum_norm_sq _ (fun p q hpq => pairAction_orthogonal u v p q hpq _ _)

/-- The one-site color factor is sqrt(3), not a triangle-inequality factor 3. -/
theorem single_sum_norm_le (u : V) (x : Fin 3 → ConfigurationHilbert V)
    (b : ℝ) (hb : 0 ≤ b) (hx : ∀ α,‖x α‖ ≤ b) :
    ‖∑ α,singleAction u α (x α)‖ ≤ Real.sqrt 3 * b := by
  have hs : ‖∑ α,singleAction u α (x α)‖^2 ≤ 3*b^2 := by
    rw [single_sum_norm_sq]
    calc
      _ ≤ ∑ _α : Fin 3,b^2 := Finset.sum_le_sum fun α _ =>
        pow_le_pow_left₀ (norm_nonneg _) ((singleAction_norm_le u α _).trans (hx α)) 2
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hs

/-- The two-site color factor is 3, not a triangle-inequality factor 9. -/
theorem pair_sum_norm_le (u v : V) (x : (Fin 3 × Fin 3) → ConfigurationHilbert V)
    (b : ℝ) (hb : 0 ≤ b) (hx : ∀ p,‖x p‖ ≤ b) :
    ‖∑ p,pairAction u v p (x p)‖ ≤ 3*b := by
  have hs : ‖∑ p,pairAction u v p (x p)‖^2 ≤ 9*b^2 := by
    rw [pair_sum_norm_sq]
    calc
      _ ≤ ∑ _p : Fin 3 × Fin 3,b^2 := Finset.sum_le_sum fun p _ =>
        pow_le_pow_left₀ (norm_nonneg _) ((pairAction_norm_le u v p _).trans (hx p)) 2
      _ = _ := by simp
  nlinarith [norm_nonneg (∑ p,pairAction u v p (x p))]

/-- The requested quadratic input bound for quartic/sextic residual terms. -/
theorem pair_sum_norm_le_three_sq (u v : V)
    (x : (Fin 3 × Fin 3) → ConfigurationHilbert V) (l : ℝ)
    (hx : ∀ p,‖x p‖ ≤ l^2) :
    ‖∑ p,pairAction u v p (x p)‖ ≤ 3*l^2 :=
  pair_sum_norm_le u v x (l^2) (sq_nonneg l) hx

/-- Curried-index interface displaying the actual two physical matrix actions. -/
theorem double_creation_sum_norm_le (u v : V)
    (x : Fin 3 → Fin 3 → ConfigurationHilbert V) (b : ℝ) (hb : 0 ≤ b)
    (hx : ∀ α β,‖x α β‖ ≤ b) :
    ‖∑ α,∑ β,
      Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate u α)
        (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (globalCreate v β)
          (x α β))‖ ≤ 3*b := by
  simpa only [Fintype.sum_prod_type, pairAction, singleAction] using
    pair_sum_norm_le u v (fun p => x p.1 p.2) b hb (fun p => hx p.1 p.2)

/-- The same one-site factor holds in the genuine Hilbert operator norm. -/
theorem single_creation_sum_opNorm_le (u : V) (A : Fin 3 → ConfigurationMatrix V)
    (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ α,‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A α)‖ ≤ b) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (∑ α,globalCreate u α * A α)‖ ≤ Real.sqrt 3*b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hb)
  intro x
  have hx : ∀ α,
      ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A α) x‖ ≤ b*‖x‖ := by
    intro α
    exact (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hA α) (norm_nonneg x))
  have hh := single_sum_norm_le u
    (fun α => Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A α) x)
    (b*‖x‖) (mul_nonneg hb (norm_nonneg x)) hx
  simpa only [map_sum, ContinuousLinearMap.sum_apply, map_mul,
    ContinuousLinearMap.mul_apply, singleAction, mul_assoc] using hh

/-- The factor 3 also bounds arbitrary two-site coefficient operators; no Wick rule is used. -/
theorem double_creation_sum_opNorm_le (u v : V)
    (A : Fin 3 → Fin 3 → ConfigurationMatrix V) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ α β,‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A α β)‖ ≤ b) :
    ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
      (∑ α,∑ β,globalCreate u α * globalCreate v β * A α β)‖ ≤ 3*b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hb)
  intro x
  have hx : ∀ p : Fin 3 × Fin 3,
      ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A p.1 p.2) x‖ ≤ b*‖x‖ := by
    intro p
    exact (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hA p.1 p.2) (norm_nonneg x))
  have hh := pair_sum_norm_le u v
    (fun p => Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (A p.1 p.2) x)
    (b*‖x‖) (mul_nonneg hb (norm_nonneg x)) hx
  simpa only [map_sum, ContinuousLinearMap.sum_apply, map_mul,
    ContinuousLinearMap.mul_apply, Fintype.sum_prod_type, pairAction, singleAction,
    mul_assoc] using hh

end BilayerDressed.ColorSector

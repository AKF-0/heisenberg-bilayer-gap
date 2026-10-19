import Dressed.PairVacuumNorm
import Dressed.ColorSectorBounds

/-!
# Exact three-matching Gram matrix on four distinct physical sites

The vectors are actual products of the frozen same-color pair creation matrices
acting on the actual vacuum. They are reduced to physical tensor basis columns;
the finite color count then gives diagonal Gram entry nine and off-diagonal
entry three. No Wick rule or independent tensor-norm premise is introduced.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticMatching
open Matrix
set_option maxHeartbeats 1800000
set_option maxRecDepth 20000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The physical configuration with prescribed triplet colors at four sites. -/
def configuration (v : Fin 4 → V) (c : Fin 4 → Fin 3) : Configuration V :=
  Function.update (Function.update (Function.update (Function.update vacuumConfiguration
    (v 3) (c 3).succ) (v 2) (c 2).succ) (v 1) (c 1).succ) (v 0) (c 0).succ

/-- The actual four physical creation factors, in a fixed site order. -/
def fourCreator (v : Fin 4 → V) (c : Fin 4 → Fin 3) : ConfigurationMatrix V :=
  globalCreate (v 0) (c 0) * globalCreate (v 1) (c 1) *
    globalCreate (v 2) (c 2) * globalCreate (v 3) (c 3)

def coloredVector (v : Fin 4 → V) (c : Fin 4 → Fin 3) : ConfigurationHilbert V :=
  Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (fourCreator v c) vacuumVector

omit [Fintype V] in
theorem configuration_at (v : Fin 4 → V) (hv : Function.Injective v)
    (c : Fin 4 → Fin 3) (i : Fin 4) : configuration v c (v i) = (c i).succ := by
  fin_cases i <;> simp [configuration, hv.eq_iff]

omit [Fintype V] in
theorem configuration_off (v : Fin 4 → V) (c : Fin 4 → Fin 3) (w : V)
    (hw : w ∉ Set.range v) : configuration v c w = 0 := by
  have hn (i : Fin 4) : w ≠ v i := by intro h; exact hw ⟨i,h.symm⟩
  simp [configuration, hn, vacuumConfiguration]

theorem configuration_injective (v : Fin 4 → V) (hv : Function.Injective v) :
    Function.Injective (configuration v) := by
  intro c d h
  funext i
  have hi := congrFun h (v i)
  rw [configuration_at v hv, configuration_at v hv] at hi
  exact Fin.succ_injective _ hi

theorem configuration_support (v : Fin 4 → V) (hv : Function.Injective v)
    (c : Fin 4 → Fin 3) (w : V) : configuration v c w ≠ 0 ↔ w ∈ Set.range v := by
  constructor
  · intro h
    by_contra hn
    exact h (configuration_off v c w hn)
  · rintro ⟨i,rfl⟩
    rw [configuration_at v hv]
    exact Fin.succ_ne_zero _

theorem configuration_eq_implies_range_eq (v w : Fin 4 → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (c d : Fin 4 → Fin 3) (h : configuration v c = configuration w d) :
    Set.range v = Set.range w := by
  ext x
  rw [← configuration_support v hv c x, ← configuration_support w hw d x, h]

/-- The genuine four-creator vector is exactly one normalized physical basis column. -/
theorem coloredVector_eq_single (v : Fin 4 → V) (hv : Function.Injective v)
    (c : Fin 4 → Fin 3) :
    coloredVector v c = EuclideanSpace.single (configuration v c) 1 := by
  simp only [coloredVector, fourCreator, map_mul, ContinuousLinearMap.mul_apply]
  simp [vacuumVector, globalCreate_single, configuration, vacuumConfiguration, hv.eq_iff]

/-- Three perfect matchings, carrying one independent color on each pair. -/
def colors (m : Fin 3) (p : Fin 3 × Fin 3) : Fin 4 → Fin 3 :=
  (![![p.1,p.1,p.2,p.2], ![p.1,p.2,p.1,p.2], ![p.1,p.2,p.2,p.1]]) m

/-- Q01 Q23, Q02 Q13, Q03 Q12, using the actual frozen pair matrices. -/
def matchingOperator (v : Fin 4 → V) (m : Fin 3) : ConfigurationMatrix V :=
  (![pairCreate (v 0) (v 1) * pairCreate (v 2) (v 3),
     pairCreate (v 0) (v 2) * pairCreate (v 1) (v 3),
     pairCreate (v 0) (v 3) * pairCreate (v 1) (v 2)]) m

def matchingVector (v : Fin 4 → V) (m : Fin 3) : ConfigurationHilbert V :=
  Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (matchingOperator v m) vacuumVector

/-- Exact finite operator expansion, including the necessary creator reordering. -/
theorem matchingOperator_expansion (v : Fin 4 → V) (m : Fin 3) :
    matchingOperator v m = ∑ p : Fin 3 × Fin 3, fourCreator v (colors m p) := by
  fin_cases m
  · simp [matchingOperator, colors, fourCreator,
      pairCreate, Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    simp [Matrix.mul_assoc]
  · simp [matchingOperator, colors,
      fourCreator, pairCreate, Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (globalCreate (v 2) α) (globalCreate (v 1) β),
      (global_creation_commute (v 2) (v 1) α β).eq]
    simp only [Matrix.mul_assoc]
  · simp [matchingOperator, colors,
      fourCreator, pairCreate, Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    simp only [Matrix.mul_assoc]
    rw [((global_creation_commute (v 3) (v 1) α β).mul_right
      (global_creation_commute (v 3) (v 2) α β)).eq]
    simp only [Matrix.mul_assoc]

theorem matchingVector_expansion (v : Fin 4 → V) (m : Fin 3) :
    matchingVector v m = ∑ p : Fin 3 × Fin 3, coloredVector v (colors m p) := by
  simp only [matchingVector, matchingOperator_expansion, map_sum,
    ContinuousLinearMap.sum_apply, coloredVector]

theorem coloredVector_inner (v : Fin 4 → V) (hv : Function.Injective v)
    (c d : Fin 4 → Fin 3) :
    ⟪coloredVector v c, coloredVector v d⟫ = if c = d then 1 else 0 := by
  rw [coloredVector_eq_single v hv, coloredVector_eq_single v hv]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
    (configuration_injective v hv).eq_iff]

/-- A small exact finite color count, checked by the kernel. -/
theorem color_count : ∀ m n : Fin 3,
    (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
      if colors m p = colors n q then (1 : ℕ) else 0) = if m = n then 9 else 3 := by
  decide +kernel

/-- The actual three-matching Gram matrix has diagonal nine and off-diagonal three. -/
theorem matching_gram (v : Fin 4 → V) (hv : Function.Injective v) (m n : Fin 3) :
    ⟪matchingVector v m, matchingVector v n⟫ = if m = n then 9 else 3 := by
  rw [matchingVector_expansion, matchingVector_expansion]
  simp only [sum_inner, inner_sum, coloredVector_inner v hv]
  rw [Finset.sum_comm]
  have h := congrArg (fun t : ℕ => (t : ℝ)) (color_count m n)
  simpa only [Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] using h

/-- The exact physical Hilbert norm of an arbitrary real matching combination. -/
theorem matching_combination_norm_sq (v : Fin 4 → V) (hv : Function.Injective v)
    (c : Fin 3 → ℝ) :
    ‖∑ m : Fin 3, c m • matchingVector v m‖^2 =
      6 * (∑ m : Fin 3, (c m)^2) + 3 * (∑ m : Fin 3, c m)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, matching_gram v hv]
  simp [Fin.sum_univ_succ]
  ring

/-- Different actual four-site support sets give orthogonal basis columns. -/
theorem coloredVector_inner_zero_of_support_ne (v w : Fin 4 → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hsupport : Set.range v ≠ Set.range w) (c d : Fin 4 → Fin 3) :
    ⟪coloredVector v c, coloredVector w d⟫ = 0 := by
  have hne : configuration v c ≠ configuration w d :=
    fun h => hsupport (configuration_eq_implies_range_eq v w hv hw c d h)
  rw [coloredVector_eq_single v hv, coloredVector_eq_single w hw]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hne]

/-- Orthogonality is by occupied support, not by a fictional independence premise. -/
theorem matching_inner_zero_of_support_ne (v w : Fin 4 → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hsupport : Set.range v ≠ Set.range w) (m n : Fin 3) :
    ⟪matchingVector v m, matchingVector w n⟫ = 0 := by
  rw [matchingVector_expansion, matchingVector_expansion]
  simp only [sum_inner, inner_sum, coloredVector_inner_zero_of_support_ne v w hv hw hsupport,
    Finset.sum_const_zero]

/-- Arbitrary matching coefficients retain cross-support orthogonality. -/
theorem combination_inner_zero_of_support_ne (v w : Fin 4 → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hsupport : Set.range v ≠ Set.range w) (c d : Fin 3 → ℝ) :
    ⟪∑ m, c m • matchingVector v m, ∑ n, d n • matchingVector w n⟫ = 0 := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    matching_inner_zero_of_support_ne v w hv hw hsupport, mul_zero, Finset.sum_const_zero]

end BilayerDressed.QuarticMatching

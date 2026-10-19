import Dressed.FinitePairCommutator
import Dressed.FiniteOccupationRotatedWords

/-!
# Actual finite graded pair-power norm recursion

This module applies the proved finite pair commutator to genuine Euclidean
occupation vectors.  The missing top-grade creations are never restored.
The adjoint step uses finite Cauchy--Schwarz, not an assumed pair norm bound.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOccupation.TotalCutoff.PairNorm
open Matrix
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Hilbert (V : Type*) [Fintype V] (M N : ℕ) := EuclideanSpace ℝ (Basis V M N)

/-- Exact total-degree support in the actual finite Euclidean Hilbert space. -/
def HasGrade {M N : ℕ} (n : ℕ) (x : Hilbert V M N) : Prop :=
  ∀ μ, totalDegree μ.val ≠ n → x μ = 0

/-- The actual pair-creation linear action. -/
def action {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) :
    Hilbert V M N →ₗ[ℝ] Hilbert V M N := (Pair.pairCreate B).toEuclideanLin

/-- Its actual real-transpose adjoint action. -/
def adjointAction {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) :
    Hilbert V M N →ₗ[ℝ] Hilbert V M N := (Pair.pairCreate B).transpose.toEuclideanLin

theorem grade_action {M N n : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    {x : Hilbert V M N} (hx : HasGrade n x) : HasGrade (n + 2) (action B x) := by
  intro ν hν
  change (WithLp.ofLp ((Pair.pairCreate B).toEuclideanLin x)) ν = 0
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro μ _
  by_cases hμ : totalDegree μ.val = n
  · rw [Pair.pairCreate_eq_zero_of_degree B ν μ (by omega), zero_mul]
  · change _ * x μ = 0
    rw [hx μ hμ, mul_zero]

theorem grade_adjointAction {M N n : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    {x : Hilbert V M N} (hx : HasGrade (n + 2) x) : HasGrade n (adjointAction B x) := by
  intro ν hν
  change (WithLp.ofLp ((Pair.pairCreate B).transpose.toEuclideanLin x)) ν = 0
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro μ _
  by_cases hμ : totalDegree μ.val = n + 2
  · rw [Matrix.transpose_apply, Pair.pairCreate_eq_zero_of_degree B μ ν (by omega), zero_mul]
  · change _ * x μ = 0
    rw [hx μ hμ, mul_zero]

theorem adjointAction_eq_zero_of_grade_zero {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) {x : Hilbert V M N} (hx : HasGrade 0 x) :
    adjointAction B x = 0 := by
  ext ν
  change (WithLp.ofLp ((Pair.pairCreate B).transpose.toEuclideanLin x)) ν = 0
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro μ _
  by_cases hμ : totalDegree μ.val = 0
  · rw [Matrix.transpose_apply, Pair.pairCreate_eq_zero_of_degree B μ ν (by omega), zero_mul]
  · change _ * x μ = 0
    rw [hx μ hμ, mul_zero]

/-- Transpose is the genuine adjoint for the finite Hilbert inner product. -/
theorem action_inner {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (x y : Hilbert V M N) : ⟪action B x, y⟫ = ⟪x, adjointAction B y⟫ := by
  simp only [action, adjointAction, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanLin_apply, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- An adjoint norm bound transferred only across the relevant pair of grades.
This finite Cauchy--Schwarz step does not assume any global creation norm. -/
theorem adjoint_norm_sq_le_of_lower_grade {M N n : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hprev : ∀ y : Hilbert V M N, HasGrade n y → ‖action B y‖ ^ 2 ≤ a * ‖y‖ ^ 2)
    (x : Hilbert V M N) (hx : HasGrade (n + 2) x) :
    ‖adjointAction B x‖ ^ 2 ≤ a * ‖x‖ ^ 2 := by
  let y := adjointAction B x
  have hy : HasGrade n y := grade_adjointAction B hx
  have hi : ⟪action B y, x⟫ = ‖y‖ ^ 2 := by
    rw [action_inner]
    exact real_inner_self_eq_norm_sq y
  have hc := real_inner_mul_inner_self_le (action B y) x
  rw [hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have hm := mul_le_mul_of_nonneg_right (hprev y hy) (sq_nonneg ‖x‖)
  have hprod : ‖y‖ ^ 2 * ‖y‖ ^ 2 ≤ (a * ‖x‖ ^ 2) * ‖y‖ ^ 2 := by
    nlinarith
  by_cases hz : ‖y‖ ^ 2 = 0
  · change ‖y‖ ^ 2 ≤ _
    rw [hz]
    exact mul_nonneg ha (sq_nonneg _)
  · have hp : 0 < ‖y‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hp).mp hprod

/-- The finite even-grade scalar bound from the commutator recurrence. -/
def amplitude (q T : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * (q * (m : ℝ) + T / 2)

lemma amplitude_nonneg {q T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T) (m : ℕ) :
    0 ≤ amplitude q T m := by unfold amplitude; positivity

lemma amplitude_step (q T : ℝ) (m : ℕ) :
    amplitude q T m + q * ((2 * (m + 1) : ℕ) : ℝ) + T / 2 =
      amplitude q T (m + 1) := by
  simp only [amplitude, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- Actual grade-2m pair-creation norm square, for every finite total cutoff.
Top and absent grades are covered by the already proved finite boundary form. -/
theorem action_norm_sq_le {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (hB : ∀ i j, B i j = B j i) (hNM : N ≤ M) (q T : ℝ)
    (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ T) (m : ℕ)
    (x : Hilbert V M N) (hx : HasGrade (2 * m) x) :
    ‖action B x‖ ^ 2 ≤ amplitude q T m * ‖x‖ ^ 2 := by
  induction m generalizing x with
  | zero =>
    have hz := adjointAction_eq_zero_of_grade_zero B hx
    have hh := Pair.pairCreate_norm_sq_sub_adjoint_norm_sq_le B hB hNM q hbound x hx
    change ‖action B x‖ ^ 2 - ‖adjointAction B x‖ ^ 2 ≤ _ at hh
    rw [hz, norm_zero, zero_pow (by omega : 2 ≠ 0), sub_zero] at hh
    simp only [Nat.cast_zero, mul_zero, zero_add] at hh
    calc
      _ ≤ (Matrix.trace (B * B) / 2) * ‖x‖ ^ 2 := hh
      _ ≤ (T / 2) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right htrace (by norm_num)) (sq_nonneg _)
      _ = _ := by simp [amplitude]
  | succ m ih =>
    have hgrade : HasGrade (2 * m + 2) x := by simpa only [Nat.mul_succ] using hx
    have ha := adjoint_norm_sq_le_of_lower_grade B (amplitude q T m)
      (amplitude_nonneg hq hT m) ih x hgrade
    have hh := Pair.pairCreate_norm_sq_sub_adjoint_norm_sq_le B hB hNM q hbound x hx
    change ‖action B x‖ ^ 2 - ‖adjointAction B x‖ ^ 2 ≤ _ at hh
    have ht := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right htrace (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg ‖x‖)
    rw [← amplitude_step q T m]
    nlinarith

/-- The normalized zero-occupation Hilbert vector, not an abstract vacuum axiom. -/
def vacuumVector {M N : ℕ} : Hilbert V M N :=
  EuclideanSpace.single TotalCutoff.vacuum 1

@[simp] theorem norm_vacuumVector {M N : ℕ} :
    ‖(vacuumVector : Hilbert V M N)‖ = 1 := by
  simp [vacuumVector, EuclideanSpace.norm_single]

omit [DecidableEq V] in
theorem grade_vacuumVector {M N : ℕ} : HasGrade 0 (vacuumVector : Hilbert V M N) := by
  intro μ hμ
  have hne : μ ≠ TotalCutoff.vacuum := by
    intro he
    subst μ
    exact hμ TotalCutoff.degree_vacuum
  simp [vacuumVector, EuclideanSpace.single_apply, hne]

/-- The actual normalized pair power S^m Ω / m! in the finite Hilbert space. -/
def pairVector {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (m : ℕ) : Hilbert V M N :=
  ((m.factorial : ℝ)⁻¹) • ((Pair.pairCreate B)^m).toEuclideanLin vacuumVector

@[simp] theorem pairVector_zero {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) :
    (pairVector B 0 : Hilbert V M N) = vacuumVector := by
  simp [pairVector, Matrix.toEuclideanLin_apply]

theorem pairVector_succ {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (m : ℕ) :
    (pairVector B (m + 1) : Hilbert V M N) =
      (((m : ℝ) + 1)⁻¹) • action B (pairVector B m) := by
  simp only [pairVector, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    _root_.mul_inv_rev, pow_succ', action, map_smul, smul_smul]
  have hc : (↑m.factorial)⁻¹ * ((m : ℝ) + 1)⁻¹ =
      ((m : ℝ) + 1)⁻¹ * (↑m.factorial)⁻¹ := mul_comm _ _
  rw [hc]
  congr 1
  ext μ
  simp only [Matrix.toEuclideanLin_apply, PiLp.toLp_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

theorem grade_pairVector {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (m : ℕ) :
    HasGrade (2 * m) (pairVector B m : Hilbert V M N) := by
  induction m with
  | zero => simpa using (grade_vacuumVector (V := V) (M := M) (N := N))
  | succ m ih =>
    rw [pairVector_succ]
    have hg := grade_action B ih
    intro μ hμ
    change ((m : ℝ) + 1)⁻¹ * (action B (pairVector B m)) μ = 0
    rw [hg μ (by simpa only [Nat.mul_succ] using hμ), mul_zero]

/-- Exact finite rational majorant; no numerical or norm oracle is used. -/
def rationalMajorant (q T : ℚ) : ℕ → ℚ
  | 0 => 1
  | m + 1 => rationalMajorant q T m * (q * (m : ℚ) + T / 2) / ((m : ℚ) + 1)

/-- The corresponding real recurrence, used before rational specialization. -/
def majorant (q T : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => majorant q T m * (q * (m : ℝ) + T / 2) / ((m : ℝ) + 1)

theorem rationalMajorant_cast (q T : ℚ) (m : ℕ) :
    (rationalMajorant q T m : ℝ) = majorant (q : ℝ) (T : ℝ) m := by
  induction m with
  | zero => simp [rationalMajorant, majorant]
  | succ m ih => simp [rationalMajorant, majorant, ih]

lemma majorant_nonneg {q T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T) (m : ℕ) :
    0 ≤ majorant q T m := by
  induction m with
  | zero => norm_num [majorant]
  | succ m ih => simp only [majorant]; positivity

/-- The actual pair powers obey the finite coefficient norm recurrence. -/
theorem pairVector_norm_sq_step {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ T) (m : ℕ) :
    ‖(pairVector B (m + 1) : Hilbert V M N)‖ ^ 2 ≤
      ((q * (m : ℝ) + T / 2) / ((m : ℝ) + 1)) * ‖(pairVector B m : Hilbert V M N)‖ ^ 2 := by
  rw [pairVector_succ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hh := action_norm_sq_le B hB hNM q T hq hT hbound htrace m
    (pairVector B m : Hilbert V M N) (grade_pairVector B m)
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ ≤ (((m : ℝ) + 1)⁻¹)^2 * (amplitude q T m * ‖(pairVector B m : Hilbert V M N)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by unfold amplitude; field_simp

theorem pairVector_norm_sq_le_majorant {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ T) (m : ℕ) :
    ‖(pairVector B m : Hilbert V M N)‖ ^ 2 ≤ majorant q T m := by
  induction m with
  | zero => simp [majorant]
  | succ m ih =>
    calc
      _ ≤ ((q * (m : ℝ) + T / 2) / ((m : ℝ) + 1)) * ‖(pairVector B m : Hilbert V M N)‖ ^ 2 :=
        pairVector_norm_sq_step B hB hNM q T hq hT hbound htrace m
      _ ≤ ((q * (m : ℝ) + T / 2) / ((m : ℝ) + 1)) * majorant q T m :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [majorant]; ring

/-- Different genuine occupation grades are orthogonal. -/
theorem inner_eq_zero_of_grades {M N n m : ℕ} {x y : Hilbert V M N}
    (hx : HasGrade n x) (hy : HasGrade m y) (hnm : n ≠ m) : ⟪x,y⟫ = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact RotatedWords.dotProduct_eq_zero_of_grades hy hx hnm.symm

/-- Orthogonality of all distinct normalized actual pair powers. -/
theorem pairVector_orthogonal {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ)
    (m n : ℕ) (hmn : m ≠ n) :
    ⟪(pairVector B m : Hilbert V M N), pairVector B n⟫ = 0 :=
  inner_eq_zero_of_grades (grade_pairVector B m) (grade_pairVector B n) (by omega)

lemma orthogonal_sum_norm_sq {I : Type*} [DecidableEq I] {M N : ℕ}
    (s : Finset I) (x : I → Hilbert V M N)
    (hx : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i,x j⟫ = 0) :
    ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact hx j hj i hi hji
  · intro hnot
    exact (hnot hi).elim

/-- The actual finite Taylor vector, including terms zero beyond the cutoff. -/
def finiteTrial {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (L : ℕ) : Hilbert V M N :=
  ∑ m ∈ Finset.range (L + 1), pairVector B m

theorem finiteTrial_norm_sq {M N : ℕ} (B : Matrix (Mode V) (Mode V) ℝ) (L : ℕ) :
    ‖(finiteTrial B L : Hilbert V M N)‖ ^ 2 =
      ∑ m ∈ Finset.range (L + 1), ‖(pairVector B m : Hilbert V M N)‖ ^ 2 :=
  orthogonal_sum_norm_sq _ _ (fun m _ n _ hmn => pairVector_orthogonal B m n hmn)

/-- Finite Taylor-vector norm bound proved from actual operators and finite grades. -/
theorem finiteTrial_norm_sq_le {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : (q • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ T) (L : ℕ) :
    ‖(finiteTrial B L : Hilbert V M N)‖ ^ 2 ≤
      ∑ m ∈ Finset.range (L + 1), majorant q T m := by
  rw [finiteTrial_norm_sq]
  exact Finset.sum_le_sum (fun m _ => pairVector_norm_sq_le_majorant B hB hNM q T hq hT hbound htrace m)

/-- The scalar majorant sum is exactly rational for rational inputs. -/
theorem finiteTrial_norm_sq_le_rational {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (hB : ∀ i j, B i j = B j i)
    (hNM : N ≤ M) (q T : ℚ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hbound : ((q : ℝ) • (1 : Matrix (Mode V) (Mode V) ℝ) - B * B).PosSemidef)
    (htrace : Matrix.trace (B * B) ≤ (T : ℝ)) (L : ℕ) :
    ‖(finiteTrial B L : Hilbert V M N)‖ ^ 2 ≤
      ((∑ m ∈ Finset.range (L + 1), rationalMajorant q T m : ℚ) : ℝ) := by
  simpa only [Rat.cast_sum, rationalMajorant_cast] using
    finiteTrial_norm_sq_le B hB hNM (q : ℝ) (T : ℝ)
      (by exact_mod_cast hq) (by exact_mod_cast hT) hbound htrace L

end BilayerDressed.FiniteOccupation.TotalCutoff.PairNorm

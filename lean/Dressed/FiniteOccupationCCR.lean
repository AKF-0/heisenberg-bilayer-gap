import Dressed.FiniteOccupationEmbedding
import Dressed.FiniteJacobi

/-!
# Exact finite occupation commutators with their boundary defect

All operators are the weighted finite-cutoff matrices from the occupation
embedding. The full product-space commutator retains the top-coordinate
projector. The usual CCR is derived only strictly below that boundary.
-/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed.FiniteOccupation
open Matrix BilayerGap.Torus
set_option maxHeartbeats 1200000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Tensor-identity lifting also preserves products at the same coordinate. -/
theorem siteLift_mul_same {I S : Type*} [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] (A B : Matrix S S ℝ) (i : I) :
    siteLift A i * siteLift B i = siteLift (A * B) i := by
  ext ν μ
  rw [Matrix.mul_apply]
  by_cases hout : ∀ j, j ≠ i → ν j = μ j
  · rw [siteLift, if_pos hout, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (fun k : S => Function.update μ i k)
      (by intro a b h; simpa using congrFun h i)
    · intro ρ hρ
      by_cases hr : ∀ j, j ≠ i → ρ j = μ j
      · exact False.elim (hρ ⟨ρ i, by
          funext j
          by_cases hj : j = i
          · subst j; simp
          · simp [Function.update_of_ne hj, (hr j hj).symm]⟩)
      · simp [siteLift, hr]
    · intro k
      have hl : ∀ j, j ≠ i → ν j = Function.update μ i k j := by
        intro j hj
        simpa [Function.update_of_ne hj] using hout j hj
      have hr : ∀ j, j ≠ i → Function.update μ i k j = μ j := by
        intro j hj
        simp [Function.update_of_ne hj]
      simp only [siteLift, if_pos hl, if_pos hr, Function.update_self]
  · rw [siteLift, if_neg hout]
    apply Finset.sum_eq_zero
    intro ρ _
    by_cases hl : ∀ j, j ≠ i → ν j = ρ j
    · by_cases hr : ∀ j, j ≠ i → ρ j = μ j
      · exact False.elim (hout (fun j hj => (hl j hj).trans (hr j hj)))
      · simp [siteLift, hr]
    · simp [siteLift, hl]

/-- Different-coordinate lifts commute even when their local matrices differ. -/
theorem siteLift_commute_of_ne {I S : Type*} [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] (A B : Matrix S S ℝ)
    (i j : I) (hij : i ≠ j) : Commute (siteLift A i) (siteLift B j) := by
  change siteLift A i * siteLift B j = siteLift B j * siteLift A i
  rw [siteLift_mul_distinct A B hij, siteLift_mul_distinct B A hij.symm]
  ext ν μ
  have he : (∀ k, k ≠ i → k ≠ j → ν k = μ k) ↔
      (∀ k, k ≠ j → k ≠ i → ν k = μ k) := by tauto
  simp only [pairLift, he, Matrix.kronecker_apply, mul_comm]

/-- Generic diagonal observable under a one-coordinate tensor lift. -/
theorem siteLift_diagonal_generic {I S : Type*} [DecidableEq I] [DecidableEq S]
    (d : S → ℝ) (i : I) :
    siteLift (Matrix.diagonal d) i =
      Matrix.diagonal (fun ν : I → S => d (ν i)) := by
  ext ν μ
  by_cases h : ν = μ
  · subst μ
    simp [siteLift]
  · have hh : ¬ ((∀ j, j ≠ i → ν j = μ j) ∧ ν i = μ i) := by
      rintro ⟨hout, hi⟩
      apply h
      funext j
      by_cases hj : j = i
      · simpa [hj] using hi
      · exact hout j hj
    simp only [siteLift, Matrix.diagonal_apply, h, if_false]
    split_ifs <;> simp_all

/-- The local weighted creation shift on levels zero through M. -/
def localCreate (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  (FiniteJacobi.upperShift (M + 1) (fun n => Real.sqrt (n : ℝ))).transpose

/-- Local annihilation after creation retains the missing top increment. -/
theorem local_annihilate_create (M : ℕ) :
    (localCreate M).transpose * localCreate M =
      Matrix.diagonal (fun n : Fin (M + 1) =>
        if n.val < M then (n.val : ℝ) + 1 else 0) := by
  rw [localCreate, Matrix.transpose_transpose, FiniteJacobi.upperShift_mul_transpose]
  congr 1
  funext n
  have hn : n.val + 1 < M + 1 ↔ n.val < M := by omega
  simp only [hn]
  split_ifs
  · rw [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one]
  · rfl

/-- Creation after annihilation is the local number, including the top level. -/
theorem local_create_annihilate (M : ℕ) :
    localCreate M * (localCreate M).transpose =
      Matrix.diagonal (fun n : Fin (M + 1) => (n.val : ℝ)) := by
  rw [localCreate, Matrix.transpose_transpose, FiniteJacobi.upperShift_transpose_mul]
  congr 1
  funext n
  by_cases hn : n.val = 0
  · simp [hn]
  · simp [hn, Real.sq_sqrt (Nat.cast_nonneg n.val)]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual occupation creation matrix is its genuine local tensor lift. -/
theorem create_eq_siteLift {M : ℕ} (i : Mode V) :
    (create (M := M) i : Op V M) = siteLift (localCreate M) i := by
  ext ν μ
  simp only [create, Raises, siteLift, localCreate, Matrix.transpose_apply,
    FiniteJacobi.upperShift]
  by_cases hout : ∀ j, j ≠ i → ν j = μ j
  · rw [if_pos hout]
    by_cases hi : (ν i).val = (μ i).val + 1
    · rw [if_pos (And.intro hi hout), if_pos hi.symm, hi, Nat.cast_add, Nat.cast_one]
    · have hnot : ¬ ((ν i).val = (μ i).val + 1 ∧ ∀ j, j ≠ i → ν j = μ j) :=
        fun h => hi h.1
      rw [if_neg hnot, if_neg (Ne.symm hi)]
  · have hnot : ¬ ((ν i).val = (μ i).val + 1 ∧ ∀ j, j ≠ i → ν j = μ j) :=
      fun h => hout h.2
    rw [if_neg hnot, if_neg hout]

/-- Actual annihilation is the real adjoint of the finite weighted creation. -/
def annihilate {M : ℕ} (i : Mode V) : Op V M := (create (M := M) i).transpose

theorem annihilate_eq_siteLift {M : ℕ} (i : Mode V) :
    (annihilate (M := M) i : Op V M) = siteLift (localCreate M).transpose i := by
  rw [annihilate, create_eq_siteLift, siteLift_transpose]

/-- Actual creations commute globally, including at the coordinate boundary. -/
theorem create_commute {M : ℕ} (i j : Mode V) :
    Commute (create (M := M) i) (create (M := M) j) := by
  rw [create_eq_siteLift, create_eq_siteLift]
  exact siteLift_self_commute _ _ _

/-- Adjoint creations also commute globally. -/
theorem annihilate_commute {M : ℕ} (i j : Mode V) :
    Commute (annihilate (M := M) i) (annihilate (M := M) j) := by
  show annihilate (M := M) i * annihilate (M := M) j =
    annihilate (M := M) j * annihilate (M := M) i
  simpa only [Matrix.transpose_mul, annihilate] using
    congrArg Matrix.transpose ((create_commute (M := M) j i).eq)

/-- Different-coordinate annihilation and creation commute exactly. -/
theorem annihilate_create_commute_of_ne {M : ℕ} (i j : Mode V) (hij : i ≠ j) :
    Commute (annihilate (M := M) i) (create (M := M) j) := by
  rw [annihilate_eq_siteLift, create_eq_siteLift]
  exact siteLift_commute_of_ne _ _ _ _ hij

/-- Exact full-product diagonal of a_i a†_i, with the top boundary visible. -/
theorem annihilate_create_same {M : ℕ} (i : Mode V) :
    annihilate (M := M) i * create (M := M) i =
      Matrix.diagonal (fun ν : Occupation V M =>
        if (ν i).val < M then ((ν i).val : ℝ) + 1 else 0) := by
  rw [annihilate_eq_siteLift, create_eq_siteLift, siteLift_mul_same,
    local_annihilate_create, siteLift_diagonal_generic]
  ext ν μ
  by_cases h : ν = μ <;> simp [h]

/-- Exact full-product diagonal of a†_i a_i, the coordinate number. -/
theorem create_annihilate_same {M : ℕ} (i : Mode V) :
    create (M := M) i * annihilate (M := M) i =
      Matrix.diagonal (fun ν : Occupation V M => ((ν i).val : ℝ)) := by
  rw [annihilate_eq_siteLift, create_eq_siteLift, siteLift_mul_same,
    local_create_annihilate, siteLift_diagonal_generic]
  ext ν μ
  by_cases h : ν = μ <;> simp [h]

/-- The true total number is the sum of creation-after-annihilation products.
The reversed product would contain the upper-boundary correction. -/
theorem sum_create_annihilate {M : ℕ} :
    (∑ i : Mode V, create (M := M) i * annihilate (M := M) i) = (number : Op V M) := by
  simp_rw [create_annihilate_same]
  ext ν μ
  by_cases hνμ : ν = μ
  · subst μ
    simp [Matrix.sum_apply, number, totalDegree, Nat.cast_sum]
  · simp [Matrix.sum_apply, number, hνμ]

/-- Orthogonal coordinate-boundary projector onto occupation M in one mode. -/
def topProjector {M : ℕ} (i : Mode V) : Op V M :=
  Matrix.diagonal (fun ν => if (ν i).val = M then 1 else 0)

omit [DecidableEq V] in
theorem topProjector_transpose {M : ℕ} (i : Mode V) :
    (topProjector (M := M) i).transpose = topProjector (M := M) i := by
  simp [topProjector]

theorem topProjector_idempotent {M : ℕ} (i : Mode V) :
    topProjector (M := M) i * topProjector (M := M) i = topProjector (M := M) i := by
  rw [topProjector, Matrix.diagonal_mul_diagonal]
  ext ν μ
  by_cases hνμ : ν = μ
  · subst μ
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> norm_num
  · simp [hνμ]

/-- Exact finite CCR: the top-coordinate correction must not be discarded. -/
theorem commutator_same {M : ℕ} (i : Mode V) :
    annihilate (M := M) i * create (M := M) i -
        create (M := M) i * annihilate (M := M) i =
      1 - (M + 1 : ℝ) • (topProjector i : Op V M) := by
  rw [annihilate_create_same, create_annihilate_same]
  ext ν μ
  by_cases hνμ : ν = μ
  · subst μ
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Matrix.smul_apply, smul_eq_mul, topProjector]
    by_cases htop : (ν i).val = M
    · simp [htop]
    · have hlt : (ν i).val < M := by have hb := (ν i).isLt; omega
      simp [htop, hlt]
  · simp [Matrix.sub_apply, hνμ, topProjector]

/-- Every mixed-mode commutator, with the exact cutoff correction. -/
theorem commutator {M : ℕ} (i j : Mode V) :
    annihilate (M := M) i * create (M := M) j -
        create (M := M) j * annihilate (M := M) i =
      if i = j then 1 - (M + 1 : ℝ) • (topProjector i : Op V M) else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using commutator_same (M := M) i
  · rw [if_neg hij, (annihilate_create_commute_of_ne (M := M) i j hij).eq, sub_self]

/-- A nonzero creation entry raises total degree exactly once. -/
theorem degree_of_create_ne_zero {M : ℕ} (i : Mode V) (ν μ : Occupation V M)
    (h : create (M := M) i ν μ ≠ 0) : totalDegree ν = totalDegree μ + 1 := by
  by_contra hn
  exact h (create_eq_zero_of_degree i ν μ hn)

/-- A nonzero annihilation entry lowers total degree exactly once. -/
theorem degree_of_annihilate_ne_zero {M : ℕ} (i : Mode V) (ν μ : Occupation V M)
    (h : annihilate (M := M) i ν μ ≠ 0) : totalDegree μ = totalDegree ν + 1 := by
  exact degree_of_create_ne_zero i μ ν h

omit [DecidableEq V] in
/-- Any occupation coordinate is bounded by total degree. -/
theorem coordinate_le_totalDegree {M : ℕ} (ν : Occupation V M) (i : Mode V) :
    (ν i).val ≤ totalDegree ν := by
  unfold totalDegree
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (ν j).val) (Finset.mem_univ i)

/-- Strictly below the per-coordinate cap, the entire total-degree subspace
is annihilated by the boundary projector. -/
theorem topProjector_degreeLE_zero {M N : ℕ} (hNM : N < M) (i : Mode V) :
    (topProjector i : Op V M) * degreeLEProjector N = 0 := by
  rw [topProjector, degreeLEProjector, Matrix.diagonal_mul_diagonal]
  ext ν μ
  by_cases hνμ : ν = μ
  · subst μ
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
    by_cases hdegree : totalDegree ν ≤ N
    · have hnot : (ν i).val ≠ M := by
        have hcoord := coordinate_le_totalDegree ν i
        omega
      simp [hdegree, hnot]
    · simp [hdegree]
  · simp [hνμ]

/-- Safe CCR on total degree at most N, provided N is strictly below M. -/
theorem commutator_on_degreeLE {M N : ℕ} (hNM : N < M) (i j : Mode V) :
    (annihilate (M := M) i * create (M := M) j -
        create (M := M) j * annihilate (M := M) i) * degreeLEProjector N =
      if i = j then (degreeLEProjector N : Op V M) else 0 := by
  rw [commutator]
  by_cases hij : i = j
  · simp [hij, sub_mul, topProjector_degreeLE_zero hNM]
  · simp [hij]

end BilayerDressed.FiniteOccupation

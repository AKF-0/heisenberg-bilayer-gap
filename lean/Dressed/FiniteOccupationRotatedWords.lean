import Dressed.FiniteOccupationTotalCutoff
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Count

/-!
# Actual rotated creation words on the finite total cutoff

All matrices below are linear combinations of the actual compressed occupation
creation matrices. The only ordinary CCR used is on input degree strictly less
than the total cutoff. Word lengths at most the cutoff ensure every suffix on
which a commutator acts satisfies this strict bound.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation.RotatedWords
open Matrix
open TotalCutoff (Basis)
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Vector (V : Type*) [Fintype V] (M N : ℕ) := Basis V M N → ℝ
abbrev ModeMatrix (V : Type*) := Matrix (Mode V) (Mode V) ℝ

/-- Exact-grade support for a genuine coordinate vector. -/
def HasGrade {M N : ℕ} (n : ℕ) (x : Vector V M N) : Prop :=
  ∀ ν, totalDegree ν.val ≠ n → x ν = 0

/-- Columns of the mode matrix rotate the actual creation matrices. -/
def create {M N : ℕ} (O : ModeMatrix V) (i : Mode V) : TotalCutoff.Op V M N :=
  ∑ j, O j i • TotalCutoff.create j

/-- Real adjoint of the rotated creation matrix. -/
def annihilate {M N : ℕ} (O : ModeMatrix V) (i : Mode V) : TotalCutoff.Op V M N :=
  (create (M := M) (N := N) O i).transpose

/-- The vacuum is the actual zero-occupation coordinate vector. -/
def vacuumVector {M N : ℕ} : Vector V M N := Pi.single TotalCutoff.vacuum 1

/-- An explicit finite word of rotated creation matrices applied to vacuum. -/
def word {M N : ℕ} (O : ModeMatrix V) : List (Mode V) → Vector V M N
  | [] => vacuumVector
  | i :: L => create O i *ᵥ word O L

@[simp] theorem word_nil {M N : ℕ} (O : ModeMatrix V) :
    word (M := M) (N := N) O [] = vacuumVector := rfl

@[simp] theorem word_cons {M N : ℕ} (O : ModeMatrix V) (i : Mode V) (L : List (Mode V)) :
    word (M := M) (N := N) O (i :: L) = create O i *ᵥ word O L := rfl

omit [DecidableEq V] in
theorem annihilate_eq_sum {M N : ℕ} (O : ModeMatrix V) (i : Mode V) :
    annihilate (M := M) (N := N) O i = ∑ j, O j i • TotalCutoff.annihilate j := by
  simp only [annihilate, create, Matrix.transpose_sum, Matrix.transpose_smul,
    TotalCutoff.annihilate]

theorem create_commute {M N : ℕ} (O : ModeMatrix V) (i j : Mode V) :
    Commute (create (M := M) (N := N) O i) (create (M := M) (N := N) O j) := by
  unfold create
  apply Commute.sum_left
  intro p _
  apply Commute.sum_right
  intro q _
  exact ((TotalCutoff.create_commute p q).smul_left (O p i)).smul_right (O q j)

theorem create_eq_zero_of_degree {M N : ℕ} (O : ModeMatrix V) (i : Mode V)
    (ν μ : Basis V M N) (h : totalDegree ν.val ≠ totalDegree μ.val + 1) :
    create O i ν μ = 0 := by
  simp only [create, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _
  have hz : TotalCutoff.create (M := M) (N := N) j ν μ = 0 := by
    by_contra hc
    exact h (TotalCutoff.degree_of_create_ne_zero j ν μ hc)
  rw [hz, mul_zero]

theorem annihilate_eq_zero_of_degree {M N : ℕ} (O : ModeMatrix V) (i : Mode V)
    (ν μ : Basis V M N) (h : totalDegree μ.val ≠ totalDegree ν.val + 1) :
    annihilate O i ν μ = 0 :=
  create_eq_zero_of_degree O i μ ν h

omit [DecidableEq V] in
theorem grade_vacuum {M N : ℕ} : HasGrade 0 (vacuumVector : Vector V M N) := by
  intro ν hν
  have hv : ν ≠ TotalCutoff.vacuum := by
    intro he
    subst ν
    exact hν TotalCutoff.degree_vacuum
  simp [vacuumVector, hv]

theorem grade_create {M N n : ℕ} (O : ModeMatrix V) (i : Mode V)
    {x : Vector V M N} (hx : HasGrade n x) :
    HasGrade (n + 1) (create O i *ᵥ x) := by
  intro ν hν
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro μ _
  by_cases hμ : totalDegree μ.val = n
  · rw [create_eq_zero_of_degree O i ν μ (by omega), zero_mul]
  · rw [hx μ hμ, mul_zero]

theorem grade_annihilate {M N n : ℕ} (O : ModeMatrix V) (i : Mode V)
    {x : Vector V M N} (hx : HasGrade (n + 1) x) :
    HasGrade n (annihilate O i *ᵥ x) := by
  intro ν hν
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro μ _
  by_cases hμ : totalDegree μ.val = n + 1
  · rw [annihilate_eq_zero_of_degree O i ν μ (by omega), zero_mul]
  · rw [hx μ hμ, mul_zero]

theorem grade_word {M N : ℕ} (O : ModeMatrix V) (L : List (Mode V)) :
    HasGrade L.length (word (M := M) (N := N) O L) := by
  induction L with
  | nil => exact grade_vacuum
  | cons i L ih => exact grade_create O i ih

theorem word_eq_of_perm {M N : ℕ} (O : ModeMatrix V) {L K : List (Mode V)}
    (h : L.Perm K) : word (M := M) (N := N) O L = word O K := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [word_cons, ih]
  | swap i j L =>
    simp only [word_cons, Matrix.mulVec_mulVec]
    rw [(create_commute O i j).eq]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem annihilate_vacuum {M N : ℕ} (O : ModeMatrix V) (i : Mode V) :
    annihilate O i *ᵥ (vacuumVector : Vector V M N) = 0 := by
  ext ν
  rw [vacuumVector, Matrix.mulVec_single_one]
  exact annihilate_eq_zero_of_degree O i ν TotalCutoff.vacuum (by
    rw [TotalCutoff.degree_vacuum]
    omega)

/-- Bilinear expansion retains the exact finite-cutoff commutator. -/
theorem commutator_expand {M N : ℕ} (O : ModeMatrix V) (i j : Mode V) :
    annihilate (M := M) (N := N) O i * create O j - create O j * annihilate O i =
      ∑ p : Mode V, ∑ q : Mode V, (O p i * O q j) •
        (TotalCutoff.annihilate p * TotalCutoff.create q -
          TotalCutoff.create q * TotalCutoff.annihilate p) := by
  rw [annihilate_eq_sum, create]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (f := fun q p => (O q j * O p i) •
    (TotalCutoff.annihilate (M := M) (N := N) p * TotalCutoff.create q))]
  simp only [← Finset.sum_sub_distrib, smul_sub]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm (O q j) (O p i)]

/-- The rotated safe-column CCR follows from column orthogonality of O.
There is deliberately no assertion for an input on the total top grade. -/
theorem commutator_safe_entry {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (i j : Mode V) (ν μ : Basis V M N)
    (hμ : totalDegree μ.val < N) :
    (annihilate (M := M) (N := N) O i * create (M := M) (N := N) O j -
        create (M := M) (N := N) O j * annihilate (M := M) (N := N) O i) ν μ =
      if i = j then if ν = μ then 1 else 0 else 0 := by
  rw [commutator_expand]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    TotalCutoff.commutator_safe_entry hNM _ _ ν μ hμ]
  by_cases hνμ : ν = μ
  · simp only [hνμ, if_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have hh := congrArg (fun A : ModeMatrix V => A i j) hO
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hh
  · simp [hνμ]

/-- Genuine action of the safe CCR on an exactly graded vector. -/
theorem commutator_on_grade {M N n : ℕ} (hNM : N ≤ M) (hnN : n < N)
    (O : ModeMatrix V) (hO : O.transpose * O = 1) (i j : Mode V)
    {x : Vector V M N} (hx : HasGrade n x) :
    annihilate O i *ᵥ (create O j *ᵥ x) - create O j *ᵥ (annihilate O i *ᵥ x) =
      if i = j then x else 0 := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]
  ext ν
  simp only [Matrix.mulVec, dotProduct]
  have he : ∀ μ : Basis V M N,
      (annihilate (M := M) (N := N) O i * create (M := M) (N := N) O j -
        create (M := M) (N := N) O j * annihilate (M := M) (N := N) O i) ν μ * x μ =
        (if i = j then if ν = μ then 1 else 0 else 0) * x μ := by
    intro μ
    by_cases hμ : totalDegree μ.val = n
    · rw [commutator_safe_entry hNM O hO i j ν μ (by omega)]
    · rw [hx μ hμ, mul_zero, mul_zero]
  simp_rw [he]
  by_cases hij : i = j <;> simp [hij]

/-- Different exact grades are orthogonal in the actual coordinate inner product. -/
theorem dotProduct_eq_zero_of_grades {M N n m : ℕ} {x y : Vector V M N}
    (hx : HasGrade n x) (hy : HasGrade m y) (hnm : n ≠ m) : x ⬝ᵥ y = 0 := by
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro ν _
  by_cases hn : totalDegree ν.val = n
  · rw [hy ν (by omega), mul_zero]
  · rw [hx ν hn, zero_mul]

/-- Moving one actual annihilator through a word uses only strictly shorter
suffixes, hence never appeals to a top-grade CCR. -/
theorem annihilate_word {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (i : Mode V) (L : List (Mode V))
    (hL : L.length ≤ N) :
    annihilate O i *ᵥ word (M := M) (N := N) O L =
      (L.count i : ℝ) • word O (L.erase i) := by
  induction L with
  | nil => simp [annihilate_vacuum]
  | cons j L ih =>
    have hlen : L.length < N := by simpa only [List.length_cons] using hL
    have hc := commutator_on_grade hNM hlen O hO i j (grade_word (M := M) O L)
    have hs : annihilate O i *ᵥ word (M := M) (N := N) O (j :: L) =
        (if i = j then word O L else 0) + create O j *ᵥ (annihilate O i *ᵥ word O L) := by
      exact sub_eq_iff_eq_add.mp hc
    rw [hs, ih (Nat.le_of_lt hlen), Matrix.mulVec_smul]
    by_cases hij : i = j
    · subst j
      by_cases hiL : i ∈ L
      · have hw := word_eq_of_perm (M := M) (N := N) O (List.perm_cons_erase hiL)
        rw [word_cons] at hw
        rw [← hw]
        simp [Nat.cast_add, add_smul, add_comm]
      · simp [List.count_eq_zero_of_not_mem hiL]
    · simp [hij, Ne.symm hij, word_cons]

/-- Occupation factorial determined by the multiplicity of every mode. -/
def wordFactorial (L : List (Mode V)) : ℕ := ∏ i : Mode V, (L.count i).factorial

@[simp] theorem wordFactorial_nil : wordFactorial ([] : List (Mode V)) = 1 := by
  simp [wordFactorial]

theorem wordFactorial_cons (i : Mode V) (L : List (Mode V)) :
    wordFactorial (i :: L) = (L.count i + 1) * wordFactorial L := by
  unfold wordFactorial
  calc
    _ = ∏ j : Mode V, (if j = i then L.count i + 1 else 1) * (L.count j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp [Nat.factorial_succ]
      · simp [hji, List.count_cons_of_ne (Ne.symm hji)]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem wordFactorial_pos (L : List (Mode V)) : 0 < wordFactorial L := by
  unfold wordFactorial
  exact Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

/-- Transposition is the adjoint for the genuine real coordinate dot product. -/
theorem create_dotProduct {M N : ℕ} (O : ModeMatrix V) (i : Mode V)
    (x y : Vector V M N) :
    (create O i *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (annihilate O i *ᵥ y) := by
  rw [dotProduct_comm (create O i *ᵥ x) y, dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm]
  rfl

/-- Exact factorial inner products for arbitrary finite rotated words.
The two length bounds are the only cutoff restrictions used. -/
theorem word_inner {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (L K : List (Mode V))
    (hL : L.length ≤ N) (hK : K.length ≤ N) :
    word (M := M) (N := N) O L ⬝ᵥ word O K =
      if L.Perm K then (wordFactorial L : ℝ) else 0 := by
  induction L generalizing K with
  | nil =>
    by_cases hK0 : K = []
    · subst K
      simp [vacuumVector]
    · have hne : 0 ≠ K.length := by
        intro h
        exact hK0 (List.length_eq_zero_iff.mp h.symm)
      rw [word_nil, dotProduct_eq_zero_of_grades grade_vacuum (grade_word O K) hne]
      simp [hK0]
  | cons i L ih =>
    have hlen : L.length ≤ N := by simp only [List.length_cons] at hL; omega
    rw [word_cons, create_dotProduct, annihilate_word hNM O hO i K hK,
      dotProduct_smul, ih (K.erase i) hlen (le_trans List.length_erase_le hK)]
    by_cases hiK : i ∈ K
    · by_cases hp : L.Perm (K.erase i)
      · have hp' : (i :: L).Perm K := List.cons_perm_iff_perm_erase.mpr ⟨hiK, hp⟩
        have hc : K.count i = L.count i + 1 := by
          simpa using (hp'.count_eq i).symm
        rw [if_pos hp, if_pos hp', wordFactorial_cons, hc]
        simp only [smul_eq_mul, Nat.cast_mul]
      · have hp' : ¬(i :: L).Perm K := by
          intro h
          exact hp (List.cons_perm_iff_perm_erase.mp h).2
        simp [hp, hp']
    · have hp' : ¬(i :: L).Perm K := by
        intro h
        exact hiK (List.cons_perm_iff_perm_erase.mp h).1
      simp [List.count_eq_zero_of_not_mem hiK, hp']

end BilayerDressed.FiniteOccupation.RotatedWords

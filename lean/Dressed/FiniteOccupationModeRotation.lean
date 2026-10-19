import Dressed.FiniteOccupationRotatedWords
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The actual finite occupation mode-rotation matrix

Its columns are normalized rotated creation words, indexed by the same actual
total-cutoff occupation basis. Consequently it is square before orthogonality
is proved. No abstract completeness or dimension hypothesis is assumed.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FiniteOccupation.ModeRotation
open Matrix RotatedWords
open TotalCutoff (Basis)
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed finite ordering of the multiset of occupied mode labels. -/
def occupationWord {M : ℕ} (ν : Occupation V M) : List (Mode V) :=
  (Finset.univ : Finset (Mode V)).toList.flatMap (fun i => List.replicate (ν i).val i)

omit [DecidableEq V] in
@[simp] theorem length_occupationWord {M : ℕ} (ν : Occupation V M) :
    (occupationWord ν).length = totalDegree ν := by
  simp [occupationWord, List.length_flatMap, Finset.sum_map_toList, totalDegree]

@[simp] theorem count_occupationWord {M : ℕ} (ν : Occupation V M) (i : Mode V) :
    (occupationWord ν).count i = (ν i).val := by
  simp [occupationWord, List.count_flatMap, Function.comp_def,
    Finset.sum_map_toList, List.count_replicate, beq_iff_eq]

theorem occupationWord_perm_iff {M : ℕ} (ν μ : Occupation V M) :
    (occupationWord ν).Perm (occupationWord μ) ↔ ν = μ := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    simpa using h.count_eq i
  · rintro rfl
    exact List.Perm.refl _

/-- The product of the usual one-mode occupation factorials. -/
def occupationFactorial {M : ℕ} (ν : Occupation V M) : ℕ :=
  ∏ i : Mode V, (ν i).val.factorial

@[simp] theorem wordFactorial_occupationWord {M : ℕ} (ν : Occupation V M) :
    wordFactorial (occupationWord ν) = occupationFactorial ν := by
  simp [wordFactorial, occupationFactorial]

omit [DecidableEq V] in
theorem occupationFactorial_pos {M : ℕ} (ν : Occupation V M) :
    0 < occupationFactorial ν :=
  Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

/-- An actual normalized vector, with the conventional square-root factorial. -/
def normalizedColumn {M N : ℕ} (O : ModeMatrix V) (ν : Basis V M N) : Vector V M N :=
  (Real.sqrt (occupationFactorial ν.val : ℝ))⁻¹ • word O (occupationWord ν.val)

/-- The square mode-rotation matrix is defined by those actual columns. -/
def unitary {M N : ℕ} (O : ModeMatrix V) : TotalCutoff.Op V M N :=
  fun ν μ => normalizedColumn O μ ν

/-- Exact orthonormality, including vacuum and every top-grade column. -/
theorem normalizedColumn_inner {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (ν μ : Basis V M N) :
    normalizedColumn O ν ⬝ᵥ normalizedColumn O μ = if ν = μ then 1 else 0 := by
  simp only [normalizedColumn, smul_dotProduct, dotProduct_smul]
  rw [word_inner hNM O hO _ _ (by simpa using ν.property) (by simpa using μ.property)]
  simp only [occupationWord_perm_iff, Subtype.val_inj, wordFactorial_occupationWord]
  by_cases hνμ : ν = μ
  · subst μ
    simp only [if_true, smul_eq_mul]
    have hp : (0 : ℝ) < occupationFactorial ν.val := by
      exact_mod_cast occupationFactorial_pos ν.val
    have hs : Real.sqrt (occupationFactorial ν.val : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hp)
    have hsq := Real.mul_self_sqrt hp.le
    field_simp
    nlinarith
  · simp [hνμ]

/-- The complete square matrix has orthonormal columns. -/
theorem unitary_transpose_mul {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) :
    (unitary (M := M) (N := N) O).transpose * unitary O = 1 := by
  ext ν μ
  change normalizedColumn O ν ⬝ᵥ normalizedColumn O μ = _
  rw [normalizedColumn_inner hNM O hO]
  rfl

/-- Squareness, not an assumed completeness statement, supplies the other inverse. -/
theorem unitary_mul_transpose {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) :
    unitary (M := M) (N := N) O * (unitary O).transpose = 1 :=
  Matrix.mul_eq_one_comm.mp (unitary_transpose_mul hNM O hO)

theorem unitary_entry_zero_of_degree {M N : ℕ} (O : ModeMatrix V) (ν μ : Basis V M N)
    (h : totalDegree ν.val ≠ totalDegree μ.val) : unitary O ν μ = 0 := by
  unfold unitary normalizedColumn
  change _ * word O (occupationWord μ.val) ν = 0
  rw [grade_word O (occupationWord μ.val) ν (by simpa using h), mul_zero]

/-- The actual rotation preserves the total number operator. -/
theorem number_commute_unitary {M N : ℕ} (O : ModeMatrix V) :
    Commute (TotalCutoff.number : TotalCutoff.Op V M N) (unitary O) := by
  change TotalCutoff.number * unitary (M := M) (N := N) O = unitary O * TotalCutoff.number
  rw [TotalCutoff.number_eq_diagonal]
  ext ν μ
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : totalDegree ν.val = totalDegree μ.val
  · rw [h, mul_comm]
  · rw [unitary_entry_zero_of_degree O ν μ h, mul_zero, zero_mul]

theorem unitary_number_conjugation {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) :
    (unitary (M := M) (N := N) O).transpose * TotalCutoff.number * unitary O =
      (TotalCutoff.number : TotalCutoff.Op V M N) := by
  rw [Matrix.mul_assoc, (number_commute_unitary O).eq, ← Matrix.mul_assoc,
    unitary_transpose_mul hNM O hO, Matrix.one_mul]

/-- A below-total-cutoff increment exists within the individual cutoff. -/
def safeIncrement {M N : ℕ} (hNM : N ≤ M) (i : Mode V) (μ : Basis V M N)
    (hμ : totalDegree μ.val < N) : Basis V M N :=
  ⟨increment i μ.val (lt_of_le_of_lt (coordinate_le_totalDegree μ.val i)
    (lt_of_lt_of_le hμ hNM)), by
    rw [totalDegree_of_raises i _ _ (raises_increment _ _ _)]
    omega⟩

theorem safeIncrement_raises {M N : ℕ} (hNM : N ≤ M) (i : Mode V) (μ : Basis V M N)
    (hμ : totalDegree μ.val < N) : Raises i (safeIncrement hNM i μ hμ).val μ.val :=
  raises_increment i μ.val (by have hc := coordinate_le_totalDegree μ.val i; omega)

theorem safeIncrement_degree {M N : ℕ} (hNM : N ≤ M) (i : Mode V) (μ : Basis V M N)
    (hμ : totalDegree μ.val < N) :
    totalDegree (safeIncrement hNM i μ hμ).val = totalDegree μ.val + 1 :=
  totalDegree_of_raises _ _ _ (safeIncrement_raises hNM i μ hμ)

/-- Exact column formula for the actual compressed occupation creation matrix. -/
theorem create_column_entry {M N : ℕ} (hNM : N ≤ M) (i : Mode V)
    (ν μ : Basis V M N) (hμ : totalDegree μ.val < N) :
    TotalCutoff.create i ν μ =
      if ν = safeIncrement hNM i μ hμ then Real.sqrt ((μ.val i).val + 1 : ℝ) else 0 := by
  by_cases hν : ν = safeIncrement hNM i μ hμ
  · subst ν
    rw [if_pos rfl]
    exact create_increment_entry i μ.val (by have hc := coordinate_le_totalDegree μ.val i; omega)
  · rw [if_neg hν]
    change (if Raises i ν.val μ.val then _ else _) = 0
    rw [if_neg]
    intro hr
    apply hν
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      apply Fin.ext
      simpa [safeIncrement, increment] using hr.1
    · simpa [safeIncrement, increment, hji] using hr.2 j hji

/-- Adding one letter gives precisely the incremented occupation word. -/
theorem occupationWord_increment_perm {M N : ℕ} (hNM : N ≤ M) (i : Mode V)
    (μ : Basis V M N) (hμ : totalDegree μ.val < N) :
    (occupationWord (safeIncrement hNM i μ hμ).val).Perm (i :: occupationWord μ.val) := by
  apply List.perm_iff_count.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simp [safeIncrement, increment]
  · simp [safeIncrement, increment, hji, Ne.symm hji]

theorem occupationFactorial_increment {M N : ℕ} (hNM : N ≤ M) (i : Mode V)
    (μ : Basis V M N) (hμ : totalDegree μ.val < N) :
    occupationFactorial (safeIncrement hNM i μ hμ).val =
      ((μ.val i).val + 1) * occupationFactorial μ.val := by
  rw [← wordFactorial_occupationWord]
  have hp := occupationWord_increment_perm hNM i μ hμ
  have hf : wordFactorial (occupationWord (safeIncrement hNM i μ hμ).val) =
      wordFactorial (i :: occupationWord μ.val) := by
    unfold wordFactorial
    apply Finset.prod_congr rfl
    intro j _
    rw [hp.count_eq j]
  rw [hf, wordFactorial_cons, count_occupationWord, wordFactorial_occupationWord]

/-- Square-root normalization gives the genuine bosonic creation weight. -/
theorem create_normalizedColumn {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (i : Mode V) (μ : Basis V M N) (hμ : totalDegree μ.val < N) :
    RotatedWords.create O i *ᵥ normalizedColumn O μ =
      Real.sqrt ((μ.val i).val + 1 : ℝ) • normalizedColumn O (safeIncrement hNM i μ hμ) := by
  unfold normalizedColumn
  rw [Matrix.mulVec_smul, ← word_cons,
    ← word_eq_of_perm O (occupationWord_increment_perm hNM i μ hμ),
    occupationFactorial_increment, smul_smul]
  congr 1
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul (by positivity)]
  have hs : Real.sqrt ((μ.val i).val + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem grade_normalizedColumn {M N : ℕ} (O : ModeMatrix V) (μ : Basis V M N) :
    HasGrade (totalDegree μ.val) (normalizedColumn O μ) := by
  intro ν hν
  change _ * word O (occupationWord μ.val) ν = 0
  rw [grade_word O (occupationWord μ.val) ν (by simpa using hν), mul_zero]

/-- On the top grade both sides of the compressed creation intertwiner vanish. -/
theorem create_normalizedColumn_top {M N : ℕ} (O : ModeMatrix V)
    (i : Mode V) (μ : Basis V M N) (hμ : totalDegree μ.val = N) :
    RotatedWords.create O i *ᵥ normalizedColumn O μ = 0 := by
  ext ν
  apply grade_create O i (grade_normalizedColumn O μ) ν
  have hν := ν.property
  omega

/-- Actual creation intertwining, valid globally including the total top grade. -/
theorem unitary_create_intertwine {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (i : Mode V) :
    unitary (M := M) (N := N) O * TotalCutoff.create i =
      RotatedWords.create O i * unitary O := by
  ext ν μ
  change (unitary (M := M) (N := N) O * TotalCutoff.create (M := M) (N := N) i) ν μ =
    (RotatedWords.create O i *ᵥ normalizedColumn O μ) ν
  by_cases hμ : totalDegree μ.val < N
  · rw [create_normalizedColumn hNM O i μ hμ, Matrix.mul_apply]
    simp_rw [create_column_entry hNM i _ μ hμ]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.smul_apply, smul_eq_mul, unitary]
    ring
  · have htop : totalDegree μ.val = N := by have := μ.property; omega
    rw [create_normalizedColumn_top O i μ htop, Matrix.mul_apply]
    simp [TotalCutoff.create_top_entry i _ μ htop]

/-- The actual finite orthogonal matrix conjugates ordinary creations into B_i. -/
theorem unitary_create_conjugation {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (i : Mode V) :
    unitary (M := M) (N := N) O * TotalCutoff.create i * (unitary O).transpose =
      RotatedWords.create O i := by
  rw [unitary_create_intertwine hNM O i, Matrix.mul_assoc,
    unitary_mul_transpose hNM O hO, Matrix.mul_one]

/-- Inverting the column mode change uses row orthogonality, obtained from
squareness of O rather than imposed as an extra hypothesis. -/
theorem inverse_rotated_create {M N : ℕ} (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (j : Mode V) :
    (∑ i : Mode V, O j i • RotatedWords.create (M := M) (N := N) O i) =
      TotalCutoff.create (M := M) (N := N) j := by
  have hOO : O * O.transpose = 1 := Matrix.mul_eq_one_comm.mp hO
  simp only [RotatedWords.create, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hc : ∀ p : Mode V, ∑ i : Mode V, O j i * O p i = if j = p then 1 else 0 := by
    intro p
    have hh := congrArg (fun A : ModeMatrix V => A j p) hOO
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hh
  simp_rw [← Finset.sum_smul, hc]
  simp [ite_smul]

theorem unitary_rotated_create_conjugation {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (i : Mode V) :
    (unitary (M := M) (N := N) O).transpose * RotatedWords.create O i * unitary O =
      TotalCutoff.create i := by
  have h := congrArg (fun A : TotalCutoff.Op V M N => (unitary O).transpose * A)
    (unitary_create_intertwine hNM O i)
  simp only [← Matrix.mul_assoc, unitary_transpose_mul hNM O hO, Matrix.one_mul] at h
  exact h.symm

/-- The inverse creation formula has the orientation needed for the final map
I_N Uᵀ W and for coefficient conjugation Oᵀ K O. -/
theorem unitary_inverse_create_conjugation {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) (j : Mode V) :
    (unitary (M := M) (N := N) O).transpose * TotalCutoff.create j * unitary O =
      ∑ i : Mode V, O j i • TotalCutoff.create i := by
  calc
    _ = (unitary O).transpose *
        (∑ i : Mode V, O j i • RotatedWords.create O i) * unitary O := by
      rw [inverse_rotated_create O hO]
    _ = ∑ i : Mode V, O j i •
        ((unitary O).transpose * RotatedWords.create O i * unitary O) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by simp_rw [unitary_rotated_create_conjugation hNM O hO]

end BilayerDressed.FiniteOccupation.ModeRotation

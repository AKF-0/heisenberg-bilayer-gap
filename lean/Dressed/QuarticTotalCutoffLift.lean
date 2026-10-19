import Dressed.QuarticFaithfulLift
import Dressed.FiniteOccupationTotalCutoff

/-! Actual faithful quartic words on the total-cutoff space used by homogeneous
creation amplification. The physical application uses N = card V. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticTotalCutoff
open Matrix
set_option maxHeartbeats 1800000
set_option maxRecDepth 20000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Hilbert (V : Type*) [Fintype V] (M N : ℕ) :=
  EuclideanSpace ℝ (FiniteOccupation.TotalCutoff.Basis V M N)

def vacuumVector {M N : ℕ} : Hilbert V M N :=
  EuclideanSpace.single FiniteOccupation.TotalCutoff.vacuum 1

/-- Literal product of four total-cutoff creators. -/
def fourCreator {M N : ℕ} (v : Fin 4 → V) (c : Fin 4 → Fin 3) :
    FiniteOccupation.TotalCutoff.Op V M N :=
  FiniteOccupation.TotalCutoff.create (v 0,c 0) * FiniteOccupation.TotalCutoff.create (v 1,c 1) *
    FiniteOccupation.TotalCutoff.create (v 2,c 2) * FiniteOccupation.TotalCutoff.create (v 3,c 3)

/-- The nine actual words for one of the three matchings. -/
def matchingOperator {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    FiniteOccupation.TotalCutoff.Op V M N :=
  ∑ p : Fin 3 × Fin 3, fourCreator v (QuarticMatching.colors m p)

def faithfulMatchingOperator {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    FiniteOccupation.TotalCutoff.Op V M N :=
  if Function.Injective v then matchingOperator v m else 0

/-- Pure-creation monotonicity discharges every excluded intermediate state. -/
theorem fourCreator_eq_compress {M N : ℕ} (v : Fin 4 → V) (c : Fin 4 → Fin 3) :
    fourCreator (M := M) (N := N) v c =
      FiniteOccupation.TotalCutoff.compress (QuarticFaithful.fourCreator v c) := by
  simp only [fourCreator, QuarticFaithful.fourCreator, Matrix.mul_assoc]
  rw [← FiniteOccupation.TotalCutoff.create_mul_compress,
    ← FiniteOccupation.TotalCutoff.create_mul_compress,
    ← FiniteOccupation.TotalCutoff.create_mul_compress]
  rfl

theorem matchingOperator_eq_compress {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    matchingOperator (M := M) (N := N) v m =
      FiniteOccupation.TotalCutoff.compress (QuarticFaithful.matchingOperator v m) := by
  rw [QuarticFaithful.matchingOperator_expansion]
  ext ν μ
  simp only [matchingOperator, fourCreator_eq_compress, Matrix.sum_apply,
    FiniteOccupation.TotalCutoff.compress, Matrix.submatrix_apply]

theorem faithfulMatchingOperator_eq_compress {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    faithfulMatchingOperator (M := M) (N := N) v m =
      FiniteOccupation.TotalCutoff.compress (QuarticFaithful.faithfulMatchingOperator v m) := by
  by_cases hv : Function.Injective v
  · simp only [faithfulMatchingOperator, QuarticFaithful.faithfulMatchingOperator, if_pos hv]
    exact matchingOperator_eq_compress v m
  · simp [faithfulMatchingOperator, QuarticFaithful.faithfulMatchingOperator, hv,
      FiniteOccupation.TotalCutoff.compress]

/-- Restriction of a genuinely physical ambient vacuum image to total cutoff. -/
theorem compressed_vacuum_eq_physical {M : ℕ} (hM : 2 ≤ M)
    (A : FiniteOccupation.Op V M) (x : ConfigurationHilbert V)
    (hA : Matrix.toEuclideanCLM (n := FiniteOccupation.Occupation V M) (𝕜 := ℝ) A
      QuarticFaithful.vacuumVector = (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin x) :
    Matrix.toEuclideanCLM (n := FiniteOccupation.TotalCutoff.Basis V M (Fintype.card V))
        (𝕜 := ℝ) (FiniteOccupation.TotalCutoff.compress A) vacuumVector =
      (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin x := by
  ext ν
  have he := congrArg (fun y : QuarticFaithful.BosonHilbert V M => y ν.val) hA
  change (A *ᵥ Pi.single QuarticFaithful.vacuum 1) ν.val =
    (FiniteOccupation.inclusion (V := V) hM *ᵥ WithLp.ofLp x) ν.val at he
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] at he
  change (FiniteOccupation.TotalCutoff.compress A *ᵥ
    Pi.single FiniteOccupation.TotalCutoff.vacuum 1) ν = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  change A ν.val QuarticFaithful.vacuum =
    (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM *ᵥ WithLp.ofLp x) ν
  rw [he]
  simp only [Matrix.mulVec, dotProduct, FiniteOccupation.inclusion,
    FiniteOccupation.TotalCutoff.physicalInclusion]
  apply Finset.sum_congr rfl
  intro s _
  have hs : ν = FiniteOccupation.encodeTotal hM s ↔ ν.val = FiniteOccupation.encode hM s :=
    Subtype.ext_iff
  simp only [hs]

/-- Matrix-level one-sided transfer through the two genuine inclusions. -/
theorem compress_intertwiner {M : ℕ} (hM : 2 ≤ M)
    (A : FiniteOccupation.Op V M) (B : ConfigurationMatrix V)
    (h : (FiniteOccupation.inclusion (V := V) hM).transpose * A = B * (FiniteOccupation.inclusion (V := V) hM).transpose) :
    (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).transpose *
        (FiniteOccupation.TotalCutoff.compress A :
          FiniteOccupation.TotalCutoff.Op V M (Fintype.card V)) =
      B * (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  let I := FiniteOccupation.TotalCutoff.inclusion (V := V) M (Fintype.card V)
  let W := FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM
  have hIW : I * W = FiniteOccupation.inclusion (V := V) hM :=
    FiniteOccupation.TotalCutoff.inclusion_mul_physicalInclusion hM
  have hI : I.transpose * I = 1 := FiniteOccupation.TotalCutoff.inclusion_transpose_mul _ _
  rw [← FiniteOccupation.TotalCutoff.compression_eq]
  change W.transpose * (I.transpose * A * I) = B * W.transpose
  calc
    _ = (I * W).transpose * A * I := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = B * (I * W).transpose * I := by rw [hIW, h]
    _ = B * W.transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc, hI, Matrix.mul_one]

def matchingVector {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) : Hilbert V M N :=
  Matrix.toEuclideanCLM (n := FiniteOccupation.TotalCutoff.Basis V M N) (𝕜 := ℝ)
    (matchingOperator v m) vacuumVector

def faithfulMatchingVector {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) : Hilbert V M N :=
  Matrix.toEuclideanCLM (n := FiniteOccupation.TotalCutoff.Basis V M N) (𝕜 := ℝ)
    (faithfulMatchingOperator v m) vacuumVector

theorem matchingVector_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (m : Fin 3) :
    matchingVector (M := M) (N := Fintype.card V) v m =
      (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin (QuarticMatching.matchingVector v m) := by
  rw [matchingVector, matchingOperator_eq_compress]
  exact compressed_vacuum_eq_physical hM _ _ (QuarticFaithful.matchingVector_eq_inclusion hM v hv m)

theorem faithfulMatchingVector_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    faithfulMatchingVector (M := M) (N := Fintype.card V) v m =
      (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin (QuarticMatching.matchingVector v m) := by
  rw [faithfulMatchingVector, faithfulMatchingOperator_eq_compress]
  exact compressed_vacuum_eq_physical hM _ _ (QuarticFaithful.faithfulMatchingVector_eq_inclusion hM v m)

theorem faithfulMatchingOperator_intertwiner {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).transpose *
        faithfulMatchingOperator (M := M) (N := Fintype.card V) v m =
      QuarticMatching.matchingOperator v m * (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  rw [faithfulMatchingOperator_eq_compress]
  exact compress_intertwiner hM _ _ (QuarticFaithful.inclusion_transpose_faithfulMatchingOperator hM v m)

theorem inclusion_inner {M : ℕ} (hM : 2 ≤ M) (x y : ConfigurationHilbert V) :
    ⟪(FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin x,
      (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin y⟫ = ⟪x,y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply, star_trivial]
  calc
    _ = WithLp.ofLp y ⬝ᵥ ((FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM).transpose *ᵥ
        (FiniteOccupation.TotalCutoff.physicalInclusion (V := V) hM *ᵥ WithLp.ofLp x)) := by
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = _ := by rw [Matrix.mulVec_mulVec, FiniteOccupation.TotalCutoff.physicalInclusion_transpose_mul,
      Matrix.one_mulVec]

theorem matching_gram {M : ℕ} (hM : 2 ≤ M) (v : Fin 4 → V)
    (hv : Function.Injective v) (m n : Fin 3) :
    ⟪matchingVector (M := M) (N := Fintype.card V) v m, matchingVector v n⟫ =
      if m=n then 9 else 3 := by
  rw [matchingVector_eq_inclusion hM v hv, matchingVector_eq_inclusion hM v hv,
    inclusion_inner, QuarticMatching.matching_gram v hv]

theorem matching_combination_norm_sq {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (c : Fin 3 → ℝ) :
    ‖∑ m : Fin 3, c m • matchingVector (M := M) (N := Fintype.card V) v m‖^2 =
      6 * (∑ m : Fin 3, (c m)^2) + 3 * (∑ m : Fin 3, c m)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, matching_gram hM v hv]
  simp [Fin.sum_univ_succ]
  ring

theorem matching_inner_zero_of_support_ne {M : ℕ} (hM : 2 ≤ M)
    (v w : Fin 4 → V) (hv : Function.Injective v) (hw : Function.Injective w)
    (hsupport : Set.range v ≠ Set.range w) (m n : Fin 3) :
    ⟪matchingVector (M := M) (N := Fintype.card V) v m, matchingVector w n⟫ = 0 := by
  rw [matchingVector_eq_inclusion hM v hv, matchingVector_eq_inclusion hM w hw,
    inclusion_inner, QuarticMatching.matching_inner_zero_of_support_ne v w hv hw hsupport]


/-- The actual mode word, in the same convention as finite-word homogenization. -/
def fourWord (v : Fin 4 → V) (c : Fin 4 → Fin 3) : List (FiniteOccupation.Mode V) :=
  [(v 0,c 0), (v 1,c 1), (v 2,c 2), (v 3,c 3)]

@[simp] theorem fourWord_length (v : Fin 4 → V) (c : Fin 4 → Fin 3) :
    (fourWord v c).length = 4 := rfl

theorem fourCreator_eq_wordProduct {M N : ℕ} (v : Fin 4 → V) (c : Fin 4 → Fin 3) :
    fourCreator (M := M) (N := N) v c =
      ((fourWord v c).map (fun i => FiniteOccupation.TotalCutoff.create (M := M) (N := N) i)).prod := by
  simp [fourWord, fourCreator, Matrix.mul_assoc]

/-- Explicit finite degree-four word representation, with repeated-site deletion
in the scalar coefficients, ready for the proved homogeneous-operator bridge. -/
theorem faithfulMatchingOperator_word_expansion {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    faithfulMatchingOperator (M := M) (N := N) v m =
      ∑ p : Fin 3 × Fin 3, (if Function.Injective v then (1 : ℝ) else 0) •
        (((fourWord v (QuarticMatching.colors m p)).map
          (fun i => FiniteOccupation.TotalCutoff.create (M := M) (N := N) i)).prod) := by
  by_cases hv : Function.Injective v
  · simp only [faithfulMatchingOperator, if_pos hv, one_smul, matchingOperator,
      fourCreator_eq_wordProduct]
  · simp [faithfulMatchingOperator, hv]

end BilayerDressed.QuarticTotalCutoff

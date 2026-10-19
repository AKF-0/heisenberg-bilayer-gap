import Dressed.QuarticMatchingNorm
import Dressed.FiniteOccupationCCR
import Dressed.GlobalResidualAlgebra

/-!
# Faithful four-site bosonic lift

Distinct-site matching products on the actual bosonic vacuum are exactly the
isometric images of the physical matching vectors. Repeated-site physical
monomials are explicitly zero and are deleted from the faithful lift.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticFaithful
open Matrix
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev BosonHilbert (V : Type*) [Fintype V] (M : ℕ) :=
  EuclideanSpace ℝ (FiniteOccupation.Occupation V M)

def vacuum {M : ℕ} : FiniteOccupation.Occupation V M := fun _ => 0

def vacuumVector {M : ℕ} : BosonHilbert V M := EuclideanSpace.single vacuum 1

omit [Fintype V] [DecidableEq V] in
theorem vacuum_eq_encode {M : ℕ} (hM : 2 ≤ M) :
    (vacuum : FiniteOccupation.Occupation V M) = FiniteOccupation.encode hM vacuumConfiguration := by
  ext i
  simp [vacuum, FiniteOccupation.encode, FiniteOccupation.rungBits, vacuumConfiguration, eq_comm]

theorem inclusion_single {M : ℕ} (hM : 2 ≤ M) (s : Configuration V) :
    (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin (EuclideanSpace.single s 1) =
      EuclideanSpace.single (FiniteOccupation.encode hM s) 1 := by
  ext ν
  change (FiniteOccupation.inclusion (V := V) hM *ᵥ Pi.single s 1) ν = _
  simp [Matrix.mulVec_single, FiniteOccupation.inclusion, EuclideanSpace.single_apply]

/-- On an unoccupied physical site, ambient creation remains entirely physical. -/
theorem create_empty_entry {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3)
    (s : Configuration V) (hs : s v = 0) (ν : FiniteOccupation.Occupation V M) :
    FiniteOccupation.create (v,α) ν (FiniteOccupation.encode hM s) =
      if ν = FiniteOccupation.encode hM (Function.update s v α.succ) then 1 else 0 := by
  have hr : FiniteOccupation.Raises (v,α) (FiniteOccupation.encode hM (Function.update s v α.succ))
      (FiniteOccupation.encode hM s) := (FiniteOccupation.raises_encode_iff hM v α _ _).mpr ⟨hs,rfl⟩
  have he : FiniteOccupation.Raises (v,α) ν (FiniteOccupation.encode hM s) ↔
      ν = FiniteOccupation.encode hM (Function.update s v α.succ) := by
    constructor
    · intro h
      funext i
      by_cases hi : i = (v,α)
      · subst i
        apply Fin.ext
        exact h.1.trans hr.1.symm
      · exact (h.2 i hi).trans (hr.2 i hi).symm
    · rintro rfl; exact hr
  simp [FiniteOccupation.create, he, FiniteOccupation.encode, FiniteOccupation.rungBits, hs, eq_comm]

/-- Actual weighted creation has weight one on each empty-site physical column. -/
theorem create_single_empty {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3)
    (s : Configuration V) (hs : s v = 0) :
    Matrix.toEuclideanCLM (n := FiniteOccupation.Occupation V M) (𝕜 := ℝ) (FiniteOccupation.create (v,α))
      (EuclideanSpace.single (FiniteOccupation.encode hM s) 1) =
        EuclideanSpace.single (FiniteOccupation.encode hM (Function.update s v α.succ)) 1 := by
  ext ν
  change (FiniteOccupation.create (v,α) *ᵥ Pi.single (FiniteOccupation.encode hM s) 1) ν = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [create_empty_entry hM v α s hs]
  simp [EuclideanSpace.single_apply]

/-- Function-coordinate version of the same actual empty-site column rule. -/
theorem create_mulVec_single_empty {M : ℕ} (hM : 2 ≤ M) (v : V) (α : Fin 3)
    (s : Configuration V) (hs : s v = 0) :
    (FiniteOccupation.create (M := M) (v,α) : FiniteOccupation.Op V M) *ᵥ
      Pi.single (FiniteOccupation.encode hM s) 1 =
        Pi.single (FiniteOccupation.encode hM (Function.update s v α.succ)) 1 := by
  funext ν
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [create_empty_entry hM v α s hs]
  simp [Pi.single_apply]

/-- The genuine ambient four-creator matrix. -/
def fourCreator {M : ℕ} (v : Fin 4 → V) (c : Fin 4 → Fin 3) : FiniteOccupation.Op V M :=
  FiniteOccupation.create (v 0,c 0) * FiniteOccupation.create (v 1,c 1) * FiniteOccupation.create (v 2,c 2) * FiniteOccupation.create (v 3,c 3)

def coloredVector {M : ℕ} (v : Fin 4 → V) (c : Fin 4 → Fin 3) : BosonHilbert V M :=
  Matrix.toEuclideanCLM (n := FiniteOccupation.Occupation V M) (𝕜 := ℝ) (fourCreator v c) vacuumVector

theorem coloredVector_eq_single {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (c : Fin 4 → Fin 3) :
    coloredVector (M := M) v c = EuclideanSpace.single (FiniteOccupation.encode hM (QuarticMatching.configuration v c)) 1 := by
  let s₃ : Configuration V := Function.update vacuumConfiguration (v 3) (c 3).succ
  let s₂ : Configuration V := Function.update s₃ (v 2) (c 2).succ
  let s₁ : Configuration V := Function.update s₂ (v 1) (c 1).succ
  have h₃ : (vacuumConfiguration : Configuration V) (v 3) = 0 := rfl
  have h₂ : s₃ (v 2) = 0 := by simp [s₃, vacuumConfiguration, hv.eq_iff]
  have h₁ : s₂ (v 1) = 0 := by simp [s₂, s₃, vacuumConfiguration, hv.eq_iff]
  have h₀ : s₁ (v 0) = 0 := by simp [s₁, s₂, s₃, vacuumConfiguration, hv.eq_iff]
  ext ν
  change (fourCreator (M := M) v c *ᵥ Pi.single (vacuum : FiniteOccupation.Occupation V M) 1) ν =
    (Pi.single (FiniteOccupation.encode hM (QuarticMatching.configuration v c)) (1 : ℝ) :
      FiniteOccupation.Occupation V M → ℝ) ν
  rw [fourCreator, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, vacuum_eq_encode hM,
    create_mulVec_single_empty hM (v 3) (c 3) vacuumConfiguration h₃,
    create_mulVec_single_empty hM (v 2) (c 2) s₃ h₂,
    create_mulVec_single_empty hM (v 1) (c 1) s₂ h₁,
    create_mulVec_single_empty hM (v 0) (c 0) s₁ h₀]
  rfl

/-- This is forward vacuum intertwining, not a false full-space creator intertwiner. -/
theorem coloredVector_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (c : Fin 4 → Fin 3) :
    coloredVector (M := M) v c = (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin (QuarticMatching.coloredVector v c) := by
  rw [coloredVector_eq_single hM v hv, QuarticMatching.coloredVector_eq_single v hv, inclusion_single]

/-- Actual bosonic matching products, prior to the repeated-site filter. -/
def matchingOperator {M : ℕ} (v : Fin 4 → V) (m : Fin 3) : FiniteOccupation.Op V M :=
  (![FiniteOccupation.pairCreate (v 0) (v 1) * FiniteOccupation.pairCreate (v 2) (v 3),
     FiniteOccupation.pairCreate (v 0) (v 2) * FiniteOccupation.pairCreate (v 1) (v 3),
     FiniteOccupation.pairCreate (v 0) (v 3) * FiniteOccupation.pairCreate (v 1) (v 2)]) m

def matchingVector {M : ℕ} (v : Fin 4 → V) (m : Fin 3) : BosonHilbert V M :=
  Matrix.toEuclideanCLM (n := FiniteOccupation.Occupation V M) (𝕜 := ℝ) (matchingOperator v m) vacuumVector

theorem matchingOperator_expansion {M : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    matchingOperator (M := M) v m = ∑ p : Fin 3 × Fin 3, fourCreator v (QuarticMatching.colors m p) := by
  fin_cases m
  · simp [matchingOperator, QuarticMatching.colors, fourCreator, FiniteOccupation.pairCreate,
      Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    simp [Matrix.mul_assoc]
  · simp [matchingOperator, QuarticMatching.colors, fourCreator, FiniteOccupation.pairCreate,
      Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (FiniteOccupation.create (v 2,α)) (FiniteOccupation.create (v 1,β)),
      (FiniteOccupation.create_commute (M := M) (v 2,α) (v 1,β)).eq]
    simp only [Matrix.mul_assoc]
  · simp [matchingOperator, QuarticMatching.colors, fourCreator, FiniteOccupation.pairCreate,
      Matrix.sum_mul, Matrix.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    simp only [Matrix.mul_assoc]
    rw [((FiniteOccupation.create_commute (M := M) (v 3,α) (v 1,β)).mul_right
      (FiniteOccupation.create_commute (M := M) (v 3,α) (v 2,β))).eq]
    simp only [Matrix.mul_assoc]

theorem matchingVector_expansion {M : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    matchingVector (M := M) v m = ∑ p : Fin 3 × Fin 3, coloredVector v (QuarticMatching.colors m p) := by
  simp only [matchingVector, matchingOperator_expansion, map_sum,
    ContinuousLinearMap.sum_apply, coloredVector]

theorem matchingVector_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (m : Fin 3) :
    matchingVector (M := M) v m = (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin (QuarticMatching.matchingVector v m) := by
  rw [matchingVector_expansion, QuarticMatching.matchingVector_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact coloredVector_eq_inclusion hM v hv _

/-- The actual rectangular W preserves all inner products. -/
theorem inclusion_inner {M : ℕ} (hM : 2 ≤ M) (x y : ConfigurationHilbert V) :
    ⟪(FiniteOccupation.inclusion (V := V) hM).toEuclideanLin x, (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin y⟫ = ⟪x,y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    star_trivial]
  calc
    _ = WithLp.ofLp y ⬝ᵥ ((FiniteOccupation.inclusion (V := V) hM).transpose *ᵥ
        (FiniteOccupation.inclusion (V := V) hM *ᵥ WithLp.ofLp x)) := by
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = _ := by rw [Matrix.mulVec_mulVec, FiniteOccupation.inclusion_transpose_mul, Matrix.one_mulVec]

/-- The bosonic Gram is derived from actual W, with no physical-norm surrogate. -/
theorem matching_gram {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (m n : Fin 3) :
    ⟪matchingVector (M := M) v m, matchingVector v n⟫ = if m=n then 9 else 3 := by
  rw [matchingVector_eq_inclusion hM v hv, matchingVector_eq_inclusion hM v hv,
    inclusion_inner, QuarticMatching.matching_gram v hv]

theorem matching_combination_norm_sq {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (hv : Function.Injective v) (c : Fin 3 → ℝ) :
    ‖∑ m : Fin 3, c m • matchingVector (M := M) v m‖^2 =
      6 * (∑ m : Fin 3, (c m)^2) + 3 * (∑ m : Fin 3, c m)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, matching_gram hM v hv]
  simp [Fin.sum_univ_succ]
  ring

theorem matching_inner_zero_of_support_ne {M : ℕ} (hM : 2 ≤ M)
    (v w : Fin 4 → V) (hv : Function.Injective v) (hw : Function.Injective w)
    (hsupport : Set.range v ≠ Set.range w) (m n : Fin 3) :
    ⟪matchingVector (M := M) v m, matchingVector w n⟫ = 0 := by
  rw [matchingVector_eq_inclusion hM v hv, matchingVector_eq_inclusion hM w hw,
    inclusion_inner, QuarticMatching.matching_inner_zero_of_support_ne v w hv hw hsupport]

/-- Repeated sites are zero in the genuine commutative hard-core subalgebra. -/
theorem physical_fourCreator_zero_of_repeated_site (v : Fin 4 → V)
    (hv : ¬ Function.Injective v) (c : Fin 4 → Fin 3) : QuarticMatching.fourCreator v c = 0 := by
  classical
  simp only [Function.Injective] at hv
  push_neg at hv
  obtain ⟨i,j,hij,hne⟩ := hv
  have hz : (∏ k : Fin 4, GlobalResidual.C (v k) (c k)) = 0 := by
    have hj : j ∈ (Finset.univ : Finset (Fin 4)).erase i := by simp [Ne.symm hne]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ hj, ← mul_assoc, hij, GlobalResidual.C_mul_same, zero_mul]
  have hm := congrArg (fun x : GlobalResidual.creationAlgebra V => (x : ConfigurationMatrix V)) hz
  simpa [Fin.prod_univ_succ, QuarticMatching.fourCreator, Matrix.mul_assoc] using hm

theorem physical_matchingOperator_zero_of_repeated_site (v : Fin 4 → V)
    (hv : ¬ Function.Injective v) (m : Fin 3) : QuarticMatching.matchingOperator v m = 0 := by
  rw [QuarticMatching.matchingOperator_expansion]
  simp only [physical_fourCreator_zero_of_repeated_site v hv, Finset.sum_const_zero]

/-- The faithful lift deletes repeated-site monomials instead of pretending
that the bosonic hard-core relations hold. -/
def faithfulMatchingOperator {M : ℕ} (v : Fin 4 → V) (m : Fin 3) : FiniteOccupation.Op V M :=
  if Function.Injective v then matchingOperator v m else 0


/-- One-sided pure-creation compression is iterated exactly, even for colliding sites. -/
theorem inclusion_transpose_fourCreator {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (c : Fin 4 → Fin 3) :
    (FiniteOccupation.inclusion (V := V) hM).transpose * fourCreator (M := M) v c =
      QuarticMatching.fourCreator v c * (FiniteOccupation.inclusion (V := V) hM).transpose := by
  let W := (FiniteOccupation.inclusion (V := V) hM).transpose
  let A (i : Fin 4) := (FiniteOccupation.create (M := M) (v i,c i) : FiniteOccupation.Op V M)
  let B (i : Fin 4) := globalCreate (v i) (c i)
  have h (i : Fin 4) : W * A i = B i * W := FiniteOccupation.inclusion_transpose_create hM _ _
  change W * (A 0 * A 1 * A 2 * A 3) = (B 0 * B 1 * B 2 * B 3) * W
  calc
    _ = ((W * A 0) * A 1) * A 2 * A 3 := by simp [Matrix.mul_assoc]
    _ = ((B 0 * W) * A 1) * A 2 * A 3 := by rw [h 0]
    _ = (B 0 * (B 1 * W)) * A 2 * A 3 := by rw [Matrix.mul_assoc (B 0) W (A 1), h 1]
    _ = (B 0 * B 1) * (B 2 * W) * A 3 := by
      rw [← Matrix.mul_assoc (B 0) (B 1) W, Matrix.mul_assoc (B 0 * B 1) W (A 2), h 2]
    _ = ((B 0 * B 1) * B 2) * (B 3 * W) := by
      rw [← Matrix.mul_assoc (B 0 * B 1) (B 2) W,
        Matrix.mul_assoc (B 0 * B 1 * B 2) W (A 3), h 3]
    _ = _ := by simp [Matrix.mul_assoc]

theorem inclusion_transpose_matchingOperator {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    ((FiniteOccupation.inclusion (V := V) hM).transpose * matchingOperator (M := M) v m :
      Matrix (Configuration V) (FiniteOccupation.Occupation V M) ℝ) =
      QuarticMatching.matchingOperator v m * (FiniteOccupation.inclusion (V := V) hM).transpose := by
  rw [matchingOperator_expansion, QuarticMatching.matchingOperator_expansion]
  simp only [Matrix.mul_sum, Matrix.sum_mul, inclusion_transpose_fourCreator]

/-- Deletion is justified by exact hard-core zero, not by small coefficients. -/
theorem inclusion_transpose_faithfulMatchingOperator {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    ((FiniteOccupation.inclusion (V := V) hM).transpose * faithfulMatchingOperator (M := M) v m :
      Matrix (Configuration V) (FiniteOccupation.Occupation V M) ℝ) =
      QuarticMatching.matchingOperator v m * (FiniteOccupation.inclusion (V := V) hM).transpose := by
  by_cases hv : Function.Injective v
  · simp only [faithfulMatchingOperator, if_pos hv]
    exact inclusion_transpose_matchingOperator hM v m
  · simp [faithfulMatchingOperator, hv, physical_matchingOperator_zero_of_repeated_site v hv]

theorem faithfulMatchingOperator_compression {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    ((FiniteOccupation.inclusion (V := V) hM).transpose * faithfulMatchingOperator (M := M) v m *
      FiniteOccupation.inclusion (V := V) hM : ConfigurationMatrix V) =
      QuarticMatching.matchingOperator v m := by
  rw [inclusion_transpose_faithfulMatchingOperator, Matrix.mul_assoc,
    FiniteOccupation.inclusion_transpose_mul, Matrix.mul_one]


/-- The vacuum vector of the filtered actual operator. -/
def faithfulMatchingVector {M : ℕ} (v : Fin 4 → V) (m : Fin 3) : BosonHilbert V M :=
  Matrix.toEuclideanCLM (n := FiniteOccupation.Occupation V M) (𝕜 := ℝ)
    (faithfulMatchingOperator v m) vacuumVector

/-- The filtered vacuum lift is faithful also when site labels collide. -/
theorem faithfulMatchingVector_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : Fin 4 → V) (m : Fin 3) :
    faithfulMatchingVector (M := M) v m =
      (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin (QuarticMatching.matchingVector v m) := by
  by_cases hv : Function.Injective v
  · simp only [faithfulMatchingVector, faithfulMatchingOperator, if_pos hv]
    exact matchingVector_eq_inclusion hM v hv m
  · simp [faithfulMatchingVector, faithfulMatchingOperator, hv, QuarticMatching.matchingVector,
      physical_matchingOperator_zero_of_repeated_site v hv]

/-- Any finite coefficient regrouping preserves the actual bosonic vacuum norm. -/
theorem faithful_sum_vacuum_inner {M : ℕ} (hM : 2 ≤ M)
    {ι : Type*} [Fintype ι] (v : ι → Fin 4 → V) (c d : ι → Fin 3 → ℝ) :
    ⟪∑ t, ∑ m, c t m • faithfulMatchingVector (M := M) (v t) m,
      ∑ t, ∑ m, d t m • faithfulMatchingVector (M := M) (v t) m⟫ =
    ⟪∑ t, ∑ m, c t m • QuarticMatching.matchingVector (v t) m,
      ∑ t, ∑ m, d t m • QuarticMatching.matchingVector (v t) m⟫ := by
  have hsum (b : ι → Fin 3 → ℝ) :
      (∑ t, ∑ m, b t m • faithfulMatchingVector (M := M) (v t) m) =
        (FiniteOccupation.inclusion (V := V) hM).toEuclideanLin
          (∑ t, ∑ m, b t m • QuarticMatching.matchingVector (v t) m) := by
    simp only [map_sum, map_smul, faithfulMatchingVector_eq_inclusion hM]
  rw [hsum c, hsum d, inclusion_inner]

end BilayerDressed.QuarticFaithful

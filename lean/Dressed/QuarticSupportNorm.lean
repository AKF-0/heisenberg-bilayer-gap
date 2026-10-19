import Dressed.QuarticCanonicalRegrouping

/-! Exact physical vacuum norm of the canonical four-site support sum.
Orthogonality is proved from actual occupied support, not assumed for the
coefficient table. The faithful bosonic lift can reuse this identity through
its separately proved vacuum isometry.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticSupportNorm
open QuarticCanonical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (enum : ∀ S : Support V, Fin 4 ≃ ↥S.val)

omit [Fintype V] in
/-- The canonical tuple has exactly its displayed physical occupied support. -/
theorem tuple_range (S : Support V) :
    Set.range (tuple enum S) = (↑S.val : Set V) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact (enum S i).property
  · intro hx
    refine ⟨(enum S).symm ⟨x,hx⟩,?_⟩
    exact congrArg Subtype.val ((enum S).apply_symm_apply ⟨x,hx⟩)

def blockVector (c : Support V → Fin 3 → ℝ) (S : Support V) : ConfigurationHilbert V :=
  ∑ m : Fin 3, c S m • QuarticMatching.matchingVector (tuple enum S) m

def weight (c : Support V → Fin 3 → ℝ) (S : Support V) : ℝ :=
  6*(∑ m : Fin 3,(c S m)^2)+3*(∑ m : Fin 3,c S m)^2

theorem block_norm_sq (c : Support V → Fin 3 → ℝ) (S : Support V) :
    ‖blockVector enum c S‖^2 = weight c S :=
  QuarticMatching.matching_combination_norm_sq (tuple enum S) (tuple_injective enum S) (c S)

theorem blocks_orthogonal (c d : Support V → Fin 3 → ℝ)
    (S T : Support V) (hST : S≠T) :
    ⟪blockVector enum c S,blockVector enum d T⟫=0 := by
  have hr : Set.range (tuple enum S) ≠ Set.range (tuple enum T) := by
    intro hh
    apply hST
    apply Subtype.ext
    apply Finset.coe_injective
    simpa only [tuple_range] using hh
  unfold blockVector
  simp only [sum_inner,inner_sum,real_inner_smul_left,inner_smul_right]
  simp only [QuarticMatching.matching_inner_zero_of_support_ne
    (tuple enum S) (tuple enum T) (tuple_injective enum S) (tuple_injective enum T) hr,
    mul_zero,Finset.sum_const_zero]

/-- Exact block Pythagoras with the non-diagonal three-matching Gram retained. -/
theorem support_sum_norm_sq (c : Support V → Fin 3 → ℝ) :
    ‖∑ S : Support V,blockVector enum c S‖^2 = ∑ S : Support V,weight c S := by
  classical
  rw [←real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (∑ T : Support V,⟪blockVector enum c T,blockVector enum c S⟫) =
        ⟪blockVector enum c S,blockVector enum c S⟫ := by
      apply Finset.sum_eq_single S
      · intro T _ hTS
        exact blocks_orthogonal enum c c T S hTS
      · simp
    _ = weight c S := by rw [real_inner_self_eq_norm_sq,block_norm_sq]

/-- The actual canonical physical polynomial, before any coefficient estimate. -/
def operator (c : Support V → Fin 3 → ℝ) : ConfigurationMatrix V :=
  ∑ S : Support V,∑ m : Fin 3,c S m • QuarticMatching.matchingOperator (tuple enum S) m

theorem operator_vacuum (c : Support V → Fin 3 → ℝ) :
    (operator enum c).toEuclideanLin vacuumVector = ∑ S : Support V,blockVector enum c S := by
  simp only [operator,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    blockVector,QuarticMatching.matchingVector]
  rfl

/-- Exact coefficient formula for the actual physical quartic vacuum norm. -/
theorem operator_vacuum_norm_sq (c : Support V → Fin 3 → ℝ) :
    ‖(operator enum c).toEuclideanLin vacuumVector‖^2 =
      ∑ S : Support V,(6*(∑ m : Fin 3,(c S m)^2)+3*(∑ m : Fin 3,c S m)^2) := by
  rw [operator_vacuum,support_sum_norm_sq]
  rfl

end BilayerDressed.QuarticSupportNorm

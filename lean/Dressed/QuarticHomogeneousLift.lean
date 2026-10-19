import Dressed.QuarticTotalCutoffLift
import Dressed.FiniteWordHomogeneous

/-! Exact finite-family homogeneous representation of the faithful quartic lift.
The coefficient family may be the literal residual terms or a proved regrouping;
no coefficient estimate or translation-counting premise is introduced here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticHomogeneous
open Matrix FiniteOccupation
set_option maxHeartbeats 300000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit normalized homogeneous coefficients, including the repeated-site filter. -/
def matchingCoefficient (v : Fin 4 → V) (m : Fin 3) : (Mode V → ℕ) → ℝ :=
  WordHomogeneous.polynomialCoefficient (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun _ => if Function.Injective v then 1 else 0)
    (fun p => QuarticTotalCutoff.fourWord v (QuarticMatching.colors m p))

theorem matching_eq_homogeneous {M N : ℕ} (v : Fin 4 → V) (m : Fin 3) :
    QuarticTotalCutoff.faithfulMatchingOperator (M := M) (N := N) v m =
      Homogeneous.homogeneousOperator 4 (matchingCoefficient v m) := by
  rw [QuarticTotalCutoff.faithfulMatchingOperator_word_expansion]
  exact WordHomogeneous.wordPolynomial_eq_homogeneousOperator _ _ _
    (fun p _ => QuarticTotalCutoff.fourWord_length v _)

section Family
variable {J : Type*} [Fintype J]

def operator {M N : ℕ} (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    TotalCutoff.Op V M N := ∑ j, c j • QuarticTotalCutoff.faithfulMatchingOperator (v j) (m j)

def physicalOperator (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    ConfigurationMatrix V := ∑ j, c j • QuarticMatching.matchingOperator (v j) (m j)

def coefficient (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ)
    (α : Mode V → ℕ) : ℝ := ∑ j, c j * matchingCoefficient (v j) (m j) α

/-- The actual finite-family operator has a proved, explicit homogeneous representation. -/
theorem operator_eq_homogeneous {M N : ℕ}
    (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    operator (M := M) (N := N) v m c = Homogeneous.homogeneousOperator 4 (coefficient v m c) := by
  simp only [operator, matching_eq_homogeneous]
  symm
  unfold coefficient
  rw [WordHomogeneous.homogeneousOperator_sum]
  simp only [WordHomogeneous.homogeneousOperator_smul]

/-- Exact physical projection for arbitrary finite real coefficients. -/
theorem operator_intertwiner {M : ℕ} (hM : 2 ≤ M)
    (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    ((TotalCutoff.physicalInclusion (V := V) hM).transpose *
      operator (M := M) (N := Fintype.card V) v m c :
      Matrix (Configuration V) (TotalCutoff.Basis V M (Fintype.card V)) ℝ) =
    physicalOperator v m c * (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  simp only [operator, physicalOperator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, QuarticTotalCutoff.faithfulMatchingOperator_intertwiner]

/-- Actual bosonic vacuum vector equals W times the actual physical finite-family vector. -/
theorem operator_vacuum_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    Matrix.toEuclideanCLM (n := TotalCutoff.Basis V M (Fintype.card V)) (𝕜 := ℝ)
        (operator v m c) QuarticTotalCutoff.vacuumVector =
      (TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin
        (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
          (physicalOperator v m c) BilayerDressed.vacuumVector) := by
  simp only [operator, physicalOperator, map_sum, ContinuousLinearMap.sum_apply,
    map_smul, ContinuousLinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact QuarticTotalCutoff.faithfulMatchingVector_eq_inclusion hM (v j) (m j)


/-- Vacuum norms of the faithful total-cutoff family and physical family agree exactly. -/
theorem operator_vacuum_norm_eq {M : ℕ} (hM : 2 ≤ M)
    (v : J → Fin 4 → V) (m : J → Fin 3) (c : J → ℝ) :
    ‖Matrix.toEuclideanCLM (n := TotalCutoff.Basis V M (Fintype.card V)) (𝕜 := ℝ)
        (operator v m c) QuarticTotalCutoff.vacuumVector‖ =
      ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (physicalOperator v m c) BilayerDressed.vacuumVector‖ := by
  rw [operator_vacuum_eq_inclusion hM]
  let x := Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
    (physicalOperator v m c) BilayerDressed.vacuumVector
  have h := QuarticTotalCutoff.inclusion_inner hM x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x, norm_nonneg ((TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin x)]

end Family
end BilayerDressed.QuarticHomogeneous

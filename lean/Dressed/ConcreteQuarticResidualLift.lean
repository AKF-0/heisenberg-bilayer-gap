import Dressed.QuarticHomogeneousLift
import Dressed.QuarticBondRegrouping

/-! The faithful finite total-cutoff lift of the literal dressed residual4.
All coefficients, including the global g/2, come from the proved finite source
expansion. No numerical F4 estimate is assumed in this exact operator adapter. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.ConcreteQuarticLift
open Matrix FiniteOccupation
set_option maxHeartbeats 300000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def sites (ex ey : V ≃ V) (t : QuarticBondRegrouping.DistinctGlobalTerm ex ey) : Fin 4 → V :=
  QuarticBondRegrouping.globalTermSites ex ey t.val

def termCoefficient (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ)
    (t : QuarticBondRegrouping.DistinctGlobalTerm ex ey) : ℝ :=
  QuarticBondRegrouping.globalTermCoefficient K ex ey g t.val

omit [Fintype V] [DecidableEq V] in
/-- Distinctness is carried by the actual filtered source subtype. -/
theorem sites_injective (ex ey : V ≃ V) (t : QuarticBondRegrouping.DistinctGlobalTerm ex ey) :
    Function.Injective (sites ex ey t) := t.property

/-- Actual degree-four total-cutoff creator matrix, not a supplied operator. -/
def operator {M N : ℕ} (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) : TotalCutoff.Op V M N :=
  QuarticHomogeneous.operator (sites ex ey) (fun _ => 0) (termCoefficient K ex ey g)

/-- Explicit normalized coefficient function for the homogeneous creation theorem. -/
def homogeneousCoefficient (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) : (Mode V → ℕ) → ℝ :=
  QuarticHomogeneous.coefficient (sites ex ey) (fun _ => 0) (termCoefficient K ex ey g)

/-- No repeated-site term remains hidden behind the faithful filter. -/
theorem operator_eq_distinct_matching_sum {M N : ℕ}
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    operator (M := M) (N := N) K ex ey g =
      ∑ t : QuarticBondRegrouping.DistinctGlobalTerm ex ey,
        termCoefficient K ex ey g t • QuarticTotalCutoff.matchingOperator (sites ex ey t) 0 := by
  simp only [operator, QuarticHomogeneous.operator, QuarticTotalCutoff.faithfulMatchingOperator,
    sites_injective, if_true]

/-- Literal physical matrix equality, retaining the original residual coefficients. -/
theorem physical_family_eq_residual (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    QuarticHomogeneous.physicalOperator (sites ex ey) (fun _ => 0) (termCoefficient K ex ey g) =
      ((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) := by
  rw [QuarticHomogeneous.physicalOperator,
    QuarticBondRegrouping.coe_residual4_eq_distinct_terms]
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem operator_eq_homogeneous {M N : ℕ}
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    operator (M := M) (N := N) K ex ey g =
      Homogeneous.homogeneousOperator 4 (homogeneousCoefficient K ex ey g) :=
  QuarticHomogeneous.operator_eq_homogeneous _ _ _

/-- The exact one-sided no-repair projection to the literal residual4 matrix. -/
theorem operator_intertwiner {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((TotalCutoff.physicalInclusion (V := V) hM).transpose *
      operator (M := M) (N := Fintype.card V) K ex ey g :
      Matrix (Configuration V) (TotalCutoff.Basis V M (Fintype.card V)) ℝ) =
    ((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) *
      (TotalCutoff.physicalInclusion (V := V) hM).transpose := by
  rw [operator, QuarticHomogeneous.operator_intertwiner, physical_family_eq_residual]

theorem operator_compression {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ((TotalCutoff.physicalInclusion (V := V) hM).transpose *
      operator (M := M) (N := Fintype.card V) K ex ey g *
        TotalCutoff.physicalInclusion (V := V) hM : ConfigurationMatrix V) =
      ((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V) := by
  rw [operator_intertwiner, Matrix.mul_assoc, TotalCutoff.physicalInclusion_transpose_mul, Matrix.mul_one]

/-- The actual bosonic vacuum image is exactly W times the actual physical residual vector. -/
theorem operator_vacuum_eq_inclusion {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    Matrix.toEuclideanCLM (n := TotalCutoff.Basis V M (Fintype.card V)) (𝕜 := ℝ)
        (operator K ex ey g) QuarticTotalCutoff.vacuumVector =
      (TotalCutoff.physicalInclusion (V := V) hM).toEuclideanLin
        (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
          (((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V))
            BilayerDressed.vacuumVector) := by
  rw [operator, QuarticHomogeneous.operator_vacuum_eq_inclusion hM, physical_family_eq_residual]

/-- This norm equality is proved before, and independently of, any numerical F4 certificate. -/
theorem operator_vacuum_norm_eq {M : ℕ} (hM : 2 ≤ M)
    (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ‖Matrix.toEuclideanCLM (n := TotalCutoff.Basis V M (Fintype.card V)) (𝕜 := ℝ)
        (operator K ex ey g) QuarticTotalCutoff.vacuumVector‖ =
      ‖Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ)
        (((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) : ConfigurationMatrix V))
          BilayerDressed.vacuumVector‖ := by
  rw [operator, QuarticHomogeneous.operator_vacuum_norm_eq hM, physical_family_eq_residual]

end BilayerDressed.ConcreteQuarticLift

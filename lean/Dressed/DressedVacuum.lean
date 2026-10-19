import Dressed.PairKernelBounds
import Dressed.FiniteExponential

/-! The exact finite hard-core exponential retains vacuum coefficient one.
In particular the dressed trial is nonzero and its norm is at least one;
this is proved from the concrete creation matrices, not a normalization premise. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A creation matrix has a zero all-singlet output row. -/
theorem globalCreate_vacuum_row_zero (v : V) (α : Fin 3) (t : Configuration V) :
    globalCreate v α (fun _ => 0) t=0 := by
  simp [globalCreate, BilayerGap.Torus.siteLift, rungCreate, Matrix.single]

theorem pairCreate_vacuum_row_zero (u v : V) (t : Configuration V) :
    pairCreate u v (fun _ => 0) t=0 := by
  simp [pairCreate, Matrix.sum_apply, Matrix.mul_apply, globalCreate_vacuum_row_zero]

theorem pairKernel_vacuum_row_zero (K : V → V → ℝ) (t : Configuration V) :
    pairKernelOperator K (fun _ => 0) t=0 := by
  simp [pairKernelOperator, Matrix.sum_apply, Matrix.smul_apply, pairCreate_vacuum_row_zero]

/-- Every positive power retains that zero row. -/
theorem matrix_pow_vacuum_row_zero (S : ConfigurationMatrix V)
    (hS : ∀ t, S (fun _ => 0) t=0) (k : ℕ) (t : Configuration V) :
    (S^(k+1)) (fun _ => 0) t=0 := by
  rw [pow_succ', Matrix.mul_apply]
  simp [hS]

/-- The vacuum coordinate is unchanged by the actual finite Taylor operator. -/
theorem matrix_taylor_vacuum_coordinate (S : ConfigurationMatrix V)
    (hS : ∀ t, S (fun _ => 0) t=0)
    (m : ℕ) (x : EuclideanSpace ℝ (Configuration V)) :
    (taylorOperator (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) S) (m+1) x) (fun _ => 0)=x (fun _ => 0) := by
  have hp (k : ℕ) :
      (((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) S)^(k+1)) x) (fun _ => 0)=0 := by
    rw [← map_pow]
    change (∑ j, (S^(k+1)) (fun _ => 0) j * x j)=0
    simp [matrix_pow_vacuum_row_zero S hS]
  simp [taylorOperator, Finset.sum_range_succ', ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : Configuration V => ℝ) (fun _ => 0))
    (∑ k ∈ Finset.range m, (((k+1).factorial : ℝ)⁻¹) •
      (((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) S)^(k+1)) x))=0
  simp only [map_sum, map_smul]
  simp [PiLp.projₗ, hp]

local instance : Module ℚ (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- The actual nilpotent pair generator as a continuous linear operator. -/
def pairGenerator (K : V → V → ℝ) : ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V :=
  Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (pairKernelS K)

theorem pairGenerator_nilpotent (K : V → V → ℝ) : IsNilpotent (pairGenerator K) :=
  (pair_kernel_nilpotent (fun u v => K u v / 2)).map
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))

/-- Exact finite hard-core dressed vector, not a formal infinite Fock state. -/
def dressedVector (K : V → V → ℝ) : ConfigurationHilbert V :=
  (IsNilpotent.exp (pairGenerator K)) vacuumVector

/-- Its all-singlet coefficient is exactly one. -/
theorem dressedVector_vacuum_coefficient (K : V → V → ℝ) :
    dressedVector K vacuumConfiguration=1 := by
  obtain ⟨m,hm⟩ := pairGenerator_nilpotent K
  have hm1 : (pairGenerator K)^(m+1)=0 := by rw [pow_succ, hm, zero_mul]
  rw [dressedVector, nilpotent_exp_eq_taylor _ (m+1) hm1]
  have hh := matrix_taylor_vacuum_coordinate (pairKernelS K)
    (pairKernel_vacuum_row_zero (fun u v => K u v / 2)) m
    (vacuumVector : ConfigurationHilbert V)
  change (taylorOperator (pairGenerator K) (m+1) vacuumVector)
    vacuumConfiguration = vacuumVector vacuumConfiguration at hh
  simpa only [vacuumVector, EuclideanSpace.single_apply, ite_true] using hh

/-- The exact dressed vector has norm at least one, without an assumed normalization. -/
theorem one_le_norm_dressedVector (K : V → V → ℝ) : 1≤‖dressedVector K‖ := by
  have hh := PiLp.norm_apply_le (dressedVector K) vacuumConfiguration
  rw [dressedVector_vacuum_coefficient, norm_one] at hh
  exact hh

/-- Actual vacuum-distance control with the first-created vector norm retained. -/
theorem dressedVector_distance_le (K : V → V → ℝ) :
    ‖dressedVector K-vacuumVector‖ ≤
      Real.exp ‖pairGenerator K‖ * ‖pairGenerator K vacuumVector‖ :=
  norm_nilpotent_exp_sub_le (pairGenerator K) (pairGenerator_nilpotent K) vacuumVector

/-- The finite checkpoint amplification constant, applied to the actual trial. -/
theorem dressedVector_distance_le_five_halves (K : V → V → ℝ)
    (hS : ‖pairGenerator K‖≤9/10) :
    ‖dressedVector K-vacuumVector‖ ≤ (5/2 : ℝ)*‖pairGenerator K vacuumVector‖ := by
  exact (dressedVector_distance_le K).trans (mul_le_mul_of_nonneg_right
    ((Real.exp_le_exp.mpr hS).trans exp_nine_tenths_lt.le) (norm_nonneg _))

end BilayerDressed

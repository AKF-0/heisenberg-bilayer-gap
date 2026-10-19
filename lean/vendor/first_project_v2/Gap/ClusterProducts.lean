import Mathlib

/-!
# Actual matrix-exponential factorization for independent clusters

These are identities of finite real matrices, not assumed partition-function
factorization laws. They form the tensor-product part of the matching seed.
-/
noncomputable section
namespace BilayerGap
namespace ClusterProducts
open Matrix
open scoped Kronecker Matrix.Norms.Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def tensorLeft : Matrix m m ℝ →+* Matrix (m×n) (m×n) ℝ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℝ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _

def tensorRight : Matrix n n ℝ →+* Matrix (m×n) (m×n) ℝ where
  toFun B := (1 : Matrix m m ℝ) ⊗ₖ B
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B

theorem tensorLeft_continuous : Continuous (tensorLeft (m:=m) (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Matrix m m ℝ => A i.1 j.1 * (1 : Matrix n n ℝ) i.2 j.2)
  fun_prop

theorem tensorRight_continuous : Continuous (tensorRight (m:=m) (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun B : Matrix n n ℝ => (1 : Matrix m m ℝ) i.1 j.1 * B i.2 j.2)
  fun_prop

theorem exp_tensorLeft (A : Matrix m m ℝ) :
    NormedSpace.exp ℝ (A ⊗ₖ (1 : Matrix n n ℝ)) =
      NormedSpace.exp ℝ A ⊗ₖ (1 : Matrix n n ℝ) :=
  (NormedSpace.map_exp ℝ (tensorLeft (m:=m) (n:=n)) tensorLeft_continuous A).symm

theorem exp_tensorRight (B : Matrix n n ℝ) :
    NormedSpace.exp ℝ ((1 : Matrix m m ℝ) ⊗ₖ B) =
      (1 : Matrix m m ℝ) ⊗ₖ NormedSpace.exp ℝ B :=
  (NormedSpace.map_exp ℝ (tensorRight (m:=m) (n:=n)) tensorRight_continuous B).symm

def tensorSum (A : Matrix m m ℝ) (B : Matrix n n ℝ) : Matrix (m×n) (m×n) ℝ :=
  A ⊗ₖ (1 : Matrix n n ℝ) + (1 : Matrix m m ℝ) ⊗ₖ B

theorem tensor_terms_commute (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    Commute (A ⊗ₖ (1 : Matrix n n ℝ)) ((1 : Matrix m m ℝ) ⊗ₖ B) := by
  change (A ⊗ₖ 1)*(1 ⊗ₖ B) = (1 ⊗ₖ B)*(A ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem exp_tensorSum (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    NormedSpace.exp ℝ (tensorSum A B) = NormedSpace.exp ℝ A ⊗ₖ NormedSpace.exp ℝ B := by
  rw [tensorSum, Matrix.exp_add_of_commute _ _ _ (tensor_terms_commute A B),
    exp_tensorLeft, exp_tensorRight, ← Matrix.mul_kronecker_mul]
  simp

theorem trace_exp_tensorSum (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    Matrix.trace (NormedSpace.exp ℝ (tensorSum A B)) =
      Matrix.trace (NormedSpace.exp ℝ A) * Matrix.trace (NormedSpace.exp ℝ B) := by
  rw [exp_tensorSum, Matrix.trace_kronecker]

theorem thermal_trace_tensorSum (A : Matrix m m ℝ) (B : Matrix n n ℝ) (b : ℝ) :
    Matrix.trace (NormedSpace.exp ℝ ((-b) • tensorSum A B)) =
      Matrix.trace (NormedSpace.exp ℝ ((-b) • A)) *
        Matrix.trace (NormedSpace.exp ℝ ((-b) • B)) := by
  have h : (-b) • tensorSum A B = tensorSum ((-b) • A) ((-b) • B) := by
    simp only [tensorSum, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [h, trace_exp_tensorSum]

/-- A concrete tensor-product basis for k independent sixteen-level clusters. -/
def PowerIndex : ℕ → Type
  | 0 => Fin 1
  | k+1 => Fin 16 × PowerIndex k

instance powerIndexFintype (k : ℕ) : Fintype (PowerIndex k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ k ih => exact @instFintypeProd (Fin 16) (PowerIndex k) inferInstance ih

instance powerIndexDecidableEq (k : ℕ) : DecidableEq (PowerIndex k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq (Fin 1))
  | succ k ih => exact @instDecidableEqProd (Fin 16) (PowerIndex k) inferInstance ih

/-- The dimension is the actual tensor-product dimension, not an extra premise. -/
theorem powerIndex_card (k : ℕ) : Fintype.card (PowerIndex k) = 16^k := by
  induction k with
  | zero => simp [PowerIndex]
  | succ k ih =>
    change Fintype.card (Fin 16 × PowerIndex k) = _
    simp [ih, pow_succ, Nat.mul_comm]

/-- A sum of k independent copies of an actual local Hamiltonian. -/
def independentHamiltonian (A : Matrix (Fin 16) (Fin 16) ℝ) :
    (k : ℕ) → Matrix (PowerIndex k) (PowerIndex k) ℝ
  | 0 => 0
  | k+1 => tensorSum A (independentHamiltonian A k)

/-- Exact partition-function factorization for an arbitrary number of clusters. -/
theorem thermal_trace_independent (A : Matrix (Fin 16) (Fin 16) ℝ) (b : ℝ) (k : ℕ) :
    Matrix.trace (NormedSpace.exp ℝ ((-b) • independentHamiltonian A k)) =
      Matrix.trace (NormedSpace.exp ℝ ((-b) • A)) ^ k := by
  induction k with
  | zero => simp [independentHamiltonian, PowerIndex, Matrix.trace]
  | succ k ih =>
    rw [independentHamiltonian, thermal_trace_tensorSum, ih, pow_succ]
    ring

#print axioms exp_tensorSum
#print axioms thermal_trace_tensorSum
#print axioms powerIndex_card
#print axioms thermal_trace_independent
end ClusterProducts
end BilayerGap

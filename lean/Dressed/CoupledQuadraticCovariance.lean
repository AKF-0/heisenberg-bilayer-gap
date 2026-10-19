import Dressed.CoupledQuadraticComparison
import Dressed.FiniteOccupationModeRotation
import Dressed.ProductOscillatorReference

/-!
# Actual finite coupled covariance and diagonal product compression

The orthogonal matrix on the total-cutoff occupation basis is the frozen
normalized-word construction. Covariance follows from its proved creation
identities. The diagonal reference is the compression of the genuine product
of finite one-mode oscillators, with every cutoff boundary retained.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CoupledQuadratic
open Matrix BilayerGap FiniteOccupation
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
variable {V : Type*} [Fintype V] [DecidableEq V]

section MatrixAlgebra
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Multiplicativity of an actual orthogonal matrix conjugation. -/
theorem orthogonal_conjugate_mul (U A B : Matrix S S ℝ)
    (hU : U * U.transpose = 1) :
    U.transpose * (A * B) * U =
      (U.transpose * A * U) * (U.transpose * B * U) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U U.transpose, hU, Matrix.one_mul]

omit [DecidableEq S] in
/-- The real adjoint commutes with orthogonal conjugation. -/
theorem conjugate_transpose (U A : Matrix S S ℝ) :
    U.transpose * A.transpose * U = (U.transpose * A * U).transpose := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
end MatrixAlgebra

/-- Actual two-creation covariance, derived from the frozen finite mode matrix. -/
theorem unitary_create_pair_conjugation {M N : ℕ} (hNM : N ≤ M)
    (O : Matrix (Mode V) (Mode V) ℝ) (hO : O.transpose * O = 1) (p q : Mode V) :
    (ModeRotation.unitary (M := M) (N := N) O).transpose *
        (TotalCutoff.create p * TotalCutoff.create q) * ModeRotation.unitary O =
      ∑ i, ∑ j, (O p i * O q j) •
        (TotalCutoff.create i * TotalCutoff.create j) := by
  rw [orthogonal_conjugate_mul _ _ _ (ModeRotation.unitary_mul_transpose hNM O hO),
    ModeRotation.unitary_inverse_create_conjugation hNM O hO,
    ModeRotation.unitary_inverse_create_conjugation hNM O hO]
  rw [Matrix.sum_mul]
  simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [mul_comm]

/-- Pair-plus-adjoint covariance, including the actual total-cutoff boundary. -/
theorem unitary_occupationPair_conjugation {M N : ℕ} (hNM : N ≤ M)
    (O : Matrix (Mode V) (Mode V) ℝ) (hO : O.transpose * O = 1) (p q : Mode V) :
    (ModeRotation.unitary (M := M) (N := N) O).transpose *
        occupationPair p q * ModeRotation.unitary O =
      ∑ i, ∑ j, (O p i * O q j) • (occupationPair i j : TotalCutoff.Op V M N) := by
  rw [occupationPair, Matrix.mul_add, Matrix.add_mul, conjugate_transpose,
    unitary_create_pair_conjugation hNM O hO]
  simp only [occupationPair, smul_add, Finset.sum_add_distrib,
    Matrix.transpose_sum, Matrix.transpose_smul]

/-- Exact coefficient regrouping fixes the orientation Oᵀ K O. -/
theorem coefficient_pair_sum {M N : ℕ}
    (O K : Matrix (Mode V) (Mode V) ℝ) :
    (∑ p, ∑ q, K p q •
      (∑ i, ∑ j, (O p i * O q j) • (occupationPair i j : TotalCutoff.Op V M N))) =
      ∑ i, ∑ j, (O.transpose * K * O) i j • occupationPair i j := by
  simp only [Finset.smul_sum, smul_smul]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ring

/-- The actual finite mode rotation conjugates the entire coupled quadratic matrix.
No conjugation identity, spectral data, or boundary-free CCR is a premise. -/
theorem coupledReference_covariance {M N : ℕ} (hNM : N ≤ M)
    (O : Matrix (Mode V) (Mode V) ℝ) (hO : O.transpose * O = 1)
    (ω : ℝ) (K : Matrix (Mode V) (Mode V) ℝ) :
    (ModeRotation.unitary (M := M) (N := N) O).transpose *
        coupledReference ω K * ModeRotation.unitary O =
      (coupledReference ω (O.transpose * K * O) : TotalCutoff.Op V M N) := by
  simp only [coupledReference, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    ModeRotation.unitary_number_conjugation hNM O hO,
    unitary_occupationPair_conjugation hNM O hO, coefficient_pair_sum]


/-- The corresponding pair-plus-adjoint on the actual product-cutoff basis. -/
def productPair {M : ℕ} (i j : Mode V) : FiniteOccupation.Op V M :=
  FiniteOccupation.create i * FiniteOccupation.create j +
    ((FiniteOccupation.create i : FiniteOccupation.Op V M) * FiniteOccupation.create j).transpose

section LocalLifts
variable {I S : Type*} [DecidableEq I] [DecidableEq S]

/-- Linearity of the actual site lift. -/
theorem siteLift_add (A B : Matrix S S ℝ) (i : I) :
    Torus.siteLift (A+B) i = Torus.siteLift A i + Torus.siteLift B i := by
  ext s t
  simp only [Torus.siteLift, Matrix.add_apply]
  split_ifs <;> simp

theorem siteLift_smul (c : ℝ) (A : Matrix S S ℝ) (i : I) :
    Torus.siteLift (c • A) i = c • Torus.siteLift A i := by
  ext s t
  simp only [Torus.siteLift, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp
end LocalLifts

/-- The frozen one-mode oscillator uses precisely the same finite creation shift. -/
theorem local_oscillator_ladder (M : ℕ) (ω z : ℝ) :
    FiniteOscillator.occupationMatrix (M+1) ω z =
      ω • (localCreate M * (localCreate M).transpose) +
        (z/2) • (localCreate M * localCreate M +
          (localCreate M * localCreate M).transpose) := by
  rw [FiniteOscillator.occupationMatrix_eq_ladder_formula, local_create_annihilate]
  congr 1
  congr 1
  simp only [localCreate, FiniteOscillator.annihilation,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  exact add_comm _ _

/-- A local oscillator lifted to its actual mode coordinate, including its cutoff. -/
theorem site_oscillator_ladder {M : ℕ} (i : Mode V) (ω z : ℝ) :
    Torus.siteLift (FiniteOscillator.occupationMatrix (M+1) ω z) i =
      ω • (FiniteOccupation.create (M := M) i * FiniteOccupation.annihilate i) +
        (z/2) • (productPair i i : FiniteOccupation.Op V M) := by
  rw [local_oscillator_ladder]
  simp only [productPair, FiniteOccupation.annihilate, create_eq_siteLift,
    Torus.siteLift_transpose, siteLift_mul_same, siteLift_add, siteLift_smul]

/-- Exact product oscillator normalization, on the actual product occupation basis. -/
theorem product_oscillator_ladder (M : ℕ) (ω : ℝ) (z : Mode V → ℝ) :
    FiniteProduct.oscillator (M+1) ω z =
      ω • (FiniteOccupation.number : FiniteOccupation.Op V M) +
        (1/2 : ℝ) • ∑ i, z i • (productPair i i : FiniteOccupation.Op V M) := by
  simp only [FiniteProduct.oscillator, FiniteProduct.hamiltonian,
    site_oscillator_ladder, Finset.sum_add_distrib, ← Finset.smul_sum,
    FiniteOccupation.sum_create_annihilate]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- Genuine total-cutoff compression of a pure creation pair and its adjoint.
This uses the proved no-excluded-intermediate identity, not a projection-product assumption. -/
theorem compress_productPair {M N : ℕ} (i j : Mode V) :
    (TotalCutoff.compress (N := N) (productPair i j) : TotalCutoff.Op V M N) =
      occupationPair i j := by
  rw [occupationPair, TotalCutoff.create_mul_create]
  ext ν μ
  rfl

/-- Diagonal kernels have exactly one same-mode pair term per mode. -/
theorem coupledReference_diagonal {M N : ℕ} (ω : ℝ) (z : Mode V → ℝ) :
    (coupledReference ω (Matrix.diagonal z) : TotalCutoff.Op V M N) =
      ω • TotalCutoff.number + (1/2 : ℝ) • ∑ i, z i • occupationPair i i := by
  simp [coupledReference, Matrix.diagonal_apply, ite_smul]

/-- The diagonal coupled reference is exactly compression of the actual finite
product oscillator. There is no spectral comparison or boundary hypothesis. -/
theorem diagonal_product_compression {M N : ℕ} (ω : ℝ) (z : Mode V → ℝ) :
    (TotalCutoff.inclusion (V := V) M N).transpose *
        FiniteProduct.oscillator (M+1) ω z * TotalCutoff.inclusion (V := V) M N =
      (coupledReference ω (Matrix.diagonal z) : TotalCutoff.Op V M N) := by
  rw [TotalCutoff.compression_eq, product_oscillator_ladder, coupledReference_diagonal]
  ext ν μ
  simp only [TotalCutoff.compress, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun A : TotalCutoff.Op V M N => A ν μ) (compress_productPair i i)

/-- Actual mode diagonalization followed by actual total-to-product inclusion.
The only diagonalization input is the finite mode coefficient matrix Oᵀ K O. -/
theorem coupledReference_diagonal_product_compression {M N : ℕ} (hNM : N ≤ M)
    (O : Matrix (Mode V) (Mode V) ℝ) (hO : O.transpose * O = 1)
    (ω : ℝ) (K : Matrix (Mode V) (Mode V) ℝ) (z : Mode V → ℝ)
    (hdiag : O.transpose * K * O = Matrix.diagonal z) :
    (ModeRotation.unitary (M := M) (N := N) O).transpose *
        coupledReference ω K * ModeRotation.unitary O =
      (TotalCutoff.inclusion (V := V) M N).transpose *
        FiniteProduct.oscillator (M+1) ω z * TotalCutoff.inclusion (V := V) M N := by
  rw [coupledReference_covariance hNM O hO, hdiag, diagonal_product_compression]

end BilayerDressed.CoupledQuadratic

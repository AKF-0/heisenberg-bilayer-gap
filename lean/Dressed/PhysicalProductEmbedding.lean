import Dressed.FiniteOccupationModeRotation
import Dressed.CoupledQuadraticComparison
import Dressed.ProductOscillatorReference

/-!
# Actual physical-to-product and spectral-label embeddings

The maps are I_N Uᵀ W and Qᵀ I_N Uᵀ W. Here U is the proved finite mode
rotation, I_N is the actual total-to-product inclusion, W is the actual physical
inclusion (with the frozen Cartesian basis map for the magic-rung Hamiltonian),
and Q is the actual tensor eigenbasis of the finite product oscillators.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.PhysicalProduct
open Matrix FiniteOccupation
open RotatedWords (ModeMatrix)
set_option maxHeartbeats 1600000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

section RectangularIsometries
variable {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ξ]

omit [Fintype ι] [DecidableEq ξ] in
/-- Genuine rectangular matrices with orthonormal columns compose isometrically. -/
theorem transpose_mul_composite (A : Matrix ξ κ ℝ) (B : Matrix κ ι ℝ)
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    (A * B).transpose * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc A.transpose A B, hA, Matrix.one_mul, hB]

omit [DecidableEq κ] in
/-- Rectangular, not only square, orthonormal-column matrices preserve norm. -/
theorem isometricMatrix_norm (A : Matrix κ ι ℝ) (hA : A.transpose * A = 1)
    (x : EuclideanSpace ℝ ι) : ‖A.toEuclideanLin x‖ = ‖x‖ := by
  have hi : ⟪A.toEuclideanLin x, A.toEuclideanLin x⟫ = ⟪x, x⟫ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      star_trivial]
    calc
      (A *ᵥ WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) =
          WithLp.ofLp x ⬝ᵥ (A.transpose *ᵥ (A *ᵥ WithLp.ofLp x)) := by
        conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = _ := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (A.toEuclideanLin x), norm_nonneg x]

omit [DecidableEq κ] in
theorem isometricMatrix_injective (A : Matrix κ ι ℝ) (hA : A.transpose * A = 1) :
    Function.Injective A.toEuclideanLin := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← isometricMatrix_norm A hA (x-y), map_sub, h, sub_self, norm_zero]
/-- Matrix compression agrees with the corresponding real Euclidean form. -/
theorem compression_inner (A : Matrix κ κ ℝ) (W : Matrix κ ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    ⟪x, (W.transpose * A * W).toEuclideanLin x⟫ =
      ⟪W.toEuclideanLin x, A.toEuclideanLin (W.toEuclideanLin x)⟫ := by
  simp only [CoupledQuadratic.euclidean_inner_matrix, Matrix.ofLp_toEuclideanLin_apply]
  exact CoupledQuadratic.compression_quadratic W A (WithLp.ofLp x)
end RectangularIsometries

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual inverse mode change followed by total-to-product inclusion. -/
def rotateToProduct {M N : ℕ} (O : ModeMatrix V) :
    Matrix (Occupation V M) (TotalCutoff.Basis V M N) ℝ :=
  TotalCutoff.inclusion M N * (ModeRotation.unitary O).transpose

theorem rotateToProduct_transpose_mul {M N : ℕ} (hNM : N ≤ M) (O : ModeMatrix V)
    (hO : O.transpose * O = 1) :
    (rotateToProduct (M := M) (N := N) O).transpose * rotateToProduct (M := M) (N := N) O = 1 := by
  apply transpose_mul_composite
  · exact TotalCutoff.inclusion_transpose_mul M N
  · rw [Matrix.transpose_transpose]
    exact ModeRotation.unitary_mul_transpose hNM O hO

/-- Cartesian physical configurations embedded into the actual product occupation space. -/
def cartesianEmbedding {M : ℕ} (hM : 2 ≤ M) (O : ModeMatrix V) :
    Matrix (Occupation V M) (Configuration V) ℝ :=
  rotateToProduct O * TotalCutoff.physicalInclusion hM

theorem cartesianEmbedding_transpose_mul {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (O : ModeMatrix V) (hO : O.transpose * O = 1) :
    (cartesianEmbedding hM O).transpose * cartesianEmbedding hM O = 1 :=
  transpose_mul_composite _ _ (rotateToProduct_transpose_mul hAM O hO)
    (TotalCutoff.physicalInclusion_transpose_mul hM)

/-- J for the actual magic-rung Hamiltonian. The rightmost basis change is the
frozen Cartesian parity matrix, not another occupation-mode rotation. -/
def physicalEmbedding {M : ℕ} (hM : 2 ≤ M) (O : ModeMatrix V) :
    Matrix (Occupation V M) (Configuration V) ℝ :=
  rotateToProduct O * CoupledQuadratic.physicalEmbedding hM

theorem physicalEmbedding_transpose_mul {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (O : ModeMatrix V) (hO : O.transpose * O = 1) :
    (physicalEmbedding hM O).transpose * physicalEmbedding hM O = 1 :=
  transpose_mul_composite _ _ (rotateToProduct_transpose_mul hAM O hO)
    (CoupledQuadratic.physicalEmbedding_transpose_mul hM)

/-- Q is the actual tensor eigenbasis of the finite local occupation oscillators. -/
def oscillatorSpectralMatrix (M : ℕ) (ω : ℝ) (z : Mode V → ℝ) :
    Matrix (Occupation V M) (Occupation V M) ℝ :=
  FiniteProduct.spectralMatrix (fun i => FiniteOscillator.occupationMatrix (M+1) ω (z i))
    (fun i => FiniteOscillator.occupationMatrix_hermitian (M+1) ω (z i))

theorem oscillatorSpectralMatrix_transpose_mul (M : ℕ) (ω : ℝ) (z : Mode V → ℝ) :
    (oscillatorSpectralMatrix M ω z).transpose * oscillatorSpectralMatrix M ω z = 1 :=
  FiniteProduct.spectralMatrix_orthogonal _ _

theorem oscillatorSpectralMatrix_mul_transpose (M : ℕ) (ω : ℝ) (z : Mode V → ℝ) :
    oscillatorSpectralMatrix M ω z * (oscillatorSpectralMatrix M ω z).transpose = 1 :=
  Matrix.mul_eq_one_comm.mp (oscillatorSpectralMatrix_transpose_mul M ω z)

/-- The final actual physical-to-spectral-label map is Qᵀ J, not Q J. -/
def spectralEmbedding {M : ℕ} (hM : 2 ≤ M) (O : ModeMatrix V)
    (ω : ℝ) (z : Mode V → ℝ) : Matrix (Occupation V M) (Configuration V) ℝ :=
  (oscillatorSpectralMatrix M ω z).transpose * physicalEmbedding hM O

theorem spectralEmbedding_transpose_mul {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (O : ModeMatrix V) (hO : O.transpose * O = 1)
    (ω : ℝ) (z : Mode V → ℝ) :
    (spectralEmbedding hM O ω z).transpose * spectralEmbedding hM O ω z = 1 := by
  apply transpose_mul_composite
  · rw [Matrix.transpose_transpose]
    exact oscillatorSpectralMatrix_mul_transpose M ω z
  · exact physicalEmbedding_transpose_mul hM hAM O hO

theorem spectralEmbedding_norm {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (O : ModeMatrix V) (hO : O.transpose * O = 1)
    (ω : ℝ) (z : Mode V → ℝ) (x : EuclideanSpace ℝ (Configuration V)) :
    ‖(spectralEmbedding hM O ω z).toEuclideanLin x‖ = ‖x‖ :=
  isometricMatrix_norm _ (spectralEmbedding_transpose_mul hM hAM O hO ω z) x

theorem spectralEmbedding_injective {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (O : ModeMatrix V) (hO : O.transpose * O = 1)
    (ω : ℝ) (z : Mode V → ℝ) :
    Function.Injective (spectralEmbedding hM O ω z).toEuclideanLin :=
  isometricMatrix_injective _ (spectralEmbedding_transpose_mul hM hAM O hO ω z)

/-- Undoing the actual spectral-label change recovers J exactly. -/
theorem spectralEmbedding_unrotate {M : ℕ} (hM : 2 ≤ M) (O : ModeMatrix V)
    (ω : ℝ) (z : Mode V → ℝ) :
    oscillatorSpectralMatrix M ω z * spectralEmbedding hM O ω z = physicalEmbedding hM O := by
  rw [spectralEmbedding, ← Matrix.mul_assoc, oscillatorSpectralMatrix_mul_transpose,
    Matrix.one_mul]

/-- The spectral-label form is the actual product-oscillator form on Jx. -/
theorem spectralEmbedding_oscillator_inner {M : ℕ} (hM : 2 ≤ M) (O : ModeMatrix V)
    (ω : ℝ) (z : Mode V → ℝ) (x : EuclideanSpace ℝ (Configuration V)) :
    ⟪(spectralEmbedding hM O ω z).toEuclideanLin x,
      ((oscillatorSpectralMatrix M ω z).transpose * FiniteProduct.oscillator (M+1) ω z *
        oscillatorSpectralMatrix M ω z).toEuclideanLin
          ((spectralEmbedding hM O ω z).toEuclideanLin x)⟫ =
      ⟪(physicalEmbedding hM O).toEuclideanLin x,
        (FiniteProduct.oscillator (M+1) ω z).toEuclideanLin
          ((physicalEmbedding hM O).toEuclideanLin x)⟫ := by
  rw [compression_inner]
  simp only [CoupledQuadratic.euclidean_inner_matrix, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.mulVec_mulVec, spectralEmbedding_unrotate]

/-- The actual symmetric one-particle kernel of the physical graph reference. -/
def graphKernel (ex ey : Equiv.Perm V) (g : ℝ) : ModeMatrix V :=
  (g/2) • CoupledQuadratic.graphAdjacency ex ey

omit [Fintype V] in
theorem graphKernel_hermitian (ex ey : Equiv.Perm V) (g : ℝ) :
    (graphKernel ex ey g).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [graphKernel, Matrix.transpose_smul, CoupledQuadratic.graphAdjacency_transpose]

/-- A canonical actual orthogonal mode matrix from the finite spectral theorem. -/
def graphModes (ex ey : Equiv.Perm V) (g : ℝ) : ModeMatrix V :=
  (graphKernel_hermitian ex ey g).eigenvectorUnitary

/-- The corresponding genuine eigenvalues, indexed by the finite mode set. -/
def graphModeEigenvalue (ex ey : Equiv.Perm V) (g : ℝ) : Mode V → ℝ :=
  (graphKernel_hermitian ex ey g).eigenvalues

theorem graphModes_transpose_mul (ex ey : Equiv.Perm V) (g : ℝ) :
    (graphModes ex ey g).transpose * graphModes ex ey g = 1 := by
  simpa only [graphModes, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
      _root_.unitary.coe_star_mul_self (graphKernel_hermitian ex ey g).eigenvectorUnitary

theorem graphModes_diagonalization (ex ey : Equiv.Perm V) (g : ℝ) :
    (graphModes ex ey g).transpose * graphKernel ex ey g * graphModes ex ey g =
      diagonal (graphModeEigenvalue ex ey g) := by
  simpa only [graphModes, graphModeEigenvalue, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
    Function.id_comp] using (graphKernel_hermitian ex ey g).star_mul_self_mul_eq_diagonal

/-- No orthogonal diagonalizer is a premise of this final concrete embedding. -/
def graphSpectralEmbedding {M : ℕ} (hM : 2 ≤ M) (ex ey : Equiv.Perm V) (g : ℝ) :
    Matrix (Occupation V M) (Configuration V) ℝ :=
  spectralEmbedding hM (graphModes ex ey g) (1-2*g) (graphModeEigenvalue ex ey g)

theorem graphSpectralEmbedding_transpose_mul {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V) (g : ℝ) :
    (graphSpectralEmbedding hM ex ey g).transpose * graphSpectralEmbedding hM ex ey g = 1 :=
  spectralEmbedding_transpose_mul hM hAM _ (graphModes_transpose_mul ex ey g) _ _

theorem graphSpectralEmbedding_norm {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V) (g : ℝ)
    (x : EuclideanSpace ℝ (Configuration V)) :
    ‖(graphSpectralEmbedding hM ex ey g).toEuclideanLin x‖ = ‖x‖ :=
  isometricMatrix_norm _ (graphSpectralEmbedding_transpose_mul hM hAM ex ey g) x

theorem graphSpectralEmbedding_injective {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V) (g : ℝ) :
    Function.Injective (graphSpectralEmbedding hM ex ey g).toEuclideanLin :=
  isometricMatrix_injective _ (graphSpectralEmbedding_transpose_mul hM hAM ex ey g)

end BilayerDressed.PhysicalProduct

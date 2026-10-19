import Dressed.PhysicalProductEmbedding
import Dressed.CoupledQuadraticCovariance

/-!
# Actual physical Hamiltonian versus the finite product-number reference

Every operator and every embedding is constructed. The coupled physical lower
bound, finite mode covariance and pure-creation product compression are applied
as proved theorems, not supplied as spectral or quadratic-form assumptions.
Scalar oscillator stability, frequency and constant estimates remain explicit
until the separate reference-adjacency bounds are instantiated.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.PhysicalProduct
open Matrix FiniteOccupation BilayerGap
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual heterogeneous finite product operator for the graph eigenmodes. -/
def graphProductOperator (M : ℕ) (ex ey : Equiv.Perm V) (g : ℝ) :
    Matrix (Occupation V M) (Occupation V M) ℝ :=
  FiniteProduct.oscillator (M+1) (1-2*g) (graphModeEigenvalue ex ey g)

/-- Exact operator identity for J, including the correct inverse mode rotation. -/
theorem graph_product_compression_identity {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V) (g : ℝ) :
    (physicalEmbedding hM (graphModes ex ey g)).transpose * graphProductOperator M ex ey g *
        physicalEmbedding hM (graphModes ex ey g) =
      (CoupledQuadratic.physicalEmbedding (V := V) hM).transpose *
        (CoupledQuadratic.coupledReference (1-2*g) (graphKernel ex ey g) :
          TotalCutoff.Op V M (Fintype.card V)) * CoupledQuadratic.physicalEmbedding hM := by
  let U : TotalCutoff.Op V M (Fintype.card V) := ModeRotation.unitary (graphModes ex ey g)
  let I := TotalCutoff.inclusion (V := V) M (Fintype.card V)
  let W := CoupledQuadratic.physicalEmbedding (V := V) hM
  let H : TotalCutoff.Op V M (Fintype.card V) :=
    CoupledQuadratic.coupledReference (1-2*g) (graphKernel ex ey g)
  have hUU : U * U.transpose = 1 :=
    ModeRotation.unitary_mul_transpose hAM _ (graphModes_transpose_mul ex ey g)
  have hd : U.transpose * H * U = I.transpose * graphProductOperator M ex ey g * I :=
    CoupledQuadratic.coupledReference_diagonal_product_compression hAM _
      (graphModes_transpose_mul ex ey g) (1-2*g) (graphKernel ex ey g)
      (graphModeEigenvalue ex ey g) (graphModes_diagonalization ex ey g)
  have hr : U * (I.transpose * graphProductOperator M ex ey g * I) * U.transpose = H := by
    rw [← hd]
    calc
      _ = (U * U.transpose) * H * (U * U.transpose) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  change ((I * U.transpose) * W).transpose * graphProductOperator M ex ey g *
    ((I * U.transpose) * W) = W.transpose * H * W
  calc
    _ = W.transpose * (U * (I.transpose * graphProductOperator M ex ey g * I) * U.transpose) * W := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by rw [hr]

/-- The actual magic-rung physical Hamiltonian dominates the actual product form
on Jx. There is no operator-comparison or isometry premise. -/
theorem graphHamiltonian_product_inner_lower {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v) (g : ℝ) (hg : 0 ≤ g)
    (x : EuclideanSpace ℝ (Configuration V)) :
    ⟪(physicalEmbedding hM (graphModes ex ey g)).toEuclideanLin x,
      (graphProductOperator M ex ey g).toEuclideanLin
        ((physicalEmbedding hM (graphModes ex ey g)).toEuclideanLin x)⟫ ≤
      ⟪x, (PhysicalGram.graphHamiltonian ex ey g).toEuclideanLin x⟫ := by
  rw [← compression_inner, graph_product_compression_identity hM hAM ex ey g,
    compression_inner]
  exact CoupledQuadratic.physical_graphHamiltonian_coupled_inner_lower hM ex ey hx hy g hg x

/-- Actual operator-form comparison with the product label-number matrix.
Only numerical one-mode stability/frequency/constant bounds remain hypotheses. -/
theorem graphHamiltonian_spectral_number_lower {M : ℕ} (hM : 2 ≤ M)
    (hAM : Fintype.card V ≤ M) (ex ey : Equiv.Perm V)
    (hx : ∀ v, v ≠ ex v) (hy : ∀ v, v ≠ ey v) (g : ℝ) (hg : 0 ≤ g)
    (a c : ℝ) (hstable : ∀ i, |graphModeEigenvalue ex ey g i| < 1-2*g)
    (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency (1-2*g) (graphModeEigenvalue ex ey g i))
    (hc : c ≤ ∑ i, -(graphModeEigenvalue ex ey g i)^2 / (2*((1-2*g)+a)))
    (x : EuclideanSpace ℝ (Configuration V)) :
    a * ⟪(graphSpectralEmbedding hM ex ey g).toEuclideanLin x,
      (FiniteProduct.number (Mode V) (M+1)).toEuclideanLin
        ((graphSpectralEmbedding hM ex ey g).toEuclideanLin x)⟫ + c * ‖x‖^2 ≤
      ⟪x, (PhysicalGram.graphHamiltonian ex ey g).toEuclideanLin x⟫ := by
  have h := FiniteProduct.oscillator_common_frequency_form (M+1) (1-2*g) a c
    (graphModeEigenvalue ex ey g) hstable ha hfreq hc
    ((graphSpectralEmbedding hM ex ey g).toEuclideanLin x)
  change a * ⟪(graphSpectralEmbedding hM ex ey g).toEuclideanLin x,
      (FiniteProduct.number (Mode V) (M+1)).toEuclideanLin
        ((graphSpectralEmbedding hM ex ey g).toEuclideanLin x)⟫ +
      c * ‖(graphSpectralEmbedding hM ex ey g).toEuclideanLin x‖^2 ≤
      ⟪(spectralEmbedding hM (graphModes ex ey g) (1-2*g) (graphModeEigenvalue ex ey g)).toEuclideanLin x,
        ((oscillatorSpectralMatrix M (1-2*g) (graphModeEigenvalue ex ey g)).transpose *
          FiniteProduct.oscillator (M+1) (1-2*g) (graphModeEigenvalue ex ey g) *
          oscillatorSpectralMatrix M (1-2*g) (graphModeEigenvalue ex ey g)).toEuclideanLin
            ((spectralEmbedding hM (graphModes ex ey g) (1-2*g) (graphModeEigenvalue ex ey g)).toEuclideanLin x)⟫ at h
  rw [graphSpectralEmbedding_norm hM hAM ex ey g x, spectralEmbedding_oscillator_inner] at h
  exact h.trans (graphHamiltonian_product_inner_lower hM hAM ex ey hx hy g hg x)

/-- The reference form bound is for the actual unchanged even-torus Hamiltonian. -/
theorem fullHamiltonian_spectral_number_lower {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (a c : ℝ)
    (hstable : ∀ i, |graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i| < 1-2*g)
    (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency (1-2*g)
      (graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i))
    (hc : c ≤ ∑ i, -(graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i)^2 /
      (2*((1-2*g)+a)))
    (x : EuclideanSpace ℝ (Torus.FullConfig (2*n) (2*m))) :
    a * ⟪(graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x,
      (FiniteProduct.number (Mode (Torus.FullVertex (2*n) (2*m))) (M+1)).toEuclideanLin
        ((graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin x)⟫ + c * ‖x‖^2 ≤
      ⟪x, (Torus.fullHamiltonian (2*n) (2*m) RealRungOperators.h RealRungOperators.G g).toEuclideanLin x⟫ := by
  have h := graphHamiltonian_spectral_number_lower hM hAM (Torus.xNext n m) (Torus.yNext n m)
    (fun v => (Torus.xNext_ne n m (by omega) v).symm)
    (fun v => (Torus.yNext_ne n m (by omega) v).symm) g hg a c hstable ha hfreq hc x
  simpa only [PhysicalGram.graphHamiltonian, PhysicalGram.number, Torus.fullHamiltonian,
    Torus.fullXNext, Torus.fullYNext, Torus.xNext, Torus.yNext] using h

/-- Zero-excluded thermal comparison for the actual physical torus Hamiltonian,
using the constructed spectral-label map. No abstract embedding/form premise remains. -/
theorem fullHamiltonian_relativePartition_tail {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (a c U β : ℝ)
    (hstable : ∀ i, |graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i| < 1-2*g)
    (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency (1-2*g)
      (graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i))
    (hc : c ≤ ∑ i, -(graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i)^2 /
      (2*((1-2*g)+a)))
    (hβ : 0 ≤ β)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) β - 1 ≤
      Real.exp (β*(U-c)) *
        ((∑ j : Fin (M+1), Real.exp (-β*a*(j.val : ℝ))) ^
          Fintype.card (Mode (Torus.FullVertex (2*n) (2*m))) - 1) := by
  exact FiniteProduct.relativePartition_tail_le_product_number M _
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin
    (graphSpectralEmbedding_injective hM hAM _ _ _)
    (graphSpectralEmbedding_norm hM hAM _ _ _)
    a c U β ha.le hβ
    (fullHamiltonian_spectral_number_lower hM n m hn hm hAM g hg a c hstable ha hfreq hc) hU

/-- Every nonlowest actual physical eigenvalue obeys the same finite reference
threshold. The separate physical ground upper bound enters with the correct sign. -/
theorem fullHamiltonian_excitation_lower {M : ℕ} (hM : 2 ≤ M)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAM : Fintype.card (Torus.FullVertex (2*n) (2*m)) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (a c U : ℝ)
    (hstable : ∀ i, |graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i| < 1-2*g)
    (ha : 0 < a)
    (hfreq : ∀ i, a ≤ FiniteOscillator.frequency (1-2*g)
      (graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i))
    (hc : c ≤ ∑ i, -(graphModeEigenvalue (Torus.xNext n m) (Torus.yNext n m) g i)^2 /
      (2*((1-2*g)+a)))
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) ≤ U)
    (k : Fin (Fintype.card (Torus.FullConfig (2*n) (2*m)))) (hk : k ≠ 0) :
    c+a-U ≤ ascendingEigenvalue (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) k -
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g) := by
  exact FiniteProduct.excitationEnergy_lower_of_product_number M _
    (PhysicalGram.fullHamiltonian_hermitian (2*n) (2*m) g)
    (graphSpectralEmbedding hM (Torus.xNext n m) (Torus.yNext n m) g).toEuclideanLin
    (graphSpectralEmbedding_injective hM hAM _ _ _)
    (graphSpectralEmbedding_norm hM hAM _ _ _)
    a c U ha.le
    (fullHamiltonian_spectral_number_lower hM n m hn hm hAM g hg a c hstable ha hfreq hc) hU k hk

end BilayerDressed.PhysicalProduct

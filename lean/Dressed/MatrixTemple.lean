import Dressed.OperatorTemple

/-! Temple's inequality specialized to a concrete finite real Hermitian matrix.
Its spectral data and orthonormal eigenvectors are obtained from the matrix's
spectral theorem, not supplied as unrelated lists. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BilayerDressed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_matrix_temple (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℝ ι) (hψ : ‖ψ‖ = 1) (ground threshold : ℝ)
    (hspectrum : ∀ i, hH.eigenvalues i = ground ∨ threshold ≤ hH.eigenvalues i)
    (hground : ∀ i, ground ≤ hH.eigenvalues i)
    (hmean : ⟪ψ,H.toEuclideanLin ψ⟫ < threshold) :
    ⟪ψ,H.toEuclideanLin ψ⟫ -
        ‖H.toEuclideanLin ψ-⟪ψ,H.toEuclideanLin ψ⟫ • ψ‖^2 /
          (threshold-⟪ψ,H.toEuclideanLin ψ⟫) ≤ ground := by
  have heig (i : ι) :
      H.toEuclideanLin (hH.eigenvectorBasis i) =
        hH.eigenvalues i • hH.eigenvectorBasis i := by
    ext j
    exact congrFun (hH.mulVec_eigenvectorBasis i) j
  exact operator_temple H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hH)
    hH.eigenvectorBasis hH.eigenvalues heig ψ hψ ground threshold
    hspectrum hground hmean

end BilayerDressed

import Dressed.FiniteDressedProjection
import Dressed.CreationResidualAction

/-! Assembly of the actual physical residual from separately certified faithful
finite degree-2,4,6 lifts. All norms are the genuine Euclidean Hilbert norms. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed
open BilayerGap FiniteOccupation
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A squared finite-lift estimate bounds the corresponding actual dressed
physical component, through the proved one-sided pure-creation intertwiner. -/
theorem faithful_component_norm_le {M : ℕ} (hM : 2 ≤ M) (K : Matrix V V ℝ)
    (Rb : TotalCutoff.Op V M (Fintype.card V)) (Rh : ConfigurationMatrix V)
    (hR : (TotalCutoff.physicalInclusion (V := V) hM).transpose*Rb =
      Rh*(TotalCutoff.physicalInclusion (V := V) hM).transpose)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ‖Rb.toEuclideanLin
      (TotalCutoff.PairNorm.finiteTrial (FiniteDressed.modeKernel K) (Fintype.card V/2))‖^2 ≤ ε^2) :
    ‖Rh.toEuclideanLin (dressedVector K)‖ ≤ ε := by
  apply (FiniteDressed.physical_action_dressed_norm_le hM K Rb Rh hR).trans
  nlinarith [norm_nonneg (Rb.toEuclideanLin
    (TotalCutoff.PairNorm.finiteTrial (FiniteDressed.modeKernel K) (Fintype.card V/2)))]

/-- The exact full Hamiltonian residual is bounded after all three component
bounds have been proved; the sextic contribution is retained explicitly. -/
theorem graph_residual_norm_le_of_components (K : Matrix V V ℝ)
    (hK : ∀ r s,K r s=K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u,ex u≠u) (hy : ∀ u,ey u≠u) (g ε2 ε4 ε6 : ℝ)
    (h2 : ‖((GlobalResidual.residual2 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)‖ ≤ ε2)
    (h4 : ‖((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)‖ ≤ ε4)
    (h6 : ‖((GlobalResidual.residual6 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)‖ ≤ ε6) :
    ‖(CartesianBasis.graphHamiltonian ex ey g).toEuclideanLin (dressedVector K)-
      GlobalResidual.residualShift K ex ey g • dressedVector K‖ ≤ ε2+ε4+ε6 := by
  change ‖(Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
    (CartesianBasis.graphHamiltonian ex ey g) (dressedVector K)-
      GlobalResidual.residualShift K ex ey g • dressedVector K‖ ≤ _
  rw [GlobalResidual.graph_dressed_residual_action K hK ex ey hx hy g]
  simp only [Subalgebra.coe_add,map_add,ContinuousLinearMap.add_apply]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add h2 h4)) h6)

/-- The same exact residual identity combines the three actual unnormalized
means. The physical trial norm remains handled separately by Temple. -/
theorem graph_residual_mean_le_of_components (K : Matrix V V ℝ)
    (hK : ∀ r s,K r s=K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u,ex u≠u) (hy : ∀ u,ey u≠u) (g m2 m4 m6 : ℝ)
    (h2 : |⟪dressedVector K,((GlobalResidual.residual2 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)⟫| ≤ m2)
    (h4 : |⟪dressedVector K,((GlobalResidual.residual4 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)⟫| ≤ m4)
    (h6 : |⟪dressedVector K,((GlobalResidual.residual6 K ex ey g : GlobalResidual.creationAlgebra V) :
      ConfigurationMatrix V).toEuclideanLin (dressedVector K)⟫| ≤ m6) :
    |⟪dressedVector K,(CartesianBasis.graphHamiltonian ex ey g).toEuclideanLin (dressedVector K)-
      GlobalResidual.residualShift K ex ey g • dressedVector K⟫| ≤ m2+m4+m6 := by
  change |⟪dressedVector K,(Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
    (CartesianBasis.graphHamiltonian ex ey g) (dressedVector K)-
      GlobalResidual.residualShift K ex ey g • dressedVector K⟫| ≤ _
  rw [GlobalResidual.graph_dressed_residual_action K hK ex ey hx hy g]
  simp only [Subalgebra.coe_add,map_add,ContinuousLinearMap.add_apply,inner_add_right]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add h2 h4)) h6)

end BilayerDressed

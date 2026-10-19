import Dressed.GlobalDressedResidual
import Dressed.FiniteDressedProjection

/-! The actual creation-only global residual acts directly on the dressed
vector. The finite nilpotent exponential commutes with every element of the
concrete creation algebra; this is not a compression-multiplicativity claim. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.GlobalResidual
variable {V : Type*} [Fintype V] [DecidableEq V]

local instance : Module ℚ (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- Every actual creation polynomial commutes with the actual pair generator. -/
theorem creation_commutes_pairGenerator (K : V→V→ℝ) (R : creationAlgebra V) :
    Commute (pairGenerator K)
      (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (R : ConfigurationMatrix V)) := by
  have hm : Commute ((S K : creationAlgebra V) : ConfigurationMatrix V)
      (R : ConfigurationMatrix V) := by
    change ((S K * R : creationAlgebra V) : ConfigurationMatrix V)=
      ((R * S K : creationAlgebra V) : ConfigurationMatrix V)
    rw [mul_comm]
  have hc := hm.map (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
  simpa only [coe_S,pairGenerator,pairKernelS] using hc

/-- Commutation is proved through the finite Taylor sum, including zero kernels. -/
theorem creation_commutes_taylor (K : V→V→ℝ) (R : creationAlgebra V) (m : ℕ) :
    Commute (taylorOperator (pairGenerator K) m)
      (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ) (R : ConfigurationMatrix V)) := by
  have hc := creation_commutes_pairGenerator K R
  change taylorOperator (pairGenerator K) m * _ = _ * taylorOperator (pairGenerator K) m
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.mul_apply,taylorOperator,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact congrArg (fun A : ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V => A x)
    (hc.pow_left k).eq

/-- Exact reversal of the exponential/residual order on the physical vacuum. -/
theorem creation_action_dressed (K : V→V→ℝ) (R : creationAlgebra V) :
    IsNilpotent.exp (pairGenerator K)
      ((Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
        (R : ConfigurationMatrix V) vacuumVector)=
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
      (R : ConfigurationMatrix V) (dressedVector K) := by
  rw [dressedVector,nilpotent_exp_eq_taylor _ (Fintype.card V/2+1)
    (FiniteDressed.pairGenerator_pow_half_eq_zero K)]
  exact congrArg (fun A : ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V =>
    A vacuumVector) (creation_commutes_taylor K R (Fintype.card V/2+1)).eq

/-- The literal degree-two, degree-four and degree-six residual acts on ψ. -/
theorem graph_dressed_residual_action (K : V→V→ℝ)
    (hK : ∀ r s,K r s=K s r) (ex ey : Equiv.Perm V)
    (hx : ∀ u,ex u≠u) (hy : ∀ u,ey u≠u) (g : ℝ) :
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
      (CartesianBasis.graphHamiltonian ex ey g) (dressedVector K)-
        residualShift K ex ey g • dressedVector K=
    (Matrix.toEuclideanCLM (n := Configuration V) (𝕜 := ℝ))
      ((residual2 K ex ey g+residual4 K ex ey g+residual6 K ex ey g :
        creationAlgebra V) : ConfigurationMatrix V) (dressedVector K) := by
  rw [graph_dressed_residual K hK ex ey hx hy g,creation_action_dressed]

end BilayerDressed.GlobalResidual

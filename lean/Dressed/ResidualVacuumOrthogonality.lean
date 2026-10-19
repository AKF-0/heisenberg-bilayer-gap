import Dressed.ConcreteResidualCoefficients
import Dressed.DressedVacuum

/-! The actual residual has no vacuum component. This is the improvement that
separates the reference shift from the true Rayleigh quotient. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed
open GlobalResidual BilayerGap
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem literalR4_vacuum_row_zero (u v : V) (A B : Fin 3 → ConfigurationMatrix V)
    (k : ℝ) (t : Configuration V) :
    QuarticSextic.literalR4 u v A B k vacuumConfiguration t=0 := by
  have hc (w : V) (α : Fin 3) (s : Configuration V) :
      globalCreate w α vacuumConfiguration s=0 := globalCreate_vacuum_row_zero w α s
  simp [QuarticSextic.literalR4,Matrix.mul_apply,Matrix.sum_apply,hc]

 theorem literalR6_vacuum_row_zero (u v : V) (A B : Fin 3 → ConfigurationMatrix V)
    (t : Configuration V) :
    QuarticSextic.literalR6 u v A B vacuumConfiguration t=0 := by
  have hc (w : V) (α : Fin 3) (s : Configuration V) :
      globalCreate w α vacuumConfiguration s=0 := globalCreate_vacuum_row_zero w α s
  simp [QuarticSextic.literalR6,Matrix.mul_apply,Matrix.sum_apply,hc]

 theorem residual4_vacuum_row_zero (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ)
    (t : Configuration V) :
    ((residual4 K ex ey g : creationAlgebra V) : ConfigurationMatrix V)
      vacuumConfiguration t=0 := by
  simp only [residual4,Subalgebra.coe_smul,Subalgebra.coe_add,
    AddSubmonoidClass.coe_finset_sum,bondResidual4,QuarticSextic.coe_bondR4]
  simp [Matrix.sum_apply,Matrix.smul_apply,literalR4_vacuum_row_zero]

 theorem residual6_vacuum_row_zero (K : V → V → ℝ) (ex ey : Equiv.Perm V) (g : ℝ)
    (t : Configuration V) :
    ((residual6 K ex ey g : creationAlgebra V) : ConfigurationMatrix V)
      vacuumConfiguration t=0 := by
  simp only [residual6,Subalgebra.coe_smul,Subalgebra.coe_add,
    AddSubmonoidClass.coe_finset_sum,bondResidual6,QuarticSextic.coe_bondR6]
  simp [Matrix.sum_apply,Matrix.smul_apply,literalR6_vacuum_row_zero]

local instance residualVacuumRatModule : Module ℚ (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- Exact nilpotent exponential preserves the vacuum coordinate of any vector. -/
 theorem pair_exp_vacuum_coordinate (K : V → V → ℝ) (x : ConfigurationHilbert V) :
    (IsNilpotent.exp (pairGenerator K) x) vacuumConfiguration=x vacuumConfiguration := by
  obtain ⟨m,hm⟩ := pairGenerator_nilpotent K
  have hm1 : pairGenerator K^(m+1)=0 := by rw [pow_succ,hm,zero_mul]
  rw [nilpotent_exp_eq_taylor _ (m+1) hm1]
  exact matrix_taylor_vacuum_coordinate (pairKernelS K)
    (pairKernel_vacuum_row_zero (fun u v => K u v/2)) m x

namespace SeedGraphs

 theorem residual_vacuum_row_zero (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) (t : Configuration (Torus.Vertex n m)) :
    ((residual2 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g +
        residual4 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g +
        residual6 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g :
          creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))
      vacuumConfiguration t=0 := by
  simp only [Subalgebra.coe_add,Matrix.add_apply,coe_residual2 n m h hi,
    residual4_vacuum_row_zero,residual6_vacuum_row_zero,add_zero]
  exact pairKernel_vacuum_row_zero (fun u v => (graph n m h).quadraticResidual g u v/2) t

/-- Orthogonality is proved for the actual Hamiltonian and actual dressed vector. -/
 theorem graph_dressed_residual_vacuum_orthogonal (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ)
    (hx : ∀ u,Torus.xNext n m u≠u) (hy : ∀ u,Torus.yNext n m u≠u) :
    ⟪(vacuumVector : ConfigurationHilbert (Torus.Vertex n m)),
      Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
        (CartesianBasis.graphHamiltonian (Torus.xNext n m) (Torus.yNext n m) g)
        (dressedVector ((graph n m h).kernel g))-
      residualShift ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g •
        dressedVector ((graph n m h).kernel g)⟫=0 := by
  rw [graph_dressed_residual _ ((graph n m h).kernel_symmetric g) _ _ hx hy]
  simp only [vacuumVector,EuclideanSpace.inner_single_left]
  rw [pair_exp_vacuum_coordinate]
  simp only [map_one,one_mul]
  change (Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ) _)
    (vacuumVector : ConfigurationHilbert (Torus.Vertex n m)) vacuumConfiguration=0
  rw [matrix_vacuum_apply]
  simpa using residual_vacuum_row_zero n m h hi g (TripletNumber.vacuum : Configuration (Torus.Vertex n m))

end SeedGraphs
end BilayerDressed

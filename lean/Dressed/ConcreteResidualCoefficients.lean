import Dressed.GlobalDressedResidual
import Dressed.QuadraticRegroupingAssembly
import Dressed.GraphHigherResidualBounds

/-! Connect the literal residual of the actual Hamiltonian to the independently
proved compact coefficient and higher-degree norm bounds. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed
open GlobalResidual BilayerGap
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem coe_outsideField_C (K : V → V → ℝ) (u v r : V) (α : Fin 3) :
    ((outsideField C K u v r α : creationAlgebra V) : ConfigurationMatrix V) =
      outsideCreationField K u v r α := by
  simp [outsideField,outsideCreationField,finiteCreationField]

namespace FourRegularData
variable (G : FourRegularData V)

 theorem coe_bondResidual4 (g : ℝ) (u v : V) :
    ((bondResidual4 (G.kernel g) u v : creationAlgebra V) : ConfigurationMatrix V)=
      G.quarticEdge g u v := by
  rw [bondResidual4,QuarticSextic.coe_bondR4]
  simp only [coe_outsideField_C,quarticEdge]

 theorem coe_bondResidual6 (g : ℝ) (u v : V) :
    ((bondResidual6 (G.kernel g) u v : creationAlgebra V) : ConfigurationMatrix V)=
      G.sexticEdge g u v := by
  rw [bondResidual6,QuarticSextic.coe_bondR6]
  simp only [coe_outsideField_C,sexticEdge]

 theorem coe_residual4 (g : ℝ) (ex ey : Equiv.Perm V) :
    ((residual4 (G.kernel g) ex ey g : creationAlgebra V) : ConfigurationMatrix V)=
      G.quarticGraph g ex ey := by
  simp only [residual4,Subalgebra.coe_smul,Subalgebra.coe_add,
    AddSubmonoidClass.coe_finset_sum,G.coe_bondResidual4,quarticGraph]

 theorem coe_residual6 (g : ℝ) (ex ey : Equiv.Perm V) :
    ((residual6 (G.kernel g) ex ey g : creationAlgebra V) : ConfigurationMatrix V)=
      G.sexticGraph g ex ey := by
  simp only [residual6,Subalgebra.coe_smul,Subalgebra.coe_add,
    AddSubmonoidClass.coe_finset_sum,G.coe_bondResidual6,sexticGraph]

 theorem residual4_norm_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (ex ey : Equiv.Perm V) (hx : ∀ u,G.adjacency u (ex u)=1)
    (hy : ∀ u,G.adjacency u (ey u)=1) :
    QuarticSextic.hnorm ((residual4 (G.kernel g) ex ey g : creationAlgebra V) :
      ConfigurationMatrix V) ≤ 9*(Fintype.card V : ℝ)*g^3 := by
  rw [G.coe_residual4]
  exact G.quarticGraph_bound g hg hmax ex ey hx hy

 theorem residual6_norm_bound (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (ex ey : Equiv.Perm V) (hx : ∀ u,G.adjacency u (ex u)=1)
    (hy : ∀ u,G.adjacency u (ey u)=1) :
    QuarticSextic.hnorm ((residual6 (G.kernel g) ex ey g : creationAlgebra V) :
      ConfigurationMatrix V) ≤ 4*(Fintype.card V : ℝ)*g^5 := by
  rw [G.coe_residual6]
  exact G.sexticGraph_bound g hg hmax ex ey hx hy

/-- The reference shift is exact and extensive, including its cubic term. -/
 theorem residualShift_eq (g : ℝ) (ex ey : Equiv.Perm V)
    (hx : ∀ u,G.adjacency u (ex u)=1) (hy : ∀ u,G.adjacency u (ey u)=1) :
    residualShift (G.kernel g) ex ey g =
      -(3/4 : ℝ)*(Fintype.card V : ℝ)*g^2-(3/8 : ℝ)*(Fintype.card V : ℝ)*g^3 := by
  simp only [residualShift,G.kernel_on_edge g _ _ (hx _),G.kernel_on_edge g _ _ (hy _),
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end FourRegularData

namespace SeedGraphs

 theorem graph_x_edge (n m : ℕ) (h : Conditions n m) (u : Torus.Vertex n m) :
    (graph n m h).adjacency u (Torus.xNext n m u)=1 := by
  simp [graph,adjacencyNat,adjacent]

 theorem graph_y_edge (n m : ℕ) (h : Conditions n m) (u : Torus.Vertex n m) :
    (graph n m h).adjacency u (Torus.yNext n m u)=1 := by
  simp [graph,adjacencyNat,adjacent]

/-- Equality in the actual creation subalgebra, not merely a scalar norm surrogate. -/
 theorem residual2_eq (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    residual2 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g =
      S ((graph n m h).quadraticResidual g) := by
  exact QuadraticRegrouping.physical_edge_compact n m h hi C
    (fun u α => C_mul_same u α α) g

/-- The literal physical degree-two residual is precisely the compact pair matrix. -/
 theorem coe_residual2 (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    ((residual2 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g :
      creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m)) =
        pairKernelS ((graph n m h).quadraticResidual g) := by
  rw [residual2_eq n m h hi,coe_S]
  rfl

 theorem residual2_vacuum_norm (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
      ((residual2 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g :
        creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))
      vacuumVector‖ ≤ 24*Real.sqrt (Fintype.card (Torus.Vertex n m) : ℝ)*g^3 := by
  rw [coe_residual2 n m h hi]
  exact (graph n m h).quadraticResidual_vacuum_norm g hg hmax

end SeedGraphs
end BilayerDressed

import Dressed.ConcreteResidualCoefficients
import Dressed.DressedVacuum

/-! Actual Hilbert-space trial and residual estimates for the finite-dimensional
backup interval 0 ≤ g ≤ 3/200. This is not the stronger cubic g ≤ 1/10 route. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed
open GlobalResidual BilayerGap
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem vacuumVector_norm : ‖(vacuumVector : ConfigurationHilbert V)‖ = 1 := by
  simp [vacuumVector]

namespace FourRegularData
variable (G : FourRegularData V)

 theorem pairGenerator_norm_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (hcard : Fintype.card V≤64) : ‖pairGenerator (G.kernel g)‖≤9/10 := by
  have hb := pairKernelS_opNorm_le_of_row (G.kernel g) ((103/100 : ℝ)*g)
    (G.kernel_row_bound_small g hg hmax)
  have hs : Real.sqrt 3≤7/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3), Real.sqrt_nonneg (3 : ℝ)]
  have hc : (Fintype.card V : ℝ)≤64 := by exact_mod_cast hcard
  have hc0 : (0 : ℝ)≤Fintype.card V := by positivity
  have h₁ := mul_le_mul_of_nonneg_right hs (mul_nonneg hc0 hg)
  have h₂ := mul_le_mul_of_nonneg_right hc hg
  have h₃ := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ)≤64)
  change ‖pairGenerator (G.kernel g)‖≤_ at hb
  nlinarith

 theorem pairGenerator_vacuum_norm_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    ‖pairGenerator (G.kernel g) vacuumVector‖≤
      (2/3 : ℝ)*g*Real.sqrt (Fintype.card V : ℝ) := by
  have hb := pairKernelS_vacuum_norm_sq_le_entry_row (G.kernel g)
    ((13/50 : ℝ)*g) ((103/100 : ℝ)*g) (G.kernel_symmetric g)
    (G.kernel_diagonal g) (G.kernel_entry_bound_small g hg hmax)
    (G.kernel_row_bound_small g hg hmax) (by positivity)
  change ‖pairGenerator (G.kernel g) vacuumVector‖^2≤_ at hb
  have hs := Real.sq_sqrt (show (0 : ℝ)≤Fintype.card V by positivity)
  have hr : 0≤(2/3 : ℝ)*g*Real.sqrt (Fintype.card V : ℝ) := by positivity
  have hn := norm_nonneg (pairGenerator (G.kernel g) vacuumVector)
  nlinarith [mul_nonneg (show (0 : ℝ)≤Fintype.card V by positivity) (sq_nonneg g)]

 theorem dressedVector_distance_small (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (hcard : Fintype.card V≤64) :
    ‖dressedVector (G.kernel g)-vacuumVector‖≤
      (5/3 : ℝ)*g*Real.sqrt (Fintype.card V : ℝ) := by
  have h := dressedVector_distance_le_five_halves (G.kernel g)
    (G.pairGenerator_norm_small g hg hmax hcard)
  have h' := mul_le_mul_of_nonneg_left (G.pairGenerator_vacuum_norm_small g hg hmax)
    (by norm_num : (0 : ℝ)≤5/2)
  exact h.trans (h'.trans_eq (by ring))

end FourRegularData

local instance trialBoundsRatModule : Module ℚ (ConfigurationHilbert V →L[ℝ] ConfigurationHilbert V) :=
  Module.compHom _ (Rat.castHom ℝ)

/-- The same Euclidean operator norm is used before and after exponentiation. -/
 theorem pair_exp_apply_norm_small (K : V → V → ℝ) (hS : ‖pairGenerator K‖≤9/10)
    (x : ConfigurationHilbert V) :
    ‖IsNilpotent.exp (pairGenerator K) x‖≤(5/2 : ℝ)*‖x‖ := by
  have h := norm_nilpotent_exp_le (pairGenerator K) (pairGenerator_nilpotent K)
  have he := (Real.exp_le_exp.mpr hS).trans exp_nine_tenths_lt.le
  exact ((IsNilpotent.exp (pairGenerator K)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (h.trans he) (norm_nonneg x))

namespace SeedGraphs

/-- Actual R2+R4+R6 vacuum norm, with the half-ordered normalization retained. -/
 theorem residual_vacuum_norm_small (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) (hg : 0≤g) (hmax : g≤3/200) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
      ((residual2 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g +
        residual4 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g +
        residual6 ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g :
          creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))
      vacuumVector‖ ≤
      (24*Real.sqrt (Fintype.card (Torus.Vertex n m) : ℝ)+
        9*(Fintype.card (Torus.Vertex n m) : ℝ))*g^3+
        4*(Fintype.card (Torus.Vertex n m) : ℝ)*g^5 := by
  let G := graph n m h
  let ex := Torus.xNext n m
  let ey := Torus.yNext n m
  let R (d : ℕ) : ConfigurationMatrix (Torus.Vertex n m) :=
    ((if d=2 then residual2 (G.kernel g) ex ey g else
      if d=4 then residual4 (G.kernel g) ex ey g else residual6 (G.kernel g) ex ey g) :
        creationAlgebra (Torus.Vertex n m))
  have h₂ := residual2_vacuum_norm n m h hi g hg hmax
  have h₄ := G.residual4_norm_bound g hg hmax ex ey (graph_x_edge n m h) (graph_y_edge n m h)
  have h₆ := G.residual6_norm_bound g hg hmax ex ey (graph_x_edge n m h) (graph_y_edge n m h)
  have ha₄ := (Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
    ((residual4 (G.kernel g) ex ey g : creationAlgebra (Torus.Vertex n m)) :
      ConfigurationMatrix (Torus.Vertex n m))).le_opNorm vacuumVector
  have ha₆ := (Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
    ((residual6 (G.kernel g) ex ey g : creationAlgebra (Torus.Vertex n m)) :
      ConfigurationMatrix (Torus.Vertex n m))).le_opNorm vacuumVector
  rw [vacuumVector_norm,mul_one] at ha₄ ha₆
  simp only [Subalgebra.coe_add,map_add,ContinuousLinearMap.add_apply]
  apply (norm_add_le _ _).trans
  apply (add_le_add_right (norm_add_le _ _) _).trans
  have hh := add_le_add (add_le_add h₂ (ha₄.trans h₄)) (ha₆.trans h₆)
  exact hh.trans_eq (by ring)

/-- The exact concrete Cartesian Hamiltonian residual, not a coefficient proxy. -/
 theorem graph_dressed_residual_norm_small (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) (hg : 0≤g) (hmax : g≤3/200)
    (hcard : Fintype.card (Torus.Vertex n m)≤64)
    (hx : ∀ u,Torus.xNext n m u≠u) (hy : ∀ u,Torus.yNext n m u≠u) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
        (CartesianBasis.graphHamiltonian (Torus.xNext n m) (Torus.yNext n m) g)
        (dressedVector ((graph n m h).kernel g))-
      residualShift ((graph n m h).kernel g) (Torus.xNext n m) (Torus.yNext n m) g •
        dressedVector ((graph n m h).kernel g)‖ ≤
      (5/2 : ℝ)*((24*Real.sqrt (Fintype.card (Torus.Vertex n m) : ℝ)+
        9*(Fintype.card (Torus.Vertex n m) : ℝ))*g^3+
        4*(Fintype.card (Torus.Vertex n m) : ℝ)*g^5) := by
  rw [graph_dressed_residual _ ((graph n m h).kernel_symmetric g) _ _ hx hy]
  exact (pair_exp_apply_norm_small _ ((graph n m h).pairGenerator_norm_small
    g hg hmax hcard) _).trans
    (mul_le_mul_of_nonneg_left (residual_vacuum_norm_small n m h hi g hg hmax) (by norm_num))

end SeedGraphs
end BilayerDressed

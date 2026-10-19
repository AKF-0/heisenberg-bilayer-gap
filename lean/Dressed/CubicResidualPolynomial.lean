import Dressed.CubicResidualPair
import Dressed.GlobalDressedResidual
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Exact rational polynomial data for the actual cubic residual.
The finite graph equality precedes every numerical interval bound. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicResidualPolynomial
open BilayerGap BilayerDressed.SeedGraphs BilayerDressed.CubicSeedChecks
open BilayerDressed.CubicWick.FourRegularData BilayerDressed.CubicResidualPair
open Polynomial

/-- Direct connection to the degree-two summand of the actual dressed Hamiltonian. -/
theorem residual2_eq (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    GlobalResidual.residual2 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g=
      GlobalResidual.S (residual (graph n m h) g) :=
  physical_edge_compact n m h hi GlobalResidual.C
    (fun u α => GlobalResidual.C_mul_same u α α) g

theorem coe_residual2 (n m : ℕ) (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    ((GlobalResidual.residual2 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g :
      GlobalResidual.creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))=
      pairKernelS (residual (graph n m h) g) := by
  rw [residual2_eq n m h hi,GlobalResidual.coe_S]
  rfl

theorem coe_residual2_eq_physicalPairResidual (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (g : ℝ) :
    ((GlobalResidual.residual2 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g :
      GlobalResidual.creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))=
      physicalPairResidual n m h g := by
  rw [coe_residual2 n m h hi,physicalPairResidual_eq n m h hi]

section Torus
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- Rational polynomial, computed only on the rung graph. -/
def kernelPoly (q : Torus.Vertex n m) : ℚ[X] :=
  C (-(adjacencyNat n m 0 q : ℚ)/4)*X+
    C (((offWalk2 n m 0 q : ℚ)-(adjacencyNat n m 0 q : ℚ))/8)*X^2-
    C ((5*(walk3 n m 0 q : ℚ)-4*(offWalk2 n m 0 q : ℚ)-
      40*(adjacencyNat n m 0 q : ℚ))/64)*X^3

def dkPoly (q : Torus.Vertex n m) : ℚ[X] :=
  ∑ r,kernelPoly n m r*C (adjacencyNat n m r q : ℚ)

def kdkPoly (q : Torus.Vertex n m) : ℚ[X] :=
  ∑ r,kernelPoly n m r*dkPoly n m (q-r)

def residualPoly (q : Torus.Vertex n m) : ℚ[X] :=
  if q=0 then 0 else
    C 2*kernelPoly n m q+C ((adjacencyNat n m 0 q : ℚ)/2)*X+
      X*dkPoly n m q-X*C (adjacencyNat n m 0 q : ℚ)*kernelPoly n m q+
      C (1/2)*X*kdkPoly n m q-C 4*X*dkPoly n m 0*kernelPoly n m q+
      C 2*X*C (adjacencyNat n m 0 q : ℚ)*(kernelPoly n m q)^2

def normSquarePoly : ℚ[X] :=
  C (3*((2*n)*(2*m) : ℚ)/2)*∑ q,(residualPoly n m q)^2

/-- Evaluation uses the canonical rational-to-real map. -/
def evaluate (g : ℝ) : ℚ[X] →+* ℝ := eval₂RingHom (algebraMap ℚ ℝ) g

@[simp] theorem evaluate_C (g : ℝ) (a : ℚ) : evaluate g (C a)=(a : ℝ) := by
  exact eval₂_C _ _

@[simp] theorem evaluate_X (g : ℝ) : evaluate g X=g := by
  exact eval₂_X _ _

 theorem kernelPoly_evaluate (g : ℝ) (q : Torus.Vertex n m) :
    evaluate g (kernelPoly n m q)=rootKernel n m g q := by
  simp only [kernelPoly,map_add,map_sub,map_mul,map_pow,evaluate_C,evaluate_X,
    Rat.cast_div,Rat.cast_neg,Rat.cast_mul,Rat.cast_sub,Rat.cast_natCast,Rat.cast_ofNat]
  unfold rootKernel
  ring

 theorem dkPoly_evaluate (g : ℝ) (q : Torus.Vertex n m) :
    evaluate g (dkPoly n m q)=rootDK n m g q := by
  simp only [dkPoly,map_sum,map_mul,kernelPoly_evaluate,evaluate_C,Rat.cast_natCast,rootDK]

 theorem kdkPoly_evaluate (g : ℝ) (q : Torus.Vertex n m) :
    evaluate g (kdkPoly n m q)=rootKDK n m g q := by
  simp only [kdkPoly,map_sum,map_mul,kernelPoly_evaluate,dkPoly_evaluate,rootKDK]

 theorem residualPoly_evaluate (g : ℝ) (q : Torus.Vertex n m) :
    evaluate g (residualPoly n m q)=rootResidual n m g q := by
  by_cases hq : q=0
  · simp [residualPoly,rootResidual,hq]
  · simp only [residualPoly,rootResidual,if_neg hq,map_add,map_sub,map_mul,map_pow,
      kernelPoly_evaluate,dkPoly_evaluate,kdkPoly_evaluate,evaluate_C,evaluate_X,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]
    ring

 theorem normSquarePoly_evaluate (g : ℝ) :
    evaluate g (normSquarePoly n m)=
      (3*((2*n)*(2*m) : ℝ)/2)*∑ q,(rootResidual n m g q)^2 := by
  simp only [normSquarePoly,map_mul,map_sum,map_pow,residualPoly_evaluate,evaluate_C,
    Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]

/-- Exact rational-polynomial evaluation equals the physical residual norm. -/
 theorem residual2_vacuum_norm_sq (h : Conditions n m) (hi : IncidenceIdentity n m) (g : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Configuration (Torus.Vertex n m)) (𝕜 := ℝ)
      ((GlobalResidual.residual2 (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g :
        GlobalResidual.creationAlgebra (Torus.Vertex n m)) : ConfigurationMatrix (Torus.Vertex n m))
      vacuumVector‖^2=evaluate g (normSquarePoly n m) := by
  rw [coe_residual2 n m h hi,residual_vacuum_norm_sq n m h hi,normSquarePoly_evaluate]

end Torus
end BilayerDressed.CubicResidualPolynomial

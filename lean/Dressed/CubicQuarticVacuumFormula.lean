import Dressed.QuarticResidualSupportNorm
import Dressed.CubicQuarticCoefficientCount

/-! Exact actual cubic quartic vacuum norm with deterministic row-major
matching coefficients and stabilizer-safe rooted counting. No numerical
coefficient aggregate is supplied or assumed by the equality theorem. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicQuarticVacuum
open BilayerGap SeedGraphs CubicWick.FourRegularData
open QuarticRootCounting CubicQuarticCoefficientCount

/-- The literal physical R4 vacuum norm is exactly its rooted Gram sum. -/
theorem norm_sq_eq_rooted (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (h : Conditions n m) (g : ℝ) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g :
      ConfigurationMatrix (Torus.Vertex n m)).toEuclideanLin vacuumVector‖^2 =
      (Fintype.card (Torus.Vertex n m) : ℝ)/4 *
        rootedMass (fun S => matchingWeight (coefficient n m h g S)) 0 := by
  rw [QuarticResidualSupportNorm.residual_vacuum_norm_sq (QuarticRowMajor.enumeration n m)]
  change (∑ S : Support (Torus.Vertex n m), matchingWeight (coefficient n m h g S)) = _
  exact actual_weight_eq_rooted n m h g

/-- A kernel-checked actual rooted aggregate transfers to the physical norm. -/
theorem norm_sq_le_of_rooted (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (h : Conditions n m) (g F : ℝ)
    (hF : (Fintype.card (Torus.Vertex n m) : ℝ)/4 *
      rootedMass (fun S => matchingWeight (coefficient n m h g S)) 0 ≤ F) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g :
      ConfigurationMatrix (Torus.Vertex n m)).toEuclideanLin vacuumVector‖^2 ≤ F := by
  rw [norm_sq_eq_rooted]
  exact hF

end BilayerDressed.CubicQuarticVacuum

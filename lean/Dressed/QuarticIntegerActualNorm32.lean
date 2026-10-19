import Dressed.QuarticIntegerMembership32Accepted
import Dressed.QuarticIntegerNormAggregate32

/-! Actual8×4 quartic vacuum bound after exact signed membership and Gram summation. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerActual
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerTable

theorem vacuum32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin vacuumVector‖^2≤
      (ScalarTrial.F32_4:ℝ) := by
  rw [physical_norm_eq 4 2 4495 kernelData32 QuarticIntegerComputationalData.raw32
    dictionary32 QuarticIntegerComputationalData.ids32 cachedKernel32_eq
    QuarticIntegerComputationalData.hypotheses32.1 QuarticIntegerMembership32Accepted.checked
    eight_by_four_conditions eight_by_four_incidence
    QuarticIntegerComputationalData.hypotheses32.2 QuarticIntegerComputationalData.count32
    8 (by decide) g,QuarticIntegerNormAggregate32.aggregate_checked]
  exact QuarticIntegerNorm.witness32_bound g hg hmax

theorem rooted32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    (Fintype.card (Torus.Vertex 4 2):ℝ)/4 *
      QuarticRootCounting.rootedMass (fun S=>QuarticRootCounting.matchingWeight
        (CubicQuarticCoefficientCount.coefficient 4 2 eight_by_four_conditions g S)) 0≤
      (ScalarTrial.F32_4:ℝ) := by
  rw [←CubicQuarticVacuum.norm_sq_eq_rooted 4 2 eight_by_four_conditions g]
  exact vacuum32 g hg hmax

end BilayerDressed.QuarticIntegerActual

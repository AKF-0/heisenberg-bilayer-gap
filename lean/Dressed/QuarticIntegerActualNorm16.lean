import Dressed.QuarticIntegerMembership16Accepted
import Dressed.QuarticIntegerNormAggregate16

/-! The actual finite4×4 R4 vacuum bound, with signed membership, all rooted
supports, exact Gram aggregation, and the full real-interval scalar bound proved. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerActual
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerRows QuarticIntegerTable

/-- No coefficient, norm, or enumeration oracle remains in this physical bound. -/
theorem vacuum16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin vacuumVector‖^2≤
      (ScalarTrial.F16_4:ℝ) := by
  rw [physical_norm_eq 2 2 455 kernelData16 raw16 dictionary16 ids16
    cachedKernel16_eq valid16 QuarticIntegerMembership16Accepted.checked
    four_by_four_conditions four_by_four_incidence codes16 count16 4 (by decide) g,
    QuarticIntegerNormAggregate16.aggregate_checked]
  exact QuarticIntegerNorm.witness16_bound g hg hmax

/-- The exact actual rooted Gram expression required by the seed interface. -/
theorem rooted16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    (Fintype.card (Torus.Vertex 2 2):ℝ)/4 *
      QuarticRootCounting.rootedMass (fun S=>QuarticRootCounting.matchingWeight
        (CubicQuarticCoefficientCount.coefficient 2 2 four_by_four_conditions g S)) 0≤
      (ScalarTrial.F16_4:ℝ) := by
  rw [←CubicQuarticVacuum.norm_sq_eq_rooted 2 2 four_by_four_conditions g]
  exact vacuum16 g hg hmax

end BilayerDressed.QuarticIntegerActual

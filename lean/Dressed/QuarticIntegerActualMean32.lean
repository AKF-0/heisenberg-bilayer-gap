import Dressed.QuarticIntegerMembership32Accepted
import Dressed.QuarticIntegerEnvelope32
import Dressed.QuarticIntegerCovarianceCache
import Dressed.QuarticIntegerWeightedTotals32

/-! The actual canonical quartic mean on all rooted supports. Signed membership,
complete row coverage, all-real envelopes and exact weighted totals are explicit
proved dependencies rather than hypotheses of this endpoint. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerActual
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerMeanEvaluation QuarticCanonicalMean

theorem mean32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    meanCoefficient (QuarticRowMajor.enumeration 4 2)
      (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g
      (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10))
        (tau 11548632)) ≤ (CubicQuarticSeed.meanBudget32:ℝ) := by
  exact (meanCoefficient_le_integer 4 2 4495 kernelData32
    QuarticIntegerComputationalData.raw32 dictionary32 QuarticIntegerComputationalData.ids32
    cachedKernel32_eq QuarticIntegerComputationalData.hypotheses32.1
    QuarticIntegerMembership32Accepted.checked eight_by_four_conditions eight_by_four_incidence
    QuarticIntegerComputationalData.hypotheses32.2 QuarticIntegerComputationalData.count32
    QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    QuarticIntegerCovarianceData.covarianceDenominator32 upperDenominator32 11548632
    (by decide) QuarticIntegerCovariance.cache32_eq g
    (QuarticIntegerEnvelope.bound32 g hg hmax)).trans
      QuarticIntegerWeightedTotals32.weightedNumerator_budget

end BilayerDressed.QuarticIntegerActual

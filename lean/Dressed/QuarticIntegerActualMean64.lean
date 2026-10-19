import Dressed.QuarticIntegerMembership64Accepted
import Dressed.QuarticIntegerEnvelope64
import Dressed.QuarticIntegerCovarianceCache
import Dressed.QuarticIntegerWeightedTotals64

/-! The actual canonical quartic mean on all rooted supports. Signed membership,
complete row coverage, all-real envelopes and exact weighted totals are explicit
proved dependencies rather than hypotheses of this endpoint. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerActual
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerMeanEvaluation QuarticCanonicalMean

theorem mean64 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    meanCoefficient (QuarticRowMajor.enumeration 4 4)
      (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g
      (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10))
        (tau 11499920)) ≤ (CubicQuarticSeed.meanBudget64:ℝ) := by
  exact (meanCoefficient_le_integer 4 4 39711 kernelData64
    QuarticIntegerComputationalData.raw64 dictionary64 QuarticIntegerComputationalData.ids64
    cachedKernel64_eq QuarticIntegerComputationalData.hypotheses64.1
    QuarticIntegerMembership64Accepted.checked eight_by_eight_conditions eight_by_eight_incidence
    QuarticIntegerComputationalData.hypotheses64.2 QuarticIntegerComputationalData.count64
    QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    QuarticIntegerCovarianceData.covarianceDenominator64 upperDenominator64 11499920
    (by decide) QuarticIntegerCovariance.cache64_eq g
    (QuarticIntegerEnvelope.bound64 g hg hmax)).trans
      QuarticIntegerWeightedTotals64.weightedNumerator_budget

end BilayerDressed.QuarticIntegerActual

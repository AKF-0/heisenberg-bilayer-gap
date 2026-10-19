import Dressed.QuarticIntegerMembership16Accepted
import Dressed.QuarticIntegerEnvelope16
import Dressed.QuarticIntegerCovarianceCache
import Dressed.QuarticIntegerWeightedTotals16

/-! The actual canonical4×4 quartic mean for every real coupling in[0,1/10].
Every signed coefficient, rooted support, covariance weight and integer aggregate
is identified by the preceding concrete kernel certificates. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerActual
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerRows QuarticIntegerMeanEvaluation
open QuarticCanonicalMean

/-- Actual coefficient mean bound, without a finite-table or sampled-coupling premise. -/
theorem mean16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    meanCoefficient (QuarticRowMajor.enumeration 2 2)
      (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g
      (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10))
        (tau 11597344)) ≤ (CubicQuarticSeed.meanBudget16:ℝ) := by
  exact (meanCoefficient_le_integer 2 2 455 kernelData16 raw16 dictionary16 ids16
    cachedKernel16_eq valid16 QuarticIntegerMembership16Accepted.checked
    four_by_four_conditions four_by_four_incidence codes16 count16
    QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
    QuarticIntegerCovarianceData.covarianceDenominator16 upperDenominator16 11597344
    (by decide) QuarticIntegerCovariance.cache16_eq g
    (QuarticIntegerEnvelope.bound16 g hg hmax)).trans
      QuarticIntegerWeightedTotals16.weightedNumerator_budget

end BilayerDressed.QuarticIntegerActual

import Dressed.QuarticRootedRowTable
import Dressed.QuarticIntegerData16
import Dressed.QuarticIntegerData32
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.CubicQuarticMeanBudgets

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotalsBudgets
open QuarticRootedRowTable QuarticIntegerData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem budget16 :
    (QuarticRootedRowTable.area 2 2 : ℝ)/4 *
      ((16795012333348594156552508673820224 : ℝ)/((upperDenominator16:ℝ)*
        (QuarticIntegerCovarianceData.covarianceDenominator16:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget16 : ℝ) := by
  norm_num [QuarticRootedRowTable.area,upperDenominator16,
    QuarticIntegerCovarianceData.covarianceDenominator16,CubicQuarticSeed.meanBudget16,
    ScalarTrial.meanCoefficient16,CubicResidualIntervalBounds.meanBound16,
    CubicSexticPhysicalMeans.coefficient16,ScalarTrial.ell16_6]

theorem budget32 :
    (QuarticRootedRowTable.area 4 2 : ℝ)/4 *
      ((55109942996939944795568447887227624 : ℝ)/((upperDenominator32:ℝ)*
        (QuarticIntegerCovarianceData.covarianceDenominator32:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget32 : ℝ) := by
  norm_num [QuarticRootedRowTable.area,upperDenominator32,
    QuarticIntegerCovarianceData.covarianceDenominator32,CubicQuarticSeed.meanBudget32,
    ScalarTrial.meanCoefficient32,CubicResidualIntervalBounds.meanBound32,
    CubicSexticPhysicalMeans.coefficient32,ScalarTrial.ell32_6]

theorem budget64 :
    (QuarticRootedRowTable.area 4 4 : ℝ)/4 *
      ((113705632345322670095652326654779440 : ℝ)/((upperDenominator64:ℝ)*
        (QuarticIntegerCovarianceData.covarianceDenominator64:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget64 : ℝ) := by
  norm_num [QuarticRootedRowTable.area,upperDenominator64,
    QuarticIntegerCovarianceData.covarianceDenominator64,CubicQuarticSeed.meanBudget64,
    ScalarTrial.meanCoefficient64,CubicResidualIntervalBounds.meanBound64,
    CubicSexticPhysicalMeans.coefficient64,ScalarTrial.ell64_6]

end BilayerDressed.QuarticIntegerWeightedTotalsBudgets

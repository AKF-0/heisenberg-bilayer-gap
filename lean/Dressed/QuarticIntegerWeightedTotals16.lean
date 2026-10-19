import Dressed.QuarticIntegerWeightedTotals16.Block000
import Dressed.QuarticIntegerWeightedTotals16.Block001
import Dressed.QuarticIntegerWeightedTotalsBudgets
import Dressed.QuarticIntegerRows16

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals16
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem aggregate_checked : weightedNumerator 2 2 455 QuarticIntegerData.raw16
    QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16 QuarticIntegerData.ids16 = 16795012333348594156552508673820224 := by
  rw [weightedNumerator_eq_list 2 2 455 QuarticIntegerData.raw16
    QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16 QuarticIntegerData.ids16 QuarticIntegerRows.size16 (by decide +kernel)]
  change weightedList 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
    (rows000 ++ rows001)
    (labels000 ++ labels001) = 16795012333348594156552508673820224
  exact ((checked000.append (c := 16795012333348594156552508673820224) checked001 (by decide +kernel))).total_eq

theorem aggregate_budget :
    (area 2 2 : ℝ)/4 * ((16795012333348594156552508673820224 : ℝ)/((upperDenominator16:ℝ)*
      (QuarticIntegerCovarianceData.covarianceDenominator16:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget16 : ℝ) :=
  QuarticIntegerWeightedTotalsBudgets.budget16

/-- The exact complete weighted numerator fits the remaining quartic budget. -/
theorem weightedNumerator_budget :
    (area 2 2 : ℝ)/4 *
      ((weightedNumerator 2 2 455 QuarticIntegerData.raw16
        QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16 QuarticIntegerData.ids16:ℝ)/
        ((upperDenominator16:ℝ)*(QuarticIntegerCovarianceData.covarianceDenominator16:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget16 : ℝ) := by
  rw [aggregate_checked]
  exact aggregate_budget

end BilayerDressed.QuarticIntegerWeightedTotals16

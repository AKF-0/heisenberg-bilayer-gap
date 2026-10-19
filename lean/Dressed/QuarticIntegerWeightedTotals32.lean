import Dressed.QuarticIntegerWeightedTotals32.Batch000
import Dressed.QuarticIntegerWeightedTotals32.Batch001
import Dressed.QuarticIntegerWeightedTotals32.Batch002
import Dressed.QuarticIntegerWeightedTotalsBudgets
import Dressed.QuarticIntegerComputationalData32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem aggregate_checked : weightedNumerator 4 2 4495 QuarticIntegerComputationalData.raw32
    QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32 QuarticIntegerComputationalData.ids32 = 55109942996939944795568447887227624 := by
  rw [weightedNumerator_eq_list 4 2 4495 QuarticIntegerComputationalData.raw32
    QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32 QuarticIntegerComputationalData.ids32 QuarticIntegerComputationalData.raw32_size QuarticIntegerComputationalData.ids32_size]
  exact (((((checked000.append (c := 28005599825048891977876216033218636) checked001 (by decide +kernel)).append (c := 36304635400860812648741827513254780) (checked002.append (c := 8299035575811920670865611480036144) checked003 (by decide +kernel)) (by decide +kernel)).append (c := 50032799196471896962529548143856692) ((checked004.append (c := 12288261441716407865000901157691322) checked005 (by decide +kernel)).append (c := 13728163795611084313787720630601912) (checked006.append (c := 1439902353894676448786819472910590) (checked007.append (c := 81454465049474941521826558379148) checked008 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 55109942996939944795568447887227624) (((checked009.append (c := 60405429520817988436206513202902) checked010 (by decide +kernel)).append (c := 62249783966877564467086001882016) (checked011.append (c := 1844354446059576030879488679114) checked012 (by decide +kernel)) (by decide +kernel)).append (c := 5077143800468047833038899743370932) ((checked013.append (c := 1727485734321178476866941562136) checked014 (by decide +kernel)).append (c := 5014894016501170268571813741488916) (checked015.append (c := 5013166530766849090094946799926780) (checked016.append (c := 5008431199270476076793604928040370) checked017 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))).total_eq

theorem aggregate_budget :
    (area 4 2 : ℝ)/4 * ((55109942996939944795568447887227624 : ℝ)/((upperDenominator32:ℝ)*
      (QuarticIntegerCovarianceData.covarianceDenominator32:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget32 : ℝ) :=
  QuarticIntegerWeightedTotalsBudgets.budget32

/-- The exact complete weighted numerator fits the remaining quartic budget. -/
theorem weightedNumerator_budget :
    (area 4 2 : ℝ)/4 *
      ((weightedNumerator 4 2 4495 QuarticIntegerComputationalData.raw32
        QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32 QuarticIntegerComputationalData.ids32:ℝ)/
        ((upperDenominator32:ℝ)*(QuarticIntegerCovarianceData.covarianceDenominator32:ℝ)^2)) ≤
      (CubicQuarticSeed.meanBudget32 : ℝ) := by
  rw [aggregate_checked]
  exact aggregate_budget

end BilayerDressed.QuarticIntegerWeightedTotals32

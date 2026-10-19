import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch014
import Dressed.QuarticIntegerComputationalData64.Batch015


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b121_00_rows : List Row := [(row3 25 39 41), (row3 25 39 42), (row3 25 39 43), (row3 25 39 44), (row3 25 39 45), (row3 25 39 46), (row3 25 39 47), (row3 25 39 48), (row3 25 39 49), (row3 25 39 50), (row3 25 39 51), (row3 25 39 52), (row3 25 39 53), (row3 25 39 54), (row3 25 39 55), (row3 25 39 56)]

def b121_00_labels : List Row := [(row3 235 232 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_00_rows b121_00_labels 982901626458814319629500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_00_rows b121_00_labels]
    decide +kernel

def b121_01_rows : List Row := [(row3 25 39 57), (row3 25 39 58), (row3 25 39 59), (row3 25 39 60), (row3 25 39 61), (row3 25 39 62), (row3 25 39 63), (row3 25 40 41), (row3 25 40 42), (row3 25 40 43), (row3 25 40 44), (row3 25 40 45), (row3 25 40 46), (row3 25 40 47), (row3 25 40 48), (row3 25 40 49)]

def b121_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 332 155 93), (row3 265 268 268), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237), (row3 265 266 266), (row3 180 154 154), (row3 371 87 325), (row3 295 297 297)]

theorem b121_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_01_rows b121_01_labels 13646176948401840945193147500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_01_rows b121_01_labels]
    decide +kernel

def b121_02_rows : List Row := [(row3 25 40 50), (row3 25 40 51), (row3 25 40 52), (row3 25 40 53), (row3 25 40 54), (row3 25 40 55), (row3 25 40 56), (row3 25 40 57), (row3 25 40 58), (row3 25 40 59), (row3 25 40 60), (row3 25 40 61), (row3 25 40 62), (row3 25 40 63), (row3 25 41 42), (row3 25 41 43)]

def b121_02_labels : List Row := [(row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 278 280 280), (row3 265 277 277), (row3 229 231 227), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 234 231 231), (row3 193 235 191), (row3 261 462 261)]

theorem b121_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_02_rows b121_02_labels 456909702140084109695626200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_02_rows b121_02_labels]
    decide +kernel

def b121_03_rows : List Row := [(row3 25 41 44), (row3 25 41 45), (row3 25 41 46), (row3 25 41 47), (row3 25 41 48), (row3 25 41 49), (row3 25 41 50), (row3 25 41 51), (row3 25 41 52), (row3 25 41 53), (row3 25 41 54), (row3 25 41 55), (row3 25 41 56), (row3 25 41 57), (row3 25 41 58), (row3 25 41 59)]

def b121_03_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 261 462 261), (row3 288 462 288), (row3 371 87 325), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 235 462 235), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462)]

theorem b121_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_03_rows b121_03_labels 9741681484337746872146176320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_03_rows b121_03_labels]
    decide +kernel

def b121_04_rows : List Row := [(row3 25 41 60), (row3 25 41 61), (row3 25 41 62), (row3 25 41 63), (row3 25 42 43), (row3 25 42 44), (row3 25 42 45), (row3 25 42 46), (row3 25 42 47), (row3 25 42 48), (row3 25 42 49), (row3 25 42 50), (row3 25 42 51), (row3 25 42 52), (row3 25 42 53), (row3 25 42 54)]

def b121_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 278 280 280), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_04_rows b121_04_labels 10882657135952448288024600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_04_rows b121_04_labels]
    decide +kernel

def b121_05_rows : List Row := [(row3 25 42 55), (row3 25 42 56), (row3 25 42 57), (row3 25 42 58), (row3 25 42 59), (row3 25 42 60), (row3 25 42 61), (row3 25 42 62), (row3 25 42 63), (row3 25 43 44), (row3 25 43 45), (row3 25 43 46), (row3 25 43 47), (row3 25 43 48), (row3 25 43 49), (row3 25 43 50)]

def b121_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462)]

theorem b121_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_05_rows b121_05_labels 942802649887182043680000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_05_rows b121_05_labels]
    decide +kernel

def b121_06_rows : List Row := [(row3 25 43 51), (row3 25 43 52), (row3 25 43 53), (row3 25 43 54), (row3 25 43 55), (row3 25 43 56), (row3 25 43 57), (row3 25 43 58), (row3 25 43 59), (row3 25 43 60), (row3 25 43 61), (row3 25 43 62), (row3 25 43 63), (row3 25 44 45), (row3 25 44 46), (row3 25 44 47)]

def b121_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_06_rows b121_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_06_rows b121_06_labels]
    decide +kernel

def b121_07_rows : List Row := [(row3 25 44 48), (row3 25 44 49), (row3 25 44 50), (row3 25 44 51), (row3 25 44 52), (row3 25 44 53), (row3 25 44 54), (row3 25 44 55), (row3 25 44 56), (row3 25 44 57), (row3 25 44 58), (row3 25 44 59), (row3 25 44 60), (row3 25 44 61), (row3 25 44 62), (row3 25 44 63)]

def b121_07_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_07_rows b121_07_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_07_rows b121_07_labels]
    decide +kernel

def b121_08_rows : List Row := [(row3 25 45 46), (row3 25 45 47), (row3 25 45 48), (row3 25 45 49), (row3 25 45 50), (row3 25 45 51), (row3 25 45 52), (row3 25 45 53), (row3 25 45 54), (row3 25 45 55), (row3 25 45 56), (row3 25 45 57), (row3 25 45 58), (row3 25 45 59), (row3 25 45 60), (row3 25 45 61)]

def b121_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_08_rows b121_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_08_rows b121_08_labels]
    decide +kernel

def b121_09_rows : List Row := [(row3 25 45 62), (row3 25 45 63), (row3 25 46 47), (row3 25 46 48), (row3 25 46 49), (row3 25 46 50), (row3 25 46 51), (row3 25 46 52), (row3 25 46 53), (row3 25 46 54), (row3 25 46 55), (row3 25 46 56), (row3 25 46 57), (row3 25 46 58), (row3 25 46 59), (row3 25 46 60)]

def b121_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_09_rows b121_09_labels 269733504168948038841000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_09_rows b121_09_labels]
    decide +kernel

def b121_10_rows : List Row := [(row3 25 46 61), (row3 25 46 62), (row3 25 46 63), (row3 25 47 48), (row3 25 47 49), (row3 25 47 50), (row3 25 47 51), (row3 25 47 52), (row3 25 47 53), (row3 25 47 54), (row3 25 47 55), (row3 25 47 56), (row3 25 47 57), (row3 25 47 58), (row3 25 47 59), (row3 25 47 60)]

def b121_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_10_rows b121_10_labels 6152841992509574565621600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_10_rows b121_10_labels]
    decide +kernel

def b121_11_rows : List Row := [(row3 25 47 61), (row3 25 47 62), (row3 25 47 63), (row3 25 48 49), (row3 25 48 50), (row3 25 48 51), (row3 25 48 52), (row3 25 48 53), (row3 25 48 54), (row3 25 48 55), (row3 25 48 56), (row3 25 48 57), (row3 25 48 58), (row3 25 48 59), (row3 25 48 60), (row3 25 48 61)]

def b121_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 332 155 93), (row3 261 261 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 261 261 462), (row3 193 191 235), (row3 193 163 193), (row3 288 288 288), (row3 235 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_11_rows b121_11_labels 4537026408239577325283252400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_11_rows b121_11_labels]
    decide +kernel

def b121_12_rows : List Row := [(row3 25 48 62), (row3 25 48 63), (row3 25 49 50), (row3 25 49 51), (row3 25 49 52), (row3 25 49 53), (row3 25 49 54), (row3 25 49 55), (row3 25 49 56), (row3 25 49 57), (row3 25 49 58), (row3 25 49 59), (row3 25 49 60), (row3 25 49 61), (row3 25 49 62), (row3 25 49 63)]

def b121_12_labels : List Row := [(row3 235 232 235), (row3 273 288 273), (row3 180 154 154), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237), (row3 265 268 268), (row3 278 301 301), (row3 357 90 187), (row3 278 282 282), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 247 247), (row3 234 226 226)]

theorem b121_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_12_rows b121_12_labels 7542747189060558610741316100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_12_rows b121_12_labels]
    decide +kernel

def b121_13_rows : List Row := [(row3 25 50 51), (row3 25 50 52), (row3 25 50 53), (row3 25 50 54), (row3 25 50 55), (row3 25 50 56), (row3 25 50 57), (row3 25 50 58), (row3 25 50 59), (row3 25 50 60), (row3 25 50 61), (row3 25 50 62), (row3 25 50 63), (row3 25 51 52), (row3 25 51 53), (row3 25 51 54)]

def b121_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_13_rows b121_13_labels 7416915041314867458988800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_13_rows b121_13_labels]
    decide +kernel

def b121_14_rows : List Row := [(row3 25 51 55), (row3 25 51 56), (row3 25 51 57), (row3 25 51 58), (row3 25 51 59), (row3 25 51 60), (row3 25 51 61), (row3 25 51 62), (row3 25 51 63), (row3 25 52 53), (row3 25 52 54), (row3 25 52 55), (row3 25 52 56), (row3 25 52 57), (row3 25 52 58), (row3 25 52 59)]

def b121_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_14_rows b121_14_labels 403899129084828525372000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_14_rows b121_14_labels]
    decide +kernel

def b121_15_rows : List Row := [(row3 25 52 60), (row3 25 52 61), (row3 25 52 62), (row3 25 52 63), (row3 25 53 54), (row3 25 53 55), (row3 25 53 56), (row3 25 53 57), (row3 25 53 58), (row3 25 53 59), (row3 25 53 60), (row3 25 53 61), (row3 25 53 62), (row3 25 53 63), (row3 25 54 55), (row3 25 54 56)]

def b121_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b121_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b121_15_rows b121_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b121_15_rows b121_15_labels]
    decide +kernel

theorem checked121 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_121 QuarticIntegerComputationalData.ids64_121 35951601143359541429537401020 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b121_00_rows ++ b121_01_rows) ++ (b121_02_rows ++ b121_03_rows)) ++ ((b121_04_rows ++ b121_05_rows) ++ (b121_06_rows ++ b121_07_rows))) ++ (((b121_08_rows ++ b121_09_rows) ++ (b121_10_rows ++ b121_11_rows)) ++ ((b121_12_rows ++ b121_13_rows) ++ (b121_14_rows ++ b121_15_rows))))
    ((((b121_00_labels ++ b121_01_labels) ++ (b121_02_labels ++ b121_03_labels)) ++ ((b121_04_labels ++ b121_05_labels) ++ (b121_06_labels ++ b121_07_labels))) ++ (((b121_08_labels ++ b121_09_labels) ++ (b121_10_labels ++ b121_11_labels)) ++ ((b121_12_labels ++ b121_13_labels) ++ (b121_14_labels ++ b121_15_labels)))) 35951601143359541429537401020
  exact ((((b121_00_checked.append (c := 13647159850028299759512777000) b121_01_checked (by decide +kernel)).append (c := 23845751036506130741354579520) (b121_02_checked.append (c := 10198591186477830981841802520) b121_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 23857584156392327274924009120) ((b121_04_checked.append (c := 11825459785839630331704600) b121_05_checked (by decide +kernel)).append (c := 11833119886196533569429600) (b121_06_checked.append (c := 7660100356903237725000) b121_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 35951601143359541429537401020) (((b121_08_checked.append (c := 269733504168948038841000) b121_09_checked (by decide +kernel)).append (c := 4543448983736255847887715000) (b121_10_checked.append (c := 4543179250232086899848874000) b121_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 12094016986967214154613391900) ((b121_12_checked.append (c := 7550164104101873478200304900) b121_13_checked (by decide +kernel)).append (c := 7550568003230958306725676900) (b121_14_checked.append (c := 403899129084828525372000) b121_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b122_00_rows : List Row := [(row3 25 54 57), (row3 25 54 58), (row3 25 54 59), (row3 25 54 60), (row3 25 54 61), (row3 25 54 62), (row3 25 54 63), (row3 25 55 56), (row3 25 55 57), (row3 25 55 58), (row3 25 55 59), (row3 25 55 60), (row3 25 55 61), (row3 25 55 62), (row3 25 55 63), (row3 25 56 57)]

def b122_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 235 232 228), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232), (row3 193 163 139)]

theorem b122_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_00_rows b122_00_labels 1633009952653228142061579000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_00_rows b122_00_labels]
    decide +kernel

def b122_01_rows : List Row := [(row3 25 56 58), (row3 25 56 59), (row3 25 56 60), (row3 25 56 61), (row3 25 56 62), (row3 25 56 63), (row3 25 57 58), (row3 25 57 59), (row3 25 57 60), (row3 25 57 61), (row3 25 57 62), (row3 25 57 63), (row3 25 58 59), (row3 25 58 60), (row3 25 58 61), (row3 25 58 62)]

def b122_01_labels : List Row := [(row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 163 163), (row3 193 189 232), (row3 261 261 462), (row3 238 238 462), (row3 462 462 462), (row3 238 230 232), (row3 261 290 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246)]

theorem b122_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_01_rows b122_01_labels 1556943723630323564023665000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_01_rows b122_01_labels]
    decide +kernel

def b122_02_rows : List Row := [(row3 25 58 63), (row3 25 59 60), (row3 25 59 61), (row3 25 59 62), (row3 25 59 63), (row3 25 60 61), (row3 25 60 62), (row3 25 60 63), (row3 25 61 62), (row3 25 61 63), (row3 25 62 63), (row3 26 27 28), (row3 26 27 29), (row3 26 27 30), (row3 26 27 31), (row3 26 27 32)]

def b122_02_labels : List Row := [(row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_02_rows b122_02_labels 4468995036708415220448000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_02_rows b122_02_labels]
    decide +kernel

def b122_03_rows : List Row := [(row3 26 27 33), (row3 26 27 34), (row3 26 27 35), (row3 26 27 36), (row3 26 27 37), (row3 26 27 38), (row3 26 27 39), (row3 26 27 40), (row3 26 27 41), (row3 26 27 42), (row3 26 27 43), (row3 26 27 44), (row3 26 27 45), (row3 26 27 46), (row3 26 27 47), (row3 26 27 48)]

def b122_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_03_rows b122_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_03_rows b122_03_labels]
    decide +kernel

def b122_04_rows : List Row := [(row3 26 27 49), (row3 26 27 50), (row3 26 27 51), (row3 26 27 52), (row3 26 27 53), (row3 26 27 54), (row3 26 27 55), (row3 26 27 56), (row3 26 27 57), (row3 26 27 58), (row3 26 27 59), (row3 26 27 60), (row3 26 27 61), (row3 26 27 62), (row3 26 27 63), (row3 26 28 29)]

def b122_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_04_rows b122_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_04_rows b122_04_labels]
    decide +kernel

def b122_05_rows : List Row := [(row3 26 28 30), (row3 26 28 31), (row3 26 28 32), (row3 26 28 33), (row3 26 28 34), (row3 26 28 35), (row3 26 28 36), (row3 26 28 37), (row3 26 28 38), (row3 26 28 39), (row3 26 28 40), (row3 26 28 41), (row3 26 28 42), (row3 26 28 43), (row3 26 28 44), (row3 26 28 45)]

def b122_05_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_05_rows b122_05_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_05_rows b122_05_labels]
    decide +kernel

def b122_06_rows : List Row := [(row3 26 28 46), (row3 26 28 47), (row3 26 28 48), (row3 26 28 49), (row3 26 28 50), (row3 26 28 51), (row3 26 28 52), (row3 26 28 53), (row3 26 28 54), (row3 26 28 55), (row3 26 28 56), (row3 26 28 57), (row3 26 28 58), (row3 26 28 59), (row3 26 28 60), (row3 26 28 61)]

def b122_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_06_rows b122_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_06_rows b122_06_labels]
    decide +kernel

def b122_07_rows : List Row := [(row3 26 28 62), (row3 26 28 63), (row3 26 29 30), (row3 26 29 31), (row3 26 29 32), (row3 26 29 33), (row3 26 29 34), (row3 26 29 35), (row3 26 29 36), (row3 26 29 37), (row3 26 29 38), (row3 26 29 39), (row3 26 29 40), (row3 26 29 41), (row3 26 29 42), (row3 26 29 43)]

def b122_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_07_rows b122_07_labels 83136797542324941912000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_07_rows b122_07_labels]
    decide +kernel

def b122_08_rows : List Row := [(row3 26 29 44), (row3 26 29 45), (row3 26 29 46), (row3 26 29 47), (row3 26 29 48), (row3 26 29 49), (row3 26 29 50), (row3 26 29 51), (row3 26 29 52), (row3 26 29 53), (row3 26 29 54), (row3 26 29 55), (row3 26 29 56), (row3 26 29 57), (row3 26 29 58), (row3 26 29 59)]

def b122_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_08_rows b122_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_08_rows b122_08_labels]
    decide +kernel

def b122_09_rows : List Row := [(row3 26 29 60), (row3 26 29 61), (row3 26 29 62), (row3 26 29 63), (row3 26 30 31), (row3 26 30 32), (row3 26 30 33), (row3 26 30 34), (row3 26 30 35), (row3 26 30 36), (row3 26 30 37), (row3 26 30 38), (row3 26 30 39), (row3 26 30 40), (row3 26 30 41), (row3 26 30 42)]

def b122_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_09_rows b122_09_labels 19726963911656214309712500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_09_rows b122_09_labels]
    decide +kernel

def b122_10_rows : List Row := [(row3 26 30 43), (row3 26 30 44), (row3 26 30 45), (row3 26 30 46), (row3 26 30 47), (row3 26 30 48), (row3 26 30 49), (row3 26 30 50), (row3 26 30 51), (row3 26 30 52), (row3 26 30 53), (row3 26 30 54), (row3 26 30 55), (row3 26 30 56), (row3 26 30 57), (row3 26 30 58)]

def b122_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_10_rows b122_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_10_rows b122_10_labels]
    decide +kernel

def b122_11_rows : List Row := [(row3 26 30 59), (row3 26 30 60), (row3 26 30 61), (row3 26 30 62), (row3 26 30 63), (row3 26 31 32), (row3 26 31 33), (row3 26 31 34), (row3 26 31 35), (row3 26 31 36), (row3 26 31 37), (row3 26 31 38), (row3 26 31 39), (row3 26 31 40), (row3 26 31 41), (row3 26 31 42)]

def b122_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 233 235 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 263 462 263), (row3 245 462 245), (row3 462 462 462), (row3 462 462 462)]

theorem b122_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_11_rows b122_11_labels 20690996579153064155485500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_11_rows b122_11_labels]
    decide +kernel

def b122_12_rows : List Row := [(row3 26 31 43), (row3 26 31 44), (row3 26 31 45), (row3 26 31 46), (row3 26 31 47), (row3 26 31 48), (row3 26 31 49), (row3 26 31 50), (row3 26 31 51), (row3 26 31 52), (row3 26 31 53), (row3 26 31 54), (row3 26 31 55), (row3 26 31 56), (row3 26 31 57), (row3 26 31 58)]

def b122_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_12_rows b122_12_labels 92222490267195080892000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_12_rows b122_12_labels]
    decide +kernel

def b122_13_rows : List Row := [(row3 26 31 59), (row3 26 31 60), (row3 26 31 61), (row3 26 31 62), (row3 26 31 63), (row3 26 32 33), (row3 26 32 34), (row3 26 32 35), (row3 26 32 36), (row3 26 32 37), (row3 26 32 38), (row3 26 32 39), (row3 26 32 40), (row3 26 32 41), (row3 26 32 42), (row3 26 32 43)]

def b122_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 237 462 237), (row3 242 462 242), (row3 462 462 462), (row3 242 462 242), (row3 237 462 237), (row3 269 462 269), (row3 170 10 218), (row3 228 232 235), (row3 244 462 244), (row3 462 462 462)]

theorem b122_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_13_rows b122_13_labels 597876099291790691040983250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_13_rows b122_13_labels]
    decide +kernel

def b122_14_rows : List Row := [(row3 26 32 44), (row3 26 32 45), (row3 26 32 46), (row3 26 32 47), (row3 26 32 48), (row3 26 32 49), (row3 26 32 50), (row3 26 32 51), (row3 26 32 52), (row3 26 32 53), (row3 26 32 54), (row3 26 32 55), (row3 26 32 56), (row3 26 32 57), (row3 26 32 58), (row3 26 32 59)]

def b122_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 237 462 237), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_14_rows b122_14_labels 878195017839374843670000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_14_rows b122_14_labels]
    decide +kernel

def b122_15_rows : List Row := [(row3 26 32 60), (row3 26 32 61), (row3 26 32 62), (row3 26 32 63), (row3 26 33 34), (row3 26 33 35), (row3 26 33 36), (row3 26 33 37), (row3 26 33 38), (row3 26 33 39), (row3 26 33 40), (row3 26 33 41), (row3 26 33 42), (row3 26 33 43), (row3 26 33 44), (row3 26 33 45)]

def b122_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b122_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b122_15_rows b122_15_labels 63059274630880947212625000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b122_15_rows b122_15_labels]
    decide +kernel

theorem checked122 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_122 QuarticIntegerComputationalData.ids64_122 3896833185407122451534267250 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b122_00_rows ++ b122_01_rows) ++ (b122_02_rows ++ b122_03_rows)) ++ ((b122_04_rows ++ b122_05_rows) ++ (b122_06_rows ++ b122_07_rows))) ++ (((b122_08_rows ++ b122_09_rows) ++ (b122_10_rows ++ b122_11_rows)) ++ ((b122_12_rows ++ b122_13_rows) ++ (b122_14_rows ++ b122_15_rows))))
    ((((b122_00_labels ++ b122_01_labels) ++ (b122_02_labels ++ b122_03_labels)) ++ ((b122_04_labels ++ b122_05_labels) ++ (b122_06_labels ++ b122_07_labels))) ++ (((b122_08_labels ++ b122_09_labels) ++ (b122_10_labels ++ b122_11_labels)) ++ ((b122_12_labels ++ b122_13_labels) ++ (b122_14_labels ++ b122_15_labels)))) 3896833185407122451534267250
  exact ((((b122_00_checked.append (c := 3189953676283551706085244000) b122_01_checked (by decide +kernel)).append (c := 3194422671320260121305692000) (b122_02_checked.append (c := 4468995036708415220448000) b122_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3194509433485534964890899000) ((b122_04_checked.append (c := 3625367732518643295000) b122_05_checked (by decide +kernel)).append (c := 86762165274843585207000) (b122_06_checked.append (c := 83136797542324941912000) b122_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 3896833185407122451534267250) (((b122_08_checked.append (c := 19726963911656214309712500) b122_09_checked (by decide +kernel)).append (c := 40417960490809278465198000) (b122_10_checked.append (c := 20690996579153064155485500) b122_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 702323751921587486643368250) ((b122_12_checked.append (c := 597968321782057886121875250) b122_13_checked (by decide +kernel)).append (c := 661905791430778208178170250) (b122_14_checked.append (c := 63937469648720322056295000) b122_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b123_00_rows : List Row := [(row3 26 33 46), (row3 26 33 47), (row3 26 33 48), (row3 26 33 49), (row3 26 33 50), (row3 26 33 51), (row3 26 33 52), (row3 26 33 53), (row3 26 33 54), (row3 26 33 55), (row3 26 33 56), (row3 26 33 57), (row3 26 33 58), (row3 26 33 59), (row3 26 33 60), (row3 26 33 61)]

def b123_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_00_rows b123_00_labels 759080440260365830843500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_00_rows b123_00_labels]
    decide +kernel

def b123_01_rows : List Row := [(row3 26 33 62), (row3 26 33 63), (row3 26 34 35), (row3 26 34 36), (row3 26 34 37), (row3 26 34 38), (row3 26 34 39), (row3 26 34 40), (row3 26 34 41), (row3 26 34 42), (row3 26 34 43), (row3 26 34 44), (row3 26 34 45), (row3 26 34 46), (row3 26 34 47), (row3 26 34 48)]

def b123_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_01_rows b123_01_labels 3974736731292688009171500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_01_rows b123_01_labels]
    decide +kernel

def b123_02_rows : List Row := [(row3 26 34 49), (row3 26 34 50), (row3 26 34 51), (row3 26 34 52), (row3 26 34 53), (row3 26 34 54), (row3 26 34 55), (row3 26 34 56), (row3 26 34 57), (row3 26 34 58), (row3 26 34 59), (row3 26 34 60), (row3 26 34 61), (row3 26 34 62), (row3 26 34 63), (row3 26 35 36)]

def b123_02_labels : List Row := [(row3 246 462 246), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_02_rows b123_02_labels 1851703297269869112835500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_02_rows b123_02_labels]
    decide +kernel

def b123_03_rows : List Row := [(row3 26 35 37), (row3 26 35 38), (row3 26 35 39), (row3 26 35 40), (row3 26 35 41), (row3 26 35 42), (row3 26 35 43), (row3 26 35 44), (row3 26 35 45), (row3 26 35 46), (row3 26 35 47), (row3 26 35 48), (row3 26 35 49), (row3 26 35 50), (row3 26 35 51), (row3 26 35 52)]

def b123_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_03_rows b123_03_labels 75474487824386394802500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_03_rows b123_03_labels]
    decide +kernel

def b123_04_rows : List Row := [(row3 26 35 53), (row3 26 35 54), (row3 26 35 55), (row3 26 35 56), (row3 26 35 57), (row3 26 35 58), (row3 26 35 59), (row3 26 35 60), (row3 26 35 61), (row3 26 35 62), (row3 26 35 63), (row3 26 36 37), (row3 26 36 38), (row3 26 36 39), (row3 26 36 40), (row3 26 36 41)]

def b123_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_04_rows b123_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_04_rows b123_04_labels]
    decide +kernel

def b123_05_rows : List Row := [(row3 26 36 42), (row3 26 36 43), (row3 26 36 44), (row3 26 36 45), (row3 26 36 46), (row3 26 36 47), (row3 26 36 48), (row3 26 36 49), (row3 26 36 50), (row3 26 36 51), (row3 26 36 52), (row3 26 36 53), (row3 26 36 54), (row3 26 36 55), (row3 26 36 56), (row3 26 36 57)]

def b123_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_05_rows b123_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_05_rows b123_05_labels]
    decide +kernel

def b123_06_rows : List Row := [(row3 26 36 58), (row3 26 36 59), (row3 26 36 60), (row3 26 36 61), (row3 26 36 62), (row3 26 36 63), (row3 26 37 38), (row3 26 37 39), (row3 26 37 40), (row3 26 37 41), (row3 26 37 42), (row3 26 37 43), (row3 26 37 44), (row3 26 37 45), (row3 26 37 46), (row3 26 37 47)]

def b123_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_06_rows b123_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_06_rows b123_06_labels]
    decide +kernel

def b123_07_rows : List Row := [(row3 26 37 48), (row3 26 37 49), (row3 26 37 50), (row3 26 37 51), (row3 26 37 52), (row3 26 37 53), (row3 26 37 54), (row3 26 37 55), (row3 26 37 56), (row3 26 37 57), (row3 26 37 58), (row3 26 37 59), (row3 26 37 60), (row3 26 37 61), (row3 26 37 62), (row3 26 37 63)]

def b123_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_07_rows b123_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_07_rows b123_07_labels]
    decide +kernel

def b123_08_rows : List Row := [(row3 26 38 39), (row3 26 38 40), (row3 26 38 41), (row3 26 38 42), (row3 26 38 43), (row3 26 38 44), (row3 26 38 45), (row3 26 38 46), (row3 26 38 47), (row3 26 38 48), (row3 26 38 49), (row3 26 38 50), (row3 26 38 51), (row3 26 38 52), (row3 26 38 53), (row3 26 38 54)]

def b123_08_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_08_rows b123_08_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_08_rows b123_08_labels]
    decide +kernel

def b123_09_rows : List Row := [(row3 26 38 55), (row3 26 38 56), (row3 26 38 57), (row3 26 38 58), (row3 26 38 59), (row3 26 38 60), (row3 26 38 61), (row3 26 38 62), (row3 26 38 63), (row3 26 39 40), (row3 26 39 41), (row3 26 39 42), (row3 26 39 43), (row3 26 39 44), (row3 26 39 45), (row3 26 39 46)]

def b123_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_09_rows b123_09_labels 413010417905223503607000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_09_rows b123_09_labels]
    decide +kernel

def b123_10_rows : List Row := [(row3 26 39 47), (row3 26 39 48), (row3 26 39 49), (row3 26 39 50), (row3 26 39 51), (row3 26 39 52), (row3 26 39 53), (row3 26 39 54), (row3 26 39 55), (row3 26 39 56), (row3 26 39 57), (row3 26 39 58), (row3 26 39 59), (row3 26 39 60), (row3 26 39 61), (row3 26 39 62)]

def b123_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_10_rows b123_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_10_rows b123_10_labels]
    decide +kernel

def b123_11_rows : List Row := [(row3 26 39 63), (row3 26 40 41), (row3 26 40 42), (row3 26 40 43), (row3 26 40 44), (row3 26 40 45), (row3 26 40 46), (row3 26 40 47), (row3 26 40 48), (row3 26 40 49), (row3 26 40 50), (row3 26 40 51), (row3 26 40 52), (row3 26 40 53), (row3 26 40 54), (row3 26 40 55)]

def b123_11_labels : List Row := [(row3 462 462 462), (row3 172 258 10), (row3 237 237 462), (row3 242 242 462), (row3 462 462 462), (row3 242 242 462), (row3 237 237 462), (row3 269 269 462), (row3 269 269 462), (row3 228 235 232), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 235 235 462)]

theorem b123_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_11_rows b123_11_labels 574587831930146081133156000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_11_rows b123_11_labels]
    decide +kernel

def b123_12_rows : List Row := [(row3 26 40 56), (row3 26 40 57), (row3 26 40 58), (row3 26 40 59), (row3 26 40 60), (row3 26 40 61), (row3 26 40 62), (row3 26 40 63), (row3 26 41 42), (row3 26 41 43), (row3 26 41 44), (row3 26 41 45), (row3 26 41 46), (row3 26 41 47), (row3 26 41 48), (row3 26 41 49)]

def b123_12_labels : List Row := [(row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 284 462 284), (row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 235 462 235), (row3 232 462 232), (row3 115 11 212)]

theorem b123_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_12_rows b123_12_labels 1736143679463273299404550250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_12_rows b123_12_labels]
    decide +kernel

def b123_13_rows : List Row := [(row3 26 41 50), (row3 26 41 51), (row3 26 41 52), (row3 26 41 53), (row3 26 41 54), (row3 26 41 55), (row3 26 41 56), (row3 26 41 57), (row3 26 41 58), (row3 26 41 59), (row3 26 41 60), (row3 26 41 61), (row3 26 41 62), (row3 26 41 63), (row3 26 42 43), (row3 26 42 44)]

def b123_13_labels : List Row := [(row3 228 235 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 246 462 246), (row3 235 462 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_13_rows b123_13_labels 2933567307603468158539500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_13_rows b123_13_labels]
    decide +kernel

def b123_14_rows : List Row := [(row3 26 42 45), (row3 26 42 46), (row3 26 42 47), (row3 26 42 48), (row3 26 42 49), (row3 26 42 50), (row3 26 42 51), (row3 26 42 52), (row3 26 42 53), (row3 26 42 54), (row3 26 42 55), (row3 26 42 56), (row3 26 42 57), (row3 26 42 58), (row3 26 42 59), (row3 26 42 60)]

def b123_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b123_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_14_rows b123_14_labels 31812090821397601904524500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_14_rows b123_14_labels]
    decide +kernel

def b123_15_rows : List Row := [(row3 26 42 61), (row3 26 42 62), (row3 26 42 63), (row3 26 43 44), (row3 26 43 45), (row3 26 43 46), (row3 26 43 47), (row3 26 43 48), (row3 26 43 49), (row3 26 43 50), (row3 26 43 51), (row3 26 43 52), (row3 26 43 53), (row3 26 43 54), (row3 26 43 55), (row3 26 43 56)]

def b123_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b123_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b123_15_rows b123_15_labels 433212553368480599487000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b123_15_rows b123_15_labels]
    decide +kernel

theorem checked123 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_123 QuarticIntegerComputationalData.ids64_123 2352995877600876818908104750 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b123_00_rows ++ b123_01_rows) ++ (b123_02_rows ++ b123_03_rows)) ++ ((b123_04_rows ++ b123_05_rows) ++ (b123_06_rows ++ b123_07_rows))) ++ (((b123_08_rows ++ b123_09_rows) ++ (b123_10_rows ++ b123_11_rows)) ++ ((b123_12_rows ++ b123_13_rows) ++ (b123_14_rows ++ b123_15_rows))))
    ((((b123_00_labels ++ b123_01_labels) ++ (b123_02_labels ++ b123_03_labels)) ++ ((b123_04_labels ++ b123_05_labels) ++ (b123_06_labels ++ b123_07_labels))) ++ (((b123_08_labels ++ b123_09_labels) ++ (b123_10_labels ++ b123_11_labels)) ++ ((b123_12_labels ++ b123_13_labels) ++ (b123_14_labels ++ b123_15_labels)))) 2352995877600876818908104750
  exact ((((b123_00_checked.append (c := 4733817171553053840015000) b123_01_checked (by decide +kernel)).append (c := 6660994956647309347653000) (b123_02_checked.append (c := 1927177785094255507638000) b123_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6660994956647309347653000) ((b123_04_checked.append (c := 0) b123_05_checked (by decide +kernel)).append (c := 0) (b123_06_checked.append (c := 0) b123_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2352995877600876818908104750) (((b123_08_checked.append (c := 424500568440578360194500) b123_09_checked (by decide +kernel)).append (c := 575012332498586659493350500) (b123_10_checked.append (c := 574587831930146081133156000) b123_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2346334882644229509560451750) ((b123_12_checked.append (c := 1739077246770876767563089750) b123_13_checked (by decide +kernel)).append (c := 1771322550145642850067101250) (b123_14_checked.append (c := 32245303374766082504011500) b123_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b124_00_rows : List Row := [(row3 26 43 57), (row3 26 43 58), (row3 26 43 59), (row3 26 43 60), (row3 26 43 61), (row3 26 43 62), (row3 26 43 63), (row3 26 44 45), (row3 26 44 46), (row3 26 44 47), (row3 26 44 48), (row3 26 44 49), (row3 26 44 50), (row3 26 44 51), (row3 26 44 52), (row3 26 44 53)]

def b124_00_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_00_rows b124_00_labels 28257364541359222875000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_00_rows b124_00_labels]
    decide +kernel

def b124_01_rows : List Row := [(row3 26 44 54), (row3 26 44 55), (row3 26 44 56), (row3 26 44 57), (row3 26 44 58), (row3 26 44 59), (row3 26 44 60), (row3 26 44 61), (row3 26 44 62), (row3 26 44 63), (row3 26 45 46), (row3 26 45 47), (row3 26 45 48), (row3 26 45 49), (row3 26 45 50), (row3 26 45 51)]

def b124_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_01_rows b124_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_01_rows b124_01_labels]
    decide +kernel

def b124_02_rows : List Row := [(row3 26 45 52), (row3 26 45 53), (row3 26 45 54), (row3 26 45 55), (row3 26 45 56), (row3 26 45 57), (row3 26 45 58), (row3 26 45 59), (row3 26 45 60), (row3 26 45 61), (row3 26 45 62), (row3 26 45 63), (row3 26 46 47), (row3 26 46 48), (row3 26 46 49), (row3 26 46 50)]

def b124_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_02_rows b124_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_02_rows b124_02_labels]
    decide +kernel

def b124_03_rows : List Row := [(row3 26 46 51), (row3 26 46 52), (row3 26 46 53), (row3 26 46 54), (row3 26 46 55), (row3 26 46 56), (row3 26 46 57), (row3 26 46 58), (row3 26 46 59), (row3 26 46 60), (row3 26 46 61), (row3 26 46 62), (row3 26 46 63), (row3 26 47 48), (row3 26 47 49), (row3 26 47 50)]

def b124_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462)]

theorem b124_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_03_rows b124_03_labels 25995303733821612075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_03_rows b124_03_labels]
    decide +kernel

def b124_04_rows : List Row := [(row3 26 47 51), (row3 26 47 52), (row3 26 47 53), (row3 26 47 54), (row3 26 47 55), (row3 26 47 56), (row3 26 47 57), (row3 26 47 58), (row3 26 47 59), (row3 26 47 60), (row3 26 47 61), (row3 26 47 62), (row3 26 47 63), (row3 26 48 49), (row3 26 48 50), (row3 26 48 51)]

def b124_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 237 237 462), (row3 462 462 462)]

theorem b124_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_04_rows b124_04_labels 61112336760747902730015000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_04_rows b124_04_labels]
    decide +kernel

def b124_05_rows : List Row := [(row3 26 48 52), (row3 26 48 53), (row3 26 48 54), (row3 26 48 55), (row3 26 48 56), (row3 26 48 57), (row3 26 48 58), (row3 26 48 59), (row3 26 48 60), (row3 26 48 61), (row3 26 48 62), (row3 26 48 63), (row3 26 49 50), (row3 26 49 51), (row3 26 49 52), (row3 26 49 53)]

def b124_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 172 258 10), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462)]

theorem b124_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_05_rows b124_05_labels 513032401474502431666806000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_05_rows b124_05_labels]
    decide +kernel

def b124_06_rows : List Row := [(row3 26 49 54), (row3 26 49 55), (row3 26 49 56), (row3 26 49 57), (row3 26 49 58), (row3 26 49 59), (row3 26 49 60), (row3 26 49 61), (row3 26 49 62), (row3 26 49 63), (row3 26 50 51), (row3 26 50 52), (row3 26 50 53), (row3 26 50 54), (row3 26 50 55), (row3 26 50 56)]

def b124_06_labels : List Row := [(row3 243 243 462), (row3 235 235 462), (row3 232 232 462), (row3 284 284 462), (row3 228 232 235), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 269 462 269), (row3 237 462 237), (row3 242 462 242), (row3 462 462 462), (row3 242 462 242), (row3 244 462 244)]

theorem b124_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_06_rows b124_06_labels 97610797413014712312699000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_06_rows b124_06_labels]
    decide +kernel

def b124_07_rows : List Row := [(row3 26 50 57), (row3 26 50 58), (row3 26 50 59), (row3 26 50 60), (row3 26 50 61), (row3 26 50 62), (row3 26 50 63), (row3 26 51 52), (row3 26 51 53), (row3 26 51 54), (row3 26 51 55), (row3 26 51 56), (row3 26 51 57), (row3 26 51 58), (row3 26 51 59), (row3 26 51 60)]

def b124_07_labels : List Row := [(row3 235 462 235), (row3 170 10 218), (row3 235 462 235), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b124_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_07_rows b124_07_labels 536254966175651804571995250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_07_rows b124_07_labels]
    decide +kernel

def b124_08_rows : List Row := [(row3 26 51 61), (row3 26 51 62), (row3 26 51 63), (row3 26 52 53), (row3 26 52 54), (row3 26 52 55), (row3 26 52 56), (row3 26 52 57), (row3 26 52 58), (row3 26 52 59), (row3 26 52 60), (row3 26 52 61), (row3 26 52 62), (row3 26 52 63), (row3 26 53 54), (row3 26 53 55)]

def b124_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_08_rows b124_08_labels 12997651866910806037500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_08_rows b124_08_labels]
    decide +kernel

def b124_09_rows : List Row := [(row3 26 53 56), (row3 26 53 57), (row3 26 53 58), (row3 26 53 59), (row3 26 53 60), (row3 26 53 61), (row3 26 53 62), (row3 26 53 63), (row3 26 54 55), (row3 26 54 56), (row3 26 54 57), (row3 26 54 58), (row3 26 54 59), (row3 26 54 60), (row3 26 54 61), (row3 26 54 62)]

def b124_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_09_rows b124_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_09_rows b124_09_labels]
    decide +kernel

def b124_10_rows : List Row := [(row3 26 54 63), (row3 26 55 56), (row3 26 55 57), (row3 26 55 58), (row3 26 55 59), (row3 26 55 60), (row3 26 55 61), (row3 26 55 62), (row3 26 55 63), (row3 26 56 57), (row3 26 56 58), (row3 26 56 59), (row3 26 56 60), (row3 26 56 61), (row3 26 56 62), (row3 26 56 63)]

def b124_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_10_rows b124_10_labels 842275830134119351068000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_10_rows b124_10_labels]
    decide +kernel

def b124_11_rows : List Row := [(row3 26 57 58), (row3 26 57 59), (row3 26 57 60), (row3 26 57 61), (row3 26 57 62), (row3 26 57 63), (row3 26 58 59), (row3 26 58 60), (row3 26 58 61), (row3 26 58 62), (row3 26 58 63), (row3 26 59 60), (row3 26 59 61), (row3 26 59 62), (row3 26 59 63), (row3 26 60 61)]

def b124_11_labels : List Row := [(row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 237 237 462), (row3 242 242 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_11_rows b124_11_labels 61045980140971623351888000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_11_rows b124_11_labels]
    decide +kernel

def b124_12_rows : List Row := [(row3 26 60 62), (row3 26 60 63), (row3 26 61 62), (row3 26 61 63), (row3 26 62 63), (row3 27 28 29), (row3 27 28 30), (row3 27 28 31), (row3 27 28 32), (row3 27 28 33), (row3 27 28 34), (row3 27 28 35), (row3 27 28 36), (row3 27 28 37), (row3 27 28 38), (row3 27 28 39)]

def b124_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_12_rows b124_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_12_rows b124_12_labels]
    decide +kernel

def b124_13_rows : List Row := [(row3 27 28 40), (row3 27 28 41), (row3 27 28 42), (row3 27 28 43), (row3 27 28 44), (row3 27 28 45), (row3 27 28 46), (row3 27 28 47), (row3 27 28 48), (row3 27 28 49), (row3 27 28 50), (row3 27 28 51), (row3 27 28 52), (row3 27 28 53), (row3 27 28 54), (row3 27 28 55)]

def b124_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_13_rows b124_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_13_rows b124_13_labels]
    decide +kernel

def b124_14_rows : List Row := [(row3 27 28 56), (row3 27 28 57), (row3 27 28 58), (row3 27 28 59), (row3 27 28 60), (row3 27 28 61), (row3 27 28 62), (row3 27 28 63), (row3 27 29 30), (row3 27 29 31), (row3 27 29 32), (row3 27 29 33), (row3 27 29 34), (row3 27 29 35), (row3 27 29 36), (row3 27 29 37)]

def b124_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_14_rows b124_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_14_rows b124_14_labels]
    decide +kernel

def b124_15_rows : List Row := [(row3 27 29 38), (row3 27 29 39), (row3 27 29 40), (row3 27 29 41), (row3 27 29 42), (row3 27 29 43), (row3 27 29 44), (row3 27 29 45), (row3 27 29 46), (row3 27 29 47), (row3 27 29 48), (row3 27 29 49), (row3 27 29 50), (row3 27 29 51), (row3 27 29 52), (row3 27 29 53)]

def b124_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b124_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b124_15_rows b124_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b124_15_rows b124_15_labels]
    decide +kernel

theorem checked124 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_124 QuarticIntegerComputationalData.ids64_124 1269966008115164685625458750 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b124_00_rows ++ b124_01_rows) ++ (b124_02_rows ++ b124_03_rows)) ++ ((b124_04_rows ++ b124_05_rows) ++ (b124_06_rows ++ b124_07_rows))) ++ (((b124_08_rows ++ b124_09_rows) ++ (b124_10_rows ++ b124_11_rows)) ++ ((b124_12_rows ++ b124_13_rows) ++ (b124_14_rows ++ b124_15_rows))))
    ((((b124_00_labels ++ b124_01_labels) ++ (b124_02_labels ++ b124_03_labels)) ++ ((b124_04_labels ++ b124_05_labels) ++ (b124_06_labels ++ b124_07_labels))) ++ (((b124_08_labels ++ b124_09_labels) ++ (b124_10_labels ++ b124_11_labels)) ++ ((b124_12_labels ++ b124_13_labels) ++ (b124_14_labels ++ b124_15_labels)))) 1269966008115164685625458750
  exact ((((b124_00_checked.append (c := 28257364541359222875000) b124_01_checked (by decide +kernel)).append (c := 54252668275180834950000) (b124_02_checked.append (c := 25995303733821612075000) b124_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1208064754492192032116465250) ((b124_04_checked.append (c := 574144738235250334396821000) b124_05_checked (by decide +kernel)).append (c := 1208010501823916851281515250) (b124_06_checked.append (c := 633865763588666516884694250) b124_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1269966008115164685625458750) (((b124_08_checked.append (c := 12997651866910806037500) b124_09_checked (by decide +kernel)).append (c := 61901253622972653508993500) (b124_10_checked.append (c := 61888255971105742702956000) b124_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 61901253622972653508993500) ((b124_12_checked.append (c := 0) b124_13_checked (by decide +kernel)).append (c := 0) (b124_14_checked.append (c := 0) b124_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b125_00_rows : List Row := [(row3 27 29 54), (row3 27 29 55), (row3 27 29 56), (row3 27 29 57), (row3 27 29 58), (row3 27 29 59), (row3 27 29 60), (row3 27 29 61), (row3 27 29 62), (row3 27 29 63), (row3 27 30 31), (row3 27 30 32), (row3 27 30 33), (row3 27 30 34), (row3 27 30 35), (row3 27 30 36)]

def b125_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_00_rows b125_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_00_rows b125_00_labels]
    decide +kernel

def b125_01_rows : List Row := [(row3 27 30 37), (row3 27 30 38), (row3 27 30 39), (row3 27 30 40), (row3 27 30 41), (row3 27 30 42), (row3 27 30 43), (row3 27 30 44), (row3 27 30 45), (row3 27 30 46), (row3 27 30 47), (row3 27 30 48), (row3 27 30 49), (row3 27 30 50), (row3 27 30 51), (row3 27 30 52)]

def b125_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_01_rows b125_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_01_rows b125_01_labels]
    decide +kernel

def b125_02_rows : List Row := [(row3 27 30 53), (row3 27 30 54), (row3 27 30 55), (row3 27 30 56), (row3 27 30 57), (row3 27 30 58), (row3 27 30 59), (row3 27 30 60), (row3 27 30 61), (row3 27 30 62), (row3 27 30 63), (row3 27 31 32), (row3 27 31 33), (row3 27 31 34), (row3 27 31 35), (row3 27 31 36)]

def b125_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_02_rows b125_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_02_rows b125_02_labels]
    decide +kernel

def b125_03_rows : List Row := [(row3 27 31 37), (row3 27 31 38), (row3 27 31 39), (row3 27 31 40), (row3 27 31 41), (row3 27 31 42), (row3 27 31 43), (row3 27 31 44), (row3 27 31 45), (row3 27 31 46), (row3 27 31 47), (row3 27 31 48), (row3 27 31 49), (row3 27 31 50), (row3 27 31 51), (row3 27 31 52)]

def b125_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_03_rows b125_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_03_rows b125_03_labels]
    decide +kernel

def b125_04_rows : List Row := [(row3 27 31 53), (row3 27 31 54), (row3 27 31 55), (row3 27 31 56), (row3 27 31 57), (row3 27 31 58), (row3 27 31 59), (row3 27 31 60), (row3 27 31 61), (row3 27 31 62), (row3 27 31 63), (row3 27 32 33), (row3 27 32 34), (row3 27 32 35), (row3 27 32 36), (row3 27 32 37)]

def b125_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_04_rows b125_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_04_rows b125_04_labels]
    decide +kernel

def b125_05_rows : List Row := [(row3 27 32 38), (row3 27 32 39), (row3 27 32 40), (row3 27 32 41), (row3 27 32 42), (row3 27 32 43), (row3 27 32 44), (row3 27 32 45), (row3 27 32 46), (row3 27 32 47), (row3 27 32 48), (row3 27 32 49), (row3 27 32 50), (row3 27 32 51), (row3 27 32 52), (row3 27 32 53)]

def b125_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_05_rows b125_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_05_rows b125_05_labels]
    decide +kernel

def b125_06_rows : List Row := [(row3 27 32 54), (row3 27 32 55), (row3 27 32 56), (row3 27 32 57), (row3 27 32 58), (row3 27 32 59), (row3 27 32 60), (row3 27 32 61), (row3 27 32 62), (row3 27 32 63), (row3 27 33 34), (row3 27 33 35), (row3 27 33 36), (row3 27 33 37), (row3 27 33 38), (row3 27 33 39)]

def b125_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_06_rows b125_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_06_rows b125_06_labels]
    decide +kernel

def b125_07_rows : List Row := [(row3 27 33 40), (row3 27 33 41), (row3 27 33 42), (row3 27 33 43), (row3 27 33 44), (row3 27 33 45), (row3 27 33 46), (row3 27 33 47), (row3 27 33 48), (row3 27 33 49), (row3 27 33 50), (row3 27 33 51), (row3 27 33 52), (row3 27 33 53), (row3 27 33 54), (row3 27 33 55)]

def b125_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_07_rows b125_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_07_rows b125_07_labels]
    decide +kernel

def b125_08_rows : List Row := [(row3 27 33 56), (row3 27 33 57), (row3 27 33 58), (row3 27 33 59), (row3 27 33 60), (row3 27 33 61), (row3 27 33 62), (row3 27 33 63), (row3 27 34 35), (row3 27 34 36), (row3 27 34 37), (row3 27 34 38), (row3 27 34 39), (row3 27 34 40), (row3 27 34 41), (row3 27 34 42)]

def b125_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_08_rows b125_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_08_rows b125_08_labels]
    decide +kernel

def b125_09_rows : List Row := [(row3 27 34 43), (row3 27 34 44), (row3 27 34 45), (row3 27 34 46), (row3 27 34 47), (row3 27 34 48), (row3 27 34 49), (row3 27 34 50), (row3 27 34 51), (row3 27 34 52), (row3 27 34 53), (row3 27 34 54), (row3 27 34 55), (row3 27 34 56), (row3 27 34 57), (row3 27 34 58)]

def b125_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_09_rows b125_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_09_rows b125_09_labels]
    decide +kernel

def b125_10_rows : List Row := [(row3 27 34 59), (row3 27 34 60), (row3 27 34 61), (row3 27 34 62), (row3 27 34 63), (row3 27 35 36), (row3 27 35 37), (row3 27 35 38), (row3 27 35 39), (row3 27 35 40), (row3 27 35 41), (row3 27 35 42), (row3 27 35 43), (row3 27 35 44), (row3 27 35 45), (row3 27 35 46)]

def b125_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_10_rows b125_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_10_rows b125_10_labels]
    decide +kernel

def b125_11_rows : List Row := [(row3 27 35 47), (row3 27 35 48), (row3 27 35 49), (row3 27 35 50), (row3 27 35 51), (row3 27 35 52), (row3 27 35 53), (row3 27 35 54), (row3 27 35 55), (row3 27 35 56), (row3 27 35 57), (row3 27 35 58), (row3 27 35 59), (row3 27 35 60), (row3 27 35 61), (row3 27 35 62)]

def b125_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_11_rows b125_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_11_rows b125_11_labels]
    decide +kernel

def b125_12_rows : List Row := [(row3 27 35 63), (row3 27 36 37), (row3 27 36 38), (row3 27 36 39), (row3 27 36 40), (row3 27 36 41), (row3 27 36 42), (row3 27 36 43), (row3 27 36 44), (row3 27 36 45), (row3 27 36 46), (row3 27 36 47), (row3 27 36 48), (row3 27 36 49), (row3 27 36 50), (row3 27 36 51)]

def b125_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_12_rows b125_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_12_rows b125_12_labels]
    decide +kernel

def b125_13_rows : List Row := [(row3 27 36 52), (row3 27 36 53), (row3 27 36 54), (row3 27 36 55), (row3 27 36 56), (row3 27 36 57), (row3 27 36 58), (row3 27 36 59), (row3 27 36 60), (row3 27 36 61), (row3 27 36 62), (row3 27 36 63), (row3 27 37 38), (row3 27 37 39), (row3 27 37 40), (row3 27 37 41)]

def b125_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_13_rows b125_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_13_rows b125_13_labels]
    decide +kernel

def b125_14_rows : List Row := [(row3 27 37 42), (row3 27 37 43), (row3 27 37 44), (row3 27 37 45), (row3 27 37 46), (row3 27 37 47), (row3 27 37 48), (row3 27 37 49), (row3 27 37 50), (row3 27 37 51), (row3 27 37 52), (row3 27 37 53), (row3 27 37 54), (row3 27 37 55), (row3 27 37 56), (row3 27 37 57)]

def b125_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_14_rows b125_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_14_rows b125_14_labels]
    decide +kernel

def b125_15_rows : List Row := [(row3 27 37 58), (row3 27 37 59), (row3 27 37 60), (row3 27 37 61), (row3 27 37 62), (row3 27 37 63), (row3 27 38 39), (row3 27 38 40), (row3 27 38 41), (row3 27 38 42), (row3 27 38 43), (row3 27 38 44), (row3 27 38 45), (row3 27 38 46), (row3 27 38 47), (row3 27 38 48)]

def b125_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b125_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b125_15_rows b125_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b125_15_rows b125_15_labels]
    decide +kernel

theorem checked125 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_125 QuarticIntegerComputationalData.ids64_125 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b125_00_rows ++ b125_01_rows) ++ (b125_02_rows ++ b125_03_rows)) ++ ((b125_04_rows ++ b125_05_rows) ++ (b125_06_rows ++ b125_07_rows))) ++ (((b125_08_rows ++ b125_09_rows) ++ (b125_10_rows ++ b125_11_rows)) ++ ((b125_12_rows ++ b125_13_rows) ++ (b125_14_rows ++ b125_15_rows))))
    ((((b125_00_labels ++ b125_01_labels) ++ (b125_02_labels ++ b125_03_labels)) ++ ((b125_04_labels ++ b125_05_labels) ++ (b125_06_labels ++ b125_07_labels))) ++ (((b125_08_labels ++ b125_09_labels) ++ (b125_10_labels ++ b125_11_labels)) ++ ((b125_12_labels ++ b125_13_labels) ++ (b125_14_labels ++ b125_15_labels)))) 0
  exact ((((b125_00_checked.append (c := 0) b125_01_checked (by decide +kernel)).append (c := 0) (b125_02_checked.append (c := 0) b125_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b125_04_checked.append (c := 0) b125_05_checked (by decide +kernel)).append (c := 0) (b125_06_checked.append (c := 0) b125_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b125_08_checked.append (c := 0) b125_09_checked (by decide +kernel)).append (c := 0) (b125_10_checked.append (c := 0) b125_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b125_12_checked.append (c := 0) b125_13_checked (by decide +kernel)).append (c := 0) (b125_14_checked.append (c := 0) b125_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b126_00_rows : List Row := [(row3 27 38 49), (row3 27 38 50), (row3 27 38 51), (row3 27 38 52), (row3 27 38 53), (row3 27 38 54), (row3 27 38 55), (row3 27 38 56), (row3 27 38 57), (row3 27 38 58), (row3 27 38 59), (row3 27 38 60), (row3 27 38 61), (row3 27 38 62), (row3 27 38 63), (row3 27 39 40)]

def b126_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_00_rows b126_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_00_rows b126_00_labels]
    decide +kernel

def b126_01_rows : List Row := [(row3 27 39 41), (row3 27 39 42), (row3 27 39 43), (row3 27 39 44), (row3 27 39 45), (row3 27 39 46), (row3 27 39 47), (row3 27 39 48), (row3 27 39 49), (row3 27 39 50), (row3 27 39 51), (row3 27 39 52), (row3 27 39 53), (row3 27 39 54), (row3 27 39 55), (row3 27 39 56)]

def b126_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_01_rows b126_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_01_rows b126_01_labels]
    decide +kernel

def b126_02_rows : List Row := [(row3 27 39 57), (row3 27 39 58), (row3 27 39 59), (row3 27 39 60), (row3 27 39 61), (row3 27 39 62), (row3 27 39 63), (row3 27 40 41), (row3 27 40 42), (row3 27 40 43), (row3 27 40 44), (row3 27 40 45), (row3 27 40 46), (row3 27 40 47), (row3 27 40 48), (row3 27 40 49)]

def b126_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_02_rows b126_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_02_rows b126_02_labels]
    decide +kernel

def b126_03_rows : List Row := [(row3 27 40 50), (row3 27 40 51), (row3 27 40 52), (row3 27 40 53), (row3 27 40 54), (row3 27 40 55), (row3 27 40 56), (row3 27 40 57), (row3 27 40 58), (row3 27 40 59), (row3 27 40 60), (row3 27 40 61), (row3 27 40 62), (row3 27 40 63), (row3 27 41 42), (row3 27 41 43)]

def b126_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_03_rows b126_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_03_rows b126_03_labels]
    decide +kernel

def b126_04_rows : List Row := [(row3 27 41 44), (row3 27 41 45), (row3 27 41 46), (row3 27 41 47), (row3 27 41 48), (row3 27 41 49), (row3 27 41 50), (row3 27 41 51), (row3 27 41 52), (row3 27 41 53), (row3 27 41 54), (row3 27 41 55), (row3 27 41 56), (row3 27 41 57), (row3 27 41 58), (row3 27 41 59)]

def b126_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_04_rows b126_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_04_rows b126_04_labels]
    decide +kernel

def b126_05_rows : List Row := [(row3 27 41 60), (row3 27 41 61), (row3 27 41 62), (row3 27 41 63), (row3 27 42 43), (row3 27 42 44), (row3 27 42 45), (row3 27 42 46), (row3 27 42 47), (row3 27 42 48), (row3 27 42 49), (row3 27 42 50), (row3 27 42 51), (row3 27 42 52), (row3 27 42 53), (row3 27 42 54)]

def b126_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_05_rows b126_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_05_rows b126_05_labels]
    decide +kernel

def b126_06_rows : List Row := [(row3 27 42 55), (row3 27 42 56), (row3 27 42 57), (row3 27 42 58), (row3 27 42 59), (row3 27 42 60), (row3 27 42 61), (row3 27 42 62), (row3 27 42 63), (row3 27 43 44), (row3 27 43 45), (row3 27 43 46), (row3 27 43 47), (row3 27 43 48), (row3 27 43 49), (row3 27 43 50)]

def b126_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_06_rows b126_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_06_rows b126_06_labels]
    decide +kernel

def b126_07_rows : List Row := [(row3 27 43 51), (row3 27 43 52), (row3 27 43 53), (row3 27 43 54), (row3 27 43 55), (row3 27 43 56), (row3 27 43 57), (row3 27 43 58), (row3 27 43 59), (row3 27 43 60), (row3 27 43 61), (row3 27 43 62), (row3 27 43 63), (row3 27 44 45), (row3 27 44 46), (row3 27 44 47)]

def b126_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_07_rows b126_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_07_rows b126_07_labels]
    decide +kernel

def b126_08_rows : List Row := [(row3 27 44 48), (row3 27 44 49), (row3 27 44 50), (row3 27 44 51), (row3 27 44 52), (row3 27 44 53), (row3 27 44 54), (row3 27 44 55), (row3 27 44 56), (row3 27 44 57), (row3 27 44 58), (row3 27 44 59), (row3 27 44 60), (row3 27 44 61), (row3 27 44 62), (row3 27 44 63)]

def b126_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_08_rows b126_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_08_rows b126_08_labels]
    decide +kernel

def b126_09_rows : List Row := [(row3 27 45 46), (row3 27 45 47), (row3 27 45 48), (row3 27 45 49), (row3 27 45 50), (row3 27 45 51), (row3 27 45 52), (row3 27 45 53), (row3 27 45 54), (row3 27 45 55), (row3 27 45 56), (row3 27 45 57), (row3 27 45 58), (row3 27 45 59), (row3 27 45 60), (row3 27 45 61)]

def b126_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_09_rows b126_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_09_rows b126_09_labels]
    decide +kernel

def b126_10_rows : List Row := [(row3 27 45 62), (row3 27 45 63), (row3 27 46 47), (row3 27 46 48), (row3 27 46 49), (row3 27 46 50), (row3 27 46 51), (row3 27 46 52), (row3 27 46 53), (row3 27 46 54), (row3 27 46 55), (row3 27 46 56), (row3 27 46 57), (row3 27 46 58), (row3 27 46 59), (row3 27 46 60)]

def b126_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_10_rows b126_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_10_rows b126_10_labels]
    decide +kernel

def b126_11_rows : List Row := [(row3 27 46 61), (row3 27 46 62), (row3 27 46 63), (row3 27 47 48), (row3 27 47 49), (row3 27 47 50), (row3 27 47 51), (row3 27 47 52), (row3 27 47 53), (row3 27 47 54), (row3 27 47 55), (row3 27 47 56), (row3 27 47 57), (row3 27 47 58), (row3 27 47 59), (row3 27 47 60)]

def b126_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_11_rows b126_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_11_rows b126_11_labels]
    decide +kernel

def b126_12_rows : List Row := [(row3 27 47 61), (row3 27 47 62), (row3 27 47 63), (row3 27 48 49), (row3 27 48 50), (row3 27 48 51), (row3 27 48 52), (row3 27 48 53), (row3 27 48 54), (row3 27 48 55), (row3 27 48 56), (row3 27 48 57), (row3 27 48 58), (row3 27 48 59), (row3 27 48 60), (row3 27 48 61)]

def b126_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_12_rows b126_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_12_rows b126_12_labels]
    decide +kernel

def b126_13_rows : List Row := [(row3 27 48 62), (row3 27 48 63), (row3 27 49 50), (row3 27 49 51), (row3 27 49 52), (row3 27 49 53), (row3 27 49 54), (row3 27 49 55), (row3 27 49 56), (row3 27 49 57), (row3 27 49 58), (row3 27 49 59), (row3 27 49 60), (row3 27 49 61), (row3 27 49 62), (row3 27 49 63)]

def b126_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_13_rows b126_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_13_rows b126_13_labels]
    decide +kernel

def b126_14_rows : List Row := [(row3 27 50 51), (row3 27 50 52), (row3 27 50 53), (row3 27 50 54), (row3 27 50 55), (row3 27 50 56), (row3 27 50 57), (row3 27 50 58), (row3 27 50 59), (row3 27 50 60), (row3 27 50 61), (row3 27 50 62), (row3 27 50 63), (row3 27 51 52), (row3 27 51 53), (row3 27 51 54)]

def b126_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_14_rows b126_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_14_rows b126_14_labels]
    decide +kernel

def b126_15_rows : List Row := [(row3 27 51 55), (row3 27 51 56), (row3 27 51 57), (row3 27 51 58), (row3 27 51 59), (row3 27 51 60), (row3 27 51 61), (row3 27 51 62), (row3 27 51 63), (row3 27 52 53), (row3 27 52 54), (row3 27 52 55), (row3 27 52 56), (row3 27 52 57), (row3 27 52 58), (row3 27 52 59)]

def b126_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b126_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b126_15_rows b126_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b126_15_rows b126_15_labels]
    decide +kernel

theorem checked126 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_126 QuarticIntegerComputationalData.ids64_126 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b126_00_rows ++ b126_01_rows) ++ (b126_02_rows ++ b126_03_rows)) ++ ((b126_04_rows ++ b126_05_rows) ++ (b126_06_rows ++ b126_07_rows))) ++ (((b126_08_rows ++ b126_09_rows) ++ (b126_10_rows ++ b126_11_rows)) ++ ((b126_12_rows ++ b126_13_rows) ++ (b126_14_rows ++ b126_15_rows))))
    ((((b126_00_labels ++ b126_01_labels) ++ (b126_02_labels ++ b126_03_labels)) ++ ((b126_04_labels ++ b126_05_labels) ++ (b126_06_labels ++ b126_07_labels))) ++ (((b126_08_labels ++ b126_09_labels) ++ (b126_10_labels ++ b126_11_labels)) ++ ((b126_12_labels ++ b126_13_labels) ++ (b126_14_labels ++ b126_15_labels)))) 0
  exact ((((b126_00_checked.append (c := 0) b126_01_checked (by decide +kernel)).append (c := 0) (b126_02_checked.append (c := 0) b126_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b126_04_checked.append (c := 0) b126_05_checked (by decide +kernel)).append (c := 0) (b126_06_checked.append (c := 0) b126_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b126_08_checked.append (c := 0) b126_09_checked (by decide +kernel)).append (c := 0) (b126_10_checked.append (c := 0) b126_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b126_12_checked.append (c := 0) b126_13_checked (by decide +kernel)).append (c := 0) (b126_14_checked.append (c := 0) b126_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b127_00_rows : List Row := [(row3 27 52 60), (row3 27 52 61), (row3 27 52 62), (row3 27 52 63), (row3 27 53 54), (row3 27 53 55), (row3 27 53 56), (row3 27 53 57), (row3 27 53 58), (row3 27 53 59), (row3 27 53 60), (row3 27 53 61), (row3 27 53 62), (row3 27 53 63), (row3 27 54 55), (row3 27 54 56)]

def b127_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_00_rows b127_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_00_rows b127_00_labels]
    decide +kernel

def b127_01_rows : List Row := [(row3 27 54 57), (row3 27 54 58), (row3 27 54 59), (row3 27 54 60), (row3 27 54 61), (row3 27 54 62), (row3 27 54 63), (row3 27 55 56), (row3 27 55 57), (row3 27 55 58), (row3 27 55 59), (row3 27 55 60), (row3 27 55 61), (row3 27 55 62), (row3 27 55 63), (row3 27 56 57)]

def b127_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_01_rows b127_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_01_rows b127_01_labels]
    decide +kernel

def b127_02_rows : List Row := [(row3 27 56 58), (row3 27 56 59), (row3 27 56 60), (row3 27 56 61), (row3 27 56 62), (row3 27 56 63), (row3 27 57 58), (row3 27 57 59), (row3 27 57 60), (row3 27 57 61), (row3 27 57 62), (row3 27 57 63), (row3 27 58 59), (row3 27 58 60), (row3 27 58 61), (row3 27 58 62)]

def b127_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_02_rows b127_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_02_rows b127_02_labels]
    decide +kernel

def b127_03_rows : List Row := [(row3 27 58 63), (row3 27 59 60), (row3 27 59 61), (row3 27 59 62), (row3 27 59 63), (row3 27 60 61), (row3 27 60 62), (row3 27 60 63), (row3 27 61 62), (row3 27 61 63), (row3 27 62 63), (row3 28 29 30), (row3 28 29 31), (row3 28 29 32), (row3 28 29 33), (row3 28 29 34)]

def b127_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_03_rows b127_03_labels 555889215118270689432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_03_rows b127_03_labels]
    decide +kernel

def b127_04_rows : List Row := [(row3 28 29 35), (row3 28 29 36), (row3 28 29 37), (row3 28 29 38), (row3 28 29 39), (row3 28 29 40), (row3 28 29 41), (row3 28 29 42), (row3 28 29 43), (row3 28 29 44), (row3 28 29 45), (row3 28 29 46), (row3 28 29 47), (row3 28 29 48), (row3 28 29 49), (row3 28 29 50)]

def b127_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_04_rows b127_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_04_rows b127_04_labels]
    decide +kernel

def b127_05_rows : List Row := [(row3 28 29 51), (row3 28 29 52), (row3 28 29 53), (row3 28 29 54), (row3 28 29 55), (row3 28 29 56), (row3 28 29 57), (row3 28 29 58), (row3 28 29 59), (row3 28 29 60), (row3 28 29 61), (row3 28 29 62), (row3 28 29 63), (row3 28 30 31), (row3 28 30 32), (row3 28 30 33)]

def b127_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_05_rows b127_05_labels 20188125678608034804015000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_05_rows b127_05_labels]
    decide +kernel

def b127_06_rows : List Row := [(row3 28 30 34), (row3 28 30 35), (row3 28 30 36), (row3 28 30 37), (row3 28 30 38), (row3 28 30 39), (row3 28 30 40), (row3 28 30 41), (row3 28 30 42), (row3 28 30 43), (row3 28 30 44), (row3 28 30 45), (row3 28 30 46), (row3 28 30 47), (row3 28 30 48), (row3 28 30 49)]

def b127_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_06_rows b127_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_06_rows b127_06_labels]
    decide +kernel

def b127_07_rows : List Row := [(row3 28 30 50), (row3 28 30 51), (row3 28 30 52), (row3 28 30 53), (row3 28 30 54), (row3 28 30 55), (row3 28 30 56), (row3 28 30 57), (row3 28 30 58), (row3 28 30 59), (row3 28 30 60), (row3 28 30 61), (row3 28 30 62), (row3 28 30 63), (row3 28 31 32), (row3 28 31 33)]

def b127_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 243 462 243)]

theorem b127_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_07_rows b127_07_labels 265670176471171165413000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_07_rows b127_07_labels]
    decide +kernel

def b127_08_rows : List Row := [(row3 28 31 34), (row3 28 31 35), (row3 28 31 36), (row3 28 31 37), (row3 28 31 38), (row3 28 31 39), (row3 28 31 40), (row3 28 31 41), (row3 28 31 42), (row3 28 31 43), (row3 28 31 44), (row3 28 31 45), (row3 28 31 46), (row3 28 31 47), (row3 28 31 48), (row3 28 31 49)]

def b127_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 263 462 263), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b127_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_08_rows b127_08_labels 20094184675308266531070000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_08_rows b127_08_labels]
    decide +kernel

def b127_09_rows : List Row := [(row3 28 31 50), (row3 28 31 51), (row3 28 31 52), (row3 28 31 53), (row3 28 31 54), (row3 28 31 55), (row3 28 31 56), (row3 28 31 57), (row3 28 31 58), (row3 28 31 59), (row3 28 31 60), (row3 28 31 61), (row3 28 31 62), (row3 28 31 63), (row3 28 32 33), (row3 28 32 34)]

def b127_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_09_rows b127_09_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_09_rows b127_09_labels]
    decide +kernel

def b127_10_rows : List Row := [(row3 28 32 35), (row3 28 32 36), (row3 28 32 37), (row3 28 32 38), (row3 28 32 39), (row3 28 32 40), (row3 28 32 41), (row3 28 32 42), (row3 28 32 43), (row3 28 32 44), (row3 28 32 45), (row3 28 32 46), (row3 28 32 47), (row3 28 32 48), (row3 28 32 49), (row3 28 32 50)]

def b127_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_10_rows b127_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_10_rows b127_10_labels]
    decide +kernel

def b127_11_rows : List Row := [(row3 28 32 51), (row3 28 32 52), (row3 28 32 53), (row3 28 32 54), (row3 28 32 55), (row3 28 32 56), (row3 28 32 57), (row3 28 32 58), (row3 28 32 59), (row3 28 32 60), (row3 28 32 61), (row3 28 32 62), (row3 28 32 63), (row3 28 33 34), (row3 28 33 35), (row3 28 33 36)]

def b127_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_11_rows b127_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_11_rows b127_11_labels]
    decide +kernel

def b127_12_rows : List Row := [(row3 28 33 37), (row3 28 33 38), (row3 28 33 39), (row3 28 33 40), (row3 28 33 41), (row3 28 33 42), (row3 28 33 43), (row3 28 33 44), (row3 28 33 45), (row3 28 33 46), (row3 28 33 47), (row3 28 33 48), (row3 28 33 49), (row3 28 33 50), (row3 28 33 51), (row3 28 33 52)]

def b127_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_12_rows b127_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_12_rows b127_12_labels]
    decide +kernel

def b127_13_rows : List Row := [(row3 28 33 53), (row3 28 33 54), (row3 28 33 55), (row3 28 33 56), (row3 28 33 57), (row3 28 33 58), (row3 28 33 59), (row3 28 33 60), (row3 28 33 61), (row3 28 33 62), (row3 28 33 63), (row3 28 34 35), (row3 28 34 36), (row3 28 34 37), (row3 28 34 38), (row3 28 34 39)]

def b127_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_13_rows b127_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_13_rows b127_13_labels]
    decide +kernel

def b127_14_rows : List Row := [(row3 28 34 40), (row3 28 34 41), (row3 28 34 42), (row3 28 34 43), (row3 28 34 44), (row3 28 34 45), (row3 28 34 46), (row3 28 34 47), (row3 28 34 48), (row3 28 34 49), (row3 28 34 50), (row3 28 34 51), (row3 28 34 52), (row3 28 34 53), (row3 28 34 54), (row3 28 34 55)]

def b127_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_14_rows b127_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_14_rows b127_14_labels]
    decide +kernel

def b127_15_rows : List Row := [(row3 28 34 56), (row3 28 34 57), (row3 28 34 58), (row3 28 34 59), (row3 28 34 60), (row3 28 34 61), (row3 28 34 62), (row3 28 34 63), (row3 28 35 36), (row3 28 35 37), (row3 28 35 38), (row3 28 35 39), (row3 28 35 40), (row3 28 35 41), (row3 28 35 42), (row3 28 35 43)]

def b127_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b127_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b127_15_rows b127_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b127_15_rows b127_15_labels]
    decide +kernel

theorem checked127 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_127 QuarticIntegerComputationalData.ids64_127 41106702339116495644005000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b127_00_rows ++ b127_01_rows) ++ (b127_02_rows ++ b127_03_rows)) ++ ((b127_04_rows ++ b127_05_rows) ++ (b127_06_rows ++ b127_07_rows))) ++ (((b127_08_rows ++ b127_09_rows) ++ (b127_10_rows ++ b127_11_rows)) ++ ((b127_12_rows ++ b127_13_rows) ++ (b127_14_rows ++ b127_15_rows))))
    ((((b127_00_labels ++ b127_01_labels) ++ (b127_02_labels ++ b127_03_labels)) ++ ((b127_04_labels ++ b127_05_labels) ++ (b127_06_labels ++ b127_07_labels))) ++ (((b127_08_labels ++ b127_09_labels) ++ (b127_10_labels ++ b127_11_labels)) ++ ((b127_12_labels ++ b127_13_labels) ++ (b127_14_labels ++ b127_15_labels)))) 41106702339116495644005000
  exact ((((b127_00_checked.append (c := 0) b127_01_checked (by decide +kernel)).append (c := 555889215118270689432000) (b127_02_checked.append (c := 555889215118270689432000) b127_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 21009685070197476658860000) ((b127_04_checked.append (c := 20188125678608034804015000) b127_05_checked (by decide +kernel)).append (c := 20453795855079205969428000) (b127_06_checked.append (c := 265670176471171165413000) b127_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 41106702339116495644005000) (((b127_08_checked.append (c := 20097017268919018985145000) b127_09_checked (by decide +kernel)).append (c := 20097017268919018985145000) (b127_10_checked.append (c := 0) b127_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 20097017268919018985145000) ((b127_12_checked.append (c := 0) b127_13_checked (by decide +kernel)).append (c := 0) (b127_14_checked.append (c := 0) b127_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b128_00_rows : List Row := [(row3 28 35 44), (row3 28 35 45), (row3 28 35 46), (row3 28 35 47), (row3 28 35 48), (row3 28 35 49), (row3 28 35 50), (row3 28 35 51), (row3 28 35 52), (row3 28 35 53), (row3 28 35 54), (row3 28 35 55), (row3 28 35 56), (row3 28 35 57), (row3 28 35 58), (row3 28 35 59)]

def b128_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_00_rows b128_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_00_rows b128_00_labels]
    decide +kernel

def b128_01_rows : List Row := [(row3 28 35 60), (row3 28 35 61), (row3 28 35 62), (row3 28 35 63), (row3 28 36 37), (row3 28 36 38), (row3 28 36 39), (row3 28 36 40), (row3 28 36 41), (row3 28 36 42), (row3 28 36 43), (row3 28 36 44), (row3 28 36 45), (row3 28 36 46), (row3 28 36 47), (row3 28 36 48)]

def b128_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_01_rows b128_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_01_rows b128_01_labels]
    decide +kernel

def b128_02_rows : List Row := [(row3 28 36 49), (row3 28 36 50), (row3 28 36 51), (row3 28 36 52), (row3 28 36 53), (row3 28 36 54), (row3 28 36 55), (row3 28 36 56), (row3 28 36 57), (row3 28 36 58), (row3 28 36 59), (row3 28 36 60), (row3 28 36 61), (row3 28 36 62), (row3 28 36 63), (row3 28 37 38)]

def b128_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_02_rows b128_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_02_rows b128_02_labels]
    decide +kernel

def b128_03_rows : List Row := [(row3 28 37 39), (row3 28 37 40), (row3 28 37 41), (row3 28 37 42), (row3 28 37 43), (row3 28 37 44), (row3 28 37 45), (row3 28 37 46), (row3 28 37 47), (row3 28 37 48), (row3 28 37 49), (row3 28 37 50), (row3 28 37 51), (row3 28 37 52), (row3 28 37 53), (row3 28 37 54)]

def b128_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_03_rows b128_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_03_rows b128_03_labels]
    decide +kernel

def b128_04_rows : List Row := [(row3 28 37 55), (row3 28 37 56), (row3 28 37 57), (row3 28 37 58), (row3 28 37 59), (row3 28 37 60), (row3 28 37 61), (row3 28 37 62), (row3 28 37 63), (row3 28 38 39), (row3 28 38 40), (row3 28 38 41), (row3 28 38 42), (row3 28 38 43), (row3 28 38 44), (row3 28 38 45)]

def b128_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_04_rows b128_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_04_rows b128_04_labels]
    decide +kernel

def b128_05_rows : List Row := [(row3 28 38 46), (row3 28 38 47), (row3 28 38 48), (row3 28 38 49), (row3 28 38 50), (row3 28 38 51), (row3 28 38 52), (row3 28 38 53), (row3 28 38 54), (row3 28 38 55), (row3 28 38 56), (row3 28 38 57), (row3 28 38 58), (row3 28 38 59), (row3 28 38 60), (row3 28 38 61)]

def b128_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_05_rows b128_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_05_rows b128_05_labels]
    decide +kernel

def b128_06_rows : List Row := [(row3 28 38 62), (row3 28 38 63), (row3 28 39 40), (row3 28 39 41), (row3 28 39 42), (row3 28 39 43), (row3 28 39 44), (row3 28 39 45), (row3 28 39 46), (row3 28 39 47), (row3 28 39 48), (row3 28 39 49), (row3 28 39 50), (row3 28 39 51), (row3 28 39 52), (row3 28 39 53)]

def b128_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_06_rows b128_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_06_rows b128_06_labels]
    decide +kernel

def b128_07_rows : List Row := [(row3 28 39 54), (row3 28 39 55), (row3 28 39 56), (row3 28 39 57), (row3 28 39 58), (row3 28 39 59), (row3 28 39 60), (row3 28 39 61), (row3 28 39 62), (row3 28 39 63), (row3 28 40 41), (row3 28 40 42), (row3 28 40 43), (row3 28 40 44), (row3 28 40 45), (row3 28 40 46)]

def b128_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_07_rows b128_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_07_rows b128_07_labels]
    decide +kernel

def b128_08_rows : List Row := [(row3 28 40 47), (row3 28 40 48), (row3 28 40 49), (row3 28 40 50), (row3 28 40 51), (row3 28 40 52), (row3 28 40 53), (row3 28 40 54), (row3 28 40 55), (row3 28 40 56), (row3 28 40 57), (row3 28 40 58), (row3 28 40 59), (row3 28 40 60), (row3 28 40 61), (row3 28 40 62)]

def b128_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_08_rows b128_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_08_rows b128_08_labels]
    decide +kernel

def b128_09_rows : List Row := [(row3 28 40 63), (row3 28 41 42), (row3 28 41 43), (row3 28 41 44), (row3 28 41 45), (row3 28 41 46), (row3 28 41 47), (row3 28 41 48), (row3 28 41 49), (row3 28 41 50), (row3 28 41 51), (row3 28 41 52), (row3 28 41 53), (row3 28 41 54), (row3 28 41 55), (row3 28 41 56)]

def b128_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_09_rows b128_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_09_rows b128_09_labels]
    decide +kernel

def b128_10_rows : List Row := [(row3 28 41 57), (row3 28 41 58), (row3 28 41 59), (row3 28 41 60), (row3 28 41 61), (row3 28 41 62), (row3 28 41 63), (row3 28 42 43), (row3 28 42 44), (row3 28 42 45), (row3 28 42 46), (row3 28 42 47), (row3 28 42 48), (row3 28 42 49), (row3 28 42 50), (row3 28 42 51)]

def b128_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_10_rows b128_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_10_rows b128_10_labels]
    decide +kernel

def b128_11_rows : List Row := [(row3 28 42 52), (row3 28 42 53), (row3 28 42 54), (row3 28 42 55), (row3 28 42 56), (row3 28 42 57), (row3 28 42 58), (row3 28 42 59), (row3 28 42 60), (row3 28 42 61), (row3 28 42 62), (row3 28 42 63), (row3 28 43 44), (row3 28 43 45), (row3 28 43 46), (row3 28 43 47)]

def b128_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_11_rows b128_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_11_rows b128_11_labels]
    decide +kernel

def b128_12_rows : List Row := [(row3 28 43 48), (row3 28 43 49), (row3 28 43 50), (row3 28 43 51), (row3 28 43 52), (row3 28 43 53), (row3 28 43 54), (row3 28 43 55), (row3 28 43 56), (row3 28 43 57), (row3 28 43 58), (row3 28 43 59), (row3 28 43 60), (row3 28 43 61), (row3 28 43 62), (row3 28 43 63)]

def b128_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_12_rows b128_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_12_rows b128_12_labels]
    decide +kernel

def b128_13_rows : List Row := [(row3 28 44 45), (row3 28 44 46), (row3 28 44 47), (row3 28 44 48), (row3 28 44 49), (row3 28 44 50), (row3 28 44 51), (row3 28 44 52), (row3 28 44 53), (row3 28 44 54), (row3 28 44 55), (row3 28 44 56), (row3 28 44 57), (row3 28 44 58), (row3 28 44 59), (row3 28 44 60)]

def b128_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_13_rows b128_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_13_rows b128_13_labels]
    decide +kernel

def b128_14_rows : List Row := [(row3 28 44 61), (row3 28 44 62), (row3 28 44 63), (row3 28 45 46), (row3 28 45 47), (row3 28 45 48), (row3 28 45 49), (row3 28 45 50), (row3 28 45 51), (row3 28 45 52), (row3 28 45 53), (row3 28 45 54), (row3 28 45 55), (row3 28 45 56), (row3 28 45 57), (row3 28 45 58)]

def b128_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_14_rows b128_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_14_rows b128_14_labels]
    decide +kernel

def b128_15_rows : List Row := [(row3 28 45 59), (row3 28 45 60), (row3 28 45 61), (row3 28 45 62), (row3 28 45 63), (row3 28 46 47), (row3 28 46 48), (row3 28 46 49), (row3 28 46 50), (row3 28 46 51), (row3 28 46 52), (row3 28 46 53), (row3 28 46 54), (row3 28 46 55), (row3 28 46 56), (row3 28 46 57)]

def b128_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b128_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b128_15_rows b128_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b128_15_rows b128_15_labels]
    decide +kernel

theorem checked128 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_128 QuarticIntegerComputationalData.ids64_128 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b128_00_rows ++ b128_01_rows) ++ (b128_02_rows ++ b128_03_rows)) ++ ((b128_04_rows ++ b128_05_rows) ++ (b128_06_rows ++ b128_07_rows))) ++ (((b128_08_rows ++ b128_09_rows) ++ (b128_10_rows ++ b128_11_rows)) ++ ((b128_12_rows ++ b128_13_rows) ++ (b128_14_rows ++ b128_15_rows))))
    ((((b128_00_labels ++ b128_01_labels) ++ (b128_02_labels ++ b128_03_labels)) ++ ((b128_04_labels ++ b128_05_labels) ++ (b128_06_labels ++ b128_07_labels))) ++ (((b128_08_labels ++ b128_09_labels) ++ (b128_10_labels ++ b128_11_labels)) ++ ((b128_12_labels ++ b128_13_labels) ++ (b128_14_labels ++ b128_15_labels)))) 0
  exact ((((b128_00_checked.append (c := 0) b128_01_checked (by decide +kernel)).append (c := 0) (b128_02_checked.append (c := 0) b128_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b128_04_checked.append (c := 0) b128_05_checked (by decide +kernel)).append (c := 0) (b128_06_checked.append (c := 0) b128_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b128_08_checked.append (c := 0) b128_09_checked (by decide +kernel)).append (c := 0) (b128_10_checked.append (c := 0) b128_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b128_12_checked.append (c := 0) b128_13_checked (by decide +kernel)).append (c := 0) (b128_14_checked.append (c := 0) b128_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
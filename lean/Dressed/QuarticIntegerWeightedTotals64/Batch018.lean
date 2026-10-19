import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch017
import Dressed.QuarticIntegerComputationalData64.Batch018


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b145_00_rows : List Row := [(row3 38 39 49), (row3 38 39 50), (row3 38 39 51), (row3 38 39 52), (row3 38 39 53), (row3 38 39 54), (row3 38 39 55), (row3 38 39 56), (row3 38 39 57), (row3 38 39 58), (row3 38 39 59), (row3 38 39 60), (row3 38 39 61), (row3 38 39 62), (row3 38 39 63), (row3 38 40 41)]

def b145_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 236 462 236), (row3 180 154 154)]

theorem b145_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_00_rows b145_00_labels 988893321618387858581464200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_00_rows b145_00_labels]
    decide +kernel

def b145_01_rows : List Row := [(row3 38 40 42), (row3 38 40 43), (row3 38 40 44), (row3 38 40 45), (row3 38 40 46), (row3 38 40 47), (row3 38 40 48), (row3 38 40 49), (row3 38 40 50), (row3 38 40 51), (row3 38 40 52), (row3 38 40 53), (row3 38 40 54), (row3 38 40 55), (row3 38 40 56), (row3 38 40 57)]

def b145_01_labels : List Row := [(row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237), (row3 265 266 266), (row3 356 159 91), (row3 370 88 211), (row3 278 279 279), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243), (row3 228 228 234), (row3 319 320 320), (row3 265 266 266), (row3 234 234 234)]

theorem b145_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_01_rows b145_01_labels 16101668735912200371160241700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_01_rows b145_01_labels]
    decide +kernel

def b145_02_rows : List Row := [(row3 38 40 58), (row3 38 40 59), (row3 38 40 60), (row3 38 40 61), (row3 38 40 62), (row3 38 40 63), (row3 38 41 42), (row3 38 41 43), (row3 38 41 44), (row3 38 41 45), (row3 38 41 46), (row3 38 41 47), (row3 38 41 48), (row3 38 41 49), (row3 38 41 50), (row3 38 41 51)]

def b145_02_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 226 234 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_02_rows b145_02_labels 17075062363131625666396500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_02_rows b145_02_labels]
    decide +kernel

def b145_03_rows : List Row := [(row3 38 41 52), (row3 38 41 53), (row3 38 41 54), (row3 38 41 55), (row3 38 41 56), (row3 38 41 57), (row3 38 41 58), (row3 38 41 59), (row3 38 41 60), (row3 38 41 61), (row3 38 41 62), (row3 38 41 63), (row3 38 42 43), (row3 38 42 44), (row3 38 42 45), (row3 38 42 46)]

def b145_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_03_rows b145_03_labels 1068097806637679270250000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_03_rows b145_03_labels]
    decide +kernel

def b145_04_rows : List Row := [(row3 38 42 47), (row3 38 42 48), (row3 38 42 49), (row3 38 42 50), (row3 38 42 51), (row3 38 42 52), (row3 38 42 53), (row3 38 42 54), (row3 38 42 55), (row3 38 42 56), (row3 38 42 57), (row3 38 42 58), (row3 38 42 59), (row3 38 42 60), (row3 38 42 61), (row3 38 42 62)]

def b145_04_labels : List Row := [(row3 236 236 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_04_rows b145_04_labels 677115485566156741437000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_04_rows b145_04_labels]
    decide +kernel

def b145_05_rows : List Row := [(row3 38 42 63), (row3 38 43 44), (row3 38 43 45), (row3 38 43 46), (row3 38 43 47), (row3 38 43 48), (row3 38 43 49), (row3 38 43 50), (row3 38 43 51), (row3 38 43 52), (row3 38 43 53), (row3 38 43 54), (row3 38 43 55), (row3 38 43 56), (row3 38 43 57), (row3 38 43 58)]

def b145_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_05_rows b145_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_05_rows b145_05_labels]
    decide +kernel

def b145_06_rows : List Row := [(row3 38 43 59), (row3 38 43 60), (row3 38 43 61), (row3 38 43 62), (row3 38 43 63), (row3 38 44 45), (row3 38 44 46), (row3 38 44 47), (row3 38 44 48), (row3 38 44 49), (row3 38 44 50), (row3 38 44 51), (row3 38 44 52), (row3 38 44 53), (row3 38 44 54), (row3 38 44 55)]

def b145_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 462 246 246)]

theorem b145_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_06_rows b145_06_labels 712091134078662141927000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_06_rows b145_06_labels]
    decide +kernel

def b145_07_rows : List Row := [(row3 38 44 56), (row3 38 44 57), (row3 38 44 58), (row3 38 44 59), (row3 38 44 60), (row3 38 44 61), (row3 38 44 62), (row3 38 44 63), (row3 38 45 46), (row3 38 45 47), (row3 38 45 48), (row3 38 45 49), (row3 38 45 50), (row3 38 45 51), (row3 38 45 52), (row3 38 45 53)]

def b145_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_07_rows b145_07_labels 7432174753989315875826300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_07_rows b145_07_labels]
    decide +kernel

def b145_08_rows : List Row := [(row3 38 45 54), (row3 38 45 55), (row3 38 45 56), (row3 38 45 57), (row3 38 45 58), (row3 38 45 59), (row3 38 45 60), (row3 38 45 61), (row3 38 45 62), (row3 38 45 63), (row3 38 46 47), (row3 38 46 48), (row3 38 46 49), (row3 38 46 50), (row3 38 46 51), (row3 38 46 52)]

def b145_08_labels : List Row := [(row3 278 278 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 163 163 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_08_rows b145_08_labels 1080468201442474988506087200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_08_rows b145_08_labels]
    decide +kernel

def b145_09_rows : List Row := [(row3 38 46 53), (row3 38 46 54), (row3 38 46 55), (row3 38 46 56), (row3 38 46 57), (row3 38 46 58), (row3 38 46 59), (row3 38 46 60), (row3 38 46 61), (row3 38 46 62), (row3 38 46 63), (row3 38 47 48), (row3 38 47 49), (row3 38 47 50), (row3 38 47 51), (row3 38 47 52)]

def b145_09_labels : List Row := [(row3 462 462 462), (row3 180 180 462), (row3 306 309 309), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 232 462 232), (row3 300 462 300), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_09_rows b145_09_labels 1292590751196971580719636160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_09_rows b145_09_labels]
    decide +kernel

def b145_10_rows : List Row := [(row3 38 47 53), (row3 38 47 54), (row3 38 47 55), (row3 38 47 56), (row3 38 47 57), (row3 38 47 58), (row3 38 47 59), (row3 38 47 60), (row3 38 47 61), (row3 38 47 62), (row3 38 47 63), (row3 38 48 49), (row3 38 48 50), (row3 38 48 51), (row3 38 48 52), (row3 38 48 53)]

def b145_10_labels : List Row := [(row3 232 462 232), (row3 300 278 288), (row3 399 83 157), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 226 234 226), (row3 288 462 288), (row3 180 180 462), (row3 265 265 462), (row3 237 237 462), (row3 462 462 462), (row3 237 237 462)]

theorem b145_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_10_rows b145_10_labels 20929302704334385886991755040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_10_rows b145_10_labels]
    decide +kernel

def b145_11_rows : List Row := [(row3 38 48 54), (row3 38 48 55), (row3 38 48 56), (row3 38 48 57), (row3 38 48 58), (row3 38 48 59), (row3 38 48 60), (row3 38 48 61), (row3 38 48 62), (row3 38 48 63), (row3 38 49 50), (row3 38 49 51), (row3 38 49 52), (row3 38 49 53), (row3 38 49 54), (row3 38 49 55)]

def b145_11_labels : List Row := [(row3 278 278 462), (row3 368 114 86), (row3 180 180 462), (row3 278 278 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 234), (row3 300 278 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 289 291 291)]

theorem b145_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_11_rows b145_11_labels 10658462407610900125846824720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_11_rows b145_11_labels]
    decide +kernel

def b145_12_rows : List Row := [(row3 38 49 56), (row3 38 49 57), (row3 38 49 58), (row3 38 49 59), (row3 38 49 60), (row3 38 49 61), (row3 38 49 62), (row3 38 49 63), (row3 38 50 51), (row3 38 50 52), (row3 38 50 53), (row3 38 50 54), (row3 38 50 55), (row3 38 50 56), (row3 38 50 57), (row3 38 50 58)]

def b145_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b145_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_12_rows b145_12_labels 1167002136509643148329000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_12_rows b145_12_labels]
    decide +kernel

def b145_13_rows : List Row := [(row3 38 50 59), (row3 38 50 60), (row3 38 50 61), (row3 38 50 62), (row3 38 50 63), (row3 38 51 52), (row3 38 51 53), (row3 38 51 54), (row3 38 51 55), (row3 38 51 56), (row3 38 51 57), (row3 38 51 58), (row3 38 51 59), (row3 38 51 60), (row3 38 51 61), (row3 38 51 62)]

def b145_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243)]

theorem b145_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_13_rows b145_13_labels 143252446673123127400500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_13_rows b145_13_labels]
    decide +kernel

def b145_14_rows : List Row := [(row3 38 51 63), (row3 38 52 53), (row3 38 52 54), (row3 38 52 55), (row3 38 52 56), (row3 38 52 57), (row3 38 52 58), (row3 38 52 59), (row3 38 52 60), (row3 38 52 61), (row3 38 52 62), (row3 38 52 63), (row3 38 53 54), (row3 38 53 55), (row3 38 53 56), (row3 38 53 57)]

def b145_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 265 265 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 180 180 462), (row3 289 291 291), (row3 462 462 462), (row3 462 462 462)]

theorem b145_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_14_rows b145_14_labels 536923866170765142529146000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_14_rows b145_14_labels]
    decide +kernel

def b145_15_rows : List Row := [(row3 38 53 58), (row3 38 53 59), (row3 38 53 60), (row3 38 53 61), (row3 38 53 62), (row3 38 53 63), (row3 38 54 55), (row3 38 54 56), (row3 38 54 57), (row3 38 54 58), (row3 38 54 59), (row3 38 54 60), (row3 38 54 61), (row3 38 54 62), (row3 38 54 63), (row3 38 55 56)]

def b145_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 279 279), (row3 232 462 232), (row3 368 86 114), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 370 88 211), (row3 300 462 300), (row3 306 309 309)]

theorem b145_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b145_15_rows b145_15_labels 19833735544108138615359011760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b145_15_rows b145_15_labels]
    decide +kernel

theorem checked145 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_145 QuarticIntegerComputationalData.ids64_145 71450320328520810775665733080 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b145_00_rows ++ b145_01_rows) ++ (b145_02_rows ++ b145_03_rows)) ++ ((b145_04_rows ++ b145_05_rows) ++ (b145_06_rows ++ b145_07_rows))) ++ (((b145_08_rows ++ b145_09_rows) ++ (b145_10_rows ++ b145_11_rows)) ++ ((b145_12_rows ++ b145_13_rows) ++ (b145_14_rows ++ b145_15_rows))))
    ((((b145_00_labels ++ b145_01_labels) ++ (b145_02_labels ++ b145_03_labels)) ++ ((b145_04_labels ++ b145_05_labels) ++ (b145_06_labels ++ b145_07_labels))) ++ (((b145_08_labels ++ b145_09_labels) ++ (b145_10_labels ++ b145_11_labels)) ++ ((b145_12_labels ++ b145_13_labels) ++ (b145_14_labels ++ b145_15_labels)))) 71450320328520810775665733080
  exact ((((b145_00_checked.append (c := 17090562057530588229741705900) b145_01_checked (by decide +kernel)).append (c := 17108705217700357534678352400) (b145_02_checked.append (c := 18143160169769304936646500) b145_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17117526599073991669437542700) ((b145_04_checked.append (c := 677115485566156741437000) b145_05_checked (by decide +kernel)).append (c := 8821381373634134759190300) (b145_06_checked.append (c := 8144265888067978017753300) b145_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 71450320328520810775665733080) (((b145_08_checked.append (c := 2373058952639446569225723360) b145_09_checked (by decide +kernel)).append (c := 33960824064584732582064303120) (b145_10_checked.append (c := 31587765111945286012838579760) b145_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 54332793729446819106228190380) ((b145_12_checked.append (c := 1310254583182766275729500) b145_13_checked (by decide +kernel)).append (c := 20371969664862086524163887260) (b145_14_checked.append (c := 20370659410278903757888157760) b145_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b146_00_rows : List Row := [(row3 38 55 57), (row3 38 55 58), (row3 38 55 59), (row3 38 55 60), (row3 38 55 61), (row3 38 55 62), (row3 38 55 63), (row3 38 56 57), (row3 38 56 58), (row3 38 56 59), (row3 38 56 60), (row3 38 56 61), (row3 38 56 62), (row3 38 56 63), (row3 38 57 58), (row3 38 57 59)]

def b146_00_labels : List Row := [(row3 224 224 224), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 224 224 224), (row3 319 320 320), (row3 399 83 157), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 163 462 163), (row3 462 462 462), (row3 462 462 462)]

theorem b146_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_00_rows b146_00_labels 21395429724751148391531112800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_00_rows b146_00_labels]
    decide +kernel

def b146_01_rows : List Row := [(row3 38 57 60), (row3 38 57 61), (row3 38 57 62), (row3 38 57 63), (row3 38 58 59), (row3 38 58 60), (row3 38 58 61), (row3 38 58 62), (row3 38 58 63), (row3 38 59 60), (row3 38 59 61), (row3 38 59 62), (row3 38 59 63), (row3 38 60 61), (row3 38 60 62), (row3 38 60 63)]

def b146_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 236 462 236)]

theorem b146_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_01_rows b146_01_labels 11581164494367396094811700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_01_rows b146_01_labels]
    decide +kernel

def b146_02_rows : List Row := [(row3 38 61 62), (row3 38 61 63), (row3 38 62 63), (row3 39 40 41), (row3 39 40 42), (row3 39 40 43), (row3 39 40 44), (row3 39 40 45), (row3 39 40 46), (row3 39 40 47), (row3 39 40 48), (row3 39 40 49), (row3 39 40 50), (row3 39 40 51), (row3 39 40 52), (row3 39 40 53)]

def b146_02_labels : List Row := [(row3 180 154 154), (row3 273 462 273), (row3 356 91 159), (row3 352 373 365), (row3 199 190 198), (row3 262 262 261), (row3 462 238 238), (row3 262 262 261), (row3 199 190 198), (row3 73 359 429), (row3 58 430 372), (row3 175 161 175), (row3 279 279 278), (row3 462 236 236), (row3 462 462 462), (row3 462 236 236)]

theorem b146_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_02_rows b146_02_labels 266028085394848712529716498730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_02_rows b146_02_labels]
    decide +kernel

def b146_03_rows : List Row := [(row3 39 40 54), (row3 39 40 55), (row3 39 40 56), (row3 39 40 57), (row3 39 40 58), (row3 39 40 59), (row3 39 40 60), (row3 39 40 61), (row3 39 40 62), (row3 39 40 63), (row3 39 41 42), (row3 39 41 43), (row3 39 41 44), (row3 39 41 45), (row3 39 41 46), (row3 39 41 47)]

def b146_03_labels : List Row := [(row3 283 283 278), (row3 128 126 125), (row3 167 190 166), (row3 279 279 278), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 296 296 295), (row3 284 462 284), (row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 191 193 235)]

theorem b146_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_03_rows b146_03_labels 7367290074081262823618874780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_03_rows b146_03_labels]
    decide +kernel

def b146_04_rows : List Row := [(row3 39 41 48), (row3 39 41 49), (row3 39 41 50), (row3 39 41 51), (row3 39 41 52), (row3 39 41 53), (row3 39 41 54), (row3 39 41 55), (row3 39 41 56), (row3 39 41 57), (row3 39 41 58), (row3 39 41 59), (row3 39 41 60), (row3 39 41 61), (row3 39 41 62), (row3 39 41 63)]

def b146_04_labels : List Row := [(row3 143 137 146), (row3 117 11 214), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 292 289 292), (row3 286 462 286), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235)]

theorem b146_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_04_rows b146_04_labels 2029721476543819186796633790 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_04_rows b146_04_labels]
    decide +kernel

def b146_05_rows : List Row := [(row3 39 42 43), (row3 39 42 44), (row3 39 42 45), (row3 39 42 46), (row3 39 42 47), (row3 39 42 48), (row3 39 42 49), (row3 39 42 50), (row3 39 42 51), (row3 39 42 52), (row3 39 42 53), (row3 39 42 54), (row3 39 42 55), (row3 39 42 56), (row3 39 42 57), (row3 39 42 58)]

def b146_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 291 291 289), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b146_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_05_rows b146_05_labels 31435709791807802769736200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_05_rows b146_05_labels]
    decide +kernel

def b146_06_rows : List Row := [(row3 39 42 59), (row3 39 42 60), (row3 39 42 61), (row3 39 42 62), (row3 39 42 63), (row3 39 43 44), (row3 39 43 45), (row3 39 43 46), (row3 39 43 47), (row3 39 43 48), (row3 39 43 49), (row3 39 43 50), (row3 39 43 51), (row3 39 43 52), (row3 39 43 53), (row3 39 43 54)]

def b146_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b146_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_06_rows b146_06_labels 301066359412777219228500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_06_rows b146_06_labels]
    decide +kernel

def b146_07_rows : List Row := [(row3 39 43 55), (row3 39 43 56), (row3 39 43 57), (row3 39 43 58), (row3 39 43 59), (row3 39 43 60), (row3 39 43 61), (row3 39 43 62), (row3 39 43 63), (row3 39 44 45), (row3 39 44 46), (row3 39 44 47), (row3 39 44 48), (row3 39 44 49), (row3 39 44 50), (row3 39 44 51)]

def b146_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b146_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_07_rows b146_07_labels 19713966259789303503675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_07_rows b146_07_labels]
    decide +kernel

def b146_08_rows : List Row := [(row3 39 44 52), (row3 39 44 53), (row3 39 44 54), (row3 39 44 55), (row3 39 44 56), (row3 39 44 57), (row3 39 44 58), (row3 39 44 59), (row3 39 44 60), (row3 39 44 61), (row3 39 44 62), (row3 39 44 63), (row3 39 45 46), (row3 39 45 47), (row3 39 45 48), (row3 39 45 49)]

def b146_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 462 235 235), (row3 462 462 462)]

theorem b146_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_08_rows b146_08_labels 348283616053274528199232500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_08_rows b146_08_labels]
    decide +kernel

def b146_09_rows : List Row := [(row3 39 45 50), (row3 39 45 51), (row3 39 45 52), (row3 39 45 53), (row3 39 45 54), (row3 39 45 55), (row3 39 45 56), (row3 39 45 57), (row3 39 45 58), (row3 39 45 59), (row3 39 45 60), (row3 39 45 61), (row3 39 45 62), (row3 39 45 63), (row3 39 46 47), (row3 39 46 48)]

def b146_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 291 289 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 235 235), (row3 358 358 462), (row3 291 291 289)]

theorem b146_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_09_rows b146_09_labels 13422848063820325740330988560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_09_rows b146_09_labels]
    decide +kernel

def b146_10_rows : List Row := [(row3 39 46 49), (row3 39 46 50), (row3 39 46 51), (row3 39 46 52), (row3 39 46 53), (row3 39 46 54), (row3 39 46 55), (row3 39 46 56), (row3 39 46 57), (row3 39 46 58), (row3 39 46 59), (row3 39 46 60), (row3 39 46 61), (row3 39 46 62), (row3 39 46 63), (row3 39 47 48)]

def b146_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 146 149 137), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 279 279 278), (row3 126 137 127)]

theorem b146_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_10_rows b146_10_labels 9298824397228710106496189820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_10_rows b146_10_labels]
    decide +kernel

def b146_11_rows : List Row := [(row3 39 47 49), (row3 39 47 50), (row3 39 47 51), (row3 39 47 52), (row3 39 47 53), (row3 39 47 54), (row3 39 47 55), (row3 39 47 56), (row3 39 47 57), (row3 39 47 58), (row3 39 47 59), (row3 39 47 60), (row3 39 47 61), (row3 39 47 62), (row3 39 47 63), (row3 39 48 49)]

def b146_11_labels : List Row := [(row3 287 462 287), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 160 228 163), (row3 41 435 95), (row3 303 462 303), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 167 190 166), (row3 361 387 391)]

theorem b146_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_11_rows b146_11_labels 383539442240275293198741667500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_11_rows b146_11_labels]
    decide +kernel

def b146_12_rows : List Row := [(row3 39 48 50), (row3 39 48 51), (row3 39 48 52), (row3 39 48 53), (row3 39 48 54), (row3 39 48 55), (row3 39 48 56), (row3 39 48 57), (row3 39 48 58), (row3 39 48 59), (row3 39 48 60), (row3 39 48 61), (row3 39 48 62), (row3 39 48 63), (row3 39 49 50), (row3 39 49 51)]

def b146_12_labels : List Row := [(row3 184 184 178), (row3 266 265 266), (row3 462 237 237), (row3 266 265 266), (row3 182 182 178), (row3 78 401 427), (row3 41 435 95), (row3 146 149 137), (row3 291 289 291), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 292 289 292), (row3 128 126 125), (row3 293 293 462), (row3 234 234 462)]

theorem b146_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_12_rows b146_12_labels 423633056270855021406438654270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_12_rows b146_12_labels]
    decide +kernel

def b146_13_rows : List Row := [(row3 39 49 52), (row3 39 49 53), (row3 39 49 54), (row3 39 49 55), (row3 39 49 56), (row3 39 49 57), (row3 39 49 58), (row3 39 49 59), (row3 39 49 60), (row3 39 49 61), (row3 39 49 62), (row3 39 49 63), (row3 39 50 51), (row3 39 50 52), (row3 39 50 53), (row3 39 50 54)]

def b146_13_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 246 246 462), (row3 182 182 178), (row3 160 228 163), (row3 293 293 462), (row3 228 228 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 283 283 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b146_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_13_rows b146_13_labels 947248355168532632782955160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_13_rows b146_13_labels]
    decide +kernel

def b146_14_rows : List Row := [(row3 39 50 55), (row3 39 50 56), (row3 39 50 57), (row3 39 50 58), (row3 39 50 59), (row3 39 50 60), (row3 39 50 61), (row3 39 50 62), (row3 39 50 63), (row3 39 51 52), (row3 39 51 53), (row3 39 51 54), (row3 39 51 55), (row3 39 51 56), (row3 39 51 57), (row3 39 51 58)]

def b146_14_labels : List Row := [(row3 266 265 266), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b146_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_14_rows b146_14_labels 63104312550433319740242900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_14_rows b146_14_labels]
    decide +kernel

def b146_15_rows : List Row := [(row3 39 51 59), (row3 39 51 60), (row3 39 51 61), (row3 39 51 62), (row3 39 51 63), (row3 39 52 53), (row3 39 52 54), (row3 39 52 55), (row3 39 52 56), (row3 39 52 57), (row3 39 52 58), (row3 39 52 59), (row3 39 52 60), (row3 39 52 61), (row3 39 52 62), (row3 39 52 63)]

def b146_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 266 265 266), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 236 236)]

theorem b146_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b146_15_rows b146_15_labels 3900307028919684142721400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b146_15_rows b146_15_labels]
    decide +kernel

theorem checked146 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_146 QuarticIntegerComputationalData.ids64_146 1128140266140110830828123223610 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b146_00_rows ++ b146_01_rows) ++ (b146_02_rows ++ b146_03_rows)) ++ ((b146_04_rows ++ b146_05_rows) ++ (b146_06_rows ++ b146_07_rows))) ++ (((b146_08_rows ++ b146_09_rows) ++ (b146_10_rows ++ b146_11_rows)) ++ ((b146_12_rows ++ b146_13_rows) ++ (b146_14_rows ++ b146_15_rows))))
    ((((b146_00_labels ++ b146_01_labels) ++ (b146_02_labels ++ b146_03_labels)) ++ ((b146_04_labels ++ b146_05_labels) ++ (b146_06_labels ++ b146_07_labels))) ++ (((b146_08_labels ++ b146_09_labels) ++ (b146_10_labels ++ b146_11_labels)) ++ ((b146_12_labels ++ b146_13_labels) ++ (b146_14_labels ++ b146_15_labels)))) 1128140266140110830828123223610
  exact ((((b146_00_checked.append (c := 21407010889245515787625924500) b146_01_checked (by decide +kernel)).append (c := 294802386358175491140961298010) (b146_02_checked.append (c := 273395375468929975353335373510) b146_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 296883558577130320211250571500) ((b146_04_checked.append (c := 2061157186335626989566369990) b146_05_checked (by decide +kernel)).append (c := 2081172218954829070289273490) (b146_06_checked.append (c := 20015032619202080722903500) b146_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1128140266140110830828123223610) (((b146_08_checked.append (c := 13771131679873600268530221060) b146_09_checked (by decide +kernel)).append (c := 406609398317377603573768078380) (b146_10_checked.append (c := 392838266637504003305237857320) b146_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 831256707562980510616872652110) ((b146_12_checked.append (c := 424580304626023554039221609430) b146_13_checked (by decide +kernel)).append (c := 424647309245602907043104573730) (b146_14_checked.append (c := 67004619579353003882964300) b146_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b147_00_rows : List Row := [(row3 39 53 54), (row3 39 53 55), (row3 39 53 56), (row3 39 53 57), (row3 39 53 58), (row3 39 53 59), (row3 39 53 60), (row3 39 53 61), (row3 39 53 62), (row3 39 53 63), (row3 39 54 55), (row3 39 54 56), (row3 39 54 57), (row3 39 54 58), (row3 39 54 59), (row3 39 54 60)]

def b147_00_labels : List Row := [(row3 293 293 462), (row3 184 184 178), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 361 387 391), (row3 287 462 287), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248)]

theorem b147_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_00_rows b147_00_labels 14789053715634956608309737270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_00_rows b147_00_labels]
    decide +kernel

def b147_01_rows : List Row := [(row3 39 54 61), (row3 39 54 62), (row3 39 54 63), (row3 39 55 56), (row3 39 55 57), (row3 39 55 58), (row3 39 55 59), (row3 39 55 60), (row3 39 55 61), (row3 39 55 62), (row3 39 55 63), (row3 39 56 57), (row3 39 56 58), (row3 39 56 59), (row3 39 56 60), (row3 39 56 61)]

def b147_01_labels : List Row := [(row3 228 462 228), (row3 117 11 214), (row3 175 161 175), (row3 126 137 127), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 291 289), (row3 143 137 146), (row3 58 430 372), (row3 358 358 462), (row3 193 193 462), (row3 263 263 462), (row3 462 462 462), (row3 263 263 462)]

theorem b147_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_01_rows b147_01_labels 163156012417855466094409946010 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_01_rows b147_01_labels]
    decide +kernel

def b147_02_rows : List Row := [(row3 39 56 62), (row3 39 56 63), (row3 39 57 58), (row3 39 57 59), (row3 39 57 60), (row3 39 57 61), (row3 39 57 62), (row3 39 57 63), (row3 39 58 59), (row3 39 58 60), (row3 39 58 61), (row3 39 58 62), (row3 39 58 63), (row3 39 59 60), (row3 39 59 61), (row3 39 59 62)]

def b147_02_labels : List Row := [(row3 191 193 235), (row3 73 359 429), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 199 190 198), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 262 262 261), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b147_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_02_rows b147_02_labels 110030337096830054015701180980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_02_rows b147_02_labels]
    decide +kernel

def b147_03_rows : List Row := [(row3 39 59 63), (row3 39 60 61), (row3 39 60 62), (row3 39 60 63), (row3 39 61 62), (row3 39 61 63), (row3 39 62 63), (row3 40 41 42), (row3 40 41 43), (row3 40 41 44), (row3 40 41 45), (row3 40 41 46), (row3 40 41 47), (row3 40 41 48), (row3 40 41 49), (row3 40 41 50)]

def b147_03_labels : List Row := [(row3 462 238 238), (row3 462 462 462), (row3 235 462 235), (row3 262 262 261), (row3 284 462 284), (row3 199 190 198), (row3 352 373 365), (row3 336 428 72), (row3 202 97 334), (row3 254 8 203), (row3 201 201 208), (row3 343 338 330), (row3 54 65 65), (row3 29 445 56), (row3 44 439 74), (row3 158 89 356)]

theorem b147_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_03_rows b147_03_labels 5060836662474940449659031252120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_03_rows b147_03_labels]
    decide +kernel

def b147_04_rows : List Row := [(row3 40 41 51), (row3 40 41 52), (row3 40 41 53), (row3 40 41 54), (row3 40 41 55), (row3 40 41 56), (row3 40 41 57), (row3 40 41 58), (row3 40 41 59), (row3 40 41 60), (row3 40 41 61), (row3 40 41 62), (row3 40 41 63), (row3 40 42 43), (row3 40 42 44), (row3 40 42 45)]

def b147_04_labels : List Row := [(row3 254 10 171), (row3 462 462 462), (row3 263 462 263), (row3 154 154 180), (row3 376 366 354), (row3 400 397 384), (row3 123 92 331), (row3 260 10 173), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 271 462 271), (row3 152 150 177), (row3 256 256 255), (row3 239 462 239), (row3 256 256 255)]

theorem b147_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_04_rows b147_04_labels 1396949433546121314058380768450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_04_rows b147_04_labels]
    decide +kernel

def b147_05_rows : List Row := [(row3 40 42 46), (row3 40 42 47), (row3 40 42 48), (row3 40 42 49), (row3 40 42 50), (row3 40 42 51), (row3 40 42 52), (row3 40 42 53), (row3 40 42 54), (row3 40 42 55), (row3 40 42 56), (row3 40 42 57), (row3 40 42 58), (row3 40 42 59), (row3 40 42 60), (row3 40 42 61)]

def b147_05_labels : List Row := [(row3 206 210 210), (row3 343 330 338), (row3 426 77 385), (row3 110 111 109), (row3 302 302 265), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 266 266 265), (row3 190 196 197), (row3 206 164 164), (row3 318 318 315), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b147_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_05_rows b147_05_labels 73831608136014693173398424430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_05_rows b147_05_labels]
    decide +kernel

def b147_06_rows : List Row := [(row3 40 42 62), (row3 40 42 63), (row3 40 43 44), (row3 40 43 45), (row3 40 43 46), (row3 40 43 47), (row3 40 43 48), (row3 40 43 49), (row3 40 43 50), (row3 40 43 51), (row3 40 43 52), (row3 40 43 53), (row3 40 43 54), (row3 40 43 55), (row3 40 43 56), (row3 40 43 57)]

def b147_06_labels : List Row := [(row3 237 462 237), (row3 266 266 265), (row3 240 462 240), (row3 239 239 239), (row3 256 255 256), (row3 201 208 201), (row3 97 334 202), (row3 317 308 317), (row3 226 226 237), (row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 256 255 256), (row3 237 226 226)]

theorem b147_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_06_rows b147_06_labels 3400301531973054245006781420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_06_rows b147_06_labels]
    decide +kernel

def b147_07_rows : List Row := [(row3 40 43 58), (row3 40 43 59), (row3 40 43 60), (row3 40 43 61), (row3 40 43 62), (row3 40 43 63), (row3 40 44 45), (row3 40 44 46), (row3 40 44 47), (row3 40 44 48), (row3 40 44 49), (row3 40 44 50), (row3 40 44 51), (row3 40 44 52), (row3 40 44 53), (row3 40 44 54)]

def b147_07_labels : List Row := [(row3 249 462 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 237 237 237), (row3 240 240 462), (row3 239 239 462), (row3 254 203 8), (row3 257 257 462), (row3 238 230 232), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 249 462)]

theorem b147_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_07_rows b147_07_labels 181890666644350192319733000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_07_rows b147_07_labels]
    decide +kernel

def b147_08_rows : List Row := [(row3 40 44 55), (row3 40 44 56), (row3 40 44 57), (row3 40 44 58), (row3 40 44 59), (row3 40 44 60), (row3 40 44 61), (row3 40 44 62), (row3 40 44 63), (row3 40 45 46), (row3 40 45 47), (row3 40 45 48), (row3 40 45 49), (row3 40 45 50), (row3 40 45 51), (row3 40 45 52)]

def b147_08_labels : List Row := [(row3 238 230 232), (row3 239 239 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 256 255 256), (row3 202 334 97), (row3 97 334 202), (row3 262 261 262), (row3 237 237 237), (row3 241 462 241), (row3 462 462 462)]

theorem b147_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_08_rows b147_08_labels 6140427279375526674162786000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_08_rows b147_08_labels]
    decide +kernel

def b147_09_rows : List Row := [(row3 40 45 53), (row3 40 45 54), (row3 40 45 55), (row3 40 45 56), (row3 40 45 57), (row3 40 45 58), (row3 40 45 59), (row3 40 45 60), (row3 40 45 61), (row3 40 45 62), (row3 40 45 63), (row3 40 46 47), (row3 40 46 48), (row3 40 46 49), (row3 40 46 50), (row3 40 46 51)]

def b147_09_labels : List Row := [(row3 241 462 241), (row3 226 226 237), (row3 317 308 317), (row3 256 255 256), (row3 237 237 237), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 462 249), (row3 237 226 226), (row3 336 72 428), (row3 426 77 385), (row3 190 196 197), (row3 266 266 265), (row3 238 462 238)]

theorem b147_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_09_rows b147_09_labels 165607075705873420700217178500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_09_rows b147_09_labels]
    decide +kernel

def b147_10_rows : List Row := [(row3 40 46 52), (row3 40 46 53), (row3 40 46 54), (row3 40 46 55), (row3 40 46 56), (row3 40 46 57), (row3 40 46 58), (row3 40 46 59), (row3 40 46 60), (row3 40 46 61), (row3 40 46 62), (row3 40 46 63), (row3 40 47 48), (row3 40 47 49), (row3 40 47 50), (row3 40 47 51)]

def b147_10_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 302 302 265), (row3 110 111 109), (row3 206 164 164), (row3 266 266 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 318 318 315), (row3 29 445 56), (row3 376 366 354), (row3 154 154 180), (row3 263 462 263)]

theorem b147_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_10_rows b147_10_labels 4179455540252855061478337661510 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_10_rows b147_10_labels]
    decide +kernel

def b147_11_rows : List Row := [(row3 40 47 52), (row3 40 47 53), (row3 40 47 54), (row3 40 47 55), (row3 40 47 56), (row3 40 47 57), (row3 40 47 58), (row3 40 47 59), (row3 40 47 60), (row3 40 47 61), (row3 40 47 62), (row3 40 47 63), (row3 40 48 49), (row3 40 48 50), (row3 40 48 51), (row3 40 48 52)]

def b147_11_labels : List Row := [(row3 462 462 462), (row3 254 10 171), (row3 158 89 356), (row3 44 439 74), (row3 400 397 384), (row3 152 150 177), (row3 271 462 271), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 260 10 173), (row3 123 92 331), (row3 448 454 449), (row3 68 69 76), (row3 343 338 330), (row3 462 208 208)]

theorem b147_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_11_rows b147_11_labels 9331036767276310150751978236350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_11_rows b147_11_labels]
    decide +kernel

def b147_12_rows : List Row := [(row3 40 48 53), (row3 40 48 54), (row3 40 48 55), (row3 40 48 56), (row3 40 48 57), (row3 40 48 58), (row3 40 48 59), (row3 40 48 60), (row3 40 48 61), (row3 40 48 62), (row3 40 48 63), (row3 40 49 50), (row3 40 49 51), (row3 40 49 52), (row3 40 49 53), (row3 40 49 54)]

def b147_12_labels : List Row := [(row3 343 338 330), (row3 68 69 76), (row3 448 454 449), (row3 21 459 441), (row3 51 53 57), (row3 393 386 363), (row3 238 192 193), (row3 462 462 462), (row3 238 192 193), (row3 393 386 363), (row3 51 53 57), (row3 395 415 407), (row3 148 137 145), (row3 279 279 278), (row3 236 235 233), (row3 298 298 295)]

theorem b147_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_12_rows b147_12_labels 877430830447219712784375035575380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_12_rows b147_12_labels]
    decide +kernel

def b147_13_rows : List Row := [(row3 40 49 55), (row3 40 49 56), (row3 40 49 57), (row3 40 49 58), (row3 40 49 59), (row3 40 49 60), (row3 40 49 61), (row3 40 49 62), (row3 40 49 63), (row3 40 50 51), (row3 40 50 52), (row3 40 50 53), (row3 40 50 54), (row3 40 50 55), (row3 40 50 56), (row3 40 50 57)]

def b147_13_labels : List Row := [(row3 107 106 106), (row3 51 53 57), (row3 40 438 413), (row3 120 112 120), (row3 310 310 306), (row3 462 232 232), (row3 243 243 462), (row3 229 226 224), (row3 324 324 323), (row3 294 462 294), (row3 234 462 234), (row3 245 462 245), (row3 234 234 234), (row3 298 295 298), (row3 393 386 363), (row3 120 112 120)]

theorem b147_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_13_rows b147_13_labels 1794859153060141708877762264430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_13_rows b147_13_labels]
    decide +kernel

def b147_14_rows : List Row := [(row3 40 50 58), (row3 40 50 59), (row3 40 50 60), (row3 40 50 61), (row3 40 50 62), (row3 40 50 63), (row3 40 51 52), (row3 40 51 53), (row3 40 51 54), (row3 40 51 55), (row3 40 51 56), (row3 40 51 57), (row3 40 51 58), (row3 40 51 59), (row3 40 51 60), (row3 40 51 61)]

def b147_14_labels : List Row := [(row3 119 11 216), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 246 462 246), (row3 229 226 224), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 236 233 235), (row3 238 192 193), (row3 310 310 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b147_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_14_rows b147_14_labels 2343137889152443554246226050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_14_rows b147_14_labels]
    decide +kernel

def b147_15_rows : List Row := [(row3 40 51 62), (row3 40 51 63), (row3 40 52 53), (row3 40 52 54), (row3 40 52 55), (row3 40 52 56), (row3 40 52 57), (row3 40 52 58), (row3 40 52 59), (row3 40 52 60), (row3 40 52 61), (row3 40 52 62), (row3 40 52 63), (row3 40 53 54), (row3 40 53 55), (row3 40 53 56)]

def b147_15_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 234 234 462), (row3 279 278 279), (row3 462 462 462), (row3 462 232 232), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 232 232), (row3 294 294 462), (row3 148 145 137), (row3 238 192 193)]

theorem b147_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b147_15_rows b147_15_labels 709688572636914679545113220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b147_15_rows b147_15_labels]
    decide +kernel

theorem checked147 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_147 QuarticIntegerComputationalData.ids64_147 899734157536842072349137842865120 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b147_00_rows ++ b147_01_rows) ++ (b147_02_rows ++ b147_03_rows)) ++ ((b147_04_rows ++ b147_05_rows) ++ (b147_06_rows ++ b147_07_rows))) ++ (((b147_08_rows ++ b147_09_rows) ++ (b147_10_rows ++ b147_11_rows)) ++ ((b147_12_rows ++ b147_13_rows) ++ (b147_14_rows ++ b147_15_rows))))
    ((((b147_00_labels ++ b147_01_labels) ++ (b147_02_labels ++ b147_03_labels)) ++ ((b147_04_labels ++ b147_05_labels) ++ (b147_06_labels ++ b147_07_labels))) ++ (((b147_08_labels ++ b147_09_labels) ++ (b147_10_labels ++ b147_11_labels)) ++ ((b147_12_labels ++ b147_13_labels) ++ (b147_14_labels ++ b147_15_labels)))) 899734157536842072349137842865120
  exact ((((b147_00_checked.append (c := 177945066133490422702719683280) b147_01_checked (by decide +kernel)).append (c := 5348812065705260926377452116380) (b147_02_checked.append (c := 5170866999571770503674732433100) b147_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6823175299586014338046557823680) ((b147_04_checked.append (c := 1470781041682136007231779192880) b147_05_checked (by decide +kernel)).append (c := 1474363233880753411669105707300) (b147_06_checked.append (c := 3582192198617404437326514420) b147_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 899734157536842072349137842865120) (((b147_08_checked.append (c := 171747502985248947374379964500) b147_09_checked (by decide +kernel)).append (c := 13682239810514414159604695862360) (b147_10_checked.append (c := 13510492307529165212230315897860) b147_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 892910982237256058011091285041440) ((b147_12_checked.append (c := 879225689600279854493252797839810) b147_13_checked (by decide +kernel)).append (c := 879228742426741643851486589179080) (b147_14_checked.append (c := 3052826461789358233791339270) b147_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b148_00_rows : List Row := [(row3 40 53 57), (row3 40 53 58), (row3 40 53 59), (row3 40 53 60), (row3 40 53 61), (row3 40 53 62), (row3 40 53 63), (row3 40 54 55), (row3 40 54 56), (row3 40 54 57), (row3 40 54 58), (row3 40 54 59), (row3 40 54 60), (row3 40 54 61), (row3 40 54 62), (row3 40 54 63)]

def b148_00_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 310 310 306), (row3 395 407 415), (row3 393 386 363), (row3 229 226 224), (row3 246 462 246), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 119 11 216), (row3 120 112 120)]

theorem b148_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_00_rows b148_00_labels 63897357651605620652441612070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_00_rows b148_00_labels]
    decide +kernel

def b148_01_rows : List Row := [(row3 40 55 56), (row3 40 55 57), (row3 40 55 58), (row3 40 55 59), (row3 40 55 60), (row3 40 55 61), (row3 40 55 62), (row3 40 55 63), (row3 40 56 57), (row3 40 56 58), (row3 40 56 59), (row3 40 56 60), (row3 40 56 61), (row3 40 56 62), (row3 40 56 63), (row3 40 57 58)]

def b148_01_labels : List Row := [(row3 51 53 57), (row3 324 324 323), (row3 229 226 224), (row3 243 243 462), (row3 462 232 232), (row3 310 310 306), (row3 120 112 120), (row3 40 438 413), (row3 448 449 454), (row3 68 76 69), (row3 343 330 338), (row3 462 208 208), (row3 343 330 338), (row3 68 76 69), (row3 448 449 454), (row3 395 407 415)]

theorem b148_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_01_rows b148_01_labels 16645790920397991037957835532390 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_01_rows b148_01_labels]
    decide +kernel

def b148_02_rows : List Row := [(row3 40 57 59), (row3 40 57 60), (row3 40 57 61), (row3 40 57 62), (row3 40 57 63), (row3 40 58 59), (row3 40 58 60), (row3 40 58 61), (row3 40 58 62), (row3 40 58 63), (row3 40 59 60), (row3 40 59 61), (row3 40 59 62), (row3 40 59 63), (row3 40 60 61), (row3 40 60 62)]

def b148_02_labels : List Row := [(row3 148 145 137), (row3 279 278 279), (row3 236 233 235), (row3 298 295 298), (row3 107 106 106), (row3 294 294 462), (row3 234 234 462), (row3 245 245 462), (row3 234 234 234), (row3 298 298 295), (row3 462 462 462), (row3 462 462 462), (row3 245 462 245), (row3 236 235 233), (row3 462 462 462), (row3 234 462 234)]

theorem b148_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_02_rows b148_02_labels 1795483063234603188656604540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_02_rows b148_02_labels]
    decide +kernel

def b148_03_rows : List Row := [(row3 40 60 63), (row3 40 61 62), (row3 40 61 63), (row3 40 62 63), (row3 41 42 43), (row3 41 42 44), (row3 41 42 45), (row3 41 42 46), (row3 41 42 47), (row3 41 42 48), (row3 41 42 49), (row3 41 42 50), (row3 41 42 51), (row3 41 42 52), (row3 41 42 53), (row3 41 42 54)]

def b148_03_labels : List Row := [(row3 279 279 278), (row3 294 462 294), (row3 148 137 145), (row3 395 415 407), (row3 462 193 193), (row3 462 263 263), (row3 462 462 462), (row3 462 263 263), (row3 238 192 193), (row3 137 126 127), (row3 436 43 383), (row3 139 124 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b148_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_03_rows b148_03_labels 422557739708545541767873142550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_03_rows b148_03_labels]
    decide +kernel

def b148_04_rows : List Row := [(row3 41 42 55), (row3 41 42 56), (row3 41 42 57), (row3 41 42 58), (row3 41 42 59), (row3 41 42 60), (row3 41 42 61), (row3 41 42 62), (row3 41 42 63), (row3 41 43 44), (row3 41 43 45), (row3 41 43 46), (row3 41 43 47), (row3 41 43 48), (row3 41 43 49), (row3 41 43 50)]

def b148_04_labels : List Row := [(row3 462 286 286), (row3 462 307 307), (row3 137 133 132), (row3 289 305 305), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 238 238), (row3 462 261 261), (row3 462 288 288), (row3 86 369 122), (row3 295 304 273)]

theorem b148_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_04_rows b148_04_labels 33903245132569844586557817660 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_04_rows b148_04_labels]
    decide +kernel

def b148_05_rows : List Row := [(row3 41 43 51), (row3 41 43 52), (row3 41 43 53), (row3 41 43 54), (row3 41 43 55), (row3 41 43 56), (row3 41 43 57), (row3 41 43 58), (row3 41 43 59), (row3 41 43 60), (row3 41 43 61), (row3 41 43 62), (row3 41 43 63), (row3 41 44 45), (row3 41 44 46), (row3 41 44 47)]

def b148_05_labels : List Row := [(row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 235 235), (row3 462 288 288), (row3 224 222 222), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 238 236 238)]

theorem b148_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_05_rows b148_05_labels 57330395820486680026983720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_05_rows b148_05_labels]
    decide +kernel

def b148_06_rows : List Row := [(row3 41 44 48), (row3 41 44 49), (row3 41 44 50), (row3 41 44 51), (row3 41 44 52), (row3 41 44 53), (row3 41 44 54), (row3 41 44 55), (row3 41 44 56), (row3 41 44 57), (row3 41 44 58), (row3 41 44 59), (row3 41 44 60), (row3 41 44 61), (row3 41 44 62), (row3 41 44 63)]

def b148_06_labels : List Row := [(row3 462 236 236), (row3 10 171 254), (row3 228 225 236), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 247 247), (row3 462 243 243), (row3 462 238 238), (row3 462 250 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b148_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_06_rows b148_06_labels 519815915845015498423731000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_06_rows b148_06_labels]
    decide +kernel

def b148_07_rows : List Row := [(row3 41 45 46), (row3 41 45 47), (row3 41 45 48), (row3 41 45 49), (row3 41 45 50), (row3 41 45 51), (row3 41 45 52), (row3 41 45 53), (row3 41 45 54), (row3 41 45 55), (row3 41 45 56), (row3 41 45 57), (row3 41 45 58), (row3 41 45 59), (row3 41 45 60), (row3 41 45 61)]

def b148_07_labels : List Row := [(row3 462 462 462), (row3 261 261 462), (row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b148_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_07_rows b148_07_labels 9016574122499625035398800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_07_rows b148_07_labels]
    decide +kernel

def b148_08_rows : List Row := [(row3 41 45 62), (row3 41 45 63), (row3 41 46 47), (row3 41 46 48), (row3 41 46 49), (row3 41 46 50), (row3 41 46 51), (row3 41 46 52), (row3 41 46 53), (row3 41 46 54), (row3 41 46 55), (row3 41 46 56), (row3 41 46 57), (row3 41 46 58), (row3 41 46 59), (row3 41 46 60)]

def b148_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 193 192 238), (row3 137 145 148), (row3 10 171 254), (row3 462 236 236), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 306 310 310), (row3 462 294 294), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462)]

theorem b148_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_08_rows b148_08_labels 1246346229178579002994420920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_08_rows b148_08_labels]
    decide +kernel

def b148_09_rows : List Row := [(row3 41 46 61), (row3 41 46 62), (row3 41 46 63), (row3 41 47 48), (row3 41 47 49), (row3 41 47 50), (row3 41 47 51), (row3 41 47 52), (row3 41 47 53), (row3 41 47 54), (row3 41 47 55), (row3 41 47 56), (row3 41 47 57), (row3 41 47 58), (row3 41 47 59), (row3 41 47 60)]

def b148_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 380 380 379), (row3 85 369 121), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 369 85 121), (row3 104 104 130), (row3 462 288 288), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462)]

theorem b148_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_09_rows b148_09_labels 38004316949927129804349125760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_09_rows b148_09_labels]
    decide +kernel

def b148_10_rows : List Row := [(row3 41 47 61), (row3 41 47 62), (row3 41 47 63), (row3 41 48 49), (row3 41 48 50), (row3 41 48 51), (row3 41 48 52), (row3 41 48 53), (row3 41 48 54), (row3 41 48 55), (row3 41 48 56), (row3 41 48 57), (row3 41 48 58), (row3 41 48 59), (row3 41 48 60), (row3 41 48 61)]

def b148_10_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 288 462 288), (row3 443 34 27), (row3 348 351 350), (row3 190 197 196), (row3 462 261 261), (row3 190 199 198), (row3 345 345 347), (row3 62 49 52), (row3 453 26 47), (row3 403 402 404), (row3 136 142 141), (row3 462 273 273), (row3 462 462 462), (row3 462 273 273)]

theorem b148_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_10_rows b148_10_labels 17639719602448053099892363086960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_10_rows b148_10_labels]
    decide +kernel

def b148_11_rows : List Row := [(row3 41 48 62), (row3 41 48 63), (row3 41 49 50), (row3 41 49 51), (row3 41 49 52), (row3 41 49 53), (row3 41 49 54), (row3 41 49 55), (row3 41 49 56), (row3 41 49 57), (row3 41 49 58), (row3 41 49 59), (row3 41 49 60), (row3 41 49 61), (row3 41 49 62), (row3 41 49 63)]

def b148_11_labels : List Row := [(row3 137 147 144), (row3 381 378 382), (row3 35 31 36), (row3 387 390 360), (row3 154 154 180), (row3 462 269 269), (row3 154 154 180), (row3 388 392 362), (row3 422 423 417), (row3 453 26 47), (row3 408 416 396), (row3 105 105 131), (row3 462 284 284), (row3 462 462 462), (row3 462 286 286), (row3 102 103 129)]

theorem b148_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_11_rows b148_11_labels 17398707647112296089637099794290 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_11_rows b148_11_labels]
    decide +kernel

def b148_12_rows : List Row := [(row3 41 50 51), (row3 41 50 52), (row3 41 50 53), (row3 41 50 54), (row3 41 50 55), (row3 41 50 56), (row3 41 50 57), (row3 41 50 58), (row3 41 50 59), (row3 41 50 60), (row3 41 50 61), (row3 41 50 62), (row3 41 50 63), (row3 41 51 52), (row3 41 51 53), (row3 41 51 54)]

def b148_12_labels : List Row := [(row3 139 232 138), (row3 278 462 278), (row3 235 462 235), (row3 462 462 462), (row3 229 226 224), (row3 102 103 129), (row3 381 378 382), (row3 398 81 134), (row3 295 462 295), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b148_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_12_rows b148_12_labels 56436672390304461816731814720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_12_rows b148_12_labels]
    decide +kernel

def b148_13_rows : List Row := [(row3 41 51 55), (row3 41 51 56), (row3 41 51 57), (row3 41 51 58), (row3 41 51 59), (row3 41 51 60), (row3 41 51 61), (row3 41 51 62), (row3 41 51 63), (row3 41 52 53), (row3 41 52 54), (row3 41 52 55), (row3 41 52 56), (row3 41 52 57), (row3 41 52 58), (row3 41 52 59)]

def b148_13_labels : List Row := [(row3 462 248 248), (row3 462 286 286), (row3 137 147 144), (row3 306 312 312), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 273 273), (row3 224 224 224), (row3 462 462 462)]

theorem b148_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_13_rows b148_13_labels 450566412702738031995418620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_13_rows b148_13_labels]
    decide +kernel

def b148_14_rows : List Row := [(row3 41 52 60), (row3 41 52 61), (row3 41 52 62), (row3 41 52 63), (row3 41 53 54), (row3 41 53 55), (row3 41 53 56), (row3 41 53 57), (row3 41 53 58), (row3 41 53 59), (row3 41 53 60), (row3 41 53 61), (row3 41 53 62), (row3 41 53 63), (row3 41 54 55), (row3 41 54 56)]

def b148_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291), (row3 462 284 284), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 131 105 105), (row3 105 105 131)]

theorem b148_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_14_rows b148_14_labels 4885409760902823351033025200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_14_rows b148_14_labels]
    decide +kernel

def b148_15_rows : List Row := [(row3 41 54 57), (row3 41 54 58), (row3 41 54 59), (row3 41 54 60), (row3 41 54 61), (row3 41 54 62), (row3 41 54 63), (row3 41 55 56), (row3 41 55 57), (row3 41 55 58), (row3 41 55 59), (row3 41 55 60), (row3 41 55 61), (row3 41 55 62), (row3 41 55 63), (row3 41 56 57)]

def b148_15_labels : List Row := [(row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 295 462 295), (row3 408 416 396), (row3 136 142 141), (row3 462 253 253), (row3 462 462 462), (row3 462 246 246), (row3 224 224 224), (row3 306 312 312), (row3 398 81 134), (row3 443 34 27)]

theorem b148_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b148_15_rows b148_15_labels 5007396131957538033015733896150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b148_15_rows b148_15_labels]
    decide +kernel

theorem checked148 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_148 QuarticIntegerComputationalData.ids64_148 57315377602100637604509151405350 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b148_00_rows ++ b148_01_rows) ++ (b148_02_rows ++ b148_03_rows)) ++ ((b148_04_rows ++ b148_05_rows) ++ (b148_06_rows ++ b148_07_rows))) ++ (((b148_08_rows ++ b148_09_rows) ++ (b148_10_rows ++ b148_11_rows)) ++ ((b148_12_rows ++ b148_13_rows) ++ (b148_14_rows ++ b148_15_rows))))
    ((((b148_00_labels ++ b148_01_labels) ++ (b148_02_labels ++ b148_03_labels)) ++ ((b148_04_labels ++ b148_05_labels) ++ (b148_06_labels ++ b148_07_labels))) ++ (((b148_08_labels ++ b148_09_labels) ++ (b148_10_labels ++ b148_11_labels)) ++ ((b148_12_labels ++ b148_13_labels) ++ (b148_14_labels ++ b148_15_labels)))) 57315377602100637604509151405350
  exact ((((b148_00_checked.append (c := 16709688278049596658610277144460) b148_01_checked (by decide +kernel)).append (c := 17134041500821376803566806891550) (b148_02_checked.append (c := 424353222771780144956529747090) b148_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17168530908839734649956850822730) ((b148_04_checked.append (c := 33960575528390331266584801380) b148_05_checked (by decide +kernel)).append (c := 34489408018357846390043931180) (b148_06_checked.append (c := 528832489967515123459129800) b148_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 57315377602100637604509151405350) (((b148_08_checked.append (c := 39250663179105708807343546680) b148_09_checked (by decide +kernel)).append (c := 35077677912739454898336806427930) (b148_10_checked.append (c := 35038427249560349189529462881250) b148_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 40146846693260902954552300582620) ((b148_12_checked.append (c := 56887238803007199848727233340) b148_13_checked (by decide +kernel)).append (c := 5069168780521448056215494154690) (b148_14_checked.append (c := 5012281541718440856366766921350) b148_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b149_00_rows : List Row := [(row3 41 56 58), (row3 41 56 59), (row3 41 56 60), (row3 41 56 61), (row3 41 56 62), (row3 41 56 63), (row3 41 57 58), (row3 41 57 59), (row3 41 57 60), (row3 41 57 61), (row3 41 57 62), (row3 41 57 63), (row3 41 58 59), (row3 41 58 60), (row3 41 58 61), (row3 41 58 62)]

def b149_00_labels : List Row := [(row3 388 362 392), (row3 154 180 154), (row3 462 269 269), (row3 154 180 154), (row3 387 360 390), (row3 35 36 31), (row3 62 52 49), (row3 345 347 345), (row3 190 198 199), (row3 462 261 261), (row3 190 196 197), (row3 348 350 351), (row3 131 105 105), (row3 289 291 291), (row3 234 234 234), (row3 462 248 248)]

theorem b149_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_00_rows b149_00_labels 1052496203255634512236969579500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_00_rows b149_00_labels]
    decide +kernel

def b149_01_rows : List Row := [(row3 41 58 63), (row3 41 59 60), (row3 41 59 61), (row3 41 59 62), (row3 41 59 63), (row3 41 60 61), (row3 41 60 62), (row3 41 60 63), (row3 41 61 62), (row3 41 61 63), (row3 41 62 63), (row3 42 43 44), (row3 42 43 45), (row3 42 43 46), (row3 42 43 47), (row3 42 43 48)]

def b149_01_labels : List Row := [(row3 229 226 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 278 462 278), (row3 139 232 138), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235)]

theorem b149_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_01_rows b149_01_labels 1120183766074639804543034400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_01_rows b149_01_labels]
    decide +kernel

def b149_02_rows : List Row := [(row3 42 43 49), (row3 42 43 50), (row3 42 43 51), (row3 42 43 52), (row3 42 43 53), (row3 42 43 54), (row3 42 43 55), (row3 42 43 56), (row3 42 43 57), (row3 42 43 58), (row3 42 43 59), (row3 42 43 60), (row3 42 43 61), (row3 42 43 62), (row3 42 43 63), (row3 42 44 45)]

def b149_02_labels : List Row := [(row3 309 306 309), (row3 139 139 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 291 289 291), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_02_rows b149_02_labels 2166575517617568634320732000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_02_rows b149_02_labels]
    decide +kernel

def b149_03_rows : List Row := [(row3 42 44 46), (row3 42 44 47), (row3 42 44 48), (row3 42 44 49), (row3 42 44 50), (row3 42 44 51), (row3 42 44 52), (row3 42 44 53), (row3 42 44 54), (row3 42 44 55), (row3 42 44 56), (row3 42 44 57), (row3 42 44 58), (row3 42 44 59), (row3 42 44 60), (row3 42 44 61)]

def b149_03_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 232 232), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_03_rows b149_03_labels 93425279829783464411965500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_03_rows b149_03_labels]
    decide +kernel

def b149_04_rows : List Row := [(row3 42 44 62), (row3 42 44 63), (row3 42 45 46), (row3 42 45 47), (row3 42 45 48), (row3 42 45 49), (row3 42 45 50), (row3 42 45 51), (row3 42 45 52), (row3 42 45 53), (row3 42 45 54), (row3 42 45 55), (row3 42 45 56), (row3 42 45 57), (row3 42 45 58), (row3 42 45 59)]

def b149_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_04_rows b149_04_labels 413694291334688503731000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_04_rows b149_04_labels]
    decide +kernel

def b149_05_rows : List Row := [(row3 42 45 60), (row3 42 45 61), (row3 42 45 62), (row3 42 45 63), (row3 42 46 47), (row3 42 46 48), (row3 42 46 49), (row3 42 46 50), (row3 42 46 51), (row3 42 46 52), (row3 42 46 53), (row3 42 46 54), (row3 42 46 55), (row3 42 46 56), (row3 42 46 57), (row3 42 46 58)]

def b149_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 291 291 289), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_05_rows b149_05_labels 31577535517080586493992200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_05_rows b149_05_labels]
    decide +kernel

def b149_06_rows : List Row := [(row3 42 46 59), (row3 42 46 60), (row3 42 46 61), (row3 42 46 62), (row3 42 46 63), (row3 42 47 48), (row3 42 47 49), (row3 42 47 50), (row3 42 47 51), (row3 42 47 52), (row3 42 47 53), (row3 42 47 54), (row3 42 47 55), (row3 42 47 56), (row3 42 47 57), (row3 42 47 58)]

def b149_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 145 137 148), (row3 310 306 310), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 171 10 254), (row3 294 462 294), (row3 462 228 228), (row3 462 462 462)]

theorem b149_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_06_rows b149_06_labels 900357530026206243155695920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_06_rows b149_06_labels]
    decide +kernel

def b149_07_rows : List Row := [(row3 42 47 59), (row3 42 47 60), (row3 42 47 61), (row3 42 47 62), (row3 42 47 63), (row3 42 48 49), (row3 42 48 50), (row3 42 48 51), (row3 42 48 52), (row3 42 48 53), (row3 42 48 54), (row3 42 48 55), (row3 42 48 56), (row3 42 48 57), (row3 42 48 58), (row3 42 48 59)]

def b149_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 238 462 238), (row3 59 410 431), (row3 140 140 178), (row3 266 265 266), (row3 462 237 237), (row3 266 265 266), (row3 184 184 178), (row3 360 387 390), (row3 42 435 181), (row3 101 98 99), (row3 313 306 313), (row3 462 235 235)]

theorem b149_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_07_rows b149_07_labels 515661397953316672907476817100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_07_rows b149_07_labels]
    decide +kernel

def b149_08_rows : List Row := [(row3 42 48 60), (row3 42 48 61), (row3 42 48 62), (row3 42 48 63), (row3 42 49 50), (row3 42 49 51), (row3 42 49 52), (row3 42 49 53), (row3 42 49 54), (row3 42 49 55), (row3 42 49 56), (row3 42 49 57), (row3 42 49 58), (row3 42 49 59), (row3 42 49 60), (row3 42 49 61)]

def b149_08_labels : List Row := [(row3 462 462 462), (row3 462 235 235), (row3 291 289 291), (row3 146 149 137), (row3 45 389 436), (row3 149 137 146), (row3 279 279 278), (row3 462 235 235), (row3 279 279 278), (row3 147 137 144), (row3 100 113 100), (row3 39 437 412), (row3 101 98 99), (row3 312 312 306), (row3 462 232 232), (row3 462 462 462)]

theorem b149_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_08_rows b149_08_labels 743591772631151479002671343360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_08_rows b149_08_labels]
    decide +kernel

def b149_09_rows : List Row := [(row3 42 49 62), (row3 42 49 63), (row3 42 50 51), (row3 42 50 52), (row3 42 50 53), (row3 42 50 54), (row3 42 50 55), (row3 42 50 56), (row3 42 50 57), (row3 42 50 58), (row3 42 50 59), (row3 42 50 60), (row3 42 50 61), (row3 42 50 62), (row3 42 50 63), (row3 42 51 52)]

def b149_09_labels : List Row := [(row3 462 232 232), (row3 309 309 306), (row3 377 462 377), (row3 180 462 180), (row3 269 462 269), (row3 462 462 462), (row3 271 462 271), (row3 316 462 316), (row3 100 113 100), (row3 42 435 181), (row3 138 232 139), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_09_rows b149_09_labels 407642114278196492614998668730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_09_rows b149_09_labels]
    decide +kernel

def b149_10_rows : List Row := [(row3 42 51 53), (row3 42 51 54), (row3 42 51 55), (row3 42 51 56), (row3 42 51 57), (row3 42 51 58), (row3 42 51 59), (row3 42 51 60), (row3 42 51 61), (row3 42 51 62), (row3 42 51 63), (row3 42 52 53), (row3 42 52 54), (row3 42 52 55), (row3 42 52 56), (row3 42 52 57)]

def b149_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 309 309 306), (row3 146 149 137), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 232 232)]

theorem b149_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_10_rows b149_10_labels 671495576002348432972860000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_10_rows b149_10_labels]
    decide +kernel

def b149_11_rows : List Row := [(row3 42 52 58), (row3 42 52 59), (row3 42 52 60), (row3 42 52 61), (row3 42 52 62), (row3 42 52 63), (row3 42 53 54), (row3 42 53 55), (row3 42 53 56), (row3 42 53 57), (row3 42 53 58), (row3 42 53 59), (row3 42 53 60), (row3 42 53 61), (row3 42 53 62), (row3 42 53 63)]

def b149_11_labels : List Row := [(row3 291 289 291), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_11_rows b149_11_labels 13077544734377094301360200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_11_rows b149_11_labels]
    decide +kernel

def b149_12_rows : List Row := [(row3 42 54 55), (row3 42 54 56), (row3 42 54 57), (row3 42 54 58), (row3 42 54 59), (row3 42 54 60), (row3 42 54 61), (row3 42 54 62), (row3 42 54 63), (row3 42 55 56), (row3 42 55 57), (row3 42 55 58), (row3 42 55 59), (row3 42 55 60), (row3 42 55 61), (row3 42 55 62)]

def b149_12_labels : List Row := [(row3 284 462 284), (row3 293 462 293), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 138 232 139), (row3 312 312 306), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 232 232 462)]

theorem b149_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_12_rows b149_12_labels 1277655800743959317119329300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_12_rows b149_12_labels]
    decide +kernel

def b149_13_rows : List Row := [(row3 42 55 63), (row3 42 56 57), (row3 42 56 58), (row3 42 56 59), (row3 42 56 60), (row3 42 56 61), (row3 42 56 62), (row3 42 56 63), (row3 42 57 58), (row3 42 57 59), (row3 42 57 60), (row3 42 57 61), (row3 42 57 62), (row3 42 57 63), (row3 42 58 59), (row3 42 58 60)]

def b149_13_labels : List Row := [(row3 284 284 462), (row3 45 389 436), (row3 140 140 178), (row3 271 271 462), (row3 462 462 462), (row3 269 269 462), (row3 180 180 462), (row3 377 377 462), (row3 59 410 431), (row3 147 144 137), (row3 279 278 279), (row3 462 235 235), (row3 279 278 279), (row3 149 146 137), (row3 360 390 387), (row3 184 178 184)]

theorem b149_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_13_rows b149_13_labels 564929880775205240517148952730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_13_rows b149_13_labels]
    decide +kernel

def b149_14_rows : List Row := [(row3 42 58 61), (row3 42 58 62), (row3 42 58 63), (row3 42 59 60), (row3 42 59 61), (row3 42 59 62), (row3 42 59 63), (row3 42 60 61), (row3 42 60 62), (row3 42 60 63), (row3 42 61 62), (row3 42 61 63), (row3 42 62 63), (row3 43 44 45), (row3 43 44 46), (row3 43 44 47)]

def b149_14_labels : List Row := [(row3 266 266 265), (row3 462 237 237), (row3 266 266 265), (row3 284 462 284), (row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_14_rows b149_14_labels 81110882302639788525419520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_14_rows b149_14_labels]
    decide +kernel

def b149_15_rows : List Row := [(row3 43 44 48), (row3 43 44 49), (row3 43 44 50), (row3 43 44 51), (row3 43 44 52), (row3 43 44 53), (row3 43 44 54), (row3 43 44 55), (row3 43 44 56), (row3 43 44 57), (row3 43 44 58), (row3 43 44 59), (row3 43 44 60), (row3 43 44 61), (row3 43 44 62), (row3 43 44 63)]

def b149_15_labels : List Row := [(row3 462 462 462), (row3 462 246 246), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b149_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b149_15_rows b149_15_labels 9345909477683409685249500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b149_15_rows b149_15_labels]
    decide +kernel

theorem checked149 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_149 QuarticIntegerComputationalData.ids64_149 3290686587930122018743298730960 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b149_00_rows ++ b149_01_rows) ++ (b149_02_rows ++ b149_03_rows)) ++ ((b149_04_rows ++ b149_05_rows) ++ (b149_06_rows ++ b149_07_rows))) ++ (((b149_08_rows ++ b149_09_rows) ++ (b149_10_rows ++ b149_11_rows)) ++ ((b149_12_rows ++ b149_13_rows) ++ (b149_14_rows ++ b149_15_rows))))
    ((((b149_00_labels ++ b149_01_labels) ++ (b149_02_labels ++ b149_03_labels)) ++ ((b149_04_labels ++ b149_05_labels) ++ (b149_06_labels ++ b149_07_labels))) ++ (((b149_08_labels ++ b149_09_labels) ++ (b149_10_labels ++ b149_11_labels)) ++ ((b149_12_labels ++ b149_13_labels) ++ (b149_14_labels ++ b149_15_labels)))) 3290686587930122018743298730960
  exact ((((b149_00_checked.append (c := 1053616387021709152041512613900) b149_01_checked (by decide +kernel)).append (c := 1055876387819156504140245311400) (b149_02_checked.append (c := 2260000797447352098732697500) b149_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1572470134532307798565875547620) ((b149_04_checked.append (c := 31991229808415274997723200) b149_05_checked (by decide +kernel)).append (c := 516593746713151294425630236220) (b149_06_checked.append (c := 516561755483342879150632513020) b149_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 3290686587930122018743298730960) (((b149_08_checked.append (c := 1151233886909347971617670012090) b149_09_checked (by decide +kernel)).append (c := 1151918460030084697144944232290) (b149_10_checked.append (c := 684573120736725527274220200) b149_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1718216453397814220177423183340) ((b149_12_checked.append (c := 566207536575949199834268282030) b149_13_checked (by decide +kernel)).append (c := 566297993367729523032478951050) (b149_14_checked.append (c := 90456791780323198210669020) b149_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b150_00_rows : List Row := [(row3 43 45 46), (row3 43 45 47), (row3 43 45 48), (row3 43 45 49), (row3 43 45 50), (row3 43 45 51), (row3 43 45 52), (row3 43 45 53), (row3 43 45 54), (row3 43 45 55), (row3 43 45 56), (row3 43 45 57), (row3 43 45 58), (row3 43 45 59), (row3 43 45 60), (row3 43 45 61)]

def b150_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_00_rows b150_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_00_rows b150_00_labels]
    decide +kernel

def b150_01_rows : List Row := [(row3 43 45 62), (row3 43 45 63), (row3 43 46 47), (row3 43 46 48), (row3 43 46 49), (row3 43 46 50), (row3 43 46 51), (row3 43 46 52), (row3 43 46 53), (row3 43 46 54), (row3 43 46 55), (row3 43 46 56), (row3 43 46 57), (row3 43 46 58), (row3 43 46 59), (row3 43 46 60)]

def b150_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_01_rows b150_01_labels 330557493792363561819000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_01_rows b150_01_labels]
    decide +kernel

def b150_02_rows : List Row := [(row3 43 46 61), (row3 43 46 62), (row3 43 46 63), (row3 43 47 48), (row3 43 47 49), (row3 43 47 50), (row3 43 47 51), (row3 43 47 52), (row3 43 47 53), (row3 43 47 54), (row3 43 47 55), (row3 43 47 56), (row3 43 47 57), (row3 43 47 58), (row3 43 47 59), (row3 43 47 60)]

def b150_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_02_rows b150_02_labels 6896564724897369017571600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_02_rows b150_02_labels]
    decide +kernel

def b150_03_rows : List Row := [(row3 43 47 61), (row3 43 47 62), (row3 43 47 63), (row3 43 48 49), (row3 43 48 50), (row3 43 48 51), (row3 43 48 52), (row3 43 48 53), (row3 43 48 54), (row3 43 48 55), (row3 43 48 56), (row3 43 48 57), (row3 43 48 58), (row3 43 48 59), (row3 43 48 60), (row3 43 48 61)]

def b150_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 369 122 86), (row3 288 288 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 261 261 462), (row3 193 193 462), (row3 193 193 462), (row3 304 273 295), (row3 222 222 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_03_rows b150_03_labels 10836121217227948519844281920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_03_rows b150_03_labels]
    decide +kernel

def b150_04_rows : List Row := [(row3 43 48 62), (row3 43 48 63), (row3 43 49 50), (row3 43 49 51), (row3 43 49 52), (row3 43 49 53), (row3 43 49 54), (row3 43 49 55), (row3 43 49 56), (row3 43 49 57), (row3 43 49 58), (row3 43 49 59), (row3 43 49 60), (row3 43 49 61), (row3 43 49 62), (row3 43 49 63)]

def b150_04_labels : List Row := [(row3 235 235 462), (row3 273 273 462), (row3 398 135 83), (row3 289 291 291), (row3 234 234 234), (row3 462 244 244), (row3 234 234 234), (row3 289 291 291), (row3 306 309 309), (row3 398 83 135), (row3 321 322 322), (row3 222 222 224), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 224 224 224)]

theorem b150_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_04_rows b150_04_labels 40878725106482957151585593100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_04_rows b150_04_labels]
    decide +kernel

def b150_05_rows : List Row := [(row3 43 50 51), (row3 43 50 52), (row3 43 50 53), (row3 43 50 54), (row3 43 50 55), (row3 43 50 56), (row3 43 50 57), (row3 43 50 58), (row3 43 50 59), (row3 43 50 60), (row3 43 50 61), (row3 43 50 62), (row3 43 50 63), (row3 43 51 52), (row3 43 51 53), (row3 43 51 54)]

def b150_05_labels : List Row := [(row3 139 462 139), (row3 278 462 278), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 228 462 228), (row3 319 462 319), (row3 398 83 135), (row3 304 273 295), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_05_rows b150_05_labels 22017889257068053528335357120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_05_rows b150_05_labels]
    decide +kernel

def b150_06_rows : List Row := [(row3 43 51 55), (row3 43 51 56), (row3 43 51 57), (row3 43 51 58), (row3 43 51 59), (row3 43 51 60), (row3 43 51 61), (row3 43 51 62), (row3 43 51 63), (row3 43 52 53), (row3 43 52 54), (row3 43 52 55), (row3 43 52 56), (row3 43 52 57), (row3 43 52 58), (row3 43 52 59)]

def b150_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 306 309 309), (row3 193 193 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 273 273 462)]

theorem b150_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_06_rows b150_06_labels 943584620572381430398125600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_06_rows b150_06_labels]
    decide +kernel

def b150_07_rows : List Row := [(row3 43 52 60), (row3 43 52 61), (row3 43 52 62), (row3 43 52 63), (row3 43 53 54), (row3 43 53 55), (row3 43 53 56), (row3 43 53 57), (row3 43 53 58), (row3 43 53 59), (row3 43 53 60), (row3 43 53 61), (row3 43 53 62), (row3 43 53 63), (row3 43 54 55), (row3 43 54 56)]

def b150_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_07_rows b150_07_labels 308270843009123509071000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_07_rows b150_07_labels]
    decide +kernel

def b150_08_rows : List Row := [(row3 43 54 57), (row3 43 54 58), (row3 43 54 59), (row3 43 54 60), (row3 43 54 61), (row3 43 54 62), (row3 43 54 63), (row3 43 55 56), (row3 43 55 57), (row3 43 55 58), (row3 43 55 59), (row3 43 55 60), (row3 43 55 61), (row3 43 55 62), (row3 43 55 63), (row3 43 56 57)]

def b150_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 139 462 139)]

theorem b150_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_08_rows b150_08_labels 1566987875088883787810295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_08_rows b150_08_labels]
    decide +kernel

def b150_09_rows : List Row := [(row3 43 56 58), (row3 43 56 59), (row3 43 56 60), (row3 43 56 61), (row3 43 56 62), (row3 43 56 63), (row3 43 57 58), (row3 43 57 59), (row3 43 57 60), (row3 43 57 61), (row3 43 57 62), (row3 43 57 63), (row3 43 58 59), (row3 43 58 60), (row3 43 58 61), (row3 43 58 62)]

def b150_09_labels : List Row := [(row3 289 291 291), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 398 135 83), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 278 278 462), (row3 369 122 86), (row3 289 291 291), (row3 234 234 234), (row3 462 244 244)]

theorem b150_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_09_rows b150_09_labels 30269630505494680292981141820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_09_rows b150_09_labels]
    decide +kernel

def b150_10_rows : List Row := [(row3 43 58 63), (row3 43 59 60), (row3 43 59 61), (row3 43 59 62), (row3 43 59 63), (row3 43 60 61), (row3 43 60 62), (row3 43 60 63), (row3 43 61 62), (row3 43 61 63), (row3 43 62 63), (row3 44 45 46), (row3 44 45 47), (row3 44 45 48), (row3 44 45 49), (row3 44 45 50)]

def b150_10_labels : List Row := [(row3 234 234 234), (row3 193 462 193), (row3 261 462 261), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_10_rows b150_10_labels 351609129298793592914083200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_10_rows b150_10_labels]
    decide +kernel

def b150_11_rows : List Row := [(row3 44 45 51), (row3 44 45 52), (row3 44 45 53), (row3 44 45 54), (row3 44 45 55), (row3 44 45 56), (row3 44 45 57), (row3 44 45 58), (row3 44 45 59), (row3 44 45 60), (row3 44 45 61), (row3 44 45 62), (row3 44 45 63), (row3 44 46 47), (row3 44 46 48), (row3 44 46 49)]

def b150_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 248 462 248), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462)]

theorem b150_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_11_rows b150_11_labels 29534035156291444489264500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_11_rows b150_11_labels]
    decide +kernel

def b150_12_rows : List Row := [(row3 44 46 50), (row3 44 46 51), (row3 44 46 52), (row3 44 46 53), (row3 44 46 54), (row3 44 46 55), (row3 44 46 56), (row3 44 46 57), (row3 44 46 58), (row3 44 46 59), (row3 44 46 60), (row3 44 46 61), (row3 44 46 62), (row3 44 46 63), (row3 44 47 48), (row3 44 47 49)]

def b150_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 234 462 234), (row3 462 462 462), (row3 236 462 236), (row3 247 462 247)]

theorem b150_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_12_rows b150_12_labels 93833248640136062465434500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_12_rows b150_12_labels]
    decide +kernel

def b150_13_rows : List Row := [(row3 44 47 50), (row3 44 47 51), (row3 44 47 52), (row3 44 47 53), (row3 44 47 54), (row3 44 47 55), (row3 44 47 56), (row3 44 47 57), (row3 44 47 58), (row3 44 47 59), (row3 44 47 60), (row3 44 47 61), (row3 44 47 62), (row3 44 47 63), (row3 44 48 49), (row3 44 48 50)]

def b150_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 225 228 236), (row3 171 10 254), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 462 250), (row3 238 462 238), (row3 284 462 284), (row3 234 234 462)]

theorem b150_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_13_rows b150_13_labels 581055134513674712132106000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_13_rows b150_13_labels]
    decide +kernel

def b150_14_rows : List Row := [(row3 44 48 51), (row3 44 48 52), (row3 44 48 53), (row3 44 48 54), (row3 44 48 55), (row3 44 48 56), (row3 44 48 57), (row3 44 48 58), (row3 44 48 59), (row3 44 48 60), (row3 44 48 61), (row3 44 48 62), (row3 44 48 63), (row3 44 49 50), (row3 44 49 51), (row3 44 49 52)]

def b150_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 117 214 11), (row3 235 235 462), (row3 243 243 462)]

theorem b150_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_14_rows b150_14_labels 1705153628800792789198548750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_14_rows b150_14_labels]
    decide +kernel

def b150_15_rows : List Row := [(row3 44 49 53), (row3 44 49 54), (row3 44 49 55), (row3 44 49 56), (row3 44 49 57), (row3 44 49 58), (row3 44 49 59), (row3 44 49 60), (row3 44 49 61), (row3 44 49 62), (row3 44 49 63), (row3 44 50 51), (row3 44 50 52), (row3 44 50 53), (row3 44 50 54), (row3 44 50 55)]

def b150_15_labels : List Row := [(row3 462 462 462), (row3 245 245 462), (row3 232 235 235), (row3 232 232 462), (row3 284 284 462), (row3 223 232 228), (row3 251 251 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 293 462 293), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 245 462 245)]

theorem b150_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b150_15_rows b150_15_labels 164819126324182694269230000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b150_15_rows b150_15_labels]
    decide +kernel

theorem checked150 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_150 QuarticIntegerComputationalData.ids64_150 109446478277730474862511923110 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b150_00_rows ++ b150_01_rows) ++ (b150_02_rows ++ b150_03_rows)) ++ ((b150_04_rows ++ b150_05_rows) ++ (b150_06_rows ++ b150_07_rows))) ++ (((b150_08_rows ++ b150_09_rows) ++ (b150_10_rows ++ b150_11_rows)) ++ ((b150_12_rows ++ b150_13_rows) ++ (b150_14_rows ++ b150_15_rows))))
    ((((b150_00_labels ++ b150_01_labels) ++ (b150_02_labels ++ b150_03_labels)) ++ ((b150_04_labels ++ b150_05_labels) ++ (b150_06_labels ++ b150_07_labels))) ++ (((b150_08_labels ++ b150_09_labels) ++ (b150_10_labels ++ b150_11_labels)) ++ ((b150_12_labels ++ b150_13_labels) ++ (b150_14_labels ++ b150_15_labels)))) 109446478277730474862511923110
  exact ((((b150_00_checked.append (c := 330557493792363561819000) b150_01_checked (by decide +kernel)).append (c := 10843348339446638252423672520) (b150_02_checked.append (c := 10843017781952845888861853520) b150_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 74683855594413039486251819340) ((b150_04_checked.append (c := 62896614363551010679920950220) b150_05_checked (by decide +kernel)).append (c := 63840507254966401233828146820) (b150_06_checked.append (c := 943892891415390553907196600) b150_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 109446478277730474862511923110) (((b150_08_checked.append (c := 31836618380583564080791436820) b150_09_checked (by decide +kernel)).append (c := 32217761545038649118194784520) (b150_10_checked.append (c := 381143164455085037403347700) b150_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 34762622683317435376260103770) ((b150_12_checked.append (c := 674888383153810774597540500) b150_13_checked (by decide +kernel)).append (c := 2544861138278786258065319250) (b150_14_checked.append (c := 1869972755124975483467778750) b150_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b151_00_rows : List Row := [(row3 44 50 56), (row3 44 50 57), (row3 44 50 58), (row3 44 50 59), (row3 44 50 60), (row3 44 50 61), (row3 44 50 62), (row3 44 50 63), (row3 44 51 52), (row3 44 51 53), (row3 44 51 54), (row3 44 51 55), (row3 44 51 56), (row3 44 51 57), (row3 44 51 58), (row3 44 51 59)]

def b151_00_labels : List Row := [(row3 248 462 248), (row3 228 462 228), (row3 118 11 215), (row3 223 232 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 284 284 462)]

theorem b151_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_00_rows b151_00_labels 1683258561136883416560360750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_00_rows b151_00_labels]
    decide +kernel

def b151_01_rows : List Row := [(row3 44 51 60), (row3 44 51 61), (row3 44 51 62), (row3 44 51 63), (row3 44 52 53), (row3 44 52 54), (row3 44 52 55), (row3 44 52 56), (row3 44 52 57), (row3 44 52 58), (row3 44 52 59), (row3 44 52 60), (row3 44 52 61), (row3 44 52 62), (row3 44 52 63), (row3 44 53 54)]

def b151_01_labels : List Row := [(row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 248 462 248), (row3 462 462 462), (row3 293 293 462)]

theorem b151_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_01_rows b151_01_labels 106280598459326979394804500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_01_rows b151_01_labels]
    decide +kernel

def b151_02_rows : List Row := [(row3 44 53 55), (row3 44 53 56), (row3 44 53 57), (row3 44 53 58), (row3 44 53 59), (row3 44 53 60), (row3 44 53 61), (row3 44 53 62), (row3 44 53 63), (row3 44 54 55), (row3 44 54 56), (row3 44 54 57), (row3 44 54 58), (row3 44 54 59), (row3 44 54 60), (row3 44 54 61)]

def b151_02_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 284 284 462), (row3 228 462 228), (row3 462 462 462), (row3 117 11 214), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 223 232 228)]

theorem b151_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_02_rows b151_02_labels 1711554137087922303632520750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_02_rows b151_02_labels]
    decide +kernel

def b151_03_rows : List Row := [(row3 44 54 62), (row3 44 54 63), (row3 44 55 56), (row3 44 55 57), (row3 44 55 58), (row3 44 55 59), (row3 44 55 60), (row3 44 55 61), (row3 44 55 62), (row3 44 55 63), (row3 44 56 57), (row3 44 56 58), (row3 44 56 59), (row3 44 56 60), (row3 44 56 61), (row3 44 56 62)]

def b151_03_labels : List Row := [(row3 118 11 215), (row3 228 462 228), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 251 462), (row3 223 232 228), (row3 284 284 462), (row3 462 462 462), (row3 234 462 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 462 234)]

theorem b151_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_03_rows b151_03_labels 1688641542869988444331079250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_03_rows b151_03_labels]
    decide +kernel

def b151_04_rows : List Row := [(row3 44 56 63), (row3 44 57 58), (row3 44 57 59), (row3 44 57 60), (row3 44 57 61), (row3 44 57 62), (row3 44 57 63), (row3 44 58 59), (row3 44 58 60), (row3 44 58 61), (row3 44 58 62), (row3 44 58 63), (row3 44 59 60), (row3 44 59 61), (row3 44 59 62), (row3 44 59 63)]

def b151_04_labels : List Row := [(row3 462 462 462), (row3 293 462 293), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 117 214 11), (row3 234 234 462), (row3 245 245 462), (row3 462 462 462), (row3 244 244 462), (row3 284 462 284), (row3 232 235 235), (row3 245 462 245), (row3 462 462 462)]

theorem b151_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_04_rows b151_04_labels 1798884651184989580949258250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_04_rows b151_04_labels]
    decide +kernel

def b151_05_rows : List Row := [(row3 44 60 61), (row3 44 60 62), (row3 44 60 63), (row3 44 61 62), (row3 44 61 63), (row3 44 62 63), (row3 45 46 47), (row3 45 46 48), (row3 45 46 49), (row3 45 46 50), (row3 45 46 51), (row3 45 46 52), (row3 45 46 53), (row3 45 46 54), (row3 45 46 55), (row3 45 46 56)]

def b151_05_labels : List Row := [(row3 284 284 462), (row3 234 462 234), (row3 462 462 462), (row3 117 11 214), (row3 235 462 235), (row3 293 293 462), (row3 193 193 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 139 139 462), (row3 306 309 309), (row3 462 462 462)]

theorem b151_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_05_rows b151_05_labels 4236606580774648351348597050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_05_rows b151_05_labels]
    decide +kernel

def b151_06_rows : List Row := [(row3 45 46 57), (row3 45 46 58), (row3 45 46 59), (row3 45 46 60), (row3 45 46 61), (row3 45 46 62), (row3 45 46 63), (row3 45 47 48), (row3 45 47 49), (row3 45 47 50), (row3 45 47 51), (row3 45 47 52), (row3 45 47 53), (row3 45 47 54), (row3 45 47 55), (row3 45 47 56)]

def b151_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 228 462 228), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 304 295 273), (row3 369 86 122), (row3 235 462 235)]

theorem b151_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_06_rows b151_06_labels 10224786470026390882281243360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_06_rows b151_06_labels]
    decide +kernel

def b151_07_rows : List Row := [(row3 45 47 57), (row3 45 47 58), (row3 45 47 59), (row3 45 47 60), (row3 45 47 61), (row3 45 47 62), (row3 45 47 63), (row3 45 48 49), (row3 45 48 50), (row3 45 48 51), (row3 45 48 52), (row3 45 48 53), (row3 45 48 54), (row3 45 48 55), (row3 45 48 56), (row3 45 48 57)]

def b151_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 222 224 222), (row3 288 462 288), (row3 193 193 462), (row3 261 261 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 288 288 462), (row3 369 122 86), (row3 193 193 462), (row3 273 273 462)]

theorem b151_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_07_rows b151_07_labels 10850055182091482204123461440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_07_rows b151_07_labels]
    decide +kernel

def b151_08_rows : List Row := [(row3 45 48 58), (row3 45 48 59), (row3 45 48 60), (row3 45 48 61), (row3 45 48 62), (row3 45 48 63), (row3 45 49 50), (row3 45 49 51), (row3 45 49 52), (row3 45 49 53), (row3 45 49 54), (row3 45 49 55), (row3 45 49 56), (row3 45 49 57), (row3 45 49 58), (row3 45 49 59)]

def b151_08_labels : List Row := [(row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 222 222 224), (row3 304 273 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b151_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_08_rows b151_08_labels 47413553646810914285371200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_08_rows b151_08_labels]
    decide +kernel

def b151_09_rows : List Row := [(row3 45 49 60), (row3 45 49 61), (row3 45 49 62), (row3 45 49 63), (row3 45 50 51), (row3 45 50 52), (row3 45 50 53), (row3 45 50 54), (row3 45 50 55), (row3 45 50 56), (row3 45 50 57), (row3 45 50 58), (row3 45 50 59), (row3 45 50 60), (row3 45 50 61), (row3 45 50 62)]

def b151_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b151_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_09_rows b151_09_labels 1607595923071589053131000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_09_rows b151_09_labels]
    decide +kernel

def b151_10_rows : List Row := [(row3 45 50 63), (row3 45 51 52), (row3 45 51 53), (row3 45 51 54), (row3 45 51 55), (row3 45 51 56), (row3 45 51 57), (row3 45 51 58), (row3 45 51 59), (row3 45 51 60), (row3 45 51 61), (row3 45 51 62), (row3 45 51 63), (row3 45 52 53), (row3 45 52 54), (row3 45 52 55)]

def b151_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 278 278 462), (row3 234 234 234)]

theorem b151_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_10_rows b151_10_labels 13061064833708591119853700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_10_rows b151_10_labels]
    decide +kernel

def b151_11_rows : List Row := [(row3 45 52 56), (row3 45 52 57), (row3 45 52 58), (row3 45 52 59), (row3 45 52 60), (row3 45 52 61), (row3 45 52 62), (row3 45 52 63), (row3 45 53 54), (row3 45 53 55), (row3 45 53 56), (row3 45 53 57), (row3 45 53 58), (row3 45 53 59), (row3 45 53 60), (row3 45 53 61)]

def b151_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 224 224 224), (row3 462 462 462), (row3 139 139 462), (row3 289 291 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462)]

theorem b151_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_11_rows b151_11_labels 2255535567053602203237876000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_11_rows b151_11_labels]
    decide +kernel

def b151_12_rows : List Row := [(row3 45 53 62), (row3 45 53 63), (row3 45 54 55), (row3 45 54 56), (row3 45 54 57), (row3 45 54 58), (row3 45 54 59), (row3 45 54 60), (row3 45 54 61), (row3 45 54 62), (row3 45 54 63), (row3 45 55 56), (row3 45 55 57), (row3 45 55 58), (row3 45 55 59), (row3 45 55 60)]

def b151_12_labels : List Row := [(row3 306 309 309), (row3 228 462 228), (row3 398 83 135), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 304 273 295), (row3 398 83 135), (row3 319 462 319), (row3 306 309 309), (row3 224 224 224), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246)]

theorem b151_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_12_rows b151_12_labels 41350571239561299283861271520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_12_rows b151_12_labels]
    decide +kernel

def b151_13_rows : List Row := [(row3 45 55 61), (row3 45 55 62), (row3 45 55 63), (row3 45 56 57), (row3 45 56 58), (row3 45 56 59), (row3 45 56 60), (row3 45 56 61), (row3 45 56 62), (row3 45 56 63), (row3 45 57 58), (row3 45 57 59), (row3 45 57 60), (row3 45 57 61), (row3 45 57 62), (row3 45 57 63)]

def b151_13_labels : List Row := [(row3 222 222 224), (row3 321 322 322), (row3 398 83 135), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 289 291 291), (row3 139 462 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 278 462 278)]

theorem b151_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_13_rows b151_13_labels 21956357178419085319946832000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_13_rows b151_13_labels]
    decide +kernel

def b151_14_rows : List Row := [(row3 45 58 59), (row3 45 58 60), (row3 45 58 61), (row3 45 58 62), (row3 45 58 63), (row3 45 59 60), (row3 45 59 61), (row3 45 59 62), (row3 45 59 63), (row3 45 60 61), (row3 45 60 62), (row3 45 60 63), (row3 45 61 62), (row3 45 61 63), (row3 45 62 63), (row3 46 47 48)]

def b151_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 244 244), (row3 235 462 235), (row3 462 462 462), (row3 261 261 462), (row3 234 234 234), (row3 462 462 462), (row3 193 193 462), (row3 289 291 291), (row3 235 462 235), (row3 369 86 122), (row3 288 462 288), (row3 398 83 135), (row3 126 137 127)]

theorem b151_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_14_rows b151_14_labels 39152977970988093992946254700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_14_rows b151_14_labels]
    decide +kernel

def b151_15_rows : List Row := [(row3 46 47 49), (row3 46 47 50), (row3 46 47 51), (row3 46 47 52), (row3 46 47 53), (row3 46 47 54), (row3 46 47 55), (row3 46 47 56), (row3 46 47 57), (row3 46 47 58), (row3 46 47 59), (row3 46 47 60), (row3 46 47 61), (row3 46 47 62), (row3 46 47 63), (row3 46 48 49)]

def b151_15_labels : List Row := [(row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 124 139 163), (row3 43 436 383), (row3 307 462 307), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 305 289 305), (row3 133 137 132), (row3 360 387 390)]

theorem b151_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b151_15_rows b151_15_labels 413764296745310759552490663750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b151_15_rows b151_15_labels]
    decide +kernel

theorem checked151 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_151 QuarticIntegerComputationalData.ids64_151 550841888639368063609562579220 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b151_00_rows ++ b151_01_rows) ++ (b151_02_rows ++ b151_03_rows)) ++ ((b151_04_rows ++ b151_05_rows) ++ (b151_06_rows ++ b151_07_rows))) ++ (((b151_08_rows ++ b151_09_rows) ++ (b151_10_rows ++ b151_11_rows)) ++ ((b151_12_rows ++ b151_13_rows) ++ (b151_14_rows ++ b151_15_rows))))
    ((((b151_00_labels ++ b151_01_labels) ++ (b151_02_labels ++ b151_03_labels)) ++ ((b151_04_labels ++ b151_05_labels) ++ (b151_06_labels ++ b151_07_labels))) ++ (((b151_08_labels ++ b151_09_labels) ++ (b151_10_labels ++ b151_11_labels)) ++ ((b151_12_labels ++ b151_13_labels) ++ (b151_14_labels ++ b151_15_labels)))) 550841888639368063609562579220
  exact ((((b151_00_checked.append (c := 1789539159596210395955165250) b151_01_checked (by decide +kernel)).append (c := 5189734839554121143918765250) (b151_02_checked.append (c := 3400195679957910747963600000) b151_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 32300067723631632162621325350) ((b151_04_checked.append (c := 6035491231959637932297855300) b151_05_checked (by decide +kernel)).append (c := 27110332884077511018702560100) (b151_06_checked.append (c := 21074841652117873086404704800) b151_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 550841888639368063609562579220) (((b151_08_checked.append (c := 49021149569882503338502200) b151_09_checked (by decide +kernel)).append (c := 2317617781457193297696231900) (b151_10_checked.append (c := 2268596631887310794357729700) b151_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 518541820915736431446941253870) ((b151_12_checked.append (c := 63306928417980384603808103520) b151_13_checked (by decide +kernel)).append (c := 516224203134279238149245021970) (b151_14_checked.append (c := 452917274716298853545436918450) b151_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b152_00_rows : List Row := [(row3 46 48 50), (row3 46 48 51), (row3 46 48 52), (row3 46 48 53), (row3 46 48 54), (row3 46 48 55), (row3 46 48 56), (row3 46 48 57), (row3 46 48 58), (row3 46 48 59), (row3 46 48 60), (row3 46 48 61), (row3 46 48 62), (row3 46 48 63), (row3 46 49 50), (row3 46 49 51)]

def b152_00_labels : List Row := [(row3 184 184 178), (row3 266 265 266), (row3 462 237 237), (row3 266 265 266), (row3 140 140 178), (row3 59 410 431), (row3 42 435 181), (row3 146 149 137), (row3 291 289 291), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 313 306 313), (row3 101 98 99), (row3 284 284 462), (row3 235 235 462)]

theorem b152_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_00_rows b152_00_labels 501679182014149770943752333510 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_00_rows b152_00_labels]
    decide +kernel

def b152_01_rows : List Row := [(row3 46 49 52), (row3 46 49 53), (row3 46 49 54), (row3 46 49 55), (row3 46 49 56), (row3 46 49 57), (row3 46 49 58), (row3 46 49 59), (row3 46 49 60), (row3 46 49 61), (row3 46 49 62), (row3 46 49 63), (row3 46 50 51), (row3 46 50 52), (row3 46 50 53), (row3 46 50 54)]

def b152_01_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 271 271 462), (row3 147 144 137), (row3 138 232 139), (row3 284 284 462), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 312 312 306), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b152_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_01_rows b152_01_labels 1551342065566308285698359020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_01_rows b152_01_labels]
    decide +kernel

def b152_02_rows : List Row := [(row3 46 50 55), (row3 46 50 56), (row3 46 50 57), (row3 46 50 58), (row3 46 50 59), (row3 46 50 60), (row3 46 50 61), (row3 46 50 62), (row3 46 50 63), (row3 46 51 52), (row3 46 51 53), (row3 46 51 54), (row3 46 51 55), (row3 46 51 56), (row3 46 51 57), (row3 46 51 58)]

def b152_02_labels : List Row := [(row3 279 278 279), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b152_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_02_rows b152_02_labels 129526386591664595078715600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_02_rows b152_02_labels]
    decide +kernel

def b152_03_rows : List Row := [(row3 46 51 59), (row3 46 51 60), (row3 46 51 61), (row3 46 51 62), (row3 46 51 63), (row3 46 52 53), (row3 46 52 54), (row3 46 52 55), (row3 46 52 56), (row3 46 52 57), (row3 46 52 58), (row3 46 52 59), (row3 46 52 60), (row3 46 52 61), (row3 46 52 62), (row3 46 52 63)]

def b152_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 180 180 462), (row3 279 278 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 291 289 291), (row3 462 232 232)]

theorem b152_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_03_rows b152_03_labels 545935191413661666964639800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_03_rows b152_03_labels]
    decide +kernel

def b152_04_rows : List Row := [(row3 46 53 54), (row3 46 53 55), (row3 46 53 56), (row3 46 53 57), (row3 46 53 58), (row3 46 53 59), (row3 46 53 60), (row3 46 53 61), (row3 46 53 62), (row3 46 53 63), (row3 46 54 55), (row3 46 54 56), (row3 46 54 57), (row3 46 54 58), (row3 46 54 59), (row3 46 54 60)]

def b152_04_labels : List Row := [(row3 377 377 462), (row3 149 146 137), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 146 149 137), (row3 309 309 306), (row3 45 436 389), (row3 316 462 316), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293)]

theorem b152_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_04_rows b152_04_labels 408152303302630408164552903660 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_04_rows b152_04_labels]
    decide +kernel

def b152_05_rows : List Row := [(row3 46 54 61), (row3 46 54 62), (row3 46 54 63), (row3 46 55 56), (row3 46 55 57), (row3 46 55 58), (row3 46 55 59), (row3 46 55 60), (row3 46 55 61), (row3 46 55 62), (row3 46 55 63), (row3 46 56 57), (row3 46 56 58), (row3 46 56 59), (row3 46 56 60), (row3 46 56 61)]

def b152_05_labels : List Row := [(row3 138 232 139), (row3 42 435 181), (row3 100 113 100), (row3 100 113 100), (row3 309 309 306), (row3 462 232 232), (row3 462 462 462), (row3 462 232 232), (row3 312 312 306), (row3 101 98 99), (row3 39 437 412), (row3 377 377 462), (row3 180 180 462), (row3 269 269 462), (row3 462 462 462), (row3 271 271 462)]

theorem b152_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_05_rows b152_05_labels 763019406910123181322913377450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_05_rows b152_05_labels]
    decide +kernel

def b152_06_rows : List Row := [(row3 46 56 62), (row3 46 56 63), (row3 46 57 58), (row3 46 57 59), (row3 46 57 60), (row3 46 57 61), (row3 46 57 62), (row3 46 57 63), (row3 46 58 59), (row3 46 58 60), (row3 46 58 61), (row3 46 58 62), (row3 46 58 63), (row3 46 59 60), (row3 46 59 61), (row3 46 59 62)]

def b152_06_labels : List Row := [(row3 140 140 178), (row3 45 389 436), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 266 265 266), (row3 149 137 146), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 237 237), (row3 279 279 278), (row3 462 462 462), (row3 235 235 462), (row3 266 265 266)]

theorem b152_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_06_rows b152_06_labels 379323990749324739698169479460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_06_rows b152_06_labels]
    decide +kernel

def b152_07_rows : List Row := [(row3 46 59 63), (row3 46 60 61), (row3 46 60 62), (row3 46 60 63), (row3 46 61 62), (row3 46 61 63), (row3 46 62 63), (row3 47 48 49), (row3 47 48 50), (row3 47 48 51), (row3 47 48 52), (row3 47 48 53), (row3 47 48 54), (row3 47 48 55), (row3 47 48 56), (row3 47 48 57)]

def b152_07_labels : List Row := [(row3 462 235 235), (row3 284 284 462), (row3 184 184 178), (row3 279 279 278), (row3 360 387 390), (row3 147 137 144), (row3 59 431 410), (row3 62 49 52), (row3 345 345 347), (row3 190 199 198), (row3 462 261 261), (row3 190 197 196), (row3 348 351 350), (row3 443 34 27), (row3 453 26 47), (row3 381 378 382)]

theorem b152_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_07_rows b152_07_labels 17782517573934953871081826491210 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_07_rows b152_07_labels]
    decide +kernel

def b152_08_rows : List Row := [(row3 47 48 58), (row3 47 48 59), (row3 47 48 60), (row3 47 48 61), (row3 47 48 62), (row3 47 48 63), (row3 47 49 50), (row3 47 49 51), (row3 47 49 52), (row3 47 49 53), (row3 47 49 54), (row3 47 49 55), (row3 47 49 56), (row3 47 49 57), (row3 47 49 58), (row3 47 49 59)]

def b152_08_labels : List Row := [(row3 137 147 144), (row3 462 273 273), (row3 462 462 462), (row3 462 273 273), (row3 136 142 141), (row3 403 402 404), (row3 131 105 105), (row3 289 291 291), (row3 234 234 234), (row3 462 248 248), (row3 229 224 226), (row3 388 362 392), (row3 408 416 396), (row3 398 81 134), (row3 306 312 312), (row3 224 224 224)]

theorem b152_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_08_rows b152_08_labels 133046126625911832822887004960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_08_rows b152_08_labels]
    decide +kernel

def b152_09_rows : List Row := [(row3 47 49 60), (row3 47 49 61), (row3 47 49 62), (row3 47 49 63), (row3 47 50 51), (row3 47 50 52), (row3 47 50 53), (row3 47 50 54), (row3 47 50 55), (row3 47 50 56), (row3 47 50 57), (row3 47 50 58), (row3 47 50 59), (row3 47 50 60), (row3 47 50 61), (row3 47 50 62)]

def b152_09_labels : List Row := [(row3 462 246 246), (row3 462 462 462), (row3 462 253 253), (row3 136 142 141), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 154 180 154), (row3 105 105 131), (row3 295 462 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b152_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_09_rows b152_09_labels 3592949342254701576551998200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_09_rows b152_09_labels]
    decide +kernel

def b152_10_rows : List Row := [(row3 47 50 63), (row3 47 51 52), (row3 47 51 53), (row3 47 51 54), (row3 47 51 55), (row3 47 51 56), (row3 47 51 57), (row3 47 51 58), (row3 47 51 59), (row3 47 51 60), (row3 47 51 61), (row3 47 51 62), (row3 47 51 63), (row3 47 52 53), (row3 47 52 54), (row3 47 52 55)]

def b152_10_labels : List Row := [(row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 269 269), (row3 462 284 284), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 278 278 462), (row3 154 180 154)]

theorem b152_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_10_rows b152_10_labels 902453177873342875842364500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_10_rows b152_10_labels]
    decide +kernel

def b152_11_rows : List Row := [(row3 47 52 56), (row3 47 52 57), (row3 47 52 58), (row3 47 52 59), (row3 47 52 60), (row3 47 52 61), (row3 47 52 62), (row3 47 52 63), (row3 47 53 54), (row3 47 53 55), (row3 47 53 56), (row3 47 53 57), (row3 47 53 58), (row3 47 53 59), (row3 47 53 60), (row3 47 53 61)]

def b152_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 273 273), (row3 139 138 232), (row3 387 360 390), (row3 462 286 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b152_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_11_rows b152_11_labels 15674418738598054628530419750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_11_rows b152_11_labels]
    decide +kernel

def b152_12_rows : List Row := [(row3 47 53 62), (row3 47 53 63), (row3 47 54 55), (row3 47 54 56), (row3 47 54 57), (row3 47 54 58), (row3 47 54 59), (row3 47 54 60), (row3 47 54 61), (row3 47 54 62), (row3 47 54 63), (row3 47 55 56), (row3 47 55 57), (row3 47 55 58), (row3 47 55 59), (row3 47 55 60)]

def b152_12_labels : List Row := [(row3 306 312 312), (row3 137 147 144), (row3 35 36 31), (row3 102 103 129), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 295 462 295), (row3 398 81 134), (row3 381 378 382), (row3 422 423 417), (row3 102 103 129), (row3 462 286 286), (row3 462 462 462), (row3 462 284 284)]

theorem b152_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_12_rows b152_12_labels 4895980633970304137017303068540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_12_rows b152_12_labels]
    decide +kernel

def b152_13_rows : List Row := [(row3 47 55 61), (row3 47 55 62), (row3 47 55 63), (row3 47 56 57), (row3 47 56 58), (row3 47 56 59), (row3 47 56 60), (row3 47 56 61), (row3 47 56 62), (row3 47 56 63), (row3 47 57 58), (row3 47 57 59), (row3 47 57 60), (row3 47 57 61), (row3 47 57 62), (row3 47 57 63)]

def b152_13_labels : List Row := [(row3 105 105 131), (row3 408 416 396), (row3 453 26 47), (row3 35 36 31), (row3 387 360 390), (row3 154 180 154), (row3 462 269 269), (row3 154 180 154), (row3 388 362 392), (row3 443 34 27), (row3 139 138 232), (row3 278 278 462), (row3 235 235 462), (row3 462 462 462), (row3 229 224 226), (row3 348 351 350)]

theorem b152_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_13_rows b152_13_labels 18284203963737329717266564650750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_13_rows b152_13_labels]
    decide +kernel

def b152_14_rows : List Row := [(row3 47 58 59), (row3 47 58 60), (row3 47 58 61), (row3 47 58 62), (row3 47 58 63), (row3 47 59 60), (row3 47 59 61), (row3 47 59 62), (row3 47 59 63), (row3 47 60 61), (row3 47 60 62), (row3 47 60 63), (row3 47 61 62), (row3 47 61 63), (row3 47 62 63), (row3 48 49 50)]

def b152_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 190 197 196), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 261 261), (row3 462 462 462), (row3 289 291 291), (row3 190 199 198), (row3 131 105 105), (row3 345 345 347), (row3 62 49 52), (row3 37 28 444)]

theorem b152_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_14_rows b152_14_labels 4718917462380419675281935485700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_14_rows b152_14_labels]
    decide +kernel

def b152_15_rows : List Row := [(row3 48 49 51), (row3 48 49 52), (row3 48 49 53), (row3 48 49 54), (row3 48 49 55), (row3 48 49 56), (row3 48 49 57), (row3 48 49 58), (row3 48 49 59), (row3 48 49 60), (row3 48 49 61), (row3 48 49 62), (row3 48 49 63), (row3 48 50 51), (row3 48 50 52), (row3 48 50 53)]

def b152_15_labels : List Row := [(row3 385 426 77), (row3 168 94 333), (row3 339 342 328), (row3 68 69 76), (row3 455 447 447), (row3 460 22 450), (row3 451 24 442), (row3 411 432 60), (row3 121 85 369), (row3 462 284 284), (row3 191 235 193), (row3 388 392 362), (row3 48 50 61), (row3 164 206 164), (row3 273 462 273), (row3 209 206 209)]

theorem b152_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b152_15_rows b152_15_labels 1006317460473127018131237940611420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b152_15_rows b152_15_labels]
    decide +kernel

theorem checked152 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_152 QuarticIntegerComputationalData.ids64_152 1054206697741654463198466511903530 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b152_00_rows ++ b152_01_rows) ++ (b152_02_rows ++ b152_03_rows)) ++ ((b152_04_rows ++ b152_05_rows) ++ (b152_06_rows ++ b152_07_rows))) ++ (((b152_08_rows ++ b152_09_rows) ++ (b152_10_rows ++ b152_11_rows)) ++ ((b152_12_rows ++ b152_13_rows) ++ (b152_14_rows ++ b152_15_rows))))
    ((((b152_00_labels ++ b152_01_labels) ++ (b152_02_labels ++ b152_03_labels)) ++ ((b152_04_labels ++ b152_05_labels) ++ (b152_06_labels ++ b152_07_labels))) ++ (((b152_08_labels ++ b152_09_labels) ++ (b152_10_labels ++ b152_11_labels)) ++ ((b152_12_labels ++ b152_13_labels) ++ (b152_14_labels ++ b152_15_labels)))) 1054206697741654463198466511903530
  exact ((((b152_00_checked.append (c := 503230524079716079229450692530) b152_01_checked (by decide +kernel)).append (c := 503905985657721405491494047930) (b152_02_checked.append (c := 675461578005326262043355400) b152_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 19836919260554753605758956299710) ((b152_04_checked.append (c := 1171171710212753589487466281110) b152_05_checked (by decide +kernel)).append (c := 19333013274897032200267462251780) (b152_06_checked.append (c := 18161841564684278610779995970670) b152_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1054206697741654463198466511903530) (((b152_08_checked.append (c := 136639075968166534399439003160) b152_09_checked (by decide +kernel)).append (c := 153215947884637931903811787410) (b152_10_checked.append (c := 16576871916471397504372784250) b152_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1034369778481099709592707555603820) ((b152_12_checked.append (c := 23180184597707633854283867719290) b152_13_checked (by decide +kernel)).append (c := 1034216562533215071660803743816410) (b152_14_checked.append (c := 1011036377935507437806519876097120) b152_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
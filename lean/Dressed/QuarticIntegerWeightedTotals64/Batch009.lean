import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch008
import Dressed.QuarticIntegerComputationalData64.Batch009


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b073_00_rows : List Row := [(row3 12 43 56), (row3 12 43 57), (row3 12 43 58), (row3 12 43 59), (row3 12 43 60), (row3 12 43 61), (row3 12 43 62), (row3 12 43 63), (row3 12 44 45), (row3 12 44 46), (row3 12 44 47), (row3 12 44 48), (row3 12 44 49), (row3 12 44 50), (row3 12 44 51), (row3 12 44 52)]

def b073_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_00_rows b073_00_labels 301066359412777219228500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_00_rows b073_00_labels]
    decide +kernel

def b073_01_rows : List Row := [(row3 12 44 53), (row3 12 44 54), (row3 12 44 55), (row3 12 44 56), (row3 12 44 57), (row3 12 44 58), (row3 12 44 59), (row3 12 44 60), (row3 12 44 61), (row3 12 44 62), (row3 12 44 63), (row3 12 45 46), (row3 12 45 47), (row3 12 45 48), (row3 12 45 49), (row3 12 45 50)]

def b073_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_01_rows b073_01_labels 51990607467643224150000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_01_rows b073_01_labels]
    decide +kernel

def b073_02_rows : List Row := [(row3 12 45 51), (row3 12 45 52), (row3 12 45 53), (row3 12 45 54), (row3 12 45 55), (row3 12 45 56), (row3 12 45 57), (row3 12 45 58), (row3 12 45 59), (row3 12 45 60), (row3 12 45 61), (row3 12 45 62), (row3 12 45 63), (row3 12 46 47), (row3 12 46 48), (row3 12 46 49)]

def b073_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_02_rows b073_02_labels 301066359412777219228500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_02_rows b073_02_labels]
    decide +kernel

def b073_03_rows : List Row := [(row3 12 46 50), (row3 12 46 51), (row3 12 46 52), (row3 12 46 53), (row3 12 46 54), (row3 12 46 55), (row3 12 46 56), (row3 12 46 57), (row3 12 46 58), (row3 12 46 59), (row3 12 46 60), (row3 12 46 61), (row3 12 46 62), (row3 12 46 63), (row3 12 47 48), (row3 12 47 49)]

def b073_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_03_rows b073_03_labels 419105409451888813749000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_03_rows b073_03_labels]
    decide +kernel

def b073_04_rows : List Row := [(row3 12 47 50), (row3 12 47 51), (row3 12 47 52), (row3 12 47 53), (row3 12 47 54), (row3 12 47 55), (row3 12 47 56), (row3 12 47 57), (row3 12 47 58), (row3 12 47 59), (row3 12 47 60), (row3 12 47 61), (row3 12 47 62), (row3 12 47 63), (row3 12 48 49), (row3 12 48 50)]

def b073_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_04_rows b073_04_labels 38992955600732418112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_04_rows b073_04_labels]
    decide +kernel

def b073_05_rows : List Row := [(row3 12 48 51), (row3 12 48 52), (row3 12 48 53), (row3 12 48 54), (row3 12 48 55), (row3 12 48 56), (row3 12 48 57), (row3 12 48 58), (row3 12 48 59), (row3 12 48 60), (row3 12 48 61), (row3 12 48 62), (row3 12 48 63), (row3 12 49 50), (row3 12 49 51), (row3 12 49 52)]

def b073_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_05_rows b073_05_labels 115974944756674762365000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_05_rows b073_05_labels]
    decide +kernel

def b073_06_rows : List Row := [(row3 12 49 53), (row3 12 49 54), (row3 12 49 55), (row3 12 49 56), (row3 12 49 57), (row3 12 49 58), (row3 12 49 59), (row3 12 49 60), (row3 12 49 61), (row3 12 49 62), (row3 12 49 63), (row3 12 50 51), (row3 12 50 52), (row3 12 50 53), (row3 12 50 54), (row3 12 50 55)]

def b073_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b073_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_06_rows b073_06_labels 1283220848821704234831000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_06_rows b073_06_labels]
    decide +kernel

def b073_07_rows : List Row := [(row3 12 50 56), (row3 12 50 57), (row3 12 50 58), (row3 12 50 59), (row3 12 50 60), (row3 12 50 61), (row3 12 50 62), (row3 12 50 63), (row3 12 51 52), (row3 12 51 53), (row3 12 51 54), (row3 12 51 55), (row3 12 51 56), (row3 12 51 57), (row3 12 51 58), (row3 12 51 59)]

def b073_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 284 284 462)]

theorem b073_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_07_rows b073_07_labels 150720955841734510512172500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_07_rows b073_07_labels]
    decide +kernel

def b073_08_rows : List Row := [(row3 12 51 60), (row3 12 51 61), (row3 12 51 62), (row3 12 51 63), (row3 12 52 53), (row3 12 52 54), (row3 12 52 55), (row3 12 52 56), (row3 12 52 57), (row3 12 52 58), (row3 12 52 59), (row3 12 52 60), (row3 12 52 61), (row3 12 52 62), (row3 12 52 63), (row3 12 53 54)]

def b073_08_labels : List Row := [(row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462)]

theorem b073_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_08_rows b073_08_labels 1744000870466214304128000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_08_rows b073_08_labels]
    decide +kernel

def b073_09_rows : List Row := [(row3 12 53 55), (row3 12 53 56), (row3 12 53 57), (row3 12 53 58), (row3 12 53 59), (row3 12 53 60), (row3 12 53 61), (row3 12 53 62), (row3 12 53 63), (row3 12 54 55), (row3 12 54 56), (row3 12 54 57), (row3 12 54 58), (row3 12 54 59), (row3 12 54 60), (row3 12 54 61)]

def b073_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 284 284 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462)]

theorem b073_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_09_rows b073_09_labels 61526075027682111393060000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_09_rows b073_09_labels]
    decide +kernel

def b073_10_rows : List Row := [(row3 12 54 62), (row3 12 54 63), (row3 12 55 56), (row3 12 55 57), (row3 12 55 58), (row3 12 55 59), (row3 12 55 60), (row3 12 55 61), (row3 12 55 62), (row3 12 55 63), (row3 12 56 57), (row3 12 56 58), (row3 12 56 59), (row3 12 56 60), (row3 12 56 61), (row3 12 56 62)]

def b073_10_labels : List Row := [(row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 462 234)]

theorem b073_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_10_rows b073_10_labels 96137668788515127460876500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_10_rows b073_10_labels]
    decide +kernel

def b073_11_rows : List Row := [(row3 12 56 63), (row3 12 57 58), (row3 12 57 59), (row3 12 57 60), (row3 12 57 61), (row3 12 57 62), (row3 12 57 63), (row3 12 58 59), (row3 12 58 60), (row3 12 58 61), (row3 12 58 62), (row3 12 58 63), (row3 12 59 60), (row3 12 59 61), (row3 12 59 62), (row3 12 59 63)]

def b073_11_labels : List Row := [(row3 462 462 462), (row3 293 462 293), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 117 214 11), (row3 234 234 462), (row3 245 245 462), (row3 462 462 462), (row3 244 244 462), (row3 284 462 284), (row3 232 235 235), (row3 245 462 245), (row3 462 462 462)]

theorem b073_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_11_rows b073_11_labels 1798884651184989580949258250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_11_rows b073_11_labels]
    decide +kernel

def b073_12_rows : List Row := [(row3 12 60 61), (row3 12 60 62), (row3 12 60 63), (row3 12 61 62), (row3 12 61 63), (row3 12 62 63), (row3 13 14 15), (row3 13 14 16), (row3 13 14 17), (row3 13 14 18), (row3 13 14 19), (row3 13 14 20), (row3 13 14 21), (row3 13 14 22), (row3 13 14 23), (row3 13 14 24)]

def b073_12_labels : List Row := [(row3 284 284 462), (row3 234 462 234), (row3 462 462 462), (row3 117 11 214), (row3 235 462 235), (row3 293 293 462), (row3 453 26 47), (row3 104 104 130), (row3 462 286 286), (row3 462 462 462), (row3 11 212 115), (row3 83 157 399), (row3 436 383 43), (row3 35 31 36), (row3 408 416 396), (row3 462 294 294)]

theorem b073_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_12_rows b073_12_labels 13706413493183947684481021966250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_12_rows b073_12_labels]
    decide +kernel

def b073_13_rows : List Row := [(row3 13 14 25), (row3 13 14 26), (row3 13 14 27), (row3 13 14 28), (row3 13 14 29), (row3 13 14 30), (row3 13 14 31), (row3 13 14 32), (row3 13 14 33), (row3 13 14 34), (row3 13 14 35), (row3 13 14 36), (row3 13 14 37), (row3 13 14 38), (row3 13 14 39), (row3 13 14 40)]

def b073_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 11 214 117), (row3 86 122 369), (row3 387 390 360), (row3 105 105 131), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 10 254 171), (row3 154 154 180), (row3 462 284 284), (row3 462 243 243)]

theorem b073_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_13_rows b073_13_labels 29800419942302507613352631400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_13_rows b073_13_labels]
    decide +kernel

def b073_14_rows : List Row := [(row3 13 14 41), (row3 13 14 42), (row3 13 14 43), (row3 13 14 44), (row3 13 14 45), (row3 13 14 46), (row3 13 14 47), (row3 13 14 48), (row3 13 14 49), (row3 13 14 50), (row3 13 14 51), (row3 13 14 52), (row3 13 14 53), (row3 13 14 54), (row3 13 14 55), (row3 13 14 56)]

def b073_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 462 462), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 10 254 171), (row3 154 154 180), (row3 462 286 286), (row3 462 307 307)]

theorem b073_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_14_rows b073_14_labels 12439335695332586808262189500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_14_rows b073_14_labels]
    decide +kernel

def b073_15_rows : List Row := [(row3 13 14 57), (row3 13 14 58), (row3 13 14 59), (row3 13 14 60), (row3 13 14 61), (row3 13 14 62), (row3 13 14 63), (row3 13 15 16), (row3 13 15 17), (row3 13 15 18), (row3 13 15 19), (row3 13 15 20), (row3 13 15 21), (row3 13 15 22), (row3 13 15 23), (row3 13 15 24)]

def b073_15_labels : List Row := [(row3 462 232 232), (row3 462 246 246), (row3 462 462 462), (row3 11 214 117), (row3 85 121 369), (row3 388 392 362), (row3 102 103 129), (row3 380 380 379), (row3 137 143 146), (row3 462 273 273), (row3 462 235 235), (row3 462 288 288), (row3 137 132 133), (row3 381 382 378), (row3 62 52 49), (row3 137 145 148)]

theorem b073_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b073_15_rows b073_15_labels 296347568515683390915276943260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b073_15_rows b073_15_labels]
    decide +kernel

theorem checked073 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_073 QuarticIntegerComputationalData.ids64_073 14047112342106464481560424890160 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b073_00_rows ++ b073_01_rows) ++ (b073_02_rows ++ b073_03_rows)) ++ ((b073_04_rows ++ b073_05_rows) ++ (b073_06_rows ++ b073_07_rows))) ++ (((b073_08_rows ++ b073_09_rows) ++ (b073_10_rows ++ b073_11_rows)) ++ ((b073_12_rows ++ b073_13_rows) ++ (b073_14_rows ++ b073_15_rows))))
    ((((b073_00_labels ++ b073_01_labels) ++ (b073_02_labels ++ b073_03_labels)) ++ ((b073_04_labels ++ b073_05_labels) ++ (b073_06_labels ++ b073_07_labels))) ++ (((b073_08_labels ++ b073_09_labels) ++ (b073_10_labels ++ b073_11_labels)) ++ ((b073_12_labels ++ b073_13_labels) ++ (b073_14_labels ++ b073_15_labels)))) 14047112342106464481560424890160
  exact ((((b073_00_checked.append (c := 353056966880420443378500) b073_01_checked (by decide +kernel)).append (c := 1073228735745086476356000) (b073_02_checked.append (c := 720171768864666032977500) b073_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 153232373326658708403837000) ((b073_04_checked.append (c := 154967900357407180477500) b073_05_checked (by decide +kernel)).append (c := 152159144590913621927481000) (b073_06_checked.append (c := 152004176690556214747003500) b073_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 14047112342106464481560424890160) (((b073_08_checked.append (c := 63270075898148325697188000) b073_09_checked (by decide +kernel)).append (c := 1958292395871653034107322750) (b073_10_checked.append (c := 1895022319973504708410134750) b073_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 14046959109733137822852021053160) ((b073_12_checked.append (c := 13736213913126250192094374597650) b073_13_checked (by decide +kernel)).append (c := 14045000817337266169817913730410) (b073_14_checked.append (c := 308786904211015977723539132760) b073_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b074_00_rows : List Row := [(row3 13 15 25), (row3 13 15 26), (row3 13 15 27), (row3 13 15 28), (row3 13 15 29), (row3 13 15 30), (row3 13 15 31), (row3 13 15 32), (row3 13 15 33), (row3 13 15 34), (row3 13 15 35), (row3 13 15 36), (row3 13 15 37), (row3 13 15 38), (row3 13 15 39), (row3 13 15 40)]

def b074_00_labels : List Row := [(row3 462 278 278), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 288 288), (row3 137 144 147), (row3 345 347 345), (row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 273 273), (row3 190 198 199), (row3 462 236 236)]

theorem b074_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_00_rows b074_00_labels 2079370734201530585572498560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_00_rows b074_00_labels]
    decide +kernel

def b074_01_rows : List Row := [(row3 13 15 41), (row3 13 15 42), (row3 13 15 43), (row3 13 15 44), (row3 13 15 45), (row3 13 15 46), (row3 13 15 47), (row3 13 15 48), (row3 13 15 49), (row3 13 15 50), (row3 13 15 51), (row3 13 15 52), (row3 13 15 53), (row3 13 15 54), (row3 13 15 55), (row3 13 15 56)]

def b074_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 462 288 288), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 273 273), (row3 190 196 197), (row3 137 126 127)]

theorem b074_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_01_rows b074_01_labels 8848868248715969474698209120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_01_rows b074_01_labels]
    decide +kernel

def b074_02_rows : List Row := [(row3 13 15 57), (row3 13 15 58), (row3 13 15 59), (row3 13 15 60), (row3 13 15 61), (row3 13 15 62), (row3 13 15 63), (row3 13 16 17), (row3 13 16 18), (row3 13 16 19), (row3 13 16 20), (row3 13 16 21), (row3 13 16 22), (row3 13 16 23), (row3 13 16 24), (row3 13 16 25)]

def b074_02_labels : List Row := [(row3 462 300 300), (row3 462 232 232), (row3 462 462 462), (row3 462 235 235), (row3 462 288 288), (row3 136 141 142), (row3 348 350 351), (row3 193 191 235), (row3 261 261 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 288 288 462), (row3 369 121 85), (row3 193 192 238), (row3 273 273 462)]

theorem b074_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_02_rows b074_02_labels 16060228960113961508863548000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_02_rows b074_02_labels]
    decide +kernel

def b074_03_rows : List Row := [(row3 13 16 26), (row3 13 16 27), (row3 13 16 28), (row3 13 16 29), (row3 13 16 30), (row3 13 16 31), (row3 13 16 32), (row3 13 16 33), (row3 13 16 34), (row3 13 16 35), (row3 13 16 36), (row3 13 16 37), (row3 13 16 38), (row3 13 16 39), (row3 13 16 40), (row3 13 16 41)]

def b074_03_labels : List Row := [(row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 273 273 462), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 238 236 238), (row3 462 462 462)]

theorem b074_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_03_rows b074_03_labels 9282970760656079178820800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_03_rows b074_03_labels]
    decide +kernel

def b074_04_rows : List Row := [(row3 13 16 42), (row3 13 16 43), (row3 13 16 44), (row3 13 16 45), (row3 13 16 46), (row3 13 16 47), (row3 13 16 48), (row3 13 16 49), (row3 13 16 50), (row3 13 16 51), (row3 13 16 52), (row3 13 16 53), (row3 13 16 54), (row3 13 16 55), (row3 13 16 56), (row3 13 16 57)]

def b074_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 238 192 193), (row3 462 273 273)]

theorem b074_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_04_rows b074_04_labels 355680742556555245309636800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_04_rows b074_04_labels]
    decide +kernel

def b074_05_rows : List Row := [(row3 13 16 58), (row3 13 16 59), (row3 13 16 60), (row3 13 16 61), (row3 13 16 62), (row3 13 16 63), (row3 13 17 18), (row3 13 17 19), (row3 13 17 20), (row3 13 17 21), (row3 13 17 22), (row3 13 17 23), (row3 13 17 24), (row3 13 17 25), (row3 13 17 26), (row3 13 17 27)]

def b074_05_labels : List Row := [(row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 289 292 292), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_05_rows b074_05_labels 18830662410559035614626800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_05_rows b074_05_labels]
    decide +kernel

def b074_06_rows : List Row := [(row3 13 17 28), (row3 13 17 29), (row3 13 17 30), (row3 13 17 31), (row3 13 17 32), (row3 13 17 33), (row3 13 17 34), (row3 13 17 35), (row3 13 17 36), (row3 13 17 37), (row3 13 17 38), (row3 13 17 39), (row3 13 17 40), (row3 13 17 41), (row3 13 17 42), (row3 13 17 43)]

def b074_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_06_rows b074_06_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_06_rows b074_06_labels]
    decide +kernel

def b074_07_rows : List Row := [(row3 13 17 44), (row3 13 17 45), (row3 13 17 46), (row3 13 17 47), (row3 13 17 48), (row3 13 17 49), (row3 13 17 50), (row3 13 17 51), (row3 13 17 52), (row3 13 17 53), (row3 13 17 54), (row3 13 17 55), (row3 13 17 56), (row3 13 17 57), (row3 13 17 58), (row3 13 17 59)]

def b074_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 284 284), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462)]

theorem b074_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_07_rows b074_07_labels 60636883659164027159130000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_07_rows b074_07_labels]
    decide +kernel

def b074_08_rows : List Row := [(row3 13 17 60), (row3 13 17 61), (row3 13 17 62), (row3 13 17 63), (row3 13 18 19), (row3 13 18 20), (row3 13 18 21), (row3 13 18 22), (row3 13 18 23), (row3 13 18 24), (row3 13 18 25), (row3 13 18 26), (row3 13 18 27), (row3 13 18 28), (row3 13 18 29), (row3 13 18 30)]

def b074_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_08_rows b074_08_labels 1165707760431550601619000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_08_rows b074_08_labels]
    decide +kernel

def b074_09_rows : List Row := [(row3 13 18 31), (row3 13 18 32), (row3 13 18 33), (row3 13 18 34), (row3 13 18 35), (row3 13 18 36), (row3 13 18 37), (row3 13 18 38), (row3 13 18 39), (row3 13 18 40), (row3 13 18 41), (row3 13 18 42), (row3 13 18 43), (row3 13 18 44), (row3 13 18 45), (row3 13 18 46)]

def b074_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_09_rows b074_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_09_rows b074_09_labels]
    decide +kernel

def b074_10_rows : List Row := [(row3 13 18 47), (row3 13 18 48), (row3 13 18 49), (row3 13 18 50), (row3 13 18 51), (row3 13 18 52), (row3 13 18 53), (row3 13 18 54), (row3 13 18 55), (row3 13 18 56), (row3 13 18 57), (row3 13 18 58), (row3 13 18 59), (row3 13 18 60), (row3 13 18 61), (row3 13 18 62)]

def b074_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_10_rows b074_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_10_rows b074_10_labels]
    decide +kernel

def b074_11_rows : List Row := [(row3 13 18 63), (row3 13 19 20), (row3 13 19 21), (row3 13 19 22), (row3 13 19 23), (row3 13 19 24), (row3 13 19 25), (row3 13 19 26), (row3 13 19 27), (row3 13 19 28), (row3 13 19 29), (row3 13 19 30), (row3 13 19 31), (row3 13 19 32), (row3 13 19 33), (row3 13 19 34)]

def b074_11_labels : List Row := [(row3 462 462 462), (row3 462 232 232), (row3 462 284 284), (row3 235 228 232), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_11_rows b074_11_labels 66174090183898139192773500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_11_rows b074_11_labels]
    decide +kernel

def b074_12_rows : List Row := [(row3 13 19 35), (row3 13 19 36), (row3 13 19 37), (row3 13 19 38), (row3 13 19 39), (row3 13 19 40), (row3 13 19 41), (row3 13 19 42), (row3 13 19 43), (row3 13 19 44), (row3 13 19 45), (row3 13 19 46), (row3 13 19 47), (row3 13 19 48), (row3 13 19 49), (row3 13 19 50)]

def b074_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b074_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_12_rows b074_12_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_12_rows b074_12_labels]
    decide +kernel

def b074_13_rows : List Row := [(row3 13 19 51), (row3 13 19 52), (row3 13 19 53), (row3 13 19 54), (row3 13 19 55), (row3 13 19 56), (row3 13 19 57), (row3 13 19 58), (row3 13 19 59), (row3 13 19 60), (row3 13 19 61), (row3 13 19 62), (row3 13 19 63), (row3 13 20 21), (row3 13 20 22), (row3 13 20 23)]

def b074_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 163 163), (row3 278 300 288), (row3 234 226 226)]

theorem b074_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_13_rows b074_13_labels 1074136290078376045875375000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_13_rows b074_13_labels]
    decide +kernel

def b074_14_rows : List Row := [(row3 13 20 24), (row3 13 20 25), (row3 13 20 26), (row3 13 20 27), (row3 13 20 28), (row3 13 20 29), (row3 13 20 30), (row3 13 20 31), (row3 13 20 32), (row3 13 20 33), (row3 13 20 34), (row3 13 20 35), (row3 13 20 36), (row3 13 20 37), (row3 13 20 38), (row3 13 20 39)]

def b074_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 273 273), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462)]

theorem b074_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_14_rows b074_14_labels 12169246176507690557884800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_14_rows b074_14_labels]
    decide +kernel

def b074_15_rows : List Row := [(row3 13 20 40), (row3 13 20 41), (row3 13 20 42), (row3 13 20 43), (row3 13 20 44), (row3 13 20 45), (row3 13 20 46), (row3 13 20 47), (row3 13 20 48), (row3 13 20 49), (row3 13 20 50), (row3 13 20 51), (row3 13 20 52), (row3 13 20 53), (row3 13 20 54), (row3 13 20 55)]

def b074_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462)]

theorem b074_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b074_15_rows b074_15_labels 258010076114267927688000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b074_15_rows b074_15_labels]
    decide +kernel

theorem checked074 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_074 QuarticIntegerComputationalData.ids64_074 28586817866894437457027260380 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b074_00_rows ++ b074_01_rows) ++ (b074_02_rows ++ b074_03_rows)) ++ ((b074_04_rows ++ b074_05_rows) ++ (b074_06_rows ++ b074_07_rows))) ++ (((b074_08_rows ++ b074_09_rows) ++ (b074_10_rows ++ b074_11_rows)) ++ ((b074_12_rows ++ b074_13_rows) ++ (b074_14_rows ++ b074_15_rows))))
    ((((b074_00_labels ++ b074_01_labels) ++ (b074_02_labels ++ b074_03_labels)) ++ ((b074_04_labels ++ b074_05_labels) ++ (b074_06_labels ++ b074_07_labels))) ++ (((b074_08_labels ++ b074_09_labels) ++ (b074_10_labels ++ b074_11_labels)) ++ ((b074_12_labels ++ b074_13_labels) ++ (b074_14_labels ++ b074_15_labels)))) 28586817866894437457027260380
  exact ((((b074_00_checked.append (c := 10928238982917500060270707680) b074_01_checked (by decide +kernel)).append (c := 26997750913792117648313076480) (b074_02_checked.append (c := 16069511930874617588042368800) b074_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 27432906862518752859634195080) ((b074_04_checked.append (c := 374511404967114280924263600) b074_05_checked (by decide +kernel)).append (c := 435155948726635211321118600) (b074_06_checked.append (c := 60644543759520930396855000) b074_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 28586817866894437457027260380) (((b074_08_checked.append (c := 1165707760431550601619000) b074_09_checked (by decide +kernel)).append (c := 67339797944329689794392500) (b074_10_checked.append (c := 66174090183898139192773500) b074_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1153911004375684597393065300) ((b074_12_checked.append (c := 1074143950178732949113100000) b074_13_checked (by decide +kernel)).append (c := 1086571206431354907598672800) (b074_14_checked.append (c := 12427256252621958485572800) b074_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b075_00_rows : List Row := [(row3 13 20 56), (row3 13 20 57), (row3 13 20 58), (row3 13 20 59), (row3 13 20 60), (row3 13 20 61), (row3 13 20 62), (row3 13 20 63), (row3 13 21 22), (row3 13 21 23), (row3 13 21 24), (row3 13 21 25), (row3 13 21 26), (row3 13 21 27), (row3 13 21 28), (row3 13 21 29)]

def b075_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 273 273), (row3 462 232 232), (row3 462 462 462), (row3 139 124 163), (row3 289 305 305), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 193 193)]

theorem b075_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_00_rows b075_00_labels 3457878108194991872633068800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_00_rows b075_00_labels]
    decide +kernel

def b075_01_rows : List Row := [(row3 13 21 30), (row3 13 21 31), (row3 13 21 32), (row3 13 21 33), (row3 13 21 34), (row3 13 21 35), (row3 13 21 36), (row3 13 21 37), (row3 13 21 38), (row3 13 21 39), (row3 13 21 40), (row3 13 21 41), (row3 13 21 42), (row3 13 21 43), (row3 13 21 44), (row3 13 21 45)]

def b075_01_labels : List Row := [(row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_01_rows b075_01_labels 82513666270044569760180000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_01_rows b075_01_labels]
    decide +kernel

def b075_02_rows : List Row := [(row3 13 21 46), (row3 13 21 47), (row3 13 21 48), (row3 13 21 49), (row3 13 21 50), (row3 13 21 51), (row3 13 21 52), (row3 13 21 53), (row3 13 21 54), (row3 13 21 55), (row3 13 21 56), (row3 13 21 57), (row3 13 21 58), (row3 13 21 59), (row3 13 21 60), (row3 13 21 61)]

def b075_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 238 192 193)]

theorem b075_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_02_rows b075_02_labels 426402669771382660600056000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_02_rows b075_02_labels]
    decide +kernel

def b075_03_rows : List Row := [(row3 13 21 62), (row3 13 21 63), (row3 13 22 23), (row3 13 22 24), (row3 13 22 25), (row3 13 22 26), (row3 13 22 27), (row3 13 22 28), (row3 13 22 29), (row3 13 22 30), (row3 13 22 31), (row3 13 22 32), (row3 13 22 33), (row3 13 22 34), (row3 13 22 35), (row3 13 22 36)]

def b075_03_labels : List Row := [(row3 462 286 286), (row3 462 462 462), (row3 398 81 134), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 232 223), (row3 295 273 304), (row3 139 232 138), (row3 295 462 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_03_rows b075_03_labels 21382355185989858852479654400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_03_rows b075_03_labels]
    decide +kernel

def b075_04_rows : List Row := [(row3 13 22 37), (row3 13 22 38), (row3 13 22 39), (row3 13 22 40), (row3 13 22 41), (row3 13 22 42), (row3 13 22 43), (row3 13 22 44), (row3 13 22 45), (row3 13 22 46), (row3 13 22 47), (row3 13 22 48), (row3 13 22 49), (row3 13 22 50), (row3 13 22 51), (row3 13 22 52)]

def b075_04_labels : List Row := [(row3 228 236 225), (row3 278 462 278), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_04_rows b075_04_labels 11832225360825958884734400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_04_rows b075_04_labels]
    decide +kernel

def b075_05_rows : List Row := [(row3 13 22 53), (row3 13 22 54), (row3 13 22 55), (row3 13 22 56), (row3 13 22 57), (row3 13 22 58), (row3 13 22 59), (row3 13 22 60), (row3 13 22 61), (row3 13 22 62), (row3 13 22 63), (row3 13 23 24), (row3 13 23 25), (row3 13 23 26), (row3 13 23 27), (row3 13 23 28)]

def b075_05_labels : List Row := [(row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 273 273), (row3 229 226 224), (row3 462 462 462), (row3 306 310 310), (row3 224 224 224), (row3 462 246 246), (row3 462 462 462), (row3 462 251 251)]

theorem b075_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_05_rows b075_05_labels 41822396786896583079704400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_05_rows b075_05_labels]
    decide +kernel

def b075_06_rows : List Row := [(row3 13 23 29), (row3 13 23 30), (row3 13 23 31), (row3 13 23 32), (row3 13 23 33), (row3 13 23 34), (row3 13 23 35), (row3 13 23 36), (row3 13 23 37), (row3 13 23 38), (row3 13 23 39), (row3 13 23 40), (row3 13 23 41), (row3 13 23 42), (row3 13 23 43), (row3 13 23 44)]

def b075_06_labels : List Row := [(row3 224 222 222), (row3 306 312 312), (row3 131 105 105), (row3 224 224 224), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 250 250), (row3 224 224 224), (row3 289 291 291), (row3 462 247 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_06_rows b075_06_labels 2455183607123272421753325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_06_rows b075_06_labels]
    decide +kernel

def b075_07_rows : List Row := [(row3 13 23 45), (row3 13 23 46), (row3 13 23 47), (row3 13 23 48), (row3 13 23 49), (row3 13 23 50), (row3 13 23 51), (row3 13 23 52), (row3 13 23 53), (row3 13 23 54), (row3 13 23 55), (row3 13 23 56), (row3 13 23 57), (row3 13 23 58), (row3 13 23 59), (row3 13 23 60)]

def b075_07_labels : List Row := [(row3 462 462 462), (row3 462 246 246), (row3 234 234 234), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 248 248), (row3 462 286 286), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246)]

theorem b075_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_07_rows b075_07_labels 101057197164547685211247500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_07_rows b075_07_labels]
    decide +kernel

def b075_08_rows : List Row := [(row3 13 23 61), (row3 13 23 62), (row3 13 23 63), (row3 13 24 25), (row3 13 24 26), (row3 13 24 27), (row3 13 24 28), (row3 13 24 29), (row3 13 24 30), (row3 13 24 31), (row3 13 24 32), (row3 13 24 33), (row3 13 24 34), (row3 13 24 35), (row3 13 24 36), (row3 13 24 37)]

def b075_08_labels : List Row := [(row3 462 235 235), (row3 462 253 253), (row3 229 226 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_08_rows b075_08_labels 3616774667439071062500000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_08_rows b075_08_labels]
    decide +kernel

def b075_09_rows : List Row := [(row3 13 24 38), (row3 13 24 39), (row3 13 24 40), (row3 13 24 41), (row3 13 24 42), (row3 13 24 43), (row3 13 24 44), (row3 13 24 45), (row3 13 24 46), (row3 13 24 47), (row3 13 24 48), (row3 13 24 49), (row3 13 24 50), (row3 13 24 51), (row3 13 24 52), (row3 13 24 53)]

def b075_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_09_rows b075_09_labels 94422265631746822932000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_09_rows b075_09_labels]
    decide +kernel

def b075_10_rows : List Row := [(row3 13 24 54), (row3 13 24 55), (row3 13 24 56), (row3 13 24 57), (row3 13 24 58), (row3 13 24 59), (row3 13 24 60), (row3 13 24 61), (row3 13 24 62), (row3 13 24 63), (row3 13 25 26), (row3 13 25 27), (row3 13 25 28), (row3 13 25 29), (row3 13 25 30), (row3 13 25 31)]

def b075_10_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 263 263), (row3 462 236 236), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_10_rows b075_10_labels 20254809394451607163026000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_10_rows b075_10_labels]
    decide +kernel

def b075_11_rows : List Row := [(row3 13 25 32), (row3 13 25 33), (row3 13 25 34), (row3 13 25 35), (row3 13 25 36), (row3 13 25 37), (row3 13 25 38), (row3 13 25 39), (row3 13 25 40), (row3 13 25 41), (row3 13 25 42), (row3 13 25 43), (row3 13 25 44), (row3 13 25 45), (row3 13 25 46), (row3 13 25 47)]

def b075_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_11_rows b075_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_11_rows b075_11_labels]
    decide +kernel

def b075_12_rows : List Row := [(row3 13 25 48), (row3 13 25 49), (row3 13 25 50), (row3 13 25 51), (row3 13 25 52), (row3 13 25 53), (row3 13 25 54), (row3 13 25 55), (row3 13 25 56), (row3 13 25 57), (row3 13 25 58), (row3 13 25 59), (row3 13 25 60), (row3 13 25 61), (row3 13 25 62), (row3 13 25 63)]

def b075_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_12_rows b075_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_12_rows b075_12_labels]
    decide +kernel

def b075_13_rows : List Row := [(row3 13 26 27), (row3 13 26 28), (row3 13 26 29), (row3 13 26 30), (row3 13 26 31), (row3 13 26 32), (row3 13 26 33), (row3 13 26 34), (row3 13 26 35), (row3 13 26 36), (row3 13 26 37), (row3 13 26 38), (row3 13 26 39), (row3 13 26 40), (row3 13 26 41), (row3 13 26 42)]

def b075_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_13_rows b075_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_13_rows b075_13_labels]
    decide +kernel

def b075_14_rows : List Row := [(row3 13 26 43), (row3 13 26 44), (row3 13 26 45), (row3 13 26 46), (row3 13 26 47), (row3 13 26 48), (row3 13 26 49), (row3 13 26 50), (row3 13 26 51), (row3 13 26 52), (row3 13 26 53), (row3 13 26 54), (row3 13 26 55), (row3 13 26 56), (row3 13 26 57), (row3 13 26 58)]

def b075_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_14_rows b075_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_14_rows b075_14_labels]
    decide +kernel

def b075_15_rows : List Row := [(row3 13 26 59), (row3 13 26 60), (row3 13 26 61), (row3 13 26 62), (row3 13 26 63), (row3 13 27 28), (row3 13 27 29), (row3 13 27 30), (row3 13 27 31), (row3 13 27 32), (row3 13 27 33), (row3 13 27 34), (row3 13 27 35), (row3 13 27 36), (row3 13 27 37), (row3 13 27 38)]

def b075_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b075_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b075_15_rows b075_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b075_15_rows b075_15_labels]
    decide +kernel

theorem checked075 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_075 QuarticIntegerComputationalData.ids64_075 27983011062989343029450428500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b075_00_rows ++ b075_01_rows) ++ (b075_02_rows ++ b075_03_rows)) ++ ((b075_04_rows ++ b075_05_rows) ++ (b075_06_rows ++ b075_07_rows))) ++ (((b075_08_rows ++ b075_09_rows) ++ (b075_10_rows ++ b075_11_rows)) ++ ((b075_12_rows ++ b075_13_rows) ++ (b075_14_rows ++ b075_15_rows))))
    ((((b075_00_labels ++ b075_01_labels) ++ (b075_02_labels ++ b075_03_labels)) ++ ((b075_04_labels ++ b075_05_labels) ++ (b075_06_labels ++ b075_07_labels))) ++ (((b075_08_labels ++ b075_09_labels) ++ (b075_10_labels ++ b075_11_labels)) ++ ((b075_12_labels ++ b075_13_labels) ++ (b075_14_labels ++ b075_15_labels)))) 27983011062989343029450428500
  exact ((((b075_00_checked.append (c := 3540391774465036442393248800) b075_01_checked (by decide +kernel)).append (c := 25349149630226277955472959200) (b075_02_checked.append (c := 21808757855761241513079710400) b075_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 27959045056661820604401970500) ((b075_04_checked.append (c := 53654622147722541964438800) b075_05_checked (by decide +kernel)).append (c := 2609895426435542648929011300) (b075_06_checked.append (c := 2556240804287820106964572500) b075_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 27983011062989343029450428500) (((b075_08_checked.append (c := 3711196933070817885432000) b075_09_checked (by decide +kernel)).append (c := 23966006327522425048458000) (b075_10_checked.append (c := 20254809394451607163026000) b075_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 23966006327522425048458000) ((b075_12_checked.append (c := 0) b075_13_checked (by decide +kernel)).append (c := 0) (b075_14_checked.append (c := 0) b075_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b076_00_rows : List Row := [(row3 13 27 39), (row3 13 27 40), (row3 13 27 41), (row3 13 27 42), (row3 13 27 43), (row3 13 27 44), (row3 13 27 45), (row3 13 27 46), (row3 13 27 47), (row3 13 27 48), (row3 13 27 49), (row3 13 27 50), (row3 13 27 51), (row3 13 27 52), (row3 13 27 53), (row3 13 27 54)]

def b076_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_00_rows b076_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_00_rows b076_00_labels]
    decide +kernel

def b076_01_rows : List Row := [(row3 13 27 55), (row3 13 27 56), (row3 13 27 57), (row3 13 27 58), (row3 13 27 59), (row3 13 27 60), (row3 13 27 61), (row3 13 27 62), (row3 13 27 63), (row3 13 28 29), (row3 13 28 30), (row3 13 28 31), (row3 13 28 32), (row3 13 28 33), (row3 13 28 34), (row3 13 28 35)]

def b076_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_01_rows b076_01_labels 1723209975187130289591000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_01_rows b076_01_labels]
    decide +kernel

def b076_02_rows : List Row := [(row3 13 28 36), (row3 13 28 37), (row3 13 28 38), (row3 13 28 39), (row3 13 28 40), (row3 13 28 41), (row3 13 28 42), (row3 13 28 43), (row3 13 28 44), (row3 13 28 45), (row3 13 28 46), (row3 13 28 47), (row3 13 28 48), (row3 13 28 49), (row3 13 28 50), (row3 13 28 51)]

def b076_02_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_02_rows b076_02_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_02_rows b076_02_labels]
    decide +kernel

def b076_03_rows : List Row := [(row3 13 28 52), (row3 13 28 53), (row3 13 28 54), (row3 13 28 55), (row3 13 28 56), (row3 13 28 57), (row3 13 28 58), (row3 13 28 59), (row3 13 28 60), (row3 13 28 61), (row3 13 28 62), (row3 13 28 63), (row3 13 29 30), (row3 13 29 31), (row3 13 29 32), (row3 13 29 33)]

def b076_03_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_03_rows b076_03_labels 2013814896183017085627000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_03_rows b076_03_labels]
    decide +kernel

def b076_04_rows : List Row := [(row3 13 29 34), (row3 13 29 35), (row3 13 29 36), (row3 13 29 37), (row3 13 29 38), (row3 13 29 39), (row3 13 29 40), (row3 13 29 41), (row3 13 29 42), (row3 13 29 43), (row3 13 29 44), (row3 13 29 45), (row3 13 29 46), (row3 13 29 47), (row3 13 29 48), (row3 13 29 49)]

def b076_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_04_rows b076_04_labels 555889215118270689432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_04_rows b076_04_labels]
    decide +kernel

def b076_05_rows : List Row := [(row3 13 29 50), (row3 13 29 51), (row3 13 29 52), (row3 13 29 53), (row3 13 29 54), (row3 13 29 55), (row3 13 29 56), (row3 13 29 57), (row3 13 29 58), (row3 13 29 59), (row3 13 29 60), (row3 13 29 61), (row3 13 29 62), (row3 13 29 63), (row3 13 30 31), (row3 13 30 32)]

def b076_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_05_rows b076_05_labels 2847220237229974887355200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_05_rows b076_05_labels]
    decide +kernel

def b076_06_rows : List Row := [(row3 13 30 33), (row3 13 30 34), (row3 13 30 35), (row3 13 30 36), (row3 13 30 37), (row3 13 30 38), (row3 13 30 39), (row3 13 30 40), (row3 13 30 41), (row3 13 30 42), (row3 13 30 43), (row3 13 30 44), (row3 13 30 45), (row3 13 30 46), (row3 13 30 47), (row3 13 30 48)]

def b076_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_06_rows b076_06_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_06_rows b076_06_labels]
    decide +kernel

def b076_07_rows : List Row := [(row3 13 30 49), (row3 13 30 50), (row3 13 30 51), (row3 13 30 52), (row3 13 30 53), (row3 13 30 54), (row3 13 30 55), (row3 13 30 56), (row3 13 30 57), (row3 13 30 58), (row3 13 30 59), (row3 13 30 60), (row3 13 30 61), (row3 13 30 62), (row3 13 30 63), (row3 13 31 32)]

def b076_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462)]

theorem b076_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_07_rows b076_07_labels 346030449920782749778500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_07_rows b076_07_labels]
    decide +kernel

def b076_08_rows : List Row := [(row3 13 31 33), (row3 13 31 34), (row3 13 31 35), (row3 13 31 36), (row3 13 31 37), (row3 13 31 38), (row3 13 31 39), (row3 13 31 40), (row3 13 31 41), (row3 13 31 42), (row3 13 31 43), (row3 13 31 44), (row3 13 31 45), (row3 13 31 46), (row3 13 31 47), (row3 13 31 48)]

def b076_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_08_rows b076_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_08_rows b076_08_labels]
    decide +kernel

def b076_09_rows : List Row := [(row3 13 31 49), (row3 13 31 50), (row3 13 31 51), (row3 13 31 52), (row3 13 31 53), (row3 13 31 54), (row3 13 31 55), (row3 13 31 56), (row3 13 31 57), (row3 13 31 58), (row3 13 31 59), (row3 13 31 60), (row3 13 31 61), (row3 13 31 62), (row3 13 31 63), (row3 13 32 33)]

def b076_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_09_rows b076_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_09_rows b076_09_labels]
    decide +kernel

def b076_10_rows : List Row := [(row3 13 32 34), (row3 13 32 35), (row3 13 32 36), (row3 13 32 37), (row3 13 32 38), (row3 13 32 39), (row3 13 32 40), (row3 13 32 41), (row3 13 32 42), (row3 13 32 43), (row3 13 32 44), (row3 13 32 45), (row3 13 32 46), (row3 13 32 47), (row3 13 32 48), (row3 13 32 49)]

def b076_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_10_rows b076_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_10_rows b076_10_labels]
    decide +kernel

def b076_11_rows : List Row := [(row3 13 32 50), (row3 13 32 51), (row3 13 32 52), (row3 13 32 53), (row3 13 32 54), (row3 13 32 55), (row3 13 32 56), (row3 13 32 57), (row3 13 32 58), (row3 13 32 59), (row3 13 32 60), (row3 13 32 61), (row3 13 32 62), (row3 13 32 63), (row3 13 33 34), (row3 13 33 35)]

def b076_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_11_rows b076_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_11_rows b076_11_labels]
    decide +kernel

def b076_12_rows : List Row := [(row3 13 33 36), (row3 13 33 37), (row3 13 33 38), (row3 13 33 39), (row3 13 33 40), (row3 13 33 41), (row3 13 33 42), (row3 13 33 43), (row3 13 33 44), (row3 13 33 45), (row3 13 33 46), (row3 13 33 47), (row3 13 33 48), (row3 13 33 49), (row3 13 33 50), (row3 13 33 51)]

def b076_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_12_rows b076_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_12_rows b076_12_labels]
    decide +kernel

def b076_13_rows : List Row := [(row3 13 33 52), (row3 13 33 53), (row3 13 33 54), (row3 13 33 55), (row3 13 33 56), (row3 13 33 57), (row3 13 33 58), (row3 13 33 59), (row3 13 33 60), (row3 13 33 61), (row3 13 33 62), (row3 13 33 63), (row3 13 34 35), (row3 13 34 36), (row3 13 34 37), (row3 13 34 38)]

def b076_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_13_rows b076_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_13_rows b076_13_labels]
    decide +kernel

def b076_14_rows : List Row := [(row3 13 34 39), (row3 13 34 40), (row3 13 34 41), (row3 13 34 42), (row3 13 34 43), (row3 13 34 44), (row3 13 34 45), (row3 13 34 46), (row3 13 34 47), (row3 13 34 48), (row3 13 34 49), (row3 13 34 50), (row3 13 34 51), (row3 13 34 52), (row3 13 34 53), (row3 13 34 54)]

def b076_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_14_rows b076_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_14_rows b076_14_labels]
    decide +kernel

def b076_15_rows : List Row := [(row3 13 34 55), (row3 13 34 56), (row3 13 34 57), (row3 13 34 58), (row3 13 34 59), (row3 13 34 60), (row3 13 34 61), (row3 13 34 62), (row3 13 34 63), (row3 13 35 36), (row3 13 35 37), (row3 13 35 38), (row3 13 35 39), (row3 13 35 40), (row3 13 35 41), (row3 13 35 42)]

def b076_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b076_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b076_15_rows b076_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b076_15_rows b076_15_labels]
    decide +kernel

theorem checked076 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_076 QuarticIntegerComputationalData.ids64_076 7518368989266408811073700 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b076_00_rows ++ b076_01_rows) ++ (b076_02_rows ++ b076_03_rows)) ++ ((b076_04_rows ++ b076_05_rows) ++ (b076_06_rows ++ b076_07_rows))) ++ (((b076_08_rows ++ b076_09_rows) ++ (b076_10_rows ++ b076_11_rows)) ++ ((b076_12_rows ++ b076_13_rows) ++ (b076_14_rows ++ b076_15_rows))))
    ((((b076_00_labels ++ b076_01_labels) ++ (b076_02_labels ++ b076_03_labels)) ++ ((b076_04_labels ++ b076_05_labels) ++ (b076_06_labels ++ b076_07_labels))) ++ (((b076_08_labels ++ b076_09_labels) ++ (b076_10_labels ++ b076_11_labels)) ++ ((b076_12_labels ++ b076_13_labels) ++ (b076_14_labels ++ b076_15_labels)))) 7518368989266408811073700
  exact ((((b076_00_checked.append (c := 1723209975187130289591000) b076_01_checked (by decide +kernel)).append (c := 3753126979183763929863000) (b076_02_checked.append (c := 2029917003996633640272000) b076_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 7518368989266408811073700) ((b076_04_checked.append (c := 3403109452348245576787200) b076_05_checked (by decide +kernel)).append (c := 3765242010082644881210700) (b076_06_checked.append (c := 362132557734399304423500) b076_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7518368989266408811073700) (((b076_08_checked.append (c := 0) b076_09_checked (by decide +kernel)).append (c := 0) (b076_10_checked.append (c := 0) b076_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b076_12_checked.append (c := 0) b076_13_checked (by decide +kernel)).append (c := 0) (b076_14_checked.append (c := 0) b076_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b077_00_rows : List Row := [(row3 13 35 43), (row3 13 35 44), (row3 13 35 45), (row3 13 35 46), (row3 13 35 47), (row3 13 35 48), (row3 13 35 49), (row3 13 35 50), (row3 13 35 51), (row3 13 35 52), (row3 13 35 53), (row3 13 35 54), (row3 13 35 55), (row3 13 35 56), (row3 13 35 57), (row3 13 35 58)]

def b077_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_00_rows b077_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_00_rows b077_00_labels]
    decide +kernel

def b077_01_rows : List Row := [(row3 13 35 59), (row3 13 35 60), (row3 13 35 61), (row3 13 35 62), (row3 13 35 63), (row3 13 36 37), (row3 13 36 38), (row3 13 36 39), (row3 13 36 40), (row3 13 36 41), (row3 13 36 42), (row3 13 36 43), (row3 13 36 44), (row3 13 36 45), (row3 13 36 46), (row3 13 36 47)]

def b077_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_01_rows b077_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_01_rows b077_01_labels]
    decide +kernel

def b077_02_rows : List Row := [(row3 13 36 48), (row3 13 36 49), (row3 13 36 50), (row3 13 36 51), (row3 13 36 52), (row3 13 36 53), (row3 13 36 54), (row3 13 36 55), (row3 13 36 56), (row3 13 36 57), (row3 13 36 58), (row3 13 36 59), (row3 13 36 60), (row3 13 36 61), (row3 13 36 62), (row3 13 36 63)]

def b077_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_02_rows b077_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_02_rows b077_02_labels]
    decide +kernel

def b077_03_rows : List Row := [(row3 13 37 38), (row3 13 37 39), (row3 13 37 40), (row3 13 37 41), (row3 13 37 42), (row3 13 37 43), (row3 13 37 44), (row3 13 37 45), (row3 13 37 46), (row3 13 37 47), (row3 13 37 48), (row3 13 37 49), (row3 13 37 50), (row3 13 37 51), (row3 13 37 52), (row3 13 37 53)]

def b077_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241)]

theorem b077_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_03_rows b077_03_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_03_rows b077_03_labels]
    decide +kernel

def b077_04_rows : List Row := [(row3 13 37 54), (row3 13 37 55), (row3 13 37 56), (row3 13 37 57), (row3 13 37 58), (row3 13 37 59), (row3 13 37 60), (row3 13 37 61), (row3 13 37 62), (row3 13 37 63), (row3 13 38 39), (row3 13 38 40), (row3 13 38 41), (row3 13 38 42), (row3 13 38 43), (row3 13 38 44)]

def b077_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 238 236 238), (row3 462 247 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_04_rows b077_04_labels 211944822321398435649000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_04_rows b077_04_labels]
    decide +kernel

def b077_05_rows : List Row := [(row3 13 38 45), (row3 13 38 46), (row3 13 38 47), (row3 13 38 48), (row3 13 38 49), (row3 13 38 50), (row3 13 38 51), (row3 13 38 52), (row3 13 38 53), (row3 13 38 54), (row3 13 38 55), (row3 13 38 56), (row3 13 38 57), (row3 13 38 58), (row3 13 38 59), (row3 13 38 60)]

def b077_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_05_rows b077_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_05_rows b077_05_labels]
    decide +kernel

def b077_06_rows : List Row := [(row3 13 38 61), (row3 13 38 62), (row3 13 38 63), (row3 13 39 40), (row3 13 39 41), (row3 13 39 42), (row3 13 39 43), (row3 13 39 44), (row3 13 39 45), (row3 13 39 46), (row3 13 39 47), (row3 13 39 48), (row3 13 39 49), (row3 13 39 50), (row3 13 39 51), (row3 13 39 52)]

def b077_06_labels : List Row := [(row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_06_rows b077_06_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_06_rows b077_06_labels]
    decide +kernel

def b077_07_rows : List Row := [(row3 13 39 53), (row3 13 39 54), (row3 13 39 55), (row3 13 39 56), (row3 13 39 57), (row3 13 39 58), (row3 13 39 59), (row3 13 39 60), (row3 13 39 61), (row3 13 39 62), (row3 13 39 63), (row3 13 40 41), (row3 13 40 42), (row3 13 40 43), (row3 13 40 44), (row3 13 40 45)]

def b077_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_07_rows b077_07_labels 413010417905223503607000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_07_rows b077_07_labels]
    decide +kernel

def b077_08_rows : List Row := [(row3 13 40 46), (row3 13 40 47), (row3 13 40 48), (row3 13 40 49), (row3 13 40 50), (row3 13 40 51), (row3 13 40 52), (row3 13 40 53), (row3 13 40 54), (row3 13 40 55), (row3 13 40 56), (row3 13 40 57), (row3 13 40 58), (row3 13 40 59), (row3 13 40 60), (row3 13 40 61)]

def b077_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 263 263), (row3 462 236 236), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_08_rows b077_08_labels 21050331293281423085070000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_08_rows b077_08_labels]
    decide +kernel

def b077_09_rows : List Row := [(row3 13 40 62), (row3 13 40 63), (row3 13 41 42), (row3 13 41 43), (row3 13 41 44), (row3 13 41 45), (row3 13 41 46), (row3 13 41 47), (row3 13 41 48), (row3 13 41 49), (row3 13 41 50), (row3 13 41 51), (row3 13 41 52), (row3 13 41 53), (row3 13 41 54), (row3 13 41 55)]

def b077_09_labels : List Row := [(row3 462 250 250), (row3 228 236 225), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_09_rows b077_09_labels 1543077781470324102991500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_09_rows b077_09_labels]
    decide +kernel

def b077_10_rows : List Row := [(row3 13 41 56), (row3 13 41 57), (row3 13 41 58), (row3 13 41 59), (row3 13 41 60), (row3 13 41 61), (row3 13 41 62), (row3 13 41 63), (row3 13 42 43), (row3 13 42 44), (row3 13 42 45), (row3 13 42 46), (row3 13 42 47), (row3 13 42 48), (row3 13 42 49), (row3 13 42 50)]

def b077_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_10_rows b077_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_10_rows b077_10_labels]
    decide +kernel

def b077_11_rows : List Row := [(row3 13 42 51), (row3 13 42 52), (row3 13 42 53), (row3 13 42 54), (row3 13 42 55), (row3 13 42 56), (row3 13 42 57), (row3 13 42 58), (row3 13 42 59), (row3 13 42 60), (row3 13 42 61), (row3 13 42 62), (row3 13 42 63), (row3 13 43 44), (row3 13 43 45), (row3 13 43 46)]

def b077_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_11_rows b077_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_11_rows b077_11_labels]
    decide +kernel

def b077_12_rows : List Row := [(row3 13 43 47), (row3 13 43 48), (row3 13 43 49), (row3 13 43 50), (row3 13 43 51), (row3 13 43 52), (row3 13 43 53), (row3 13 43 54), (row3 13 43 55), (row3 13 43 56), (row3 13 43 57), (row3 13 43 58), (row3 13 43 59), (row3 13 43 60), (row3 13 43 61), (row3 13 43 62)]

def b077_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_12_rows b077_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_12_rows b077_12_labels]
    decide +kernel

def b077_13_rows : List Row := [(row3 13 43 63), (row3 13 44 45), (row3 13 44 46), (row3 13 44 47), (row3 13 44 48), (row3 13 44 49), (row3 13 44 50), (row3 13 44 51), (row3 13 44 52), (row3 13 44 53), (row3 13 44 54), (row3 13 44 55), (row3 13 44 56), (row3 13 44 57), (row3 13 44 58), (row3 13 44 59)]

def b077_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_13_rows b077_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_13_rows b077_13_labels]
    decide +kernel

def b077_14_rows : List Row := [(row3 13 44 60), (row3 13 44 61), (row3 13 44 62), (row3 13 44 63), (row3 13 45 46), (row3 13 45 47), (row3 13 45 48), (row3 13 45 49), (row3 13 45 50), (row3 13 45 51), (row3 13 45 52), (row3 13 45 53), (row3 13 45 54), (row3 13 45 55), (row3 13 45 56), (row3 13 45 57)]

def b077_14_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_14_rows b077_14_labels 301066359412777219228500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_14_rows b077_14_labels]
    decide +kernel

def b077_15_rows : List Row := [(row3 13 45 58), (row3 13 45 59), (row3 13 45 60), (row3 13 45 61), (row3 13 45 62), (row3 13 45 63), (row3 13 46 47), (row3 13 46 48), (row3 13 46 49), (row3 13 46 50), (row3 13 46 51), (row3 13 46 52), (row3 13 46 53), (row3 13 46 54), (row3 13 46 55), (row3 13 46 56)]

def b077_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 261 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b077_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b077_15_rows b077_15_labels 3188107204239935288077200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b077_15_rows b077_15_labels]
    decide +kernel

theorem checked077 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_077 QuarticIntegerComputationalData.ids64_077 27035538320613485096218200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b077_00_rows ++ b077_01_rows) ++ (b077_02_rows ++ b077_03_rows)) ++ ((b077_04_rows ++ b077_05_rows) ++ (b077_06_rows ++ b077_07_rows))) ++ (((b077_08_rows ++ b077_09_rows) ++ (b077_10_rows ++ b077_11_rows)) ++ ((b077_12_rows ++ b077_13_rows) ++ (b077_14_rows ++ b077_15_rows))))
    ((((b077_00_labels ++ b077_01_labels) ++ (b077_02_labels ++ b077_03_labels)) ++ ((b077_04_labels ++ b077_05_labels) ++ (b077_06_labels ++ b077_07_labels))) ++ (((b077_08_labels ++ b077_09_labels) ++ (b077_10_labels ++ b077_11_labels)) ++ ((b077_12_labels ++ b077_13_labels) ++ (b077_14_labels ++ b077_15_labels)))) 27035538320613485096218200
  exact ((((b077_00_checked.append (c := 0) b077_01_checked (by decide +kernel)).append (c := 3625367732518643295000) (b077_02_checked.append (c := 3625367732518643295000) b077_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 952955682209025400851000) ((b077_04_checked.append (c := 211944822321398435649000) b077_05_checked (by decide +kernel)).append (c := 949330314476506757556000) (b077_06_checked.append (c := 737385492155108321907000) b077_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 27035538320613485096218200) (((b077_08_checked.append (c := 22593409074751747188061500) b077_09_checked (by decide +kernel)).append (c := 22593409074751747188061500) (b077_10_checked.append (c := 0) b077_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 26082582638404459695367200) ((b077_12_checked.append (c := 0) b077_13_checked (by decide +kernel)).append (c := 3489173563652712507305700) (b077_14_checked.append (c := 3489173563652712507305700) b077_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b078_00_rows : List Row := [(row3 13 46 57), (row3 13 46 58), (row3 13 46 59), (row3 13 46 60), (row3 13 46 61), (row3 13 46 62), (row3 13 46 63), (row3 13 47 48), (row3 13 47 49), (row3 13 47 50), (row3 13 47 51), (row3 13 47 52), (row3 13 47 53), (row3 13 47 54), (row3 13 47 55), (row3 13 47 56)]

def b078_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b078_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_00_rows b078_00_labels 11721743532018499266061200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_00_rows b078_00_labels]
    decide +kernel

def b078_01_rows : List Row := [(row3 13 47 57), (row3 13 47 58), (row3 13 47 59), (row3 13 47 60), (row3 13 47 61), (row3 13 47 62), (row3 13 47 63), (row3 13 48 49), (row3 13 48 50), (row3 13 48 51), (row3 13 48 52), (row3 13 48 53), (row3 13 48 54), (row3 13 48 55), (row3 13 48 56), (row3 13 48 57)]

def b078_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 278 462 278), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 193 193), (row3 462 273 273)]

theorem b078_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_01_rows b078_01_labels 526566611486923214921557200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_01_rows b078_01_labels]
    decide +kernel

def b078_02_rows : List Row := [(row3 13 48 58), (row3 13 48 59), (row3 13 48 60), (row3 13 48 61), (row3 13 48 62), (row3 13 48 63), (row3 13 49 50), (row3 13 49 51), (row3 13 49 52), (row3 13 49 53), (row3 13 49 54), (row3 13 49 55), (row3 13 49 56), (row3 13 49 57), (row3 13 49 58), (row3 13 49 59)]

def b078_02_labels : List Row := [(row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 222 222), (row3 295 273 304), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 284 284), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462)]

theorem b078_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_02_rows b078_02_labels 101186006747149090567521000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_02_rows b078_02_labels]
    decide +kernel

def b078_03_rows : List Row := [(row3 13 49 60), (row3 13 49 61), (row3 13 49 62), (row3 13 49 63), (row3 13 50 51), (row3 13 50 52), (row3 13 50 53), (row3 13 50 54), (row3 13 50 55), (row3 13 50 56), (row3 13 50 57), (row3 13 50 58), (row3 13 50 59), (row3 13 50 60), (row3 13 50 61), (row3 13 50 62)]

def b078_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 251 251), (row3 228 232 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b078_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_03_rows b078_03_labels 2149879557373509968910000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_03_rows b078_03_labels]
    decide +kernel

def b078_04_rows : List Row := [(row3 13 50 63), (row3 13 51 52), (row3 13 51 53), (row3 13 51 54), (row3 13 51 55), (row3 13 51 56), (row3 13 51 57), (row3 13 51 58), (row3 13 51 59), (row3 13 51 60), (row3 13 51 61), (row3 13 51 62), (row3 13 51 63), (row3 13 52 53), (row3 13 52 54), (row3 13 52 55)]

def b078_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b078_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_04_rows b078_04_labels 288068707545866413191000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_04_rows b078_04_labels]
    decide +kernel

def b078_05_rows : List Row := [(row3 13 52 56), (row3 13 52 57), (row3 13 52 58), (row3 13 52 59), (row3 13 52 60), (row3 13 52 61), (row3 13 52 62), (row3 13 52 63), (row3 13 53 54), (row3 13 53 55), (row3 13 53 56), (row3 13 53 57), (row3 13 53 58), (row3 13 53 59), (row3 13 53 60), (row3 13 53 61)]

def b078_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 193 192 238)]

theorem b078_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_05_rows b078_05_labels 354120786265780195514472600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_05_rows b078_05_labels]
    decide +kernel

def b078_06_rows : List Row := [(row3 13 53 62), (row3 13 53 63), (row3 13 54 55), (row3 13 54 56), (row3 13 54 57), (row3 13 54 58), (row3 13 54 59), (row3 13 54 60), (row3 13 54 61), (row3 13 54 62), (row3 13 54 63), (row3 13 55 56), (row3 13 55 57), (row3 13 55 58), (row3 13 55 59), (row3 13 55 60)]

def b078_06_labels : List Row := [(row3 306 310 310), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 131 105 105), (row3 295 462 295), (row3 462 284 284), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462)]

theorem b078_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_06_rows b078_06_labels 2530608333495853375353871800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_06_rows b078_06_labels]
    decide +kernel

def b078_07_rows : List Row := [(row3 13 55 61), (row3 13 55 62), (row3 13 55 63), (row3 13 56 57), (row3 13 56 58), (row3 13 56 59), (row3 13 56 60), (row3 13 56 61), (row3 13 56 62), (row3 13 56 63), (row3 13 57 58), (row3 13 57 59), (row3 13 57 60), (row3 13 57 61), (row3 13 57 62), (row3 13 57 63)]

def b078_07_labels : List Row := [(row3 235 235 462), (row3 306 312 312), (row3 139 232 138), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 289 305 305), (row3 139 163 124), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 226 226), (row3 278 288 300)]

theorem b078_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_07_rows b078_07_labels 5151923815445541066375405000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_07_rows b078_07_labels]
    decide +kernel

def b078_08_rows : List Row := [(row3 13 58 59), (row3 13 58 60), (row3 13 58 61), (row3 13 58 62), (row3 13 58 63), (row3 13 59 60), (row3 13 59 61), (row3 13 59 62), (row3 13 59 63), (row3 13 60 61), (row3 13 60 62), (row3 13 60 63), (row3 13 61 62), (row3 13 61 63), (row3 13 62 63), (row3 14 15 16)]

def b078_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 248 248), (row3 235 232 228), (row3 462 462 462), (row3 261 261 462), (row3 234 234 234), (row3 462 462 462), (row3 193 191 235), (row3 289 292 292), (row3 235 462 235), (row3 369 85 121), (row3 288 462 288), (row3 398 81 134), (row3 33 33 38)]

theorem b078_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_08_rows b078_08_labels 1633953046341067737717441822300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_08_rows b078_08_labels]
    decide +kernel

def b078_09_rows : List Row := [(row3 14 15 17), (row3 14 15 18), (row3 14 15 19), (row3 14 15 20), (row3 14 15 21), (row3 14 15 22), (row3 14 15 23), (row3 14 15 24), (row3 14 15 25), (row3 14 15 26), (row3 14 15 27), (row3 14 15 28), (row3 14 15 29), (row3 14 15 30), (row3 14 15 31), (row3 14 15 32)]

def b078_09_labels : List Row := [(row3 416 408 396), (row3 228 160 163), (row3 284 462 284), (row3 83 157 399), (row3 437 412 39), (row3 25 32 452), (row3 456 458 456), (row3 415 407 395), (row3 232 138 139), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 83 135 398), (row3 431 410 59), (row3 49 52 62), (row3 235 162 163)]

theorem b078_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_09_rows b078_09_labels 33098115067190263707741028668900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_09_rows b078_09_labels]
    decide +kernel

def b078_10_rows : List Row := [(row3 14 15 33), (row3 14 15 34), (row3 14 15 35), (row3 14 15 36), (row3 14 15 37), (row3 14 15 38), (row3 14 15 39), (row3 14 15 40), (row3 14 15 41), (row3 14 15 42), (row3 14 15 43), (row3 14 15 44), (row3 14 15 45), (row3 14 15 46), (row3 14 15 47), (row3 14 15 48)]

def b078_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 91 159 356), (row3 373 365 352), (row3 279 278 279), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 232 189 193), (row3 137 126 127)]

theorem b078_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_10_rows b078_10_labels 26024046004827865475063094630 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_10_rows b078_10_labels]
    decide +kernel

def b078_11_rows : List Row := [(row3 14 15 49), (row3 14 15 50), (row3 14 15 51), (row3 14 15 52), (row3 14 15 53), (row3 14 15 54), (row3 14 15 55), (row3 14 15 56), (row3 14 15 57), (row3 14 15 58), (row3 14 15 59), (row3 14 15 60), (row3 14 15 61), (row3 14 15 62), (row3 14 15 63), (row3 14 16 17)]

def b078_11_labels : List Row := [(row3 309 306 309), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 89 158 356), (row3 376 366 354), (row3 424 422 418), (row3 113 100 100), (row3 309 306 309), (row3 232 232 462), (row3 293 462 293), (row3 81 134 398), (row3 432 411 60), (row3 48 50 61), (row3 362 388 392)]

theorem b078_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_11_rows b078_11_labels 5696357875002618631898147398740 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_11_rows b078_11_labels]
    decide +kernel

def b078_12_rows : List Row := [(row3 14 16 18), (row3 14 16 19), (row3 14 16 20), (row3 14 16 21), (row3 14 16 22), (row3 14 16 23), (row3 14 16 24), (row3 14 16 25), (row3 14 16 26), (row3 14 16 27), (row3 14 16 28), (row3 14 16 29), (row3 14 16 30), (row3 14 16 31), (row3 14 16 32), (row3 14 16 33)]

def b078_12_labels : List Row := [(row3 182 182 178), (row3 268 265 268), (row3 224 223 223), (row3 318 315 318), (row3 108 367 84), (row3 60 411 432), (row3 363 386 393), (row3 144 147 137), (row3 291 289 291), (row3 462 235 235), (row3 248 462 248), (row3 224 222 222), (row3 313 306 313), (row3 141 142 136), (row3 183 183 178), (row3 291 289 291)]

theorem b078_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_12_rows b078_12_labels 287260032207589305784815963690 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_12_rows b078_12_labels]
    decide +kernel

def b078_13_rows : List Row := [(row3 14 16 34), (row3 14 16 35), (row3 14 16 36), (row3 14 16 37), (row3 14 16 38), (row3 14 16 39), (row3 14 16 40), (row3 14 16 41), (row3 14 16 42), (row3 14 16 43), (row3 14 16 44), (row3 14 16 45), (row3 14 16 46), (row3 14 16 47), (row3 14 16 48), (row3 14 16 49)]

def b078_13_labels : List Row := [(row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 228 228), (row3 292 289 292), (row3 281 278 281), (row3 235 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 232 235), (row3 178 183 183), (row3 291 289 291)]

theorem b078_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_13_rows b078_13_labels 142667587395723521439415260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_13_rows b078_13_labels]
    decide +kernel

def b078_14_rows : List Row := [(row3 14 16 50), (row3 14 16 51), (row3 14 16 52), (row3 14 16 53), (row3 14 16 54), (row3 14 16 55), (row3 14 16 56), (row3 14 16 57), (row3 14 16 58), (row3 14 16 59), (row3 14 16 60), (row3 14 16 61), (row3 14 16 62), (row3 14 16 63), (row3 14 17 18), (row3 14 17 19)]

def b078_14_labels : List Row := [(row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 228 228 234), (row3 292 289 292), (row3 393 386 363), (row3 137 147 144), (row3 291 289 291), (row3 235 235 462), (row3 248 462 248), (row3 222 222 224), (row3 313 306 313), (row3 136 142 141), (row3 287 287 462), (row3 235 235 462)]

theorem b078_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_14_rows b078_14_labels 24749705227935690736999444530 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_14_rows b078_14_labels]
    decide +kernel

def b078_15_rows : List Row := [(row3 14 17 20), (row3 14 17 21), (row3 14 17 22), (row3 14 17 23), (row3 14 17 24), (row3 14 17 25), (row3 14 17 26), (row3 14 17 27), (row3 14 17 28), (row3 14 17 29), (row3 14 17 30), (row3 14 17 31), (row3 14 17 32), (row3 14 17 33), (row3 14 17 34), (row3 14 17 35)]

def b078_15_labels : List Row := [(row3 247 247 462), (row3 232 232 462), (row3 260 173 10), (row3 142 141 136), (row3 224 226 229), (row3 286 286 462), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 253 253 462), (row3 248 248 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462)]

theorem b078_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b078_15_rows b078_15_labels 1316348286841511143036561800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b078_15_rows b078_15_labels]
    decide +kernel

theorem checked078 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_078 QuarticIntegerComputationalData.ids64_078 40776597353093778358836353359650 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b078_00_rows ++ b078_01_rows) ++ (b078_02_rows ++ b078_03_rows)) ++ ((b078_04_rows ++ b078_05_rows) ++ (b078_06_rows ++ b078_07_rows))) ++ (((b078_08_rows ++ b078_09_rows) ++ (b078_10_rows ++ b078_11_rows)) ++ ((b078_12_rows ++ b078_13_rows) ++ (b078_14_rows ++ b078_15_rows))))
    ((((b078_00_labels ++ b078_01_labels) ++ (b078_02_labels ++ b078_03_labels)) ++ ((b078_04_labels ++ b078_05_labels) ++ (b078_06_labels ++ b078_07_labels))) ++ (((b078_08_labels ++ b078_09_labels) ++ (b078_10_labels ++ b078_11_labels)) ++ ((b078_12_labels ++ b078_13_labels) ++ (b078_14_labels ++ b078_15_labels)))) 40776597353093778358836353359650
  exact ((((b078_00_checked.append (c := 538288355018941714187618400) b078_01_checked (by decide +kernel)).append (c := 641624241323464314724049400) (b078_02_checked.append (c := 103335886304522600536431000) b078_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 8678565245238184818380989800) ((b078_04_checked.append (c := 354408854973326061927663600) b078_05_checked (by decide +kernel)).append (c := 8036941003914720503656940400) (b078_06_checked.append (c := 7682532148941394441729276800) b078_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 40776597353093778358836353359650) (((b078_08_checked.append (c := 34732068113531331445458470491200) b078_09_checked (by decide +kernel)).append (c := 40454450034538777942831680984570) (b078_10_checked.append (c := 5722381921007446497373210493370) b078_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 40767918787848540174017972369850) ((b078_12_checked.append (c := 287402699794985029306255378950) b078_13_checked (by decide +kernel)).append (c := 313468753309762231186291385280) (b078_14_checked.append (c := 26066053514777201880036006330) b078_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b079_00_rows : List Row := [(row3 14 17 36), (row3 14 17 37), (row3 14 17 38), (row3 14 17 39), (row3 14 17 40), (row3 14 17 41), (row3 14 17 42), (row3 14 17 43), (row3 14 17 44), (row3 14 17 45), (row3 14 17 46), (row3 14 17 47), (row3 14 17 48), (row3 14 17 49), (row3 14 17 50), (row3 14 17 51)]

def b079_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 234 234 234), (row3 247 247 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 291 291 289), (row3 224 224 224), (row3 248 248 462), (row3 462 462 462)]

theorem b079_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_00_rows b079_00_labels 11752947789773893650191700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_00_rows b079_00_labels]
    decide +kernel

def b079_01_rows : List Row := [(row3 14 17 52), (row3 14 17 53), (row3 14 17 54), (row3 14 17 55), (row3 14 17 56), (row3 14 17 57), (row3 14 17 58), (row3 14 17 59), (row3 14 17 60), (row3 14 17 61), (row3 14 17 62), (row3 14 17 63), (row3 14 18 19), (row3 14 18 20), (row3 14 18 21), (row3 14 18 22)]

def b079_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 250 250 462), (row3 224 224 224), (row3 105 105 131), (row3 310 310 306), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 251 251 462), (row3 222 222 224), (row3 312 312 306), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_01_rows b079_01_labels 2475648174207550225692284100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_01_rows b079_01_labels]
    decide +kernel

def b079_02_rows : List Row := [(row3 14 18 23), (row3 14 18 24), (row3 14 18 25), (row3 14 18 26), (row3 14 18 27), (row3 14 18 28), (row3 14 18 29), (row3 14 18 30), (row3 14 18 31), (row3 14 18 32), (row3 14 18 33), (row3 14 18 34), (row3 14 18 35), (row3 14 18 36), (row3 14 18 37), (row3 14 18 38)]

def b079_02_labels : List Row := [(row3 283 278 283), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_02_rows b079_02_labels 10337449296235878350621100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_02_rows b079_02_labels]
    decide +kernel

def b079_03_rows : List Row := [(row3 14 18 39), (row3 14 18 40), (row3 14 18 41), (row3 14 18 42), (row3 14 18 43), (row3 14 18 44), (row3 14 18 45), (row3 14 18 46), (row3 14 18 47), (row3 14 18 48), (row3 14 18 49), (row3 14 18 50), (row3 14 18 51), (row3 14 18 52), (row3 14 18 53), (row3 14 18 54)]

def b079_03_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_03_rows b079_03_labels 443593211854154476374000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_03_rows b079_03_labels]
    decide +kernel

def b079_04_rows : List Row := [(row3 14 18 55), (row3 14 18 56), (row3 14 18 57), (row3 14 18 58), (row3 14 18 59), (row3 14 18 60), (row3 14 18 61), (row3 14 18 62), (row3 14 18 63), (row3 14 19 20), (row3 14 19 21), (row3 14 19 22), (row3 14 19 23), (row3 14 19 24), (row3 14 19 25), (row3 14 19 26)]

def b079_04_labels : List Row := [(row3 248 462 248), (row3 293 462 293), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 246 246 462), (row3 232 232 462), (row3 258 172 10), (row3 232 228 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_04_rows b079_04_labels 607968570502467425653789500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_04_rows b079_04_labels]
    decide +kernel

def b079_05_rows : List Row := [(row3 14 19 27), (row3 14 19 28), (row3 14 19 29), (row3 14 19 30), (row3 14 19 31), (row3 14 19 32), (row3 14 19 33), (row3 14 19 34), (row3 14 19 35), (row3 14 19 36), (row3 14 19 37), (row3 14 19 38), (row3 14 19 39), (row3 14 19 40), (row3 14 19 41), (row3 14 19 42)]

def b079_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_05_rows b079_05_labels 329263235914778383491000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_05_rows b079_05_labels]
    decide +kernel

def b079_06_rows : List Row := [(row3 14 19 43), (row3 14 19 44), (row3 14 19 45), (row3 14 19 46), (row3 14 19 47), (row3 14 19 48), (row3 14 19 49), (row3 14 19 50), (row3 14 19 51), (row3 14 19 52), (row3 14 19 53), (row3 14 19 54), (row3 14 19 55), (row3 14 19 56), (row3 14 19 57), (row3 14 19 58)]

def b079_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_06_rows b079_06_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_06_rows b079_06_labels]
    decide +kernel

def b079_07_rows : List Row := [(row3 14 19 59), (row3 14 19 60), (row3 14 19 61), (row3 14 19 62), (row3 14 19 63), (row3 14 20 21), (row3 14 20 22), (row3 14 20 23), (row3 14 20 24), (row3 14 20 25), (row3 14 20 26), (row3 14 20 27), (row3 14 20 28), (row3 14 20 29), (row3 14 20 30), (row3 14 20 31)]

def b079_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 309 306 309), (row3 114 368 86), (row3 320 319 320), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 291 289 291), (row3 224 224 224)]

theorem b079_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_07_rows b079_07_labels 10245679553582820921865415400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_07_rows b079_07_labels]
    decide +kernel

def b079_08_rows : List Row := [(row3 14 20 32), (row3 14 20 33), (row3 14 20 34), (row3 14 20 35), (row3 14 20 36), (row3 14 20 37), (row3 14 20 38), (row3 14 20 39), (row3 14 20 40), (row3 14 20 41), (row3 14 20 42), (row3 14 20 43), (row3 14 20 44), (row3 14 20 45), (row3 14 20 46), (row3 14 20 47)]

def b079_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462)]

theorem b079_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_08_rows b079_08_labels 396902457862625968987500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_08_rows b079_08_labels]
    decide +kernel

def b079_09_rows : List Row := [(row3 14 20 48), (row3 14 20 49), (row3 14 20 50), (row3 14 20 51), (row3 14 20 52), (row3 14 20 53), (row3 14 20 54), (row3 14 20 55), (row3 14 20 56), (row3 14 20 57), (row3 14 20 58), (row3 14 20 59), (row3 14 20 60), (row3 14 20 61), (row3 14 20 62), (row3 14 20 63)]

def b079_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 291 289 291), (row3 224 224 224)]

theorem b079_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_09_rows b079_09_labels 18226279721309964102124200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_09_rows b079_09_labels]
    decide +kernel

def b079_10_rows : List Row := [(row3 14 21 22), (row3 14 21 23), (row3 14 21 24), (row3 14 21 25), (row3 14 21 26), (row3 14 21 27), (row3 14 21 28), (row3 14 21 29), (row3 14 21 30), (row3 14 21 31), (row3 14 21 32), (row3 14 21 33), (row3 14 21 34), (row3 14 21 35), (row3 14 21 36), (row3 14 21 37)]

def b079_10_labels : List Row := [(row3 389 45 436), (row3 98 101 99), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 309 309 306), (row3 137 149 146), (row3 312 312 306), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232)]

theorem b079_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_10_rows b079_10_labels 375967519071241723958819844180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_10_rows b079_10_labels]
    decide +kernel

def b079_11_rows : List Row := [(row3 14 21 38), (row3 14 21 39), (row3 14 21 40), (row3 14 21 41), (row3 14 21 42), (row3 14 21 43), (row3 14 21 44), (row3 14 21 45), (row3 14 21 46), (row3 14 21 47), (row3 14 21 48), (row3 14 21 49), (row3 14 21 50), (row3 14 21 51), (row3 14 21 52), (row3 14 21 53)]

def b079_11_labels : List Row := [(row3 279 279 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232)]

theorem b079_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_11_rows b079_11_labels 12501536993863562860239600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_11_rows b079_11_labels]
    decide +kernel

def b079_12_rows : List Row := [(row3 14 21 54), (row3 14 21 55), (row3 14 21 56), (row3 14 21 57), (row3 14 21 58), (row3 14 21 59), (row3 14 21 60), (row3 14 21 61), (row3 14 21 62), (row3 14 21 63), (row3 14 22 23), (row3 14 22 24), (row3 14 22 25), (row3 14 22 26), (row3 14 22 27), (row3 14 22 28)]

def b079_12_labels : List Row := [(row3 279 279 278), (row3 232 462 232), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 310 310 306), (row3 137 147 144), (row3 309 309 306), (row3 46 440 46), (row3 216 11 119), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 215 11 118)]

theorem b079_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_12_rows b079_12_labels 928783472934989059933858074360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_12_rows b079_12_labels]
    decide +kernel

def b079_13_rows : List Row := [(row3 14 22 29), (row3 14 22 30), (row3 14 22 31), (row3 14 22 32), (row3 14 22 33), (row3 14 22 34), (row3 14 22 35), (row3 14 22 36), (row3 14 22 37), (row3 14 22 38), (row3 14 22 39), (row3 14 22 40), (row3 14 22 41), (row3 14 22 42), (row3 14 22 43), (row3 14 22 44)]

def b079_13_labels : List Row := [(row3 135 83 398), (row3 181 435 42), (row3 134 81 398), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 214 11 117), (row3 211 88 370), (row3 214 11 117), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_13_rows b079_13_labels 397537765020962513724219507450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_13_rows b079_13_labels]
    decide +kernel

def b079_14_rows : List Row := [(row3 14 22 45), (row3 14 22 46), (row3 14 22 47), (row3 14 22 48), (row3 14 22 49), (row3 14 22 50), (row3 14 22 51), (row3 14 22 52), (row3 14 22 53), (row3 14 22 54), (row3 14 22 55), (row3 14 22 56), (row3 14 22 57), (row3 14 22 58), (row3 14 22 59), (row3 14 22 60)]

def b079_14_labels : List Row := [(row3 462 462 462), (row3 218 10 170), (row3 462 462 462), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 154 154 180), (row3 287 462 287), (row3 316 462 316), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 293 462 293)]

theorem b079_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_14_rows b079_14_labels 14854457753968434084048183750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_14_rows b079_14_labels]
    decide +kernel

def b079_15_rows : List Row := [(row3 14 22 61), (row3 14 22 62), (row3 14 22 63), (row3 14 23 24), (row3 14 23 25), (row3 14 23 26), (row3 14 23 27), (row3 14 23 28), (row3 14 23 29), (row3 14 23 30), (row3 14 23 31), (row3 14 23 32), (row3 14 23 33), (row3 14 23 34), (row3 14 23 35), (row3 14 23 36)]

def b079_15_labels : List Row := [(row3 105 105 131), (row3 393 386 363), (row3 102 103 129), (row3 120 112 120), (row3 312 312 306), (row3 462 232 232), (row3 462 462 462), (row3 228 232 223), (row3 322 322 321), (row3 99 98 101), (row3 396 416 408), (row3 311 311 306), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b079_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b079_15_rows b079_15_labels 97434351502191426774539261340 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b079_15_rows b079_15_labels]
    decide +kernel

theorem checked079 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_079 QuarticIntegerComputationalData.ids64_079 1827960858214453168809726114180 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b079_00_rows ++ b079_01_rows) ++ (b079_02_rows ++ b079_03_rows)) ++ ((b079_04_rows ++ b079_05_rows) ++ (b079_06_rows ++ b079_07_rows))) ++ (((b079_08_rows ++ b079_09_rows) ++ (b079_10_rows ++ b079_11_rows)) ++ ((b079_12_rows ++ b079_13_rows) ++ (b079_14_rows ++ b079_15_rows))))
    ((((b079_00_labels ++ b079_01_labels) ++ (b079_02_labels ++ b079_03_labels)) ++ ((b079_04_labels ++ b079_05_labels) ++ (b079_06_labels ++ b079_07_labels))) ++ (((b079_08_labels ++ b079_09_labels) ++ (b079_10_labels ++ b079_11_labels)) ++ ((b079_12_labels ++ b079_13_labels) ++ (b079_14_labels ++ b079_15_labels)))) 1827960858214453168809726114180
  exact ((((b079_00_checked.append (c := 2487401121997324119342475800) b079_01_checked (by decide +kernel)).append (c := 2498182164505414152169470900) (b079_02_checked.append (c := 10781042508090032826995100) b079_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 13352167211926974181309891800) ((b079_04_checked.append (c := 608297833738382204037280500) b079_05_checked (by decide +kernel)).append (c := 10853985047421560029140420900) (b079_06_checked.append (c := 10245687213683177825103140400) b079_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1827960858214453168809726114180) (((b079_08_checked.append (c := 18623182179172590071111700) b079_09_checked (by decide +kernel)).append (c := 375998643790414760111751195480) (b079_10_checked.append (c := 375980020608235587521680083780) b079_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1814608691002526194628416222380) ((b079_12_checked.append (c := 1326321237955951573658077581810) b079_13_checked (by decide +kernel)).append (c := 1438610047212111434516665026900) (b079_14_checked.append (c := 112288809256159860858587445090) b079_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b080_00_rows : List Row := [(row3 14 23 37), (row3 14 23 38), (row3 14 23 39), (row3 14 23 40), (row3 14 23 41), (row3 14 23 42), (row3 14 23 43), (row3 14 23 44), (row3 14 23 45), (row3 14 23 46), (row3 14 23 47), (row3 14 23 48), (row3 14 23 49), (row3 14 23 50), (row3 14 23 51), (row3 14 23 52)]

def b080_00_labels : List Row := [(row3 232 228 223), (row3 320 320 319), (row3 146 137 143), (row3 234 226 226), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 232 228), (row3 282 282 278), (row3 291 291 289), (row3 224 224 224), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_00_rows b080_00_labels 393058415057437237154051700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_00_rows b080_00_labels]
    decide +kernel

def b080_01_rows : List Row := [(row3 14 23 53), (row3 14 23 54), (row3 14 23 55), (row3 14 23 56), (row3 14 23 57), (row3 14 23 58), (row3 14 23 59), (row3 14 23 60), (row3 14 23 61), (row3 14 23 62), (row3 14 23 63), (row3 14 24 25), (row3 14 24 26), (row3 14 24 27), (row3 14 24 28), (row3 14 24 29)]

def b080_01_labels : List Row := [(row3 232 462 232), (row3 283 283 278), (row3 221 222 220), (row3 102 103 129), (row3 309 309 306), (row3 224 224 224), (row3 246 246 462), (row3 228 462 228), (row3 312 312 306), (row3 136 142 141), (row3 324 324 323), (row3 271 271 462), (row3 237 237 462), (row3 242 242 462), (row3 462 462 462), (row3 249 249 462)]

theorem b080_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_01_rows b080_01_labels 20777901446520952126325188380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_01_rows b080_01_labels]
    decide +kernel

def b080_02_rows : List Row := [(row3 14 24 30), (row3 14 24 31), (row3 14 24 32), (row3 14 24 33), (row3 14 24 34), (row3 14 24 35), (row3 14 24 36), (row3 14 24 37), (row3 14 24 38), (row3 14 24 39), (row3 14 24 40), (row3 14 24 41), (row3 14 24 42), (row3 14 24 43), (row3 14 24 44), (row3 14 24 45)]

def b080_02_labels : List Row := [(row3 232 232 462), (row3 173 260 10), (row3 270 270 462), (row3 235 235 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 235 235 237), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_02_rows b080_02_labels 896285219663704372500325500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_02_rows b080_02_labels]
    decide +kernel

def b080_03_rows : List Row := [(row3 14 24 46), (row3 14 24 47), (row3 14 24 48), (row3 14 24 49), (row3 14 24 50), (row3 14 24 51), (row3 14 24 52), (row3 14 24 53), (row3 14 24 54), (row3 14 24 55), (row3 14 24 56), (row3 14 24 57), (row3 14 24 58), (row3 14 24 59), (row3 14 24 60), (row3 14 24 61)]

def b080_03_labels : List Row := [(row3 462 462 462), (row3 245 245 462), (row3 267 267 265), (row3 234 234 234), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 234 234 234), (row3 154 154 180), (row3 279 279 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 250 250 462)]

theorem b080_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_03_rows b080_03_labels 811044338519706306522894000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_03_rows b080_03_labels]
    decide +kernel

def b080_04_rows : List Row := [(row3 14 24 62), (row3 14 24 63), (row3 14 25 26), (row3 14 25 27), (row3 14 25 28), (row3 14 25 29), (row3 14 25 30), (row3 14 25 31), (row3 14 25 32), (row3 14 25 33), (row3 14 25 34), (row3 14 25 35), (row3 14 25 36), (row3 14 25 37), (row3 14 25 38), (row3 14 25 39)]

def b080_04_labels : List Row := [(row3 228 228 234), (row3 283 283 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_04_rows b080_04_labels 11810422815579987006302100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_04_rows b080_04_labels]
    decide +kernel

def b080_05_rows : List Row := [(row3 14 25 40), (row3 14 25 41), (row3 14 25 42), (row3 14 25 43), (row3 14 25 44), (row3 14 25 45), (row3 14 25 46), (row3 14 25 47), (row3 14 25 48), (row3 14 25 49), (row3 14 25 50), (row3 14 25 51), (row3 14 25 52), (row3 14 25 53), (row3 14 25 54), (row3 14 25 55)]

def b080_05_labels : List Row := [(row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246)]

theorem b080_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_05_rows b080_05_labels 326750194488716009991000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_05_rows b080_05_labels]
    decide +kernel

def b080_06_rows : List Row := [(row3 14 25 56), (row3 14 25 57), (row3 14 25 58), (row3 14 25 59), (row3 14 25 60), (row3 14 25 61), (row3 14 25 62), (row3 14 25 63), (row3 14 26 27), (row3 14 26 28), (row3 14 26 29), (row3 14 26 30), (row3 14 26 31), (row3 14 26 32), (row3 14 26 33), (row3 14 26 34)]

def b080_06_labels : List Row := [(row3 284 462 284), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_06_rows b080_06_labels 61195663017606275734428000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_06_rows b080_06_labels]
    decide +kernel

def b080_07_rows : List Row := [(row3 14 26 35), (row3 14 26 36), (row3 14 26 37), (row3 14 26 38), (row3 14 26 39), (row3 14 26 40), (row3 14 26 41), (row3 14 26 42), (row3 14 26 43), (row3 14 26 44), (row3 14 26 45), (row3 14 26 46), (row3 14 26 47), (row3 14 26 48), (row3 14 26 49), (row3 14 26 50)]

def b080_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_07_rows b080_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_07_rows b080_07_labels]
    decide +kernel

def b080_08_rows : List Row := [(row3 14 26 51), (row3 14 26 52), (row3 14 26 53), (row3 14 26 54), (row3 14 26 55), (row3 14 26 56), (row3 14 26 57), (row3 14 26 58), (row3 14 26 59), (row3 14 26 60), (row3 14 26 61), (row3 14 26 62), (row3 14 26 63), (row3 14 27 28), (row3 14 27 29), (row3 14 27 30)]

def b080_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_08_rows b080_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_08_rows b080_08_labels]
    decide +kernel

def b080_09_rows : List Row := [(row3 14 27 31), (row3 14 27 32), (row3 14 27 33), (row3 14 27 34), (row3 14 27 35), (row3 14 27 36), (row3 14 27 37), (row3 14 27 38), (row3 14 27 39), (row3 14 27 40), (row3 14 27 41), (row3 14 27 42), (row3 14 27 43), (row3 14 27 44), (row3 14 27 45), (row3 14 27 46)]

def b080_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_09_rows b080_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_09_rows b080_09_labels]
    decide +kernel

def b080_10_rows : List Row := [(row3 14 27 47), (row3 14 27 48), (row3 14 27 49), (row3 14 27 50), (row3 14 27 51), (row3 14 27 52), (row3 14 27 53), (row3 14 27 54), (row3 14 27 55), (row3 14 27 56), (row3 14 27 57), (row3 14 27 58), (row3 14 27 59), (row3 14 27 60), (row3 14 27 61), (row3 14 27 62)]

def b080_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_10_rows b080_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_10_rows b080_10_labels]
    decide +kernel

def b080_11_rows : List Row := [(row3 14 27 63), (row3 14 28 29), (row3 14 28 30), (row3 14 28 31), (row3 14 28 32), (row3 14 28 33), (row3 14 28 34), (row3 14 28 35), (row3 14 28 36), (row3 14 28 37), (row3 14 28 38), (row3 14 28 39), (row3 14 28 40), (row3 14 28 41), (row3 14 28 42), (row3 14 28 43)]

def b080_11_labels : List Row := [(row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_11_rows b080_11_labels 2124610920373487296081500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_11_rows b080_11_labels]
    decide +kernel

def b080_12_rows : List Row := [(row3 14 28 44), (row3 14 28 45), (row3 14 28 46), (row3 14 28 47), (row3 14 28 48), (row3 14 28 49), (row3 14 28 50), (row3 14 28 51), (row3 14 28 52), (row3 14 28 53), (row3 14 28 54), (row3 14 28 55), (row3 14 28 56), (row3 14 28 57), (row3 14 28 58), (row3 14 28 59)]

def b080_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b080_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_12_rows b080_12_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_12_rows b080_12_labels]
    decide +kernel

def b080_13_rows : List Row := [(row3 14 28 60), (row3 14 28 61), (row3 14 28 62), (row3 14 28 63), (row3 14 29 30), (row3 14 29 31), (row3 14 29 32), (row3 14 29 33), (row3 14 29 34), (row3 14 29 35), (row3 14 29 36), (row3 14 29 37), (row3 14 29 38), (row3 14 29 39), (row3 14 29 40), (row3 14 29 41)]

def b080_13_labels : List Row := [(row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 248 248 462), (row3 291 289 291), (row3 222 222 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462)]

theorem b080_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_13_rows b080_13_labels 178154445306912694412398200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_13_rows b080_13_labels]
    decide +kernel

def b080_14_rows : List Row := [(row3 14 29 42), (row3 14 29 43), (row3 14 29 44), (row3 14 29 45), (row3 14 29 46), (row3 14 29 47), (row3 14 29 48), (row3 14 29 49), (row3 14 29 50), (row3 14 29 51), (row3 14 29 52), (row3 14 29 53), (row3 14 29 54), (row3 14 29 55), (row3 14 29 56), (row3 14 29 57)]

def b080_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 248 462 248), (row3 462 462 462)]

theorem b080_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_14_rows b080_14_labels 1712520457903044125100000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_14_rows b080_14_labels]
    decide +kernel

def b080_15_rows : List Row := [(row3 14 29 58), (row3 14 29 59), (row3 14 29 60), (row3 14 29 61), (row3 14 29 62), (row3 14 29 63), (row3 14 30 31), (row3 14 30 32), (row3 14 30 33), (row3 14 30 34), (row3 14 30 35), (row3 14 30 36), (row3 14 30 37), (row3 14 30 38), (row3 14 30 39), (row3 14 30 40)]

def b080_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 291 289 291), (row3 224 224 224), (row3 305 305 289), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462)]

theorem b080_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b080_15_rows b080_15_labels 347571879063795367462212300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b080_15_rows b080_15_labels]
    decide +kernel

theorem checked080 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_080 QuarticIntegerComputationalData.ids64_080 23481197201688994969405560180 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b080_00_rows ++ b080_01_rows) ++ (b080_02_rows ++ b080_03_rows)) ++ ((b080_04_rows ++ b080_05_rows) ++ (b080_06_rows ++ b080_07_rows))) ++ (((b080_08_rows ++ b080_09_rows) ++ (b080_10_rows ++ b080_11_rows)) ++ ((b080_12_rows ++ b080_13_rows) ++ (b080_14_rows ++ b080_15_rows))))
    ((((b080_00_labels ++ b080_01_labels) ++ (b080_02_labels ++ b080_03_labels)) ++ ((b080_04_labels ++ b080_05_labels) ++ (b080_06_labels ++ b080_07_labels))) ++ (((b080_08_labels ++ b080_09_labels) ++ (b080_10_labels ++ b080_11_labels)) ++ ((b080_12_labels ++ b080_13_labels) ++ (b080_14_labels ++ b080_15_labels)))) 23481197201688994969405560180
  exact ((((b080_00_checked.append (c := 21170959861578389363479240080) b080_01_checked (by decide +kernel)).append (c := 22878289419761800042502459580) (b080_02_checked.append (c := 1707329558183410679023219500) b080_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 22951622255789475021253180680) ((b080_04_checked.append (c := 12137173010068703016293100) b080_05_checked (by decide +kernel)).append (c := 73332836027674978750721100) (b080_06_checked.append (c := 61195663017606275734428000) b080_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 23481197201688994969405560180) (((b080_08_checked.append (c := 0) b080_09_checked (by decide +kernel)).append (c := 2124610920373487296081500) (b080_10_checked.append (c := 2124610920373487296081500) b080_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 529574945899519948152379500) ((b080_12_checked.append (c := 178165935457448049268985700) b080_13_checked (by decide +kernel)).append (c := 527450334979146460856298000) (b080_14_checked.append (c := 349284399521698411587312300) b080_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
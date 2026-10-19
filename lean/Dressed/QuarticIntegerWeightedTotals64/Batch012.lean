import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch011
import Dressed.QuarticIntegerComputationalData64.Batch012


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b097_00_rows : List Row := [(row3 18 26 41), (row3 18 26 42), (row3 18 26 43), (row3 18 26 44), (row3 18 26 45), (row3 18 26 46), (row3 18 26 47), (row3 18 26 48), (row3 18 26 49), (row3 18 26 50), (row3 18 26 51), (row3 18 26 52), (row3 18 26 53), (row3 18 26 54), (row3 18 26 55), (row3 18 26 56)]

def b097_00_labels : List Row := [(row3 462 462 462), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_00_rows b097_00_labels 30282188517912052206022500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_00_rows b097_00_labels]
    decide +kernel

def b097_01_rows : List Row := [(row3 18 26 57), (row3 18 26 58), (row3 18 26 59), (row3 18 26 60), (row3 18 26 61), (row3 18 26 62), (row3 18 26 63), (row3 18 27 28), (row3 18 27 29), (row3 18 27 30), (row3 18 27 31), (row3 18 27 32), (row3 18 27 33), (row3 18 27 34), (row3 18 27 35), (row3 18 27 36)]

def b097_01_labels : List Row := [(row3 462 462 462), (row3 462 270 270), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 462 278 278), (row3 462 228 228), (row3 462 462 462)]

theorem b097_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_01_rows b097_01_labels 72336296369188231073116200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_01_rows b097_01_labels]
    decide +kernel

def b097_02_rows : List Row := [(row3 18 27 37), (row3 18 27 38), (row3 18 27 39), (row3 18 27 40), (row3 18 27 41), (row3 18 27 42), (row3 18 27 43), (row3 18 27 44), (row3 18 27 45), (row3 18 27 46), (row3 18 27 47), (row3 18 27 48), (row3 18 27 49), (row3 18 27 50), (row3 18 27 51), (row3 18 27 52)]

def b097_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_02_rows b097_02_labels 399678125356471866912000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_02_rows b097_02_labels]
    decide +kernel

def b097_03_rows : List Row := [(row3 18 27 53), (row3 18 27 54), (row3 18 27 55), (row3 18 27 56), (row3 18 27 57), (row3 18 27 58), (row3 18 27 59), (row3 18 27 60), (row3 18 27 61), (row3 18 27 62), (row3 18 27 63), (row3 18 28 29), (row3 18 28 30), (row3 18 28 31), (row3 18 28 32), (row3 18 28 33)]

def b097_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248)]

theorem b097_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_03_rows b097_03_labels 640536516324603009652500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_03_rows b097_03_labels]
    decide +kernel

def b097_04_rows : List Row := [(row3 18 28 34), (row3 18 28 35), (row3 18 28 36), (row3 18 28 37), (row3 18 28 38), (row3 18 28 39), (row3 18 28 40), (row3 18 28 41), (row3 18 28 42), (row3 18 28 43), (row3 18 28 44), (row3 18 28 45), (row3 18 28 46), (row3 18 28 47), (row3 18 28 48), (row3 18 28 49)]

def b097_04_labels : List Row := [(row3 462 234 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_04_rows b097_04_labels 500576762186969365584000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_04_rows b097_04_labels]
    decide +kernel

def b097_05_rows : List Row := [(row3 18 28 50), (row3 18 28 51), (row3 18 28 52), (row3 18 28 53), (row3 18 28 54), (row3 18 28 55), (row3 18 28 56), (row3 18 28 57), (row3 18 28 58), (row3 18 28 59), (row3 18 28 60), (row3 18 28 61), (row3 18 28 62), (row3 18 28 63), (row3 18 29 30), (row3 18 29 31)]

def b097_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_05_rows b097_05_labels 15259712674448416837500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_05_rows b097_05_labels]
    decide +kernel

def b097_06_rows : List Row := [(row3 18 29 32), (row3 18 29 33), (row3 18 29 34), (row3 18 29 35), (row3 18 29 36), (row3 18 29 37), (row3 18 29 38), (row3 18 29 39), (row3 18 29 40), (row3 18 29 41), (row3 18 29 42), (row3 18 29 43), (row3 18 29 44), (row3 18 29 45), (row3 18 29 46), (row3 18 29 47)]

def b097_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_06_rows b097_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_06_rows b097_06_labels]
    decide +kernel

def b097_07_rows : List Row := [(row3 18 29 48), (row3 18 29 49), (row3 18 29 50), (row3 18 29 51), (row3 18 29 52), (row3 18 29 53), (row3 18 29 54), (row3 18 29 55), (row3 18 29 56), (row3 18 29 57), (row3 18 29 58), (row3 18 29 59), (row3 18 29 60), (row3 18 29 61), (row3 18 29 62), (row3 18 29 63)]

def b097_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_07_rows b097_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_07_rows b097_07_labels]
    decide +kernel

def b097_08_rows : List Row := [(row3 18 30 31), (row3 18 30 32), (row3 18 30 33), (row3 18 30 34), (row3 18 30 35), (row3 18 30 36), (row3 18 30 37), (row3 18 30 38), (row3 18 30 39), (row3 18 30 40), (row3 18 30 41), (row3 18 30 42), (row3 18 30 43), (row3 18 30 44), (row3 18 30 45), (row3 18 30 46)]

def b097_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_08_rows b097_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_08_rows b097_08_labels]
    decide +kernel

def b097_09_rows : List Row := [(row3 18 30 47), (row3 18 30 48), (row3 18 30 49), (row3 18 30 50), (row3 18 30 51), (row3 18 30 52), (row3 18 30 53), (row3 18 30 54), (row3 18 30 55), (row3 18 30 56), (row3 18 30 57), (row3 18 30 58), (row3 18 30 59), (row3 18 30 60), (row3 18 30 61), (row3 18 30 62)]

def b097_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_09_rows b097_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_09_rows b097_09_labels]
    decide +kernel

def b097_10_rows : List Row := [(row3 18 30 63), (row3 18 31 32), (row3 18 31 33), (row3 18 31 34), (row3 18 31 35), (row3 18 31 36), (row3 18 31 37), (row3 18 31 38), (row3 18 31 39), (row3 18 31 40), (row3 18 31 41), (row3 18 31 42), (row3 18 31 43), (row3 18 31 44), (row3 18 31 45), (row3 18 31 46)]

def b097_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_10_rows b097_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_10_rows b097_10_labels]
    decide +kernel

def b097_11_rows : List Row := [(row3 18 31 47), (row3 18 31 48), (row3 18 31 49), (row3 18 31 50), (row3 18 31 51), (row3 18 31 52), (row3 18 31 53), (row3 18 31 54), (row3 18 31 55), (row3 18 31 56), (row3 18 31 57), (row3 18 31 58), (row3 18 31 59), (row3 18 31 60), (row3 18 31 61), (row3 18 31 62)]

def b097_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_11_rows b097_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_11_rows b097_11_labels]
    decide +kernel

def b097_12_rows : List Row := [(row3 18 31 63), (row3 18 32 33), (row3 18 32 34), (row3 18 32 35), (row3 18 32 36), (row3 18 32 37), (row3 18 32 38), (row3 18 32 39), (row3 18 32 40), (row3 18 32 41), (row3 18 32 42), (row3 18 32 43), (row3 18 32 44), (row3 18 32 45), (row3 18 32 46), (row3 18 32 47)]

def b097_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_12_rows b097_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_12_rows b097_12_labels]
    decide +kernel

def b097_13_rows : List Row := [(row3 18 32 48), (row3 18 32 49), (row3 18 32 50), (row3 18 32 51), (row3 18 32 52), (row3 18 32 53), (row3 18 32 54), (row3 18 32 55), (row3 18 32 56), (row3 18 32 57), (row3 18 32 58), (row3 18 32 59), (row3 18 32 60), (row3 18 32 61), (row3 18 32 62), (row3 18 32 63)]

def b097_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_13_rows b097_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_13_rows b097_13_labels]
    decide +kernel

def b097_14_rows : List Row := [(row3 18 33 34), (row3 18 33 35), (row3 18 33 36), (row3 18 33 37), (row3 18 33 38), (row3 18 33 39), (row3 18 33 40), (row3 18 33 41), (row3 18 33 42), (row3 18 33 43), (row3 18 33 44), (row3 18 33 45), (row3 18 33 46), (row3 18 33 47), (row3 18 33 48), (row3 18 33 49)]

def b097_14_labels : List Row := [(row3 462 234 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b097_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_14_rows b097_14_labels 2608968124501120266354000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_14_rows b097_14_labels]
    decide +kernel

def b097_15_rows : List Row := [(row3 18 33 50), (row3 18 33 51), (row3 18 33 52), (row3 18 33 53), (row3 18 33 54), (row3 18 33 55), (row3 18 33 56), (row3 18 33 57), (row3 18 33 58), (row3 18 33 59), (row3 18 33 60), (row3 18 33 61), (row3 18 33 62), (row3 18 33 63), (row3 18 34 35), (row3 18 34 36)]

def b097_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 462 462)]

theorem b097_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b097_15_rows b097_15_labels 2953289385342352475626500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b097_15_rows b097_15_labels]
    decide +kernel

theorem checked097 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_097 QuarticIntegerComputationalData.ids64_097 109736793513486248680105200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b097_00_rows ++ b097_01_rows) ++ (b097_02_rows ++ b097_03_rows)) ++ ((b097_04_rows ++ b097_05_rows) ++ (b097_06_rows ++ b097_07_rows))) ++ (((b097_08_rows ++ b097_09_rows) ++ (b097_10_rows ++ b097_11_rows)) ++ ((b097_12_rows ++ b097_13_rows) ++ (b097_14_rows ++ b097_15_rows))))
    ((((b097_00_labels ++ b097_01_labels) ++ (b097_02_labels ++ b097_03_labels)) ++ ((b097_04_labels ++ b097_05_labels) ++ (b097_06_labels ++ b097_07_labels))) ++ (((b097_08_labels ++ b097_09_labels) ++ (b097_10_labels ++ b097_11_labels)) ++ ((b097_12_labels ++ b097_13_labels) ++ (b097_14_labels ++ b097_15_labels)))) 109736793513486248680105200
  exact ((((b097_00_checked.append (c := 102618484887100283279138700) b097_01_checked (by decide +kernel)).append (c := 103658699528781358155703200) (b097_02_checked.append (c := 1040214641681074876564500) b097_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 104174536003642775938124700) ((b097_04_checked.append (c := 515836474861417782421500) b097_05_checked (by decide +kernel)).append (c := 515836474861417782421500) (b097_06_checked.append (c := 0) b097_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 109736793513486248680105200) (((b097_08_checked.append (c := 0) b097_09_checked (by decide +kernel)).append (c := 0) (b097_10_checked.append (c := 0) b097_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 5562257509843472741980500) ((b097_12_checked.append (c := 0) b097_13_checked (by decide +kernel)).append (c := 5562257509843472741980500) (b097_14_checked.append (c := 5562257509843472741980500) b097_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b098_00_rows : List Row := [(row3 18 34 37), (row3 18 34 38), (row3 18 34 39), (row3 18 34 40), (row3 18 34 41), (row3 18 34 42), (row3 18 34 43), (row3 18 34 44), (row3 18 34 45), (row3 18 34 46), (row3 18 34 47), (row3 18 34 48), (row3 18 34 49), (row3 18 34 50), (row3 18 34 51), (row3 18 34 52)]

def b098_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_00_rows b098_00_labels 833833822677406034148000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_00_rows b098_00_labels]
    decide +kernel

def b098_01_rows : List Row := [(row3 18 34 53), (row3 18 34 54), (row3 18 34 55), (row3 18 34 56), (row3 18 34 57), (row3 18 34 58), (row3 18 34 59), (row3 18 34 60), (row3 18 34 61), (row3 18 34 62), (row3 18 34 63), (row3 18 35 36), (row3 18 35 37), (row3 18 35 38), (row3 18 35 39), (row3 18 35 40)]

def b098_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_01_rows b098_01_labels 430008164825677097310000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_01_rows b098_01_labels]
    decide +kernel

def b098_02_rows : List Row := [(row3 18 35 41), (row3 18 35 42), (row3 18 35 43), (row3 18 35 44), (row3 18 35 45), (row3 18 35 46), (row3 18 35 47), (row3 18 35 48), (row3 18 35 49), (row3 18 35 50), (row3 18 35 51), (row3 18 35 52), (row3 18 35 53), (row3 18 35 54), (row3 18 35 55), (row3 18 35 56)]

def b098_02_labels : List Row := [(row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_02_rows b098_02_labels 24153161720424831967500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_02_rows b098_02_labels]
    decide +kernel

def b098_03_rows : List Row := [(row3 18 35 57), (row3 18 35 58), (row3 18 35 59), (row3 18 35 60), (row3 18 35 61), (row3 18 35 62), (row3 18 35 63), (row3 18 36 37), (row3 18 36 38), (row3 18 36 39), (row3 18 36 40), (row3 18 36 41), (row3 18 36 42), (row3 18 36 43), (row3 18 36 44), (row3 18 36 45)]

def b098_03_labels : List Row := [(row3 462 462 462), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_03_rows b098_03_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_03_rows b098_03_labels]
    decide +kernel

def b098_04_rows : List Row := [(row3 18 36 46), (row3 18 36 47), (row3 18 36 48), (row3 18 36 49), (row3 18 36 50), (row3 18 36 51), (row3 18 36 52), (row3 18 36 53), (row3 18 36 54), (row3 18 36 55), (row3 18 36 56), (row3 18 36 57), (row3 18 36 58), (row3 18 36 59), (row3 18 36 60), (row3 18 36 61)]

def b098_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_04_rows b098_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_04_rows b098_04_labels]
    decide +kernel

def b098_05_rows : List Row := [(row3 18 36 62), (row3 18 36 63), (row3 18 37 38), (row3 18 37 39), (row3 18 37 40), (row3 18 37 41), (row3 18 37 42), (row3 18 37 43), (row3 18 37 44), (row3 18 37 45), (row3 18 37 46), (row3 18 37 47), (row3 18 37 48), (row3 18 37 49), (row3 18 37 50), (row3 18 37 51)]

def b098_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_05_rows b098_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_05_rows b098_05_labels]
    decide +kernel

def b098_06_rows : List Row := [(row3 18 37 52), (row3 18 37 53), (row3 18 37 54), (row3 18 37 55), (row3 18 37 56), (row3 18 37 57), (row3 18 37 58), (row3 18 37 59), (row3 18 37 60), (row3 18 37 61), (row3 18 37 62), (row3 18 37 63), (row3 18 38 39), (row3 18 38 40), (row3 18 38 41), (row3 18 38 42)]

def b098_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_06_rows b098_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_06_rows b098_06_labels]
    decide +kernel

def b098_07_rows : List Row := [(row3 18 38 43), (row3 18 38 44), (row3 18 38 45), (row3 18 38 46), (row3 18 38 47), (row3 18 38 48), (row3 18 38 49), (row3 18 38 50), (row3 18 38 51), (row3 18 38 52), (row3 18 38 53), (row3 18 38 54), (row3 18 38 55), (row3 18 38 56), (row3 18 38 57), (row3 18 38 58)]

def b098_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_07_rows b098_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_07_rows b098_07_labels]
    decide +kernel

def b098_08_rows : List Row := [(row3 18 38 59), (row3 18 38 60), (row3 18 38 61), (row3 18 38 62), (row3 18 38 63), (row3 18 39 40), (row3 18 39 41), (row3 18 39 42), (row3 18 39 43), (row3 18 39 44), (row3 18 39 45), (row3 18 39 46), (row3 18 39 47), (row3 18 39 48), (row3 18 39 49), (row3 18 39 50)]

def b098_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_08_rows b098_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_08_rows b098_08_labels]
    decide +kernel

def b098_09_rows : List Row := [(row3 18 39 51), (row3 18 39 52), (row3 18 39 53), (row3 18 39 54), (row3 18 39 55), (row3 18 39 56), (row3 18 39 57), (row3 18 39 58), (row3 18 39 59), (row3 18 39 60), (row3 18 39 61), (row3 18 39 62), (row3 18 39 63), (row3 18 40 41), (row3 18 40 42), (row3 18 40 43)]

def b098_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_09_rows b098_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_09_rows b098_09_labels]
    decide +kernel

def b098_10_rows : List Row := [(row3 18 40 44), (row3 18 40 45), (row3 18 40 46), (row3 18 40 47), (row3 18 40 48), (row3 18 40 49), (row3 18 40 50), (row3 18 40 51), (row3 18 40 52), (row3 18 40 53), (row3 18 40 54), (row3 18 40 55), (row3 18 40 56), (row3 18 40 57), (row3 18 40 58), (row3 18 40 59)]

def b098_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 269 269), (row3 232 235 228), (row3 462 246 246), (row3 462 462 462)]

theorem b098_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_10_rows b098_10_labels 32405070037446917942656500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_10_rows b098_10_labels]
    decide +kernel

def b098_11_rows : List Row := [(row3 18 40 60), (row3 18 40 61), (row3 18 40 62), (row3 18 40 63), (row3 18 41 42), (row3 18 41 43), (row3 18 41 44), (row3 18 41 45), (row3 18 41 46), (row3 18 41 47), (row3 18 41 48), (row3 18 41 49), (row3 18 41 50), (row3 18 41 51), (row3 18 41 52), (row3 18 41 53)]

def b098_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_11_rows b098_11_labels 411168275891826723499500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_11_rows b098_11_labels]
    decide +kernel

def b098_12_rows : List Row := [(row3 18 41 54), (row3 18 41 55), (row3 18 41 56), (row3 18 41 57), (row3 18 41 58), (row3 18 41 59), (row3 18 41 60), (row3 18 41 61), (row3 18 41 62), (row3 18 41 63), (row3 18 42 43), (row3 18 42 44), (row3 18 42 45), (row3 18 42 46), (row3 18 42 47), (row3 18 42 48)]

def b098_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_12_rows b098_12_labels 6152841992509574565621600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_12_rows b098_12_labels]
    decide +kernel

def b098_13_rows : List Row := [(row3 18 42 49), (row3 18 42 50), (row3 18 42 51), (row3 18 42 52), (row3 18 42 53), (row3 18 42 54), (row3 18 42 55), (row3 18 42 56), (row3 18 42 57), (row3 18 42 58), (row3 18 42 59), (row3 18 42 60), (row3 18 42 61), (row3 18 42 62), (row3 18 42 63), (row3 18 43 44)]

def b098_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 265 267 267), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_13_rows b098_13_labels 4341068780563739173122900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_13_rows b098_13_labels]
    decide +kernel

def b098_14_rows : List Row := [(row3 18 43 45), (row3 18 43 46), (row3 18 43 47), (row3 18 43 48), (row3 18 43 49), (row3 18 43 50), (row3 18 43 51), (row3 18 43 52), (row3 18 43 53), (row3 18 43 54), (row3 18 43 55), (row3 18 43 56), (row3 18 43 57), (row3 18 43 58), (row3 18 43 59), (row3 18 43 60)]

def b098_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462)]

theorem b098_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_14_rows b098_14_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_14_rows b098_14_labels]
    decide +kernel

def b098_15_rows : List Row := [(row3 18 43 61), (row3 18 43 62), (row3 18 43 63), (row3 18 44 45), (row3 18 44 46), (row3 18 44 47), (row3 18 44 48), (row3 18 44 49), (row3 18 44 50), (row3 18 44 51), (row3 18 44 52), (row3 18 44 53), (row3 18 44 54), (row3 18 44 55), (row3 18 44 56), (row3 18 44 57)]

def b098_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b098_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b098_15_rows b098_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b098_15_rows b098_15_labels]
    decide +kernel

theorem checked098 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_098 QuarticIntegerComputationalData.ids64_098 44947952164342865214688500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b098_00_rows ++ b098_01_rows) ++ (b098_02_rows ++ b098_03_rows)) ++ ((b098_04_rows ++ b098_05_rows) ++ (b098_06_rows ++ b098_07_rows))) ++ (((b098_08_rows ++ b098_09_rows) ++ (b098_10_rows ++ b098_11_rows)) ++ ((b098_12_rows ++ b098_13_rows) ++ (b098_14_rows ++ b098_15_rows))))
    ((((b098_00_labels ++ b098_01_labels) ++ (b098_02_labels ++ b098_03_labels)) ++ ((b098_04_labels ++ b098_05_labels) ++ (b098_06_labels ++ b098_07_labels))) ++ (((b098_08_labels ++ b098_09_labels) ++ (b098_10_labels ++ b098_11_labels)) ++ ((b098_12_labels ++ b098_13_labels) ++ (b098_14_labels ++ b098_15_labels)))) 44947952164342865214688500
  exact ((((b098_00_checked.append (c := 1263841987503083131458000) b098_01_checked (by decide +kernel)).append (c := 1313428003680921991488000) (b098_02_checked.append (c := 49586016177838860030000) b098_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1313428003680921991488000) ((b098_04_checked.append (c := 0) b098_05_checked (by decide +kernel)).append (c := 0) (b098_06_checked.append (c := 0) b098_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 44947952164342865214688500) (((b098_08_checked.append (c := 0) b098_09_checked (by decide +kernel)).append (c := 32816238313338744666156000) (b098_10_checked.append (c := 32816238313338744666156000) b098_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 43634524160661943223200500) ((b098_12_checked.append (c := 10493910773073313738744500) b098_13_checked (by decide +kernel)).append (c := 10818285847323198557044500) (b098_14_checked.append (c := 324375074249884818300000) b098_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b099_00_rows : List Row := [(row3 18 44 58), (row3 18 44 59), (row3 18 44 60), (row3 18 44 61), (row3 18 44 62), (row3 18 44 63), (row3 18 45 46), (row3 18 45 47), (row3 18 45 48), (row3 18 45 49), (row3 18 45 50), (row3 18 45 51), (row3 18 45 52), (row3 18 45 53), (row3 18 45 54), (row3 18 45 55)]

def b099_00_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_00_rows b099_00_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_00_rows b099_00_labels]
    decide +kernel

def b099_01_rows : List Row := [(row3 18 45 56), (row3 18 45 57), (row3 18 45 58), (row3 18 45 59), (row3 18 45 60), (row3 18 45 61), (row3 18 45 62), (row3 18 45 63), (row3 18 46 47), (row3 18 46 48), (row3 18 46 49), (row3 18 46 50), (row3 18 46 51), (row3 18 46 52), (row3 18 46 53), (row3 18 46 54)]

def b099_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_01_rows b099_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_01_rows b099_01_labels]
    decide +kernel

def b099_02_rows : List Row := [(row3 18 46 55), (row3 18 46 56), (row3 18 46 57), (row3 18 46 58), (row3 18 46 59), (row3 18 46 60), (row3 18 46 61), (row3 18 46 62), (row3 18 46 63), (row3 18 47 48), (row3 18 47 49), (row3 18 47 50), (row3 18 47 51), (row3 18 47 52), (row3 18 47 53), (row3 18 47 54)]

def b099_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_02_rows b099_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_02_rows b099_02_labels]
    decide +kernel

def b099_03_rows : List Row := [(row3 18 47 55), (row3 18 47 56), (row3 18 47 57), (row3 18 47 58), (row3 18 47 59), (row3 18 47 60), (row3 18 47 61), (row3 18 47 62), (row3 18 47 63), (row3 18 48 49), (row3 18 48 50), (row3 18 48 51), (row3 18 48 52), (row3 18 48 53), (row3 18 48 54), (row3 18 48 55)]

def b099_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234)]

theorem b099_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_03_rows b099_03_labels 5053654980804716106408000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_03_rows b099_03_labels]
    decide +kernel

def b099_04_rows : List Row := [(row3 18 48 56), (row3 18 48 57), (row3 18 48 58), (row3 18 48 59), (row3 18 48 60), (row3 18 48 61), (row3 18 48 62), (row3 18 48 63), (row3 18 49 50), (row3 18 49 51), (row3 18 49 52), (row3 18 49 53), (row3 18 49 54), (row3 18 49 55), (row3 18 49 56), (row3 18 49 57)]

def b099_04_labels : List Row := [(row3 462 180 180), (row3 288 278 300), (row3 234 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 278 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 293 293), (row3 163 228 160)]

theorem b099_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_04_rows b099_04_labels 1625251354242063581969269200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_04_rows b099_04_labels]
    decide +kernel

def b099_05_rows : List Row := [(row3 18 49 58), (row3 18 49 59), (row3 18 49 60), (row3 18 49 61), (row3 18 49 62), (row3 18 49 63), (row3 18 50 51), (row3 18 50 52), (row3 18 50 53), (row3 18 50 54), (row3 18 50 55), (row3 18 50 56), (row3 18 50 57), (row3 18 50 58), (row3 18 50 59), (row3 18 50 60)]

def b099_05_labels : List Row := [(row3 278 283 283), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 180 154 154), (row3 462 462 462), (row3 462 462 462)]

theorem b099_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_05_rows b099_05_labels 823465865984674866018442200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_05_rows b099_05_labels]
    decide +kernel

def b099_06_rows : List Row := [(row3 18 50 61), (row3 18 50 62), (row3 18 50 63), (row3 18 51 52), (row3 18 51 53), (row3 18 51 54), (row3 18 51 55), (row3 18 51 56), (row3 18 51 57), (row3 18 51 58), (row3 18 51 59), (row3 18 51 60), (row3 18 51 61), (row3 18 51 62), (row3 18 51 63), (row3 18 52 53)]

def b099_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_06_rows b099_06_labels 10330661955109590566643600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_06_rows b099_06_labels]
    decide +kernel

def b099_07_rows : List Row := [(row3 18 52 54), (row3 18 52 55), (row3 18 52 56), (row3 18 52 57), (row3 18 52 58), (row3 18 52 59), (row3 18 52 60), (row3 18 52 61), (row3 18 52 62), (row3 18 52 63), (row3 18 53 54), (row3 18 53 55), (row3 18 53 56), (row3 18 53 57), (row3 18 53 58), (row3 18 53 59)]

def b099_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462)]

theorem b099_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_07_rows b099_07_labels 332035174606788056025000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_07_rows b099_07_labels]
    decide +kernel

def b099_08_rows : List Row := [(row3 18 53 60), (row3 18 53 61), (row3 18 53 62), (row3 18 53 63), (row3 18 54 55), (row3 18 54 56), (row3 18 54 57), (row3 18 54 58), (row3 18 54 59), (row3 18 54 60), (row3 18 54 61), (row3 18 54 62), (row3 18 54 63), (row3 18 55 56), (row3 18 55 57), (row3 18 55 58)]

def b099_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 232 228 223), (row3 462 250 250)]

theorem b099_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_08_rows b099_08_labels 95623386887964082244895000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_08_rows b099_08_labels]
    decide +kernel

def b099_09_rows : List Row := [(row3 18 55 59), (row3 18 55 60), (row3 18 55 61), (row3 18 55 62), (row3 18 55 63), (row3 18 56 57), (row3 18 56 58), (row3 18 56 59), (row3 18 56 60), (row3 18 56 61), (row3 18 56 62), (row3 18 56 63), (row3 18 57 58), (row3 18 57 59), (row3 18 57 60), (row3 18 57 61)]

def b099_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 228 228), (row3 163 139 124), (row3 265 302 302), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 462 139 139), (row3 356 158 89), (row3 273 273 462), (row3 236 236 462), (row3 462 462 462)]

theorem b099_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_09_rows b099_09_labels 10840813271230020271797271500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_09_rows b099_09_labels]
    decide +kernel

def b099_10_rows : List Row := [(row3 18 57 62), (row3 18 57 63), (row3 18 58 59), (row3 18 58 60), (row3 18 58 61), (row3 18 58 62), (row3 18 58 63), (row3 18 59 60), (row3 18 59 61), (row3 18 59 62), (row3 18 59 63), (row3 18 60 61), (row3 18 60 62), (row3 18 60 63), (row3 18 61 62), (row3 18 61 63)]

def b099_10_labels : List Row := [(row3 236 225 228), (row3 273 304 295), (row3 180 154 154), (row3 265 266 266), (row3 237 237 237), (row3 462 249 249), (row3 237 226 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_10_rows b099_10_labels 835699010142699624556103400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_10_rows b099_10_labels]
    decide +kernel

def b099_11_rows : List Row := [(row3 18 62 63), (row3 19 20 21), (row3 19 20 22), (row3 19 20 23), (row3 19 20 24), (row3 19 20 25), (row3 19 20 26), (row3 19 20 27), (row3 19 20 28), (row3 19 20 29), (row3 19 20 30), (row3 19 20 31), (row3 19 20 32), (row3 19 20 33), (row3 19 20 34), (row3 19 20 35)]

def b099_11_labels : List Row := [(row3 462 228 228), (row3 462 462 462), (row3 237 237 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_11_rows b099_11_labels 6457945189576094910436500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_11_rows b099_11_labels]
    decide +kernel

def b099_12_rows : List Row := [(row3 19 20 36), (row3 19 20 37), (row3 19 20 38), (row3 19 20 39), (row3 19 20 40), (row3 19 20 41), (row3 19 20 42), (row3 19 20 43), (row3 19 20 44), (row3 19 20 45), (row3 19 20 46), (row3 19 20 47), (row3 19 20 48), (row3 19 20 49), (row3 19 20 50), (row3 19 20 51)]

def b099_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_12_rows b099_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_12_rows b099_12_labels]
    decide +kernel

def b099_13_rows : List Row := [(row3 19 20 52), (row3 19 20 53), (row3 19 20 54), (row3 19 20 55), (row3 19 20 56), (row3 19 20 57), (row3 19 20 58), (row3 19 20 59), (row3 19 20 60), (row3 19 20 61), (row3 19 20 62), (row3 19 20 63), (row3 19 21 22), (row3 19 21 23), (row3 19 21 24), (row3 19 21 25)]

def b099_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b099_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_13_rows b099_13_labels 30531438688500048656020500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_13_rows b099_13_labels]
    decide +kernel

def b099_14_rows : List Row := [(row3 19 21 26), (row3 19 21 27), (row3 19 21 28), (row3 19 21 29), (row3 19 21 30), (row3 19 21 31), (row3 19 21 32), (row3 19 21 33), (row3 19 21 34), (row3 19 21 35), (row3 19 21 36), (row3 19 21 37), (row3 19 21 38), (row3 19 21 39), (row3 19 21 40), (row3 19 21 41)]

def b099_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_14_rows b099_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_14_rows b099_14_labels]
    decide +kernel

def b099_15_rows : List Row := [(row3 19 21 42), (row3 19 21 43), (row3 19 21 44), (row3 19 21 45), (row3 19 21 46), (row3 19 21 47), (row3 19 21 48), (row3 19 21 49), (row3 19 21 50), (row3 19 21 51), (row3 19 21 52), (row3 19 21 53), (row3 19 21 54), (row3 19 21 55), (row3 19 21 56), (row3 19 21 57)]

def b099_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b099_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b099_15_rows b099_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b099_15_rows b099_15_labels]
    decide +kernel

theorem checked099 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_099 QuarticIntegerComputationalData.ids64_099 14273570114626555019738102400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b099_00_rows ++ b099_01_rows) ++ (b099_02_rows ++ b099_03_rows)) ++ ((b099_04_rows ++ b099_05_rows) ++ (b099_06_rows ++ b099_07_rows))) ++ (((b099_08_rows ++ b099_09_rows) ++ (b099_10_rows ++ b099_11_rows)) ++ ((b099_12_rows ++ b099_13_rows) ++ (b099_14_rows ++ b099_15_rows))))
    ((((b099_00_labels ++ b099_01_labels) ++ (b099_02_labels ++ b099_03_labels)) ++ ((b099_04_labels ++ b099_05_labels) ++ (b099_06_labels ++ b099_07_labels))) ++ (((b099_08_labels ++ b099_09_labels) ++ (b099_10_labels ++ b099_11_labels)) ++ ((b099_12_labels ++ b099_13_labels) ++ (b099_14_labels ++ b099_15_labels)))) 14273570114626555019738102400
  exact ((((b099_00_checked.append (c := 11490150535354856587500) b099_01_checked (by decide +kernel)).append (c := 5065145131340070962995500) (b099_02_checked.append (c := 5053654980804716106408000) b099_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2464445062487794897573375500) ((b099_04_checked.append (c := 2448717220226738447987711400) b099_05_checked (by decide +kernel)).append (c := 2459379917356454826610380000) (b099_06_checked.append (c := 10662697129716378622668600) b099_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 14273570114626555019738102400) (((b099_08_checked.append (c := 10936436658117984354042166500) b099_09_checked (by decide +kernel)).append (c := 11778593613450260073508706400) (b099_10_checked.append (c := 842156955332275719466539900) b099_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 11809125052138760122164726900) ((b099_12_checked.append (c := 30531438688500048656020500) b099_13_checked (by decide +kernel)).append (c := 30531438688500048656020500) (b099_14_checked.append (c := 0) b099_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b100_00_rows : List Row := [(row3 19 21 58), (row3 19 21 59), (row3 19 21 60), (row3 19 21 61), (row3 19 21 62), (row3 19 21 63), (row3 19 22 23), (row3 19 22 24), (row3 19 22 25), (row3 19 22 26), (row3 19 22 27), (row3 19 22 28), (row3 19 22 29), (row3 19 22 30), (row3 19 22 31), (row3 19 22 32)]

def b100_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 170 10 218), (row3 245 462 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 269 462 269), (row3 235 462 235), (row3 462 462 462)]

theorem b100_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_00_rows b100_00_labels 565121309352042867391280250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_00_rows b100_00_labels]
    decide +kernel

def b100_01_rows : List Row := [(row3 19 22 33), (row3 19 22 34), (row3 19 22 35), (row3 19 22 36), (row3 19 22 37), (row3 19 22 38), (row3 19 22 39), (row3 19 22 40), (row3 19 22 41), (row3 19 22 42), (row3 19 22 43), (row3 19 22 44), (row3 19 22 45), (row3 19 22 46), (row3 19 22 47), (row3 19 22 48)]

def b100_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 237 462 237), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462)]

theorem b100_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_01_rows b100_01_labels 148902545254618432525500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_01_rows b100_01_labels]
    decide +kernel

def b100_02_rows : List Row := [(row3 19 22 49), (row3 19 22 50), (row3 19 22 51), (row3 19 22 52), (row3 19 22 53), (row3 19 22 54), (row3 19 22 55), (row3 19 22 56), (row3 19 22 57), (row3 19 22 58), (row3 19 22 59), (row3 19 22 60), (row3 19 22 61), (row3 19 22 62), (row3 19 22 63), (row3 19 23 24)]

def b100_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 233 235 236)]

theorem b100_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_02_rows b100_02_labels 678821106800295109552500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_02_rows b100_02_labels]
    decide +kernel

def b100_03_rows : List Row := [(row3 19 23 25), (row3 19 23 26), (row3 19 23 27), (row3 19 23 28), (row3 19 23 29), (row3 19 23 30), (row3 19 23 31), (row3 19 23 32), (row3 19 23 33), (row3 19 23 34), (row3 19 23 35), (row3 19 23 36), (row3 19 23 37), (row3 19 23 38), (row3 19 23 39), (row3 19 23 40)]

def b100_03_labels : List Row := [(row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 235 235 462), (row3 269 269 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 237 237 462), (row3 462 462 462)]

theorem b100_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_03_rows b100_03_labels 30368292030010763580217500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_03_rows b100_03_labels]
    decide +kernel

def b100_04_rows : List Row := [(row3 19 23 41), (row3 19 23 42), (row3 19 23 43), (row3 19 23 44), (row3 19 23 45), (row3 19 23 46), (row3 19 23 47), (row3 19 23 48), (row3 19 23 49), (row3 19 23 50), (row3 19 23 51), (row3 19 23 52), (row3 19 23 53), (row3 19 23 54), (row3 19 23 55), (row3 19 23 56)]

def b100_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_04_rows b100_04_labels 3830050178451618862500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_04_rows b100_04_labels]
    decide +kernel

def b100_05_rows : List Row := [(row3 19 23 57), (row3 19 23 58), (row3 19 23 59), (row3 19 23 60), (row3 19 23 61), (row3 19 23 62), (row3 19 23 63), (row3 19 24 25), (row3 19 24 26), (row3 19 24 27), (row3 19 24 28), (row3 19 24 29), (row3 19 24 30), (row3 19 24 31), (row3 19 24 32), (row3 19 24 33)]

def b100_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 171 254 10), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 263 263 462), (row3 263 263 462), (row3 236 236 462)]

theorem b100_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_05_rows b100_05_labels 557480259723433562288808000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_05_rows b100_05_labels]
    decide +kernel

def b100_06_rows : List Row := [(row3 19 24 34), (row3 19 24 35), (row3 19 24 36), (row3 19 24 37), (row3 19 24 38), (row3 19 24 39), (row3 19 24 40), (row3 19 24 41), (row3 19 24 42), (row3 19 24 43), (row3 19 24 44), (row3 19 24 45), (row3 19 24 46), (row3 19 24 47), (row3 19 24 48), (row3 19 24 49)]

def b100_06_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 241 241 462), (row3 462 462 462)]

theorem b100_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_06_rows b100_06_labels 377255324179782554595000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_06_rows b100_06_labels]
    decide +kernel

def b100_07_rows : List Row := [(row3 19 24 50), (row3 19 24 51), (row3 19 24 52), (row3 19 24 53), (row3 19 24 54), (row3 19 24 55), (row3 19 24 56), (row3 19 24 57), (row3 19 24 58), (row3 19 24 59), (row3 19 24 60), (row3 19 24 61), (row3 19 24 62), (row3 19 24 63), (row3 19 25 26), (row3 19 25 27)]

def b100_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 235 462 235)]

theorem b100_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_07_rows b100_07_labels 64010092251704773658301000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_07_rows b100_07_labels]
    decide +kernel

def b100_08_rows : List Row := [(row3 19 25 28), (row3 19 25 29), (row3 19 25 30), (row3 19 25 31), (row3 19 25 32), (row3 19 25 33), (row3 19 25 34), (row3 19 25 35), (row3 19 25 36), (row3 19 25 37), (row3 19 25 38), (row3 19 25 39), (row3 19 25 40), (row3 19 25 41), (row3 19 25 42), (row3 19 25 43)]

def b100_08_labels : List Row := [(row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 235 462 235), (row3 232 462 232), (row3 284 462 284), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 246 462 246), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462)]

theorem b100_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_08_rows b100_08_labels 61788572900574629398155000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_08_rows b100_08_labels]
    decide +kernel

def b100_09_rows : List Row := [(row3 19 25 44), (row3 19 25 45), (row3 19 25 46), (row3 19 25 47), (row3 19 25 48), (row3 19 25 49), (row3 19 25 50), (row3 19 25 51), (row3 19 25 52), (row3 19 25 53), (row3 19 25 54), (row3 19 25 55), (row3 19 25 56), (row3 19 25 57), (row3 19 25 58), (row3 19 25 59)]

def b100_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_09_rows b100_09_labels 10173141782965611225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_09_rows b100_09_labels]
    decide +kernel

def b100_10_rows : List Row := [(row3 19 25 60), (row3 19 25 61), (row3 19 25 62), (row3 19 25 63), (row3 19 26 27), (row3 19 26 28), (row3 19 26 29), (row3 19 26 30), (row3 19 26 31), (row3 19 26 32), (row3 19 26 33), (row3 19 26 34), (row3 19 26 35), (row3 19 26 36), (row3 19 26 37), (row3 19 26 38)]

def b100_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_10_rows b100_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_10_rows b100_10_labels]
    decide +kernel

def b100_11_rows : List Row := [(row3 19 26 39), (row3 19 26 40), (row3 19 26 41), (row3 19 26 42), (row3 19 26 43), (row3 19 26 44), (row3 19 26 45), (row3 19 26 46), (row3 19 26 47), (row3 19 26 48), (row3 19 26 49), (row3 19 26 50), (row3 19 26 51), (row3 19 26 52), (row3 19 26 53), (row3 19 26 54)]

def b100_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_11_rows b100_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_11_rows b100_11_labels]
    decide +kernel

def b100_12_rows : List Row := [(row3 19 26 55), (row3 19 26 56), (row3 19 26 57), (row3 19 26 58), (row3 19 26 59), (row3 19 26 60), (row3 19 26 61), (row3 19 26 62), (row3 19 26 63), (row3 19 27 28), (row3 19 27 29), (row3 19 27 30), (row3 19 27 31), (row3 19 27 32), (row3 19 27 33), (row3 19 27 34)]

def b100_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_12_rows b100_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_12_rows b100_12_labels]
    decide +kernel

def b100_13_rows : List Row := [(row3 19 27 35), (row3 19 27 36), (row3 19 27 37), (row3 19 27 38), (row3 19 27 39), (row3 19 27 40), (row3 19 27 41), (row3 19 27 42), (row3 19 27 43), (row3 19 27 44), (row3 19 27 45), (row3 19 27 46), (row3 19 27 47), (row3 19 27 48), (row3 19 27 49), (row3 19 27 50)]

def b100_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_13_rows b100_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_13_rows b100_13_labels]
    decide +kernel

def b100_14_rows : List Row := [(row3 19 27 51), (row3 19 27 52), (row3 19 27 53), (row3 19 27 54), (row3 19 27 55), (row3 19 27 56), (row3 19 27 57), (row3 19 27 58), (row3 19 27 59), (row3 19 27 60), (row3 19 27 61), (row3 19 27 62), (row3 19 27 63), (row3 19 28 29), (row3 19 28 30), (row3 19 28 31)]

def b100_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_14_rows b100_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_14_rows b100_14_labels]
    decide +kernel

def b100_15_rows : List Row := [(row3 19 28 32), (row3 19 28 33), (row3 19 28 34), (row3 19 28 35), (row3 19 28 36), (row3 19 28 37), (row3 19 28 38), (row3 19 28 39), (row3 19 28 40), (row3 19 28 41), (row3 19 28 42), (row3 19 28 43), (row3 19 28 44), (row3 19 28 45), (row3 19 28 46), (row3 19 28 47)]

def b100_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b100_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b100_15_rows b100_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b100_15_rows b100_15_labels]
    decide +kernel

theorem checked100 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_100 QuarticIntegerComputationalData.ids64_100 1279987508425962709643522250 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b100_00_rows ++ b100_01_rows) ++ (b100_02_rows ++ b100_03_rows)) ++ ((b100_04_rows ++ b100_05_rows) ++ (b100_06_rows ++ b100_07_rows))) ++ (((b100_08_rows ++ b100_09_rows) ++ (b100_10_rows ++ b100_11_rows)) ++ ((b100_12_rows ++ b100_13_rows) ++ (b100_14_rows ++ b100_15_rows))))
    ((((b100_00_labels ++ b100_01_labels) ++ (b100_02_labels ++ b100_03_labels)) ++ ((b100_04_labels ++ b100_05_labels) ++ (b100_06_labels ++ b100_07_labels))) ++ (((b100_08_labels ++ b100_09_labels) ++ (b100_10_labels ++ b100_11_labels)) ++ ((b100_12_labels ++ b100_13_labels) ++ (b100_14_labels ++ b100_15_labels)))) 1279987508425962709643522250
  exact ((((b100_00_checked.append (c := 565270211897297485823805750) b100_01_checked (by decide +kernel)).append (c := 596317325034108544513575750) (b100_02_checked.append (c := 31047113136811058689770000) b100_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1218188762383605114634142250) ((b100_04_checked.append (c := 557484089773612013907670500) b100_05_checked (by decide +kernel)).append (c := 621871437349496570120566500) (b100_06_checked.append (c := 64387347575884556212896000) b100_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1279987508425962709643522250) (((b100_08_checked.append (c := 61798746042357595009380000) b100_09_checked (by decide +kernel)).append (c := 61798746042357595009380000) (b100_10_checked.append (c := 0) b100_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 61798746042357595009380000) ((b100_12_checked.append (c := 0) b100_13_checked (by decide +kernel)).append (c := 0) (b100_14_checked.append (c := 0) b100_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b101_00_rows : List Row := [(row3 19 28 48), (row3 19 28 49), (row3 19 28 50), (row3 19 28 51), (row3 19 28 52), (row3 19 28 53), (row3 19 28 54), (row3 19 28 55), (row3 19 28 56), (row3 19 28 57), (row3 19 28 58), (row3 19 28 59), (row3 19 28 60), (row3 19 28 61), (row3 19 28 62), (row3 19 28 63)]

def b101_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_00_rows b101_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_00_rows b101_00_labels]
    decide +kernel

def b101_01_rows : List Row := [(row3 19 29 30), (row3 19 29 31), (row3 19 29 32), (row3 19 29 33), (row3 19 29 34), (row3 19 29 35), (row3 19 29 36), (row3 19 29 37), (row3 19 29 38), (row3 19 29 39), (row3 19 29 40), (row3 19 29 41), (row3 19 29 42), (row3 19 29 43), (row3 19 29 44), (row3 19 29 45)]

def b101_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_01_rows b101_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_01_rows b101_01_labels]
    decide +kernel

def b101_02_rows : List Row := [(row3 19 29 46), (row3 19 29 47), (row3 19 29 48), (row3 19 29 49), (row3 19 29 50), (row3 19 29 51), (row3 19 29 52), (row3 19 29 53), (row3 19 29 54), (row3 19 29 55), (row3 19 29 56), (row3 19 29 57), (row3 19 29 58), (row3 19 29 59), (row3 19 29 60), (row3 19 29 61)]

def b101_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_02_rows b101_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_02_rows b101_02_labels]
    decide +kernel

def b101_03_rows : List Row := [(row3 19 29 62), (row3 19 29 63), (row3 19 30 31), (row3 19 30 32), (row3 19 30 33), (row3 19 30 34), (row3 19 30 35), (row3 19 30 36), (row3 19 30 37), (row3 19 30 38), (row3 19 30 39), (row3 19 30 40), (row3 19 30 41), (row3 19 30 42), (row3 19 30 43), (row3 19 30 44)]

def b101_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_03_rows b101_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_03_rows b101_03_labels]
    decide +kernel

def b101_04_rows : List Row := [(row3 19 30 45), (row3 19 30 46), (row3 19 30 47), (row3 19 30 48), (row3 19 30 49), (row3 19 30 50), (row3 19 30 51), (row3 19 30 52), (row3 19 30 53), (row3 19 30 54), (row3 19 30 55), (row3 19 30 56), (row3 19 30 57), (row3 19 30 58), (row3 19 30 59), (row3 19 30 60)]

def b101_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_04_rows b101_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_04_rows b101_04_labels]
    decide +kernel

def b101_05_rows : List Row := [(row3 19 30 61), (row3 19 30 62), (row3 19 30 63), (row3 19 31 32), (row3 19 31 33), (row3 19 31 34), (row3 19 31 35), (row3 19 31 36), (row3 19 31 37), (row3 19 31 38), (row3 19 31 39), (row3 19 31 40), (row3 19 31 41), (row3 19 31 42), (row3 19 31 43), (row3 19 31 44)]

def b101_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_05_rows b101_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_05_rows b101_05_labels]
    decide +kernel

def b101_06_rows : List Row := [(row3 19 31 45), (row3 19 31 46), (row3 19 31 47), (row3 19 31 48), (row3 19 31 49), (row3 19 31 50), (row3 19 31 51), (row3 19 31 52), (row3 19 31 53), (row3 19 31 54), (row3 19 31 55), (row3 19 31 56), (row3 19 31 57), (row3 19 31 58), (row3 19 31 59), (row3 19 31 60)]

def b101_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_06_rows b101_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_06_rows b101_06_labels]
    decide +kernel

def b101_07_rows : List Row := [(row3 19 31 61), (row3 19 31 62), (row3 19 31 63), (row3 19 32 33), (row3 19 32 34), (row3 19 32 35), (row3 19 32 36), (row3 19 32 37), (row3 19 32 38), (row3 19 32 39), (row3 19 32 40), (row3 19 32 41), (row3 19 32 42), (row3 19 32 43), (row3 19 32 44), (row3 19 32 45)]

def b101_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_07_rows b101_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_07_rows b101_07_labels]
    decide +kernel

def b101_08_rows : List Row := [(row3 19 32 46), (row3 19 32 47), (row3 19 32 48), (row3 19 32 49), (row3 19 32 50), (row3 19 32 51), (row3 19 32 52), (row3 19 32 53), (row3 19 32 54), (row3 19 32 55), (row3 19 32 56), (row3 19 32 57), (row3 19 32 58), (row3 19 32 59), (row3 19 32 60), (row3 19 32 61)]

def b101_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_08_rows b101_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_08_rows b101_08_labels]
    decide +kernel

def b101_09_rows : List Row := [(row3 19 32 62), (row3 19 32 63), (row3 19 33 34), (row3 19 33 35), (row3 19 33 36), (row3 19 33 37), (row3 19 33 38), (row3 19 33 39), (row3 19 33 40), (row3 19 33 41), (row3 19 33 42), (row3 19 33 43), (row3 19 33 44), (row3 19 33 45), (row3 19 33 46), (row3 19 33 47)]

def b101_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_09_rows b101_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_09_rows b101_09_labels]
    decide +kernel

def b101_10_rows : List Row := [(row3 19 33 48), (row3 19 33 49), (row3 19 33 50), (row3 19 33 51), (row3 19 33 52), (row3 19 33 53), (row3 19 33 54), (row3 19 33 55), (row3 19 33 56), (row3 19 33 57), (row3 19 33 58), (row3 19 33 59), (row3 19 33 60), (row3 19 33 61), (row3 19 33 62), (row3 19 33 63)]

def b101_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_10_rows b101_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_10_rows b101_10_labels]
    decide +kernel

def b101_11_rows : List Row := [(row3 19 34 35), (row3 19 34 36), (row3 19 34 37), (row3 19 34 38), (row3 19 34 39), (row3 19 34 40), (row3 19 34 41), (row3 19 34 42), (row3 19 34 43), (row3 19 34 44), (row3 19 34 45), (row3 19 34 46), (row3 19 34 47), (row3 19 34 48), (row3 19 34 49), (row3 19 34 50)]

def b101_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_11_rows b101_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_11_rows b101_11_labels]
    decide +kernel

def b101_12_rows : List Row := [(row3 19 34 51), (row3 19 34 52), (row3 19 34 53), (row3 19 34 54), (row3 19 34 55), (row3 19 34 56), (row3 19 34 57), (row3 19 34 58), (row3 19 34 59), (row3 19 34 60), (row3 19 34 61), (row3 19 34 62), (row3 19 34 63), (row3 19 35 36), (row3 19 35 37), (row3 19 35 38)]

def b101_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_12_rows b101_12_labels 10173141782965611225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_12_rows b101_12_labels]
    decide +kernel

def b101_13_rows : List Row := [(row3 19 35 39), (row3 19 35 40), (row3 19 35 41), (row3 19 35 42), (row3 19 35 43), (row3 19 35 44), (row3 19 35 45), (row3 19 35 46), (row3 19 35 47), (row3 19 35 48), (row3 19 35 49), (row3 19 35 50), (row3 19 35 51), (row3 19 35 52), (row3 19 35 53), (row3 19 35 54)]

def b101_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_13_rows b101_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_13_rows b101_13_labels]
    decide +kernel

def b101_14_rows : List Row := [(row3 19 35 55), (row3 19 35 56), (row3 19 35 57), (row3 19 35 58), (row3 19 35 59), (row3 19 35 60), (row3 19 35 61), (row3 19 35 62), (row3 19 35 63), (row3 19 36 37), (row3 19 36 38), (row3 19 36 39), (row3 19 36 40), (row3 19 36 41), (row3 19 36 42), (row3 19 36 43)]

def b101_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_14_rows b101_14_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_14_rows b101_14_labels]
    decide +kernel

def b101_15_rows : List Row := [(row3 19 36 44), (row3 19 36 45), (row3 19 36 46), (row3 19 36 47), (row3 19 36 48), (row3 19 36 49), (row3 19 36 50), (row3 19 36 51), (row3 19 36 52), (row3 19 36 53), (row3 19 36 54), (row3 19 36 55), (row3 19 36 56), (row3 19 36 57), (row3 19 36 58), (row3 19 36 59)]

def b101_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b101_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b101_15_rows b101_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b101_15_rows b101_15_labels]
    decide +kernel

theorem checked101 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_101 QuarticIntegerComputationalData.ids64_101 13798509515484254520000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b101_00_rows ++ b101_01_rows) ++ (b101_02_rows ++ b101_03_rows)) ++ ((b101_04_rows ++ b101_05_rows) ++ (b101_06_rows ++ b101_07_rows))) ++ (((b101_08_rows ++ b101_09_rows) ++ (b101_10_rows ++ b101_11_rows)) ++ ((b101_12_rows ++ b101_13_rows) ++ (b101_14_rows ++ b101_15_rows))))
    ((((b101_00_labels ++ b101_01_labels) ++ (b101_02_labels ++ b101_03_labels)) ++ ((b101_04_labels ++ b101_05_labels) ++ (b101_06_labels ++ b101_07_labels))) ++ (((b101_08_labels ++ b101_09_labels) ++ (b101_10_labels ++ b101_11_labels)) ++ ((b101_12_labels ++ b101_13_labels) ++ (b101_14_labels ++ b101_15_labels)))) 13798509515484254520000
  exact ((((b101_00_checked.append (c := 0) b101_01_checked (by decide +kernel)).append (c := 0) (b101_02_checked.append (c := 0) b101_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b101_04_checked.append (c := 0) b101_05_checked (by decide +kernel)).append (c := 0) (b101_06_checked.append (c := 0) b101_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 13798509515484254520000) (((b101_08_checked.append (c := 0) b101_09_checked (by decide +kernel)).append (c := 0) (b101_10_checked.append (c := 0) b101_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 13798509515484254520000) ((b101_12_checked.append (c := 10173141782965611225000) b101_13_checked (by decide +kernel)).append (c := 13798509515484254520000) (b101_14_checked.append (c := 3625367732518643295000) b101_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b102_00_rows : List Row := [(row3 19 36 60), (row3 19 36 61), (row3 19 36 62), (row3 19 36 63), (row3 19 37 38), (row3 19 37 39), (row3 19 37 40), (row3 19 37 41), (row3 19 37 42), (row3 19 37 43), (row3 19 37 44), (row3 19 37 45), (row3 19 37 46), (row3 19 37 47), (row3 19 37 48), (row3 19 37 49)]

def b102_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_00_rows b102_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_00_rows b102_00_labels]
    decide +kernel

def b102_01_rows : List Row := [(row3 19 37 50), (row3 19 37 51), (row3 19 37 52), (row3 19 37 53), (row3 19 37 54), (row3 19 37 55), (row3 19 37 56), (row3 19 37 57), (row3 19 37 58), (row3 19 37 59), (row3 19 37 60), (row3 19 37 61), (row3 19 37 62), (row3 19 37 63), (row3 19 38 39), (row3 19 38 40)]

def b102_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_01_rows b102_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_01_rows b102_01_labels]
    decide +kernel

def b102_02_rows : List Row := [(row3 19 38 41), (row3 19 38 42), (row3 19 38 43), (row3 19 38 44), (row3 19 38 45), (row3 19 38 46), (row3 19 38 47), (row3 19 38 48), (row3 19 38 49), (row3 19 38 50), (row3 19 38 51), (row3 19 38 52), (row3 19 38 53), (row3 19 38 54), (row3 19 38 55), (row3 19 38 56)]

def b102_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_02_rows b102_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_02_rows b102_02_labels]
    decide +kernel

def b102_03_rows : List Row := [(row3 19 38 57), (row3 19 38 58), (row3 19 38 59), (row3 19 38 60), (row3 19 38 61), (row3 19 38 62), (row3 19 38 63), (row3 19 39 40), (row3 19 39 41), (row3 19 39 42), (row3 19 39 43), (row3 19 39 44), (row3 19 39 45), (row3 19 39 46), (row3 19 39 47), (row3 19 39 48)]

def b102_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_03_rows b102_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_03_rows b102_03_labels]
    decide +kernel

def b102_04_rows : List Row := [(row3 19 39 49), (row3 19 39 50), (row3 19 39 51), (row3 19 39 52), (row3 19 39 53), (row3 19 39 54), (row3 19 39 55), (row3 19 39 56), (row3 19 39 57), (row3 19 39 58), (row3 19 39 59), (row3 19 39 60), (row3 19 39 61), (row3 19 39 62), (row3 19 39 63), (row3 19 40 41)]

def b102_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_04_rows b102_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_04_rows b102_04_labels]
    decide +kernel

def b102_05_rows : List Row := [(row3 19 40 42), (row3 19 40 43), (row3 19 40 44), (row3 19 40 45), (row3 19 40 46), (row3 19 40 47), (row3 19 40 48), (row3 19 40 49), (row3 19 40 50), (row3 19 40 51), (row3 19 40 52), (row3 19 40 53), (row3 19 40 54), (row3 19 40 55), (row3 19 40 56), (row3 19 40 57)]

def b102_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_05_rows b102_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_05_rows b102_05_labels]
    decide +kernel

def b102_06_rows : List Row := [(row3 19 40 58), (row3 19 40 59), (row3 19 40 60), (row3 19 40 61), (row3 19 40 62), (row3 19 40 63), (row3 19 41 42), (row3 19 41 43), (row3 19 41 44), (row3 19 41 45), (row3 19 41 46), (row3 19 41 47), (row3 19 41 48), (row3 19 41 49), (row3 19 41 50), (row3 19 41 51)]

def b102_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_06_rows b102_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_06_rows b102_06_labels]
    decide +kernel

def b102_07_rows : List Row := [(row3 19 41 52), (row3 19 41 53), (row3 19 41 54), (row3 19 41 55), (row3 19 41 56), (row3 19 41 57), (row3 19 41 58), (row3 19 41 59), (row3 19 41 60), (row3 19 41 61), (row3 19 41 62), (row3 19 41 63), (row3 19 42 43), (row3 19 42 44), (row3 19 42 45), (row3 19 42 46)]

def b102_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_07_rows b102_07_labels 25995303733821612075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_07_rows b102_07_labels]
    decide +kernel

def b102_08_rows : List Row := [(row3 19 42 47), (row3 19 42 48), (row3 19 42 49), (row3 19 42 50), (row3 19 42 51), (row3 19 42 52), (row3 19 42 53), (row3 19 42 54), (row3 19 42 55), (row3 19 42 56), (row3 19 42 57), (row3 19 42 58), (row3 19 42 59), (row3 19 42 60), (row3 19 42 61), (row3 19 42 62)]

def b102_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_08_rows b102_08_labels 269733504168948038841000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_08_rows b102_08_labels]
    decide +kernel

def b102_09_rows : List Row := [(row3 19 42 63), (row3 19 43 44), (row3 19 43 45), (row3 19 43 46), (row3 19 43 47), (row3 19 43 48), (row3 19 43 49), (row3 19 43 50), (row3 19 43 51), (row3 19 43 52), (row3 19 43 53), (row3 19 43 54), (row3 19 43 55), (row3 19 43 56), (row3 19 43 57), (row3 19 43 58)]

def b102_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246)]

theorem b102_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_09_rows b102_09_labels 28508345159883985575000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_09_rows b102_09_labels]
    decide +kernel

def b102_10_rows : List Row := [(row3 19 43 59), (row3 19 43 60), (row3 19 43 61), (row3 19 43 62), (row3 19 43 63), (row3 19 44 45), (row3 19 44 46), (row3 19 44 47), (row3 19 44 48), (row3 19 44 49), (row3 19 44 50), (row3 19 44 51), (row3 19 44 52), (row3 19 44 53), (row3 19 44 54), (row3 19 44 55)]

def b102_10_labels : List Row := [(row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_10_rows b102_10_labels 83136797542324941912000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_10_rows b102_10_labels]
    decide +kernel

def b102_11_rows : List Row := [(row3 19 44 56), (row3 19 44 57), (row3 19 44 58), (row3 19 44 59), (row3 19 44 60), (row3 19 44 61), (row3 19 44 62), (row3 19 44 63), (row3 19 45 46), (row3 19 45 47), (row3 19 45 48), (row3 19 45 49), (row3 19 45 50), (row3 19 45 51), (row3 19 45 52), (row3 19 45 53)]

def b102_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_11_rows b102_11_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_11_rows b102_11_labels]
    decide +kernel

def b102_12_rows : List Row := [(row3 19 45 54), (row3 19 45 55), (row3 19 45 56), (row3 19 45 57), (row3 19 45 58), (row3 19 45 59), (row3 19 45 60), (row3 19 45 61), (row3 19 45 62), (row3 19 45 63), (row3 19 46 47), (row3 19 46 48), (row3 19 46 49), (row3 19 46 50), (row3 19 46 51), (row3 19 46 52)]

def b102_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_12_rows b102_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_12_rows b102_12_labels]
    decide +kernel

def b102_13_rows : List Row := [(row3 19 46 53), (row3 19 46 54), (row3 19 46 55), (row3 19 46 56), (row3 19 46 57), (row3 19 46 58), (row3 19 46 59), (row3 19 46 60), (row3 19 46 61), (row3 19 46 62), (row3 19 46 63), (row3 19 47 48), (row3 19 47 49), (row3 19 47 50), (row3 19 47 51), (row3 19 47 52)]

def b102_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_13_rows b102_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_13_rows b102_13_labels]
    decide +kernel

def b102_14_rows : List Row := [(row3 19 47 53), (row3 19 47 54), (row3 19 47 55), (row3 19 47 56), (row3 19 47 57), (row3 19 47 58), (row3 19 47 59), (row3 19 47 60), (row3 19 47 61), (row3 19 47 62), (row3 19 47 63), (row3 19 48 49), (row3 19 48 50), (row3 19 48 51), (row3 19 48 52), (row3 19 48 53)]

def b102_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_14_rows b102_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_14_rows b102_14_labels]
    decide +kernel

def b102_15_rows : List Row := [(row3 19 48 54), (row3 19 48 55), (row3 19 48 56), (row3 19 48 57), (row3 19 48 58), (row3 19 48 59), (row3 19 48 60), (row3 19 48 61), (row3 19 48 62), (row3 19 48 63), (row3 19 49 50), (row3 19 49 51), (row3 19 49 52), (row3 19 49 53), (row3 19 49 54), (row3 19 49 55)]

def b102_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b102_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b102_15_rows b102_15_labels 38658314918891587455000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b102_15_rows b102_15_labels]
    decide +kernel

theorem checked102 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_102 QuarticIntegerComputationalData.ids64_102 453692365880773403583000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b102_00_rows ++ b102_01_rows) ++ (b102_02_rows ++ b102_03_rows)) ++ ((b102_04_rows ++ b102_05_rows) ++ (b102_06_rows ++ b102_07_rows))) ++ (((b102_08_rows ++ b102_09_rows) ++ (b102_10_rows ++ b102_11_rows)) ++ ((b102_12_rows ++ b102_13_rows) ++ (b102_14_rows ++ b102_15_rows))))
    ((((b102_00_labels ++ b102_01_labels) ++ (b102_02_labels ++ b102_03_labels)) ++ ((b102_04_labels ++ b102_05_labels) ++ (b102_06_labels ++ b102_07_labels))) ++ (((b102_08_labels ++ b102_09_labels) ++ (b102_10_labels ++ b102_11_labels)) ++ ((b102_12_labels ++ b102_13_labels) ++ (b102_14_labels ++ b102_15_labels)))) 453692365880773403583000
  exact ((((b102_00_checked.append (c := 0) b102_01_checked (by decide +kernel)).append (c := 0) (b102_02_checked.append (c := 0) b102_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 25995303733821612075000) ((b102_04_checked.append (c := 0) b102_05_checked (by decide +kernel)).append (c := 25995303733821612075000) (b102_06_checked.append (c := 25995303733821612075000) b102_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 453692365880773403583000) (((b102_08_checked.append (c := 298241849328832024416000) b102_09_checked (by decide +kernel)).append (c := 389038747228060204053000) (b102_10_checked.append (c := 90796897899228179637000) b102_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 427697062146951791508000) ((b102_12_checked.append (c := 0) b102_13_checked (by decide +kernel)).append (c := 38658314918891587455000) (b102_14_checked.append (c := 38658314918891587455000) b102_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b103_00_rows : List Row := [(row3 19 49 56), (row3 19 49 57), (row3 19 49 58), (row3 19 49 59), (row3 19 49 60), (row3 19 49 61), (row3 19 49 62), (row3 19 49 63), (row3 19 50 51), (row3 19 50 52), (row3 19 50 53), (row3 19 50 54), (row3 19 50 55), (row3 19 50 56), (row3 19 50 57), (row3 19 50 58)]

def b103_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284)]

theorem b103_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_00_rows b103_00_labels 60323211140783905484154000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_00_rows b103_00_labels]
    decide +kernel

def b103_01_rows : List Row := [(row3 19 50 59), (row3 19 50 60), (row3 19 50 61), (row3 19 50 62), (row3 19 50 63), (row3 19 51 52), (row3 19 51 53), (row3 19 51 54), (row3 19 51 55), (row3 19 51 56), (row3 19 51 57), (row3 19 51 58), (row3 19 51 59), (row3 19 51 60), (row3 19 51 61), (row3 19 51 62)]

def b103_01_labels : List Row := [(row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_01_rows b103_01_labels 20779774594073228482107000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_01_rows b103_01_labels]
    decide +kernel

def b103_02_rows : List Row := [(row3 19 51 63), (row3 19 52 53), (row3 19 52 54), (row3 19 52 55), (row3 19 52 56), (row3 19 52 57), (row3 19 52 58), (row3 19 52 59), (row3 19 52 60), (row3 19 52 61), (row3 19 52 62), (row3 19 52 63), (row3 19 53 54), (row3 19 53 55), (row3 19 53 56), (row3 19 53 57)]

def b103_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_02_rows b103_02_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_02_rows b103_02_labels]
    decide +kernel

def b103_03_rows : List Row := [(row3 19 53 58), (row3 19 53 59), (row3 19 53 60), (row3 19 53 61), (row3 19 53 62), (row3 19 53 63), (row3 19 54 55), (row3 19 54 56), (row3 19 54 57), (row3 19 54 58), (row3 19 54 59), (row3 19 54 60), (row3 19 54 61), (row3 19 54 62), (row3 19 54 63), (row3 19 55 56)]

def b103_03_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_03_rows b103_03_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_03_rows b103_03_labels]
    decide +kernel

def b103_04_rows : List Row := [(row3 19 55 57), (row3 19 55 58), (row3 19 55 59), (row3 19 55 60), (row3 19 55 61), (row3 19 55 62), (row3 19 55 63), (row3 19 56 57), (row3 19 56 58), (row3 19 56 59), (row3 19 56 60), (row3 19 56 61), (row3 19 56 62), (row3 19 56 63), (row3 19 57 58), (row3 19 57 59)]

def b103_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 238 238 462)]

theorem b103_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_04_rows b103_04_labels 64278611569512891437244000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_04_rows b103_04_labels]
    decide +kernel

def b103_05_rows : List Row := [(row3 19 57 60), (row3 19 57 61), (row3 19 57 62), (row3 19 57 63), (row3 19 58 59), (row3 19 58 60), (row3 19 58 61), (row3 19 58 62), (row3 19 58 63), (row3 19 59 60), (row3 19 59 61), (row3 19 59 62), (row3 19 59 63), (row3 19 60 61), (row3 19 60 62), (row3 19 60 63)]

def b103_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 254 10), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 263 462 263), (row3 238 462 238), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_05_rows b103_05_labels 537517548627797629394665500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_05_rows b103_05_labels]
    decide +kernel

def b103_06_rows : List Row := [(row3 19 61 62), (row3 19 61 63), (row3 19 62 63), (row3 20 21 22), (row3 20 21 23), (row3 20 21 24), (row3 20 21 25), (row3 20 21 26), (row3 20 21 27), (row3 20 21 28), (row3 20 21 29), (row3 20 21 30), (row3 20 21 31), (row3 20 21 32), (row3 20 21 33), (row3 20 21 34)]

def b103_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 180 462), (row3 265 266 266), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_06_rows b103_06_labels 816333993701002688906840400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_06_rows b103_06_labels]
    decide +kernel

def b103_07_rows : List Row := [(row3 20 21 35), (row3 20 21 36), (row3 20 21 37), (row3 20 21 38), (row3 20 21 39), (row3 20 21 40), (row3 20 21 41), (row3 20 21 42), (row3 20 21 43), (row3 20 21 44), (row3 20 21 45), (row3 20 21 46), (row3 20 21 47), (row3 20 21 48), (row3 20 21 49), (row3 20 21 50)]

def b103_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_07_rows b103_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_07_rows b103_07_labels]
    decide +kernel

def b103_08_rows : List Row := [(row3 20 21 51), (row3 20 21 52), (row3 20 21 53), (row3 20 21 54), (row3 20 21 55), (row3 20 21 56), (row3 20 21 57), (row3 20 21 58), (row3 20 21 59), (row3 20 21 60), (row3 20 21 61), (row3 20 21 62), (row3 20 21 63), (row3 20 22 23), (row3 20 22 24), (row3 20 22 25)]

def b103_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 370 88 211), (row3 234 462 234), (row3 462 462 462)]

theorem b103_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_08_rows b103_08_labels 9536936872765711861400346000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_08_rows b103_08_labels]
    decide +kernel

def b103_09_rows : List Row := [(row3 20 22 26), (row3 20 22 27), (row3 20 22 28), (row3 20 22 29), (row3 20 22 30), (row3 20 22 31), (row3 20 22 32), (row3 20 22 33), (row3 20 22 34), (row3 20 22 35), (row3 20 22 36), (row3 20 22 37), (row3 20 22 38), (row3 20 22 39), (row3 20 22 40), (row3 20 22 41)]

def b103_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 180 462 180), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 265 462 265), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462)]

theorem b103_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_09_rows b103_09_labels 547780952837763920036084400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_09_rows b103_09_labels]
    decide +kernel

def b103_10_rows : List Row := [(row3 20 22 42), (row3 20 22 43), (row3 20 22 44), (row3 20 22 45), (row3 20 22 46), (row3 20 22 47), (row3 20 22 48), (row3 20 22 49), (row3 20 22 50), (row3 20 22 51), (row3 20 22 52), (row3 20 22 53), (row3 20 22 54), (row3 20 22 55), (row3 20 22 56), (row3 20 22 57)]

def b103_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_10_rows b103_10_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_10_rows b103_10_labels]
    decide +kernel

def b103_11_rows : List Row := [(row3 20 22 58), (row3 20 22 59), (row3 20 22 60), (row3 20 22 61), (row3 20 22 62), (row3 20 22 63), (row3 20 23 24), (row3 20 23 25), (row3 20 23 26), (row3 20 23 27), (row3 20 23 28), (row3 20 23 29), (row3 20 23 30), (row3 20 23 31), (row3 20 23 32), (row3 20 23 33)]

def b103_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 278 279 279), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 278 279 279), (row3 180 154 154), (row3 234 234 234), (row3 462 244 244)]

theorem b103_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_11_rows b103_11_labels 819629676170091730845344700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_11_rows b103_11_labels]
    decide +kernel

def b103_12_rows : List Row := [(row3 20 23 34), (row3 20 23 35), (row3 20 23 36), (row3 20 23 37), (row3 20 23 38), (row3 20 23 39), (row3 20 23 40), (row3 20 23 41), (row3 20 23 42), (row3 20 23 43), (row3 20 23 44), (row3 20 23 45), (row3 20 23 46), (row3 20 23 47), (row3 20 23 48), (row3 20 23 49)]

def b103_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 234 234 234), (row3 265 266 266), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462)]

theorem b103_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_12_rows b103_12_labels 3676333273541756435421900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_12_rows b103_12_labels]
    decide +kernel

def b103_13_rows : List Row := [(row3 20 23 50), (row3 20 23 51), (row3 20 23 52), (row3 20 23 53), (row3 20 23 54), (row3 20 23 55), (row3 20 23 56), (row3 20 23 57), (row3 20 23 58), (row3 20 23 59), (row3 20 23 60), (row3 20 23 61), (row3 20 23 62), (row3 20 23 63), (row3 20 24 25), (row3 20 24 26)]

def b103_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462)]

theorem b103_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_13_rows b103_13_labels 543180656445072201742500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_13_rows b103_13_labels]
    decide +kernel

def b103_14_rows : List Row := [(row3 20 24 27), (row3 20 24 28), (row3 20 24 29), (row3 20 24 30), (row3 20 24 31), (row3 20 24 32), (row3 20 24 33), (row3 20 24 34), (row3 20 24 35), (row3 20 24 36), (row3 20 24 37), (row3 20 24 38), (row3 20 24 39), (row3 20 24 40), (row3 20 24 41), (row3 20 24 42)]

def b103_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_14_rows b103_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_14_rows b103_14_labels]
    decide +kernel

def b103_15_rows : List Row := [(row3 20 24 43), (row3 20 24 44), (row3 20 24 45), (row3 20 24 46), (row3 20 24 47), (row3 20 24 48), (row3 20 24 49), (row3 20 24 50), (row3 20 24 51), (row3 20 24 52), (row3 20 24 53), (row3 20 24 54), (row3 20 24 55), (row3 20 24 56), (row3 20 24 57), (row3 20 24 58)]

def b103_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b103_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b103_15_rows b103_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b103_15_rows b103_15_labels]
    decide +kernel

theorem checked103 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_103 QuarticIntegerComputationalData.ids64_103 12408214415511378986485076400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b103_00_rows ++ b103_01_rows) ++ (b103_02_rows ++ b103_03_rows)) ++ ((b103_04_rows ++ b103_05_rows) ++ (b103_06_rows ++ b103_07_rows))) ++ (((b103_08_rows ++ b103_09_rows) ++ (b103_10_rows ++ b103_11_rows)) ++ ((b103_12_rows ++ b103_13_rows) ++ (b103_14_rows ++ b103_15_rows))))
    ((((b103_00_labels ++ b103_01_labels) ++ (b103_02_labels ++ b103_03_labels)) ++ ((b103_04_labels ++ b103_05_labels) ++ (b103_06_labels ++ b103_07_labels))) ++ (((b103_08_labels ++ b103_09_labels) ++ (b103_10_labels ++ b103_11_labels)) ++ ((b103_12_labels ++ b103_13_labels) ++ (b103_14_labels ++ b103_15_labels)))) 12408214415511378986485076400
  exact ((((b103_00_checked.append (c := 81102985734857133966261000) b103_01_checked (by decide +kernel)).append (c := 81394651215062126743749000) (b103_02_checked.append (c := 291665480204992777488000) b103_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1499524805113375336482498900) ((b103_04_checked.append (c := 601796160197310520831909500) b103_05_checked (by decide +kernel)).append (c := 1418130153898313209738749900) (b103_06_checked.append (c := 816333993701002688906840400) b103_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 12408214415511378986485076400) (((b103_08_checked.append (c := 10084717825603475781436430400) b103_09_checked (by decide +kernel)).append (c := 10904470096468016821365413100) (b103_10_checked.append (c := 819752270864541039928982700) b103_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 10908689610398003650002577500) ((b103_12_checked.append (c := 4219513929986828637164400) b103_13_checked (by decide +kernel)).append (c := 4219513929986828637164400) (b103_14_checked.append (c := 0) b103_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b104_00_rows : List Row := [(row3 20 24 59), (row3 20 24 60), (row3 20 24 61), (row3 20 24 62), (row3 20 24 63), (row3 20 25 26), (row3 20 25 27), (row3 20 25 28), (row3 20 25 29), (row3 20 25 30), (row3 20 25 31), (row3 20 25 32), (row3 20 25 33), (row3 20 25 34), (row3 20 25 35), (row3 20 25 36)]

def b104_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_00_rows b104_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_00_rows b104_00_labels]
    decide +kernel

def b104_01_rows : List Row := [(row3 20 25 37), (row3 20 25 38), (row3 20 25 39), (row3 20 25 40), (row3 20 25 41), (row3 20 25 42), (row3 20 25 43), (row3 20 25 44), (row3 20 25 45), (row3 20 25 46), (row3 20 25 47), (row3 20 25 48), (row3 20 25 49), (row3 20 25 50), (row3 20 25 51), (row3 20 25 52)]

def b104_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_01_rows b104_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_01_rows b104_01_labels]
    decide +kernel

def b104_02_rows : List Row := [(row3 20 25 53), (row3 20 25 54), (row3 20 25 55), (row3 20 25 56), (row3 20 25 57), (row3 20 25 58), (row3 20 25 59), (row3 20 25 60), (row3 20 25 61), (row3 20 25 62), (row3 20 25 63), (row3 20 26 27), (row3 20 26 28), (row3 20 26 29), (row3 20 26 30), (row3 20 26 31)]

def b104_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_02_rows b104_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_02_rows b104_02_labels]
    decide +kernel

def b104_03_rows : List Row := [(row3 20 26 32), (row3 20 26 33), (row3 20 26 34), (row3 20 26 35), (row3 20 26 36), (row3 20 26 37), (row3 20 26 38), (row3 20 26 39), (row3 20 26 40), (row3 20 26 41), (row3 20 26 42), (row3 20 26 43), (row3 20 26 44), (row3 20 26 45), (row3 20 26 46), (row3 20 26 47)]

def b104_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_03_rows b104_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_03_rows b104_03_labels]
    decide +kernel

def b104_04_rows : List Row := [(row3 20 26 48), (row3 20 26 49), (row3 20 26 50), (row3 20 26 51), (row3 20 26 52), (row3 20 26 53), (row3 20 26 54), (row3 20 26 55), (row3 20 26 56), (row3 20 26 57), (row3 20 26 58), (row3 20 26 59), (row3 20 26 60), (row3 20 26 61), (row3 20 26 62), (row3 20 26 63)]

def b104_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_04_rows b104_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_04_rows b104_04_labels]
    decide +kernel

def b104_05_rows : List Row := [(row3 20 27 28), (row3 20 27 29), (row3 20 27 30), (row3 20 27 31), (row3 20 27 32), (row3 20 27 33), (row3 20 27 34), (row3 20 27 35), (row3 20 27 36), (row3 20 27 37), (row3 20 27 38), (row3 20 27 39), (row3 20 27 40), (row3 20 27 41), (row3 20 27 42), (row3 20 27 43)]

def b104_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_05_rows b104_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_05_rows b104_05_labels]
    decide +kernel

def b104_06_rows : List Row := [(row3 20 27 44), (row3 20 27 45), (row3 20 27 46), (row3 20 27 47), (row3 20 27 48), (row3 20 27 49), (row3 20 27 50), (row3 20 27 51), (row3 20 27 52), (row3 20 27 53), (row3 20 27 54), (row3 20 27 55), (row3 20 27 56), (row3 20 27 57), (row3 20 27 58), (row3 20 27 59)]

def b104_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_06_rows b104_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_06_rows b104_06_labels]
    decide +kernel

def b104_07_rows : List Row := [(row3 20 27 60), (row3 20 27 61), (row3 20 27 62), (row3 20 27 63), (row3 20 28 29), (row3 20 28 30), (row3 20 28 31), (row3 20 28 32), (row3 20 28 33), (row3 20 28 34), (row3 20 28 35), (row3 20 28 36), (row3 20 28 37), (row3 20 28 38), (row3 20 28 39), (row3 20 28 40)]

def b104_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_07_rows b104_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_07_rows b104_07_labels]
    decide +kernel

def b104_08_rows : List Row := [(row3 20 28 41), (row3 20 28 42), (row3 20 28 43), (row3 20 28 44), (row3 20 28 45), (row3 20 28 46), (row3 20 28 47), (row3 20 28 48), (row3 20 28 49), (row3 20 28 50), (row3 20 28 51), (row3 20 28 52), (row3 20 28 53), (row3 20 28 54), (row3 20 28 55), (row3 20 28 56)]

def b104_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_08_rows b104_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_08_rows b104_08_labels]
    decide +kernel

def b104_09_rows : List Row := [(row3 20 28 57), (row3 20 28 58), (row3 20 28 59), (row3 20 28 60), (row3 20 28 61), (row3 20 28 62), (row3 20 28 63), (row3 20 29 30), (row3 20 29 31), (row3 20 29 32), (row3 20 29 33), (row3 20 29 34), (row3 20 29 35), (row3 20 29 36), (row3 20 29 37), (row3 20 29 38)]

def b104_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_09_rows b104_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_09_rows b104_09_labels]
    decide +kernel

def b104_10_rows : List Row := [(row3 20 29 39), (row3 20 29 40), (row3 20 29 41), (row3 20 29 42), (row3 20 29 43), (row3 20 29 44), (row3 20 29 45), (row3 20 29 46), (row3 20 29 47), (row3 20 29 48), (row3 20 29 49), (row3 20 29 50), (row3 20 29 51), (row3 20 29 52), (row3 20 29 53), (row3 20 29 54)]

def b104_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_10_rows b104_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_10_rows b104_10_labels]
    decide +kernel

def b104_11_rows : List Row := [(row3 20 29 55), (row3 20 29 56), (row3 20 29 57), (row3 20 29 58), (row3 20 29 59), (row3 20 29 60), (row3 20 29 61), (row3 20 29 62), (row3 20 29 63), (row3 20 30 31), (row3 20 30 32), (row3 20 30 33), (row3 20 30 34), (row3 20 30 35), (row3 20 30 36), (row3 20 30 37)]

def b104_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_11_rows b104_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_11_rows b104_11_labels]
    decide +kernel

def b104_12_rows : List Row := [(row3 20 30 38), (row3 20 30 39), (row3 20 30 40), (row3 20 30 41), (row3 20 30 42), (row3 20 30 43), (row3 20 30 44), (row3 20 30 45), (row3 20 30 46), (row3 20 30 47), (row3 20 30 48), (row3 20 30 49), (row3 20 30 50), (row3 20 30 51), (row3 20 30 52), (row3 20 30 53)]

def b104_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_12_rows b104_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_12_rows b104_12_labels]
    decide +kernel

def b104_13_rows : List Row := [(row3 20 30 54), (row3 20 30 55), (row3 20 30 56), (row3 20 30 57), (row3 20 30 58), (row3 20 30 59), (row3 20 30 60), (row3 20 30 61), (row3 20 30 62), (row3 20 30 63), (row3 20 31 32), (row3 20 31 33), (row3 20 31 34), (row3 20 31 35), (row3 20 31 36), (row3 20 31 37)]

def b104_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_13_rows b104_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_13_rows b104_13_labels]
    decide +kernel

def b104_14_rows : List Row := [(row3 20 31 38), (row3 20 31 39), (row3 20 31 40), (row3 20 31 41), (row3 20 31 42), (row3 20 31 43), (row3 20 31 44), (row3 20 31 45), (row3 20 31 46), (row3 20 31 47), (row3 20 31 48), (row3 20 31 49), (row3 20 31 50), (row3 20 31 51), (row3 20 31 52), (row3 20 31 53)]

def b104_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_14_rows b104_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_14_rows b104_14_labels]
    decide +kernel

def b104_15_rows : List Row := [(row3 20 31 54), (row3 20 31 55), (row3 20 31 56), (row3 20 31 57), (row3 20 31 58), (row3 20 31 59), (row3 20 31 60), (row3 20 31 61), (row3 20 31 62), (row3 20 31 63), (row3 20 32 33), (row3 20 32 34), (row3 20 32 35), (row3 20 32 36), (row3 20 32 37), (row3 20 32 38)]

def b104_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b104_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b104_15_rows b104_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b104_15_rows b104_15_labels]
    decide +kernel

theorem checked104 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_104 QuarticIntegerComputationalData.ids64_104 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b104_00_rows ++ b104_01_rows) ++ (b104_02_rows ++ b104_03_rows)) ++ ((b104_04_rows ++ b104_05_rows) ++ (b104_06_rows ++ b104_07_rows))) ++ (((b104_08_rows ++ b104_09_rows) ++ (b104_10_rows ++ b104_11_rows)) ++ ((b104_12_rows ++ b104_13_rows) ++ (b104_14_rows ++ b104_15_rows))))
    ((((b104_00_labels ++ b104_01_labels) ++ (b104_02_labels ++ b104_03_labels)) ++ ((b104_04_labels ++ b104_05_labels) ++ (b104_06_labels ++ b104_07_labels))) ++ (((b104_08_labels ++ b104_09_labels) ++ (b104_10_labels ++ b104_11_labels)) ++ ((b104_12_labels ++ b104_13_labels) ++ (b104_14_labels ++ b104_15_labels)))) 0
  exact ((((b104_00_checked.append (c := 0) b104_01_checked (by decide +kernel)).append (c := 0) (b104_02_checked.append (c := 0) b104_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b104_04_checked.append (c := 0) b104_05_checked (by decide +kernel)).append (c := 0) (b104_06_checked.append (c := 0) b104_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b104_08_checked.append (c := 0) b104_09_checked (by decide +kernel)).append (c := 0) (b104_10_checked.append (c := 0) b104_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b104_12_checked.append (c := 0) b104_13_checked (by decide +kernel)).append (c := 0) (b104_14_checked.append (c := 0) b104_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
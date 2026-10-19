import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch015
import Dressed.QuarticIntegerComputationalData64.Batch016


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b129_00_rows : List Row := [(row3 28 46 58), (row3 28 46 59), (row3 28 46 60), (row3 28 46 61), (row3 28 46 62), (row3 28 46 63), (row3 28 47 48), (row3 28 47 49), (row3 28 47 50), (row3 28 47 51), (row3 28 47 52), (row3 28 47 53), (row3 28 47 54), (row3 28 47 55), (row3 28 47 56), (row3 28 47 57)]

def b129_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_00_rows b129_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_00_rows b129_00_labels]
    decide +kernel

def b129_01_rows : List Row := [(row3 28 47 58), (row3 28 47 59), (row3 28 47 60), (row3 28 47 61), (row3 28 47 62), (row3 28 47 63), (row3 28 48 49), (row3 28 48 50), (row3 28 48 51), (row3 28 48 52), (row3 28 48 53), (row3 28 48 54), (row3 28 48 55), (row3 28 48 56), (row3 28 48 57), (row3 28 48 58)]

def b129_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_01_rows b129_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_01_rows b129_01_labels]
    decide +kernel

def b129_02_rows : List Row := [(row3 28 48 59), (row3 28 48 60), (row3 28 48 61), (row3 28 48 62), (row3 28 48 63), (row3 28 49 50), (row3 28 49 51), (row3 28 49 52), (row3 28 49 53), (row3 28 49 54), (row3 28 49 55), (row3 28 49 56), (row3 28 49 57), (row3 28 49 58), (row3 28 49 59), (row3 28 49 60)]

def b129_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_02_rows b129_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_02_rows b129_02_labels]
    decide +kernel

def b129_03_rows : List Row := [(row3 28 49 61), (row3 28 49 62), (row3 28 49 63), (row3 28 50 51), (row3 28 50 52), (row3 28 50 53), (row3 28 50 54), (row3 28 50 55), (row3 28 50 56), (row3 28 50 57), (row3 28 50 58), (row3 28 50 59), (row3 28 50 60), (row3 28 50 61), (row3 28 50 62), (row3 28 50 63)]

def b129_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_03_rows b129_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_03_rows b129_03_labels]
    decide +kernel

def b129_04_rows : List Row := [(row3 28 51 52), (row3 28 51 53), (row3 28 51 54), (row3 28 51 55), (row3 28 51 56), (row3 28 51 57), (row3 28 51 58), (row3 28 51 59), (row3 28 51 60), (row3 28 51 61), (row3 28 51 62), (row3 28 51 63), (row3 28 52 53), (row3 28 52 54), (row3 28 52 55), (row3 28 52 56)]

def b129_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_04_rows b129_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_04_rows b129_04_labels]
    decide +kernel

def b129_05_rows : List Row := [(row3 28 52 57), (row3 28 52 58), (row3 28 52 59), (row3 28 52 60), (row3 28 52 61), (row3 28 52 62), (row3 28 52 63), (row3 28 53 54), (row3 28 53 55), (row3 28 53 56), (row3 28 53 57), (row3 28 53 58), (row3 28 53 59), (row3 28 53 60), (row3 28 53 61), (row3 28 53 62)]

def b129_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_05_rows b129_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_05_rows b129_05_labels]
    decide +kernel

def b129_06_rows : List Row := [(row3 28 53 63), (row3 28 54 55), (row3 28 54 56), (row3 28 54 57), (row3 28 54 58), (row3 28 54 59), (row3 28 54 60), (row3 28 54 61), (row3 28 54 62), (row3 28 54 63), (row3 28 55 56), (row3 28 55 57), (row3 28 55 58), (row3 28 55 59), (row3 28 55 60), (row3 28 55 61)]

def b129_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_06_rows b129_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_06_rows b129_06_labels]
    decide +kernel

def b129_07_rows : List Row := [(row3 28 55 62), (row3 28 55 63), (row3 28 56 57), (row3 28 56 58), (row3 28 56 59), (row3 28 56 60), (row3 28 56 61), (row3 28 56 62), (row3 28 56 63), (row3 28 57 58), (row3 28 57 59), (row3 28 57 60), (row3 28 57 61), (row3 28 57 62), (row3 28 57 63), (row3 28 58 59)]

def b129_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_07_rows b129_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_07_rows b129_07_labels]
    decide +kernel

def b129_08_rows : List Row := [(row3 28 58 60), (row3 28 58 61), (row3 28 58 62), (row3 28 58 63), (row3 28 59 60), (row3 28 59 61), (row3 28 59 62), (row3 28 59 63), (row3 28 60 61), (row3 28 60 62), (row3 28 60 63), (row3 28 61 62), (row3 28 61 63), (row3 28 62 63), (row3 29 30 31), (row3 29 30 32)]

def b129_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 462 462 462)]

theorem b129_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_08_rows b129_08_labels 505969794941044656167064000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_08_rows b129_08_labels]
    decide +kernel

def b129_09_rows : List Row := [(row3 29 30 33), (row3 29 30 34), (row3 29 30 35), (row3 29 30 36), (row3 29 30 37), (row3 29 30 38), (row3 29 30 39), (row3 29 30 40), (row3 29 30 41), (row3 29 30 42), (row3 29 30 43), (row3 29 30 44), (row3 29 30 45), (row3 29 30 46), (row3 29 30 47), (row3 29 30 48)]

def b129_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_09_rows b129_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_09_rows b129_09_labels]
    decide +kernel

def b129_10_rows : List Row := [(row3 29 30 49), (row3 29 30 50), (row3 29 30 51), (row3 29 30 52), (row3 29 30 53), (row3 29 30 54), (row3 29 30 55), (row3 29 30 56), (row3 29 30 57), (row3 29 30 58), (row3 29 30 59), (row3 29 30 60), (row3 29 30 61), (row3 29 30 62), (row3 29 30 63), (row3 29 31 32)]

def b129_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273)]

theorem b129_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_10_rows b129_10_labels 5828466918259689747321600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_10_rows b129_10_labels]
    decide +kernel

def b129_11_rows : List Row := [(row3 29 31 33), (row3 29 31 34), (row3 29 31 35), (row3 29 31 36), (row3 29 31 37), (row3 29 31 38), (row3 29 31 39), (row3 29 31 40), (row3 29 31 41), (row3 29 31 42), (row3 29 31 43), (row3 29 31 44), (row3 29 31 45), (row3 29 31 46), (row3 29 31 47), (row3 29 31 48)]

def b129_11_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 193 462 193), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 261 462 261), (row3 462 462 462)]

theorem b129_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_11_rows b129_11_labels 359660884122215403186312000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_11_rows b129_11_labels]
    decide +kernel

def b129_12_rows : List Row := [(row3 29 31 49), (row3 29 31 50), (row3 29 31 51), (row3 29 31 52), (row3 29 31 53), (row3 29 31 54), (row3 29 31 55), (row3 29 31 56), (row3 29 31 57), (row3 29 31 58), (row3 29 31 59), (row3 29 31 60), (row3 29 31 61), (row3 29 31 62), (row3 29 31 63), (row3 29 32 33)]

def b129_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_12_rows b129_12_labels 121705541119974164220000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_12_rows b129_12_labels]
    decide +kernel

def b129_13_rows : List Row := [(row3 29 32 34), (row3 29 32 35), (row3 29 32 36), (row3 29 32 37), (row3 29 32 38), (row3 29 32 39), (row3 29 32 40), (row3 29 32 41), (row3 29 32 42), (row3 29 32 43), (row3 29 32 44), (row3 29 32 45), (row3 29 32 46), (row3 29 32 47), (row3 29 32 48), (row3 29 32 49)]

def b129_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_13_rows b129_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_13_rows b129_13_labels]
    decide +kernel

def b129_14_rows : List Row := [(row3 29 32 50), (row3 29 32 51), (row3 29 32 52), (row3 29 32 53), (row3 29 32 54), (row3 29 32 55), (row3 29 32 56), (row3 29 32 57), (row3 29 32 58), (row3 29 32 59), (row3 29 32 60), (row3 29 32 61), (row3 29 32 62), (row3 29 32 63), (row3 29 33 34), (row3 29 33 35)]

def b129_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_14_rows b129_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_14_rows b129_14_labels]
    decide +kernel

def b129_15_rows : List Row := [(row3 29 33 36), (row3 29 33 37), (row3 29 33 38), (row3 29 33 39), (row3 29 33 40), (row3 29 33 41), (row3 29 33 42), (row3 29 33 43), (row3 29 33 44), (row3 29 33 45), (row3 29 33 46), (row3 29 33 47), (row3 29 33 48), (row3 29 33 49), (row3 29 33 50), (row3 29 33 51)]

def b129_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b129_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b129_15_rows b129_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b129_15_rows b129_15_labels]
    decide +kernel

theorem checked129 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_129 QuarticIntegerComputationalData.ids64_129 871580851522639723264917600 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b129_00_rows ++ b129_01_rows) ++ (b129_02_rows ++ b129_03_rows)) ++ ((b129_04_rows ++ b129_05_rows) ++ (b129_06_rows ++ b129_07_rows))) ++ (((b129_08_rows ++ b129_09_rows) ++ (b129_10_rows ++ b129_11_rows)) ++ ((b129_12_rows ++ b129_13_rows) ++ (b129_14_rows ++ b129_15_rows))))
    ((((b129_00_labels ++ b129_01_labels) ++ (b129_02_labels ++ b129_03_labels)) ++ ((b129_04_labels ++ b129_05_labels) ++ (b129_06_labels ++ b129_07_labels))) ++ (((b129_08_labels ++ b129_09_labels) ++ (b129_10_labels ++ b129_11_labels)) ++ ((b129_12_labels ++ b129_13_labels) ++ (b129_14_labels ++ b129_15_labels)))) 871580851522639723264917600
  exact ((((b129_00_checked.append (c := 0) b129_01_checked (by decide +kernel)).append (c := 0) (b129_02_checked.append (c := 0) b129_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b129_04_checked.append (c := 0) b129_05_checked (by decide +kernel)).append (c := 0) (b129_06_checked.append (c := 0) b129_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 871580851522639723264917600) (((b129_08_checked.append (c := 505969794941044656167064000) b129_09_checked (by decide +kernel)).append (c := 871459145981519749100697600) (b129_10_checked.append (c := 365489351040475092933633600) b129_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 871580851522639723264917600) ((b129_12_checked.append (c := 121705541119974164220000) b129_13_checked (by decide +kernel)).append (c := 121705541119974164220000) (b129_14_checked.append (c := 0) b129_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b130_00_rows : List Row := [(row3 29 33 52), (row3 29 33 53), (row3 29 33 54), (row3 29 33 55), (row3 29 33 56), (row3 29 33 57), (row3 29 33 58), (row3 29 33 59), (row3 29 33 60), (row3 29 33 61), (row3 29 33 62), (row3 29 33 63), (row3 29 34 35), (row3 29 34 36), (row3 29 34 37), (row3 29 34 38)]

def b130_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_00_rows b130_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_00_rows b130_00_labels]
    decide +kernel

def b130_01_rows : List Row := [(row3 29 34 39), (row3 29 34 40), (row3 29 34 41), (row3 29 34 42), (row3 29 34 43), (row3 29 34 44), (row3 29 34 45), (row3 29 34 46), (row3 29 34 47), (row3 29 34 48), (row3 29 34 49), (row3 29 34 50), (row3 29 34 51), (row3 29 34 52), (row3 29 34 53), (row3 29 34 54)]

def b130_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_01_rows b130_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_01_rows b130_01_labels]
    decide +kernel

def b130_02_rows : List Row := [(row3 29 34 55), (row3 29 34 56), (row3 29 34 57), (row3 29 34 58), (row3 29 34 59), (row3 29 34 60), (row3 29 34 61), (row3 29 34 62), (row3 29 34 63), (row3 29 35 36), (row3 29 35 37), (row3 29 35 38), (row3 29 35 39), (row3 29 35 40), (row3 29 35 41), (row3 29 35 42)]

def b130_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_02_rows b130_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_02_rows b130_02_labels]
    decide +kernel

def b130_03_rows : List Row := [(row3 29 35 43), (row3 29 35 44), (row3 29 35 45), (row3 29 35 46), (row3 29 35 47), (row3 29 35 48), (row3 29 35 49), (row3 29 35 50), (row3 29 35 51), (row3 29 35 52), (row3 29 35 53), (row3 29 35 54), (row3 29 35 55), (row3 29 35 56), (row3 29 35 57), (row3 29 35 58)]

def b130_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_03_rows b130_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_03_rows b130_03_labels]
    decide +kernel

def b130_04_rows : List Row := [(row3 29 35 59), (row3 29 35 60), (row3 29 35 61), (row3 29 35 62), (row3 29 35 63), (row3 29 36 37), (row3 29 36 38), (row3 29 36 39), (row3 29 36 40), (row3 29 36 41), (row3 29 36 42), (row3 29 36 43), (row3 29 36 44), (row3 29 36 45), (row3 29 36 46), (row3 29 36 47)]

def b130_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_04_rows b130_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_04_rows b130_04_labels]
    decide +kernel

def b130_05_rows : List Row := [(row3 29 36 48), (row3 29 36 49), (row3 29 36 50), (row3 29 36 51), (row3 29 36 52), (row3 29 36 53), (row3 29 36 54), (row3 29 36 55), (row3 29 36 56), (row3 29 36 57), (row3 29 36 58), (row3 29 36 59), (row3 29 36 60), (row3 29 36 61), (row3 29 36 62), (row3 29 36 63)]

def b130_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_05_rows b130_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_05_rows b130_05_labels]
    decide +kernel

def b130_06_rows : List Row := [(row3 29 37 38), (row3 29 37 39), (row3 29 37 40), (row3 29 37 41), (row3 29 37 42), (row3 29 37 43), (row3 29 37 44), (row3 29 37 45), (row3 29 37 46), (row3 29 37 47), (row3 29 37 48), (row3 29 37 49), (row3 29 37 50), (row3 29 37 51), (row3 29 37 52), (row3 29 37 53)]

def b130_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_06_rows b130_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_06_rows b130_06_labels]
    decide +kernel

def b130_07_rows : List Row := [(row3 29 37 54), (row3 29 37 55), (row3 29 37 56), (row3 29 37 57), (row3 29 37 58), (row3 29 37 59), (row3 29 37 60), (row3 29 37 61), (row3 29 37 62), (row3 29 37 63), (row3 29 38 39), (row3 29 38 40), (row3 29 38 41), (row3 29 38 42), (row3 29 38 43), (row3 29 38 44)]

def b130_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_07_rows b130_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_07_rows b130_07_labels]
    decide +kernel

def b130_08_rows : List Row := [(row3 29 38 45), (row3 29 38 46), (row3 29 38 47), (row3 29 38 48), (row3 29 38 49), (row3 29 38 50), (row3 29 38 51), (row3 29 38 52), (row3 29 38 53), (row3 29 38 54), (row3 29 38 55), (row3 29 38 56), (row3 29 38 57), (row3 29 38 58), (row3 29 38 59), (row3 29 38 60)]

def b130_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_08_rows b130_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_08_rows b130_08_labels]
    decide +kernel

def b130_09_rows : List Row := [(row3 29 38 61), (row3 29 38 62), (row3 29 38 63), (row3 29 39 40), (row3 29 39 41), (row3 29 39 42), (row3 29 39 43), (row3 29 39 44), (row3 29 39 45), (row3 29 39 46), (row3 29 39 47), (row3 29 39 48), (row3 29 39 49), (row3 29 39 50), (row3 29 39 51), (row3 29 39 52)]

def b130_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_09_rows b130_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_09_rows b130_09_labels]
    decide +kernel

def b130_10_rows : List Row := [(row3 29 39 53), (row3 29 39 54), (row3 29 39 55), (row3 29 39 56), (row3 29 39 57), (row3 29 39 58), (row3 29 39 59), (row3 29 39 60), (row3 29 39 61), (row3 29 39 62), (row3 29 39 63), (row3 29 40 41), (row3 29 40 42), (row3 29 40 43), (row3 29 40 44), (row3 29 40 45)]

def b130_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_10_rows b130_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_10_rows b130_10_labels]
    decide +kernel

def b130_11_rows : List Row := [(row3 29 40 46), (row3 29 40 47), (row3 29 40 48), (row3 29 40 49), (row3 29 40 50), (row3 29 40 51), (row3 29 40 52), (row3 29 40 53), (row3 29 40 54), (row3 29 40 55), (row3 29 40 56), (row3 29 40 57), (row3 29 40 58), (row3 29 40 59), (row3 29 40 60), (row3 29 40 61)]

def b130_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_11_rows b130_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_11_rows b130_11_labels]
    decide +kernel

def b130_12_rows : List Row := [(row3 29 40 62), (row3 29 40 63), (row3 29 41 42), (row3 29 41 43), (row3 29 41 44), (row3 29 41 45), (row3 29 41 46), (row3 29 41 47), (row3 29 41 48), (row3 29 41 49), (row3 29 41 50), (row3 29 41 51), (row3 29 41 52), (row3 29 41 53), (row3 29 41 54), (row3 29 41 55)]

def b130_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_12_rows b130_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_12_rows b130_12_labels]
    decide +kernel

def b130_13_rows : List Row := [(row3 29 41 56), (row3 29 41 57), (row3 29 41 58), (row3 29 41 59), (row3 29 41 60), (row3 29 41 61), (row3 29 41 62), (row3 29 41 63), (row3 29 42 43), (row3 29 42 44), (row3 29 42 45), (row3 29 42 46), (row3 29 42 47), (row3 29 42 48), (row3 29 42 49), (row3 29 42 50)]

def b130_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_13_rows b130_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_13_rows b130_13_labels]
    decide +kernel

def b130_14_rows : List Row := [(row3 29 42 51), (row3 29 42 52), (row3 29 42 53), (row3 29 42 54), (row3 29 42 55), (row3 29 42 56), (row3 29 42 57), (row3 29 42 58), (row3 29 42 59), (row3 29 42 60), (row3 29 42 61), (row3 29 42 62), (row3 29 42 63), (row3 29 43 44), (row3 29 43 45), (row3 29 43 46)]

def b130_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_14_rows b130_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_14_rows b130_14_labels]
    decide +kernel

def b130_15_rows : List Row := [(row3 29 43 47), (row3 29 43 48), (row3 29 43 49), (row3 29 43 50), (row3 29 43 51), (row3 29 43 52), (row3 29 43 53), (row3 29 43 54), (row3 29 43 55), (row3 29 43 56), (row3 29 43 57), (row3 29 43 58), (row3 29 43 59), (row3 29 43 60), (row3 29 43 61), (row3 29 43 62)]

def b130_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b130_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b130_15_rows b130_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b130_15_rows b130_15_labels]
    decide +kernel

theorem checked130 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_130 QuarticIntegerComputationalData.ids64_130 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b130_00_rows ++ b130_01_rows) ++ (b130_02_rows ++ b130_03_rows)) ++ ((b130_04_rows ++ b130_05_rows) ++ (b130_06_rows ++ b130_07_rows))) ++ (((b130_08_rows ++ b130_09_rows) ++ (b130_10_rows ++ b130_11_rows)) ++ ((b130_12_rows ++ b130_13_rows) ++ (b130_14_rows ++ b130_15_rows))))
    ((((b130_00_labels ++ b130_01_labels) ++ (b130_02_labels ++ b130_03_labels)) ++ ((b130_04_labels ++ b130_05_labels) ++ (b130_06_labels ++ b130_07_labels))) ++ (((b130_08_labels ++ b130_09_labels) ++ (b130_10_labels ++ b130_11_labels)) ++ ((b130_12_labels ++ b130_13_labels) ++ (b130_14_labels ++ b130_15_labels)))) 0
  exact ((((b130_00_checked.append (c := 0) b130_01_checked (by decide +kernel)).append (c := 0) (b130_02_checked.append (c := 0) b130_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b130_04_checked.append (c := 0) b130_05_checked (by decide +kernel)).append (c := 0) (b130_06_checked.append (c := 0) b130_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b130_08_checked.append (c := 0) b130_09_checked (by decide +kernel)).append (c := 0) (b130_10_checked.append (c := 0) b130_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b130_12_checked.append (c := 0) b130_13_checked (by decide +kernel)).append (c := 0) (b130_14_checked.append (c := 0) b130_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b131_00_rows : List Row := [(row3 29 43 63), (row3 29 44 45), (row3 29 44 46), (row3 29 44 47), (row3 29 44 48), (row3 29 44 49), (row3 29 44 50), (row3 29 44 51), (row3 29 44 52), (row3 29 44 53), (row3 29 44 54), (row3 29 44 55), (row3 29 44 56), (row3 29 44 57), (row3 29 44 58), (row3 29 44 59)]

def b131_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_00_rows b131_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_00_rows b131_00_labels]
    decide +kernel

def b131_01_rows : List Row := [(row3 29 44 60), (row3 29 44 61), (row3 29 44 62), (row3 29 44 63), (row3 29 45 46), (row3 29 45 47), (row3 29 45 48), (row3 29 45 49), (row3 29 45 50), (row3 29 45 51), (row3 29 45 52), (row3 29 45 53), (row3 29 45 54), (row3 29 45 55), (row3 29 45 56), (row3 29 45 57)]

def b131_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_01_rows b131_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_01_rows b131_01_labels]
    decide +kernel

def b131_02_rows : List Row := [(row3 29 45 58), (row3 29 45 59), (row3 29 45 60), (row3 29 45 61), (row3 29 45 62), (row3 29 45 63), (row3 29 46 47), (row3 29 46 48), (row3 29 46 49), (row3 29 46 50), (row3 29 46 51), (row3 29 46 52), (row3 29 46 53), (row3 29 46 54), (row3 29 46 55), (row3 29 46 56)]

def b131_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_02_rows b131_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_02_rows b131_02_labels]
    decide +kernel

def b131_03_rows : List Row := [(row3 29 46 57), (row3 29 46 58), (row3 29 46 59), (row3 29 46 60), (row3 29 46 61), (row3 29 46 62), (row3 29 46 63), (row3 29 47 48), (row3 29 47 49), (row3 29 47 50), (row3 29 47 51), (row3 29 47 52), (row3 29 47 53), (row3 29 47 54), (row3 29 47 55), (row3 29 47 56)]

def b131_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_03_rows b131_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_03_rows b131_03_labels]
    decide +kernel

def b131_04_rows : List Row := [(row3 29 47 57), (row3 29 47 58), (row3 29 47 59), (row3 29 47 60), (row3 29 47 61), (row3 29 47 62), (row3 29 47 63), (row3 29 48 49), (row3 29 48 50), (row3 29 48 51), (row3 29 48 52), (row3 29 48 53), (row3 29 48 54), (row3 29 48 55), (row3 29 48 56), (row3 29 48 57)]

def b131_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_04_rows b131_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_04_rows b131_04_labels]
    decide +kernel

def b131_05_rows : List Row := [(row3 29 48 58), (row3 29 48 59), (row3 29 48 60), (row3 29 48 61), (row3 29 48 62), (row3 29 48 63), (row3 29 49 50), (row3 29 49 51), (row3 29 49 52), (row3 29 49 53), (row3 29 49 54), (row3 29 49 55), (row3 29 49 56), (row3 29 49 57), (row3 29 49 58), (row3 29 49 59)]

def b131_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_05_rows b131_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_05_rows b131_05_labels]
    decide +kernel

def b131_06_rows : List Row := [(row3 29 49 60), (row3 29 49 61), (row3 29 49 62), (row3 29 49 63), (row3 29 50 51), (row3 29 50 52), (row3 29 50 53), (row3 29 50 54), (row3 29 50 55), (row3 29 50 56), (row3 29 50 57), (row3 29 50 58), (row3 29 50 59), (row3 29 50 60), (row3 29 50 61), (row3 29 50 62)]

def b131_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_06_rows b131_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_06_rows b131_06_labels]
    decide +kernel

def b131_07_rows : List Row := [(row3 29 50 63), (row3 29 51 52), (row3 29 51 53), (row3 29 51 54), (row3 29 51 55), (row3 29 51 56), (row3 29 51 57), (row3 29 51 58), (row3 29 51 59), (row3 29 51 60), (row3 29 51 61), (row3 29 51 62), (row3 29 51 63), (row3 29 52 53), (row3 29 52 54), (row3 29 52 55)]

def b131_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_07_rows b131_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_07_rows b131_07_labels]
    decide +kernel

def b131_08_rows : List Row := [(row3 29 52 56), (row3 29 52 57), (row3 29 52 58), (row3 29 52 59), (row3 29 52 60), (row3 29 52 61), (row3 29 52 62), (row3 29 52 63), (row3 29 53 54), (row3 29 53 55), (row3 29 53 56), (row3 29 53 57), (row3 29 53 58), (row3 29 53 59), (row3 29 53 60), (row3 29 53 61)]

def b131_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_08_rows b131_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_08_rows b131_08_labels]
    decide +kernel

def b131_09_rows : List Row := [(row3 29 53 62), (row3 29 53 63), (row3 29 54 55), (row3 29 54 56), (row3 29 54 57), (row3 29 54 58), (row3 29 54 59), (row3 29 54 60), (row3 29 54 61), (row3 29 54 62), (row3 29 54 63), (row3 29 55 56), (row3 29 55 57), (row3 29 55 58), (row3 29 55 59), (row3 29 55 60)]

def b131_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_09_rows b131_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_09_rows b131_09_labels]
    decide +kernel

def b131_10_rows : List Row := [(row3 29 55 61), (row3 29 55 62), (row3 29 55 63), (row3 29 56 57), (row3 29 56 58), (row3 29 56 59), (row3 29 56 60), (row3 29 56 61), (row3 29 56 62), (row3 29 56 63), (row3 29 57 58), (row3 29 57 59), (row3 29 57 60), (row3 29 57 61), (row3 29 57 62), (row3 29 57 63)]

def b131_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_10_rows b131_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_10_rows b131_10_labels]
    decide +kernel

def b131_11_rows : List Row := [(row3 29 58 59), (row3 29 58 60), (row3 29 58 61), (row3 29 58 62), (row3 29 58 63), (row3 29 59 60), (row3 29 59 61), (row3 29 59 62), (row3 29 59 63), (row3 29 60 61), (row3 29 60 62), (row3 29 60 63), (row3 29 61 62), (row3 29 61 63), (row3 29 62 63), (row3 30 31 32)]

def b131_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 162 235 163)]

theorem b131_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_11_rows b131_11_labels 728890988441336569516248000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_11_rows b131_11_labels]
    decide +kernel

def b131_12_rows : List Row := [(row3 30 31 33), (row3 30 31 34), (row3 30 31 35), (row3 30 31 36), (row3 30 31 37), (row3 30 31 38), (row3 30 31 39), (row3 30 31 40), (row3 30 31 41), (row3 30 31 42), (row3 30 31 43), (row3 30 31 44), (row3 30 31 45), (row3 30 31 46), (row3 30 31 47), (row3 30 31 48)]

def b131_12_labels : List Row := [(row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 163 462 163), (row3 358 462 358), (row3 285 462 285), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 191 235 193), (row3 462 462 462)]

theorem b131_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_12_rows b131_12_labels 15003317029744358964146998500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_12_rows b131_12_labels]
    decide +kernel

def b131_13_rows : List Row := [(row3 30 31 49), (row3 30 31 50), (row3 30 31 51), (row3 30 31 52), (row3 30 31 53), (row3 30 31 54), (row3 30 31 55), (row3 30 31 56), (row3 30 31 57), (row3 30 31 58), (row3 30 31 59), (row3 30 31 60), (row3 30 31 61), (row3 30 31 62), (row3 30 31 63), (row3 30 32 33)]

def b131_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 462 264), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269)]

theorem b131_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_13_rows b131_13_labels 62602246368402968922562500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_13_rows b131_13_labels]
    decide +kernel

def b131_14_rows : List Row := [(row3 30 32 34), (row3 30 32 35), (row3 30 32 36), (row3 30 32 37), (row3 30 32 38), (row3 30 32 39), (row3 30 32 40), (row3 30 32 41), (row3 30 32 42), (row3 30 32 43), (row3 30 32 44), (row3 30 32 45), (row3 30 32 46), (row3 30 32 47), (row3 30 32 48), (row3 30 32 49)]

def b131_14_labels : List Row := [(row3 237 462 237), (row3 242 462 242), (row3 462 462 462), (row3 242 462 242), (row3 237 462 237), (row3 269 462 269), (row3 170 10 218), (row3 235 462 235), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 228 232 235), (row3 237 462 237), (row3 244 462 244)]

theorem b131_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_14_rows b131_14_labels 568818721418074357611615750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_14_rows b131_14_labels]
    decide +kernel

def b131_15_rows : List Row := [(row3 30 32 50), (row3 30 32 51), (row3 30 32 52), (row3 30 32 53), (row3 30 32 54), (row3 30 32 55), (row3 30 32 56), (row3 30 32 57), (row3 30 32 58), (row3 30 32 59), (row3 30 32 60), (row3 30 32 61), (row3 30 32 62), (row3 30 32 63), (row3 30 33 34), (row3 30 33 35)]

def b131_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b131_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b131_15_rows b131_15_labels 195280852293634695975000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b131_15_rows b131_15_labels]
    decide +kernel

theorem checked131 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_131 QuarticIntegerComputationalData.ids64_131 16363824266824466494893399750 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b131_00_rows ++ b131_01_rows) ++ (b131_02_rows ++ b131_03_rows)) ++ ((b131_04_rows ++ b131_05_rows) ++ (b131_06_rows ++ b131_07_rows))) ++ (((b131_08_rows ++ b131_09_rows) ++ (b131_10_rows ++ b131_11_rows)) ++ ((b131_12_rows ++ b131_13_rows) ++ (b131_14_rows ++ b131_15_rows))))
    ((((b131_00_labels ++ b131_01_labels) ++ (b131_02_labels ++ b131_03_labels)) ++ ((b131_04_labels ++ b131_05_labels) ++ (b131_06_labels ++ b131_07_labels))) ++ (((b131_08_labels ++ b131_09_labels) ++ (b131_10_labels ++ b131_11_labels)) ++ ((b131_12_labels ++ b131_13_labels) ++ (b131_14_labels ++ b131_15_labels)))) 16363824266824466494893399750
  exact ((((b131_00_checked.append (c := 0) b131_01_checked (by decide +kernel)).append (c := 0) (b131_02_checked.append (c := 0) b131_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b131_04_checked.append (c := 0) b131_05_checked (by decide +kernel)).append (c := 0) (b131_06_checked.append (c := 0) b131_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 16363824266824466494893399750) (((b131_08_checked.append (c := 0) b131_09_checked (by decide +kernel)).append (c := 728890988441336569516248000) (b131_10_checked.append (c := 728890988441336569516248000) b131_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 16363824266824466494893399750) ((b131_12_checked.append (c := 15065919276112761933069561000) b131_13_checked (by decide +kernel)).append (c := 15634933278383129925377151750) (b131_14_checked.append (c := 569014002270367992307590750) b131_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b132_00_rows : List Row := [(row3 30 33 36), (row3 30 33 37), (row3 30 33 38), (row3 30 33 39), (row3 30 33 40), (row3 30 33 41), (row3 30 33 42), (row3 30 33 43), (row3 30 33 44), (row3 30 33 45), (row3 30 33 46), (row3 30 33 47), (row3 30 33 48), (row3 30 33 49), (row3 30 33 50), (row3 30 33 51)]

def b132_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_00_rows b132_00_labels 413010417905223503607000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_00_rows b132_00_labels]
    decide +kernel

def b132_01_rows : List Row := [(row3 30 33 52), (row3 30 33 53), (row3 30 33 54), (row3 30 33 55), (row3 30 33 56), (row3 30 33 57), (row3 30 33 58), (row3 30 33 59), (row3 30 33 60), (row3 30 33 61), (row3 30 33 62), (row3 30 33 63), (row3 30 34 35), (row3 30 34 36), (row3 30 34 37), (row3 30 34 38)]

def b132_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_01_rows b132_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_01_rows b132_01_labels]
    decide +kernel

def b132_02_rows : List Row := [(row3 30 34 39), (row3 30 34 40), (row3 30 34 41), (row3 30 34 42), (row3 30 34 43), (row3 30 34 44), (row3 30 34 45), (row3 30 34 46), (row3 30 34 47), (row3 30 34 48), (row3 30 34 49), (row3 30 34 50), (row3 30 34 51), (row3 30 34 52), (row3 30 34 53), (row3 30 34 54)]

def b132_02_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_02_rows b132_02_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_02_rows b132_02_labels]
    decide +kernel

def b132_03_rows : List Row := [(row3 30 34 55), (row3 30 34 56), (row3 30 34 57), (row3 30 34 58), (row3 30 34 59), (row3 30 34 60), (row3 30 34 61), (row3 30 34 62), (row3 30 34 63), (row3 30 35 36), (row3 30 35 37), (row3 30 35 38), (row3 30 35 39), (row3 30 35 40), (row3 30 35 41), (row3 30 35 42)]

def b132_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_03_rows b132_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_03_rows b132_03_labels]
    decide +kernel

def b132_04_rows : List Row := [(row3 30 35 43), (row3 30 35 44), (row3 30 35 45), (row3 30 35 46), (row3 30 35 47), (row3 30 35 48), (row3 30 35 49), (row3 30 35 50), (row3 30 35 51), (row3 30 35 52), (row3 30 35 53), (row3 30 35 54), (row3 30 35 55), (row3 30 35 56), (row3 30 35 57), (row3 30 35 58)]

def b132_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_04_rows b132_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_04_rows b132_04_labels]
    decide +kernel

def b132_05_rows : List Row := [(row3 30 35 59), (row3 30 35 60), (row3 30 35 61), (row3 30 35 62), (row3 30 35 63), (row3 30 36 37), (row3 30 36 38), (row3 30 36 39), (row3 30 36 40), (row3 30 36 41), (row3 30 36 42), (row3 30 36 43), (row3 30 36 44), (row3 30 36 45), (row3 30 36 46), (row3 30 36 47)]

def b132_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_05_rows b132_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_05_rows b132_05_labels]
    decide +kernel

def b132_06_rows : List Row := [(row3 30 36 48), (row3 30 36 49), (row3 30 36 50), (row3 30 36 51), (row3 30 36 52), (row3 30 36 53), (row3 30 36 54), (row3 30 36 55), (row3 30 36 56), (row3 30 36 57), (row3 30 36 58), (row3 30 36 59), (row3 30 36 60), (row3 30 36 61), (row3 30 36 62), (row3 30 36 63)]

def b132_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_06_rows b132_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_06_rows b132_06_labels]
    decide +kernel

def b132_07_rows : List Row := [(row3 30 37 38), (row3 30 37 39), (row3 30 37 40), (row3 30 37 41), (row3 30 37 42), (row3 30 37 43), (row3 30 37 44), (row3 30 37 45), (row3 30 37 46), (row3 30 37 47), (row3 30 37 48), (row3 30 37 49), (row3 30 37 50), (row3 30 37 51), (row3 30 37 52), (row3 30 37 53)]

def b132_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_07_rows b132_07_labels 51321326103961562835000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_07_rows b132_07_labels]
    decide +kernel

def b132_08_rows : List Row := [(row3 30 37 54), (row3 30 37 55), (row3 30 37 56), (row3 30 37 57), (row3 30 37 58), (row3 30 37 59), (row3 30 37 60), (row3 30 37 61), (row3 30 37 62), (row3 30 37 63), (row3 30 38 39), (row3 30 38 40), (row3 30 38 41), (row3 30 38 42), (row3 30 38 43), (row3 30 38 44)]

def b132_08_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_08_rows b132_08_labels 346135121931067988355000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_08_rows b132_08_labels]
    decide +kernel

def b132_09_rows : List Row := [(row3 30 38 45), (row3 30 38 46), (row3 30 38 47), (row3 30 38 48), (row3 30 38 49), (row3 30 38 50), (row3 30 38 51), (row3 30 38 52), (row3 30 38 53), (row3 30 38 54), (row3 30 38 55), (row3 30 38 56), (row3 30 38 57), (row3 30 38 58), (row3 30 38 59), (row3 30 38 60)]

def b132_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_09_rows b132_09_labels 5359478858076292368507000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_09_rows b132_09_labels]
    decide +kernel

def b132_10_rows : List Row := [(row3 30 38 61), (row3 30 38 62), (row3 30 38 63), (row3 30 39 40), (row3 30 39 41), (row3 30 39 42), (row3 30 39 43), (row3 30 39 44), (row3 30 39 45), (row3 30 39 46), (row3 30 39 47), (row3 30 39 48), (row3 30 39 49), (row3 30 39 50), (row3 30 39 51), (row3 30 39 52)]

def b132_10_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_10_rows b132_10_labels 63204253841156568809737500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_10_rows b132_10_labels]
    decide +kernel

def b132_11_rows : List Row := [(row3 30 39 53), (row3 30 39 54), (row3 30 39 55), (row3 30 39 56), (row3 30 39 57), (row3 30 39 58), (row3 30 39 59), (row3 30 39 60), (row3 30 39 61), (row3 30 39 62), (row3 30 39 63), (row3 30 40 41), (row3 30 40 42), (row3 30 40 43), (row3 30 40 44), (row3 30 40 45)]

def b132_11_labels : List Row := [(row3 462 462 462), (row3 244 244 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 237 237 462), (row3 242 242 462), (row3 462 462 462), (row3 242 242 462)]

theorem b132_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_11_rows b132_11_labels 30460200964544358486819000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_11_rows b132_11_labels]
    decide +kernel

def b132_12_rows : List Row := [(row3 30 40 46), (row3 30 40 47), (row3 30 40 48), (row3 30 40 49), (row3 30 40 50), (row3 30 40 51), (row3 30 40 52), (row3 30 40 53), (row3 30 40 54), (row3 30 40 55), (row3 30 40 56), (row3 30 40 57), (row3 30 40 58), (row3 30 40 59), (row3 30 40 60), (row3 30 40 61)]

def b132_12_labels : List Row := [(row3 237 237 462), (row3 172 258 10), (row3 269 269 462), (row3 235 235 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 228 235 232), (row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_12_rows b132_12_labels 545744698390259919343296000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_12_rows b132_12_labels]
    decide +kernel

def b132_13_rows : List Row := [(row3 30 40 62), (row3 30 40 63), (row3 30 41 42), (row3 30 41 43), (row3 30 41 44), (row3 30 41 45), (row3 30 41 46), (row3 30 41 47), (row3 30 41 48), (row3 30 41 49), (row3 30 41 50), (row3 30 41 51), (row3 30 41 52), (row3 30 41 53), (row3 30 41 54), (row3 30 41 55)]

def b132_13_labels : List Row := [(row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246)]

theorem b132_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_13_rows b132_13_labels 312221869266291245158500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_13_rows b132_13_labels]
    decide +kernel

def b132_14_rows : List Row := [(row3 30 41 56), (row3 30 41 57), (row3 30 41 58), (row3 30 41 59), (row3 30 41 60), (row3 30 41 61), (row3 30 41 62), (row3 30 41 63), (row3 30 42 43), (row3 30 42 44), (row3 30 42 45), (row3 30 42 46), (row3 30 42 47), (row3 30 42 48), (row3 30 42 49), (row3 30 42 50)]

def b132_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_14_rows b132_14_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_14_rows b132_14_labels]
    decide +kernel

def b132_15_rows : List Row := [(row3 30 42 51), (row3 30 42 52), (row3 30 42 53), (row3 30 42 54), (row3 30 42 55), (row3 30 42 56), (row3 30 42 57), (row3 30 42 58), (row3 30 42 59), (row3 30 42 60), (row3 30 42 61), (row3 30 42 62), (row3 30 42 63), (row3 30 43 44), (row3 30 43 45), (row3 30 43 46)]

def b132_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b132_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b132_15_rows b132_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b132_15_rows b132_15_labels]
    decide +kernel

theorem checked132 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_132 QuarticIntegerComputationalData.ids64_132 645910471040135941402627500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b132_00_rows ++ b132_01_rows) ++ (b132_02_rows ++ b132_03_rows)) ++ ((b132_04_rows ++ b132_05_rows) ++ (b132_06_rows ++ b132_07_rows))) ++ (((b132_08_rows ++ b132_09_rows) ++ (b132_10_rows ++ b132_11_rows)) ++ ((b132_12_rows ++ b132_13_rows) ++ (b132_14_rows ++ b132_15_rows))))
    ((((b132_00_labels ++ b132_01_labels) ++ (b132_02_labels ++ b132_03_labels)) ++ ((b132_04_labels ++ b132_05_labels) ++ (b132_06_labels ++ b132_07_labels))) ++ (((b132_08_labels ++ b132_09_labels) ++ (b132_10_labels ++ b132_11_labels)) ++ ((b132_12_labels ++ b132_13_labels) ++ (b132_14_labels ++ b132_15_labels)))) 645910471040135941402627500
  exact ((((b132_00_checked.append (c := 413010417905223503607000) b132_01_checked (by decide +kernel)).append (c := 424500568440578360194500) (b132_02_checked.append (c := 11490150535354856587500) b132_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 475821894544539923029500) ((b132_04_checked.append (c := 0) b132_05_checked (by decide +kernel)).append (c := 51321326103961562835000) (b132_06_checked.append (c := 51321326103961562835000) b132_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 645910471040135941402627500) (((b132_08_checked.append (c := 5705613980007360356862000) b132_09_checked (by decide +kernel)).append (c := 99370068785708287653418500) (b132_10_checked.append (c := 93664454805700927296556500) b132_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 645434649145591401479598000) ((b132_12_checked.append (c := 546056920259526210588454500) b132_13_checked (by decide +kernel)).append (c := 546064580359883113826179500) (b132_14_checked.append (c := 7660100356903237725000) b132_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b133_00_rows : List Row := [(row3 30 43 47), (row3 30 43 48), (row3 30 43 49), (row3 30 43 50), (row3 30 43 51), (row3 30 43 52), (row3 30 43 53), (row3 30 43 54), (row3 30 43 55), (row3 30 43 56), (row3 30 43 57), (row3 30 43 58), (row3 30 43 59), (row3 30 43 60), (row3 30 43 61), (row3 30 43 62)]

def b133_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_00_rows b133_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_00_rows b133_00_labels]
    decide +kernel

def b133_01_rows : List Row := [(row3 30 43 63), (row3 30 44 45), (row3 30 44 46), (row3 30 44 47), (row3 30 44 48), (row3 30 44 49), (row3 30 44 50), (row3 30 44 51), (row3 30 44 52), (row3 30 44 53), (row3 30 44 54), (row3 30 44 55), (row3 30 44 56), (row3 30 44 57), (row3 30 44 58), (row3 30 44 59)]

def b133_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_01_rows b133_01_labels 19150250892258094312500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_01_rows b133_01_labels]
    decide +kernel

def b133_02_rows : List Row := [(row3 30 44 60), (row3 30 44 61), (row3 30 44 62), (row3 30 44 63), (row3 30 45 46), (row3 30 45 47), (row3 30 45 48), (row3 30 45 49), (row3 30 45 50), (row3 30 45 51), (row3 30 45 52), (row3 30 45 53), (row3 30 45 54), (row3 30 45 55), (row3 30 45 56), (row3 30 45 57)]

def b133_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462)]

theorem b133_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_02_rows b133_02_labels 707948968365595375983000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_02_rows b133_02_labels]
    decide +kernel

def b133_03_rows : List Row := [(row3 30 45 58), (row3 30 45 59), (row3 30 45 60), (row3 30 45 61), (row3 30 45 62), (row3 30 45 63), (row3 30 46 47), (row3 30 46 48), (row3 30 46 49), (row3 30 46 50), (row3 30 46 51), (row3 30 46 52), (row3 30 46 53), (row3 30 46 54), (row3 30 46 55), (row3 30 46 56)]

def b133_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 232 462 232), (row3 462 462 462)]

theorem b133_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_03_rows b133_03_labels 92482670199795950875959000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_03_rows b133_03_labels]
    decide +kernel

def b133_04_rows : List Row := [(row3 30 46 57), (row3 30 46 58), (row3 30 46 59), (row3 30 46 60), (row3 30 46 61), (row3 30 46 62), (row3 30 46 63), (row3 30 47 48), (row3 30 47 49), (row3 30 47 50), (row3 30 47 51), (row3 30 47 52), (row3 30 47 53), (row3 30 47 54), (row3 30 47 55), (row3 30 47 56)]

def b133_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 228 235 232), (row3 115 11 212), (row3 246 462 246)]

theorem b133_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_04_rows b133_04_labels 1676203935520285247109059250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_04_rows b133_04_labels]
    decide +kernel

def b133_05_rows : List Row := [(row3 30 47 57), (row3 30 47 58), (row3 30 47 59), (row3 30 47 60), (row3 30 47 61), (row3 30 47 62), (row3 30 47 63), (row3 30 48 49), (row3 30 48 50), (row3 30 48 51), (row3 30 48 52), (row3 30 48 53), (row3 30 48 54), (row3 30 48 55), (row3 30 48 56), (row3 30 48 57)]

def b133_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462)]

theorem b133_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_05_rows b133_05_labels 61897565681305856827753500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_05_rows b133_05_labels]
    decide +kernel

def b133_06_rows : List Row := [(row3 30 48 58), (row3 30 48 59), (row3 30 48 60), (row3 30 48 61), (row3 30 48 62), (row3 30 48 63), (row3 30 49 50), (row3 30 49 51), (row3 30 49 52), (row3 30 49 53), (row3 30 49 54), (row3 30 49 55), (row3 30 49 56), (row3 30 49 57), (row3 30 49 58), (row3 30 49 59)]

def b133_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_06_rows b133_06_labels 298314462872689251336000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_06_rows b133_06_labels]
    decide +kernel

def b133_07_rows : List Row := [(row3 30 49 60), (row3 30 49 61), (row3 30 49 62), (row3 30 49 63), (row3 30 50 51), (row3 30 50 52), (row3 30 50 53), (row3 30 50 54), (row3 30 50 55), (row3 30 50 56), (row3 30 50 57), (row3 30 50 58), (row3 30 50 59), (row3 30 50 60), (row3 30 50 61), (row3 30 50 62)]

def b133_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_07_rows b133_07_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_07_rows b133_07_labels]
    decide +kernel

def b133_08_rows : List Row := [(row3 30 50 63), (row3 30 51 52), (row3 30 51 53), (row3 30 51 54), (row3 30 51 55), (row3 30 51 56), (row3 30 51 57), (row3 30 51 58), (row3 30 51 59), (row3 30 51 60), (row3 30 51 61), (row3 30 51 62), (row3 30 51 63), (row3 30 52 53), (row3 30 52 54), (row3 30 52 55)]

def b133_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 243 462 243)]

theorem b133_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_08_rows b133_08_labels 133582344540811957075500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_08_rows b133_08_labels]
    decide +kernel

def b133_09_rows : List Row := [(row3 30 52 56), (row3 30 52 57), (row3 30 52 58), (row3 30 52 59), (row3 30 52 60), (row3 30 52 61), (row3 30 52 62), (row3 30 52 63), (row3 30 53 54), (row3 30 53 55), (row3 30 53 56), (row3 30 53 57), (row3 30 53 58), (row3 30 53 59), (row3 30 53 60), (row3 30 53 61)]

def b133_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 269 269 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_09_rows b133_09_labels 29846020445362910862666000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_09_rows b133_09_labels]
    decide +kernel

def b133_10_rows : List Row := [(row3 30 53 62), (row3 30 53 63), (row3 30 54 55), (row3 30 54 56), (row3 30 54 57), (row3 30 54 58), (row3 30 54 59), (row3 30 54 60), (row3 30 54 61), (row3 30 54 62), (row3 30 54 63), (row3 30 55 56), (row3 30 55 57), (row3 30 55 58), (row3 30 55 59), (row3 30 55 60)]

def b133_10_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 172 10 258), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 170 10 218), (row3 235 462 235), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_10_rows b133_10_labels 1053024363045922491978239250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_10_rows b133_10_labels]
    decide +kernel

def b133_11_rows : List Row := [(row3 30 55 61), (row3 30 55 62), (row3 30 55 63), (row3 30 56 57), (row3 30 56 58), (row3 30 56 59), (row3 30 56 60), (row3 30 56 61), (row3 30 56 62), (row3 30 56 63), (row3 30 57 58), (row3 30 57 59), (row3 30 57 60), (row3 30 57 61), (row3 30 57 62), (row3 30 57 63)]

def b133_11_labels : List Row := [(row3 246 246 462), (row3 228 232 235), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462)]

theorem b133_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_11_rows b133_11_labels 64451549200020979698886500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_11_rows b133_11_labels]
    decide +kernel

def b133_12_rows : List Row := [(row3 30 58 59), (row3 30 58 60), (row3 30 58 61), (row3 30 58 62), (row3 30 58 63), (row3 30 59 60), (row3 30 59 61), (row3 30 59 62), (row3 30 59 63), (row3 30 60 61), (row3 30 60 62), (row3 30 60 63), (row3 30 61 62), (row3 30 61 63), (row3 30 62 63), (row3 31 32 33)]

def b133_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 269 269 462), (row3 193 232 189)]

theorem b133_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_12_rows b133_12_labels 428222989386044633472277500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_12_rows b133_12_labels]
    decide +kernel

def b133_13_rows : List Row := [(row3 31 32 34), (row3 31 32 35), (row3 31 32 36), (row3 31 32 37), (row3 31 32 38), (row3 31 32 39), (row3 31 32 40), (row3 31 32 41), (row3 31 32 42), (row3 31 32 43), (row3 31 32 44), (row3 31 32 45), (row3 31 32 46), (row3 31 32 47), (row3 31 32 48), (row3 31 32 49)]

def b133_13_labels : List Row := [(row3 261 462 261), (row3 238 462 238), (row3 462 462 462), (row3 238 232 230), (row3 261 288 290), (row3 193 163 139), (row3 357 90 187), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 232 228), (row3 288 288 288), (row3 273 462 273), (row3 235 462 235)]

theorem b133_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_13_rows b133_13_labels 8188820328011355602213474160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_13_rows b133_13_labels]
    decide +kernel

def b133_14_rows : List Row := [(row3 31 32 50), (row3 31 32 51), (row3 31 32 52), (row3 31 32 53), (row3 31 32 54), (row3 31 32 55), (row3 31 32 56), (row3 31 32 57), (row3 31 32 58), (row3 31 32 59), (row3 31 32 60), (row3 31 32 61), (row3 31 32 62), (row3 31 32 63), (row3 31 33 34), (row3 31 33 35)]

def b133_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 229 231 227), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_14_rows b133_14_labels 10404999253413655292808000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_14_rows b133_14_labels]
    decide +kernel

def b133_15_rows : List Row := [(row3 31 33 36), (row3 31 33 37), (row3 31 33 38), (row3 31 33 39), (row3 31 33 40), (row3 31 33 41), (row3 31 33 42), (row3 31 33 43), (row3 31 33 44), (row3 31 33 45), (row3 31 33 46), (row3 31 33 47), (row3 31 33 48), (row3 31 33 49), (row3 31 33 50), (row3 31 33 51)]

def b133_15_labels : List Row := [(row3 462 462 462), (row3 462 246 246), (row3 462 232 232), (row3 462 284 284), (row3 278 282 282), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 232 235), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b133_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b133_15_rows b133_15_labels 72982779363463902875229600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b133_15_rows b133_15_labels]
    decide +kernel

theorem checked133 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_133 QuarticIntegerComputationalData.ids64_133 11679503856233999489122784760 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b133_00_rows ++ b133_01_rows) ++ (b133_02_rows ++ b133_03_rows)) ++ ((b133_04_rows ++ b133_05_rows) ++ (b133_06_rows ++ b133_07_rows))) ++ (((b133_08_rows ++ b133_09_rows) ++ (b133_10_rows ++ b133_11_rows)) ++ ((b133_12_rows ++ b133_13_rows) ++ (b133_14_rows ++ b133_15_rows))))
    ((((b133_00_labels ++ b133_01_labels) ++ (b133_02_labels ++ b133_03_labels)) ++ ((b133_04_labels ++ b133_05_labels) ++ (b133_06_labels ++ b133_07_labels))) ++ (((b133_08_labels ++ b133_09_labels) ++ (b133_10_labels ++ b133_11_labels)) ++ ((b133_12_labels ++ b133_13_labels) ++ (b133_14_labels ++ b133_15_labels)))) 11679503856233999489122784760
  exact ((((b133_00_checked.append (c := 19150250892258094312500) b133_01_checked (by decide +kernel)).append (c := 93209769419053804346254500) (b133_02_checked.append (c := 93190619168161546251942000) b133_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1831617245183874500772128250) ((b133_04_checked.append (c := 1738101501201591103936812750) b133_05_checked (by decide +kernel)).append (c := 1738407475764820696425873750) (b133_06_checked.append (c := 305974563229592489061000) b133_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11679503856233999489122784760) (((b133_08_checked.append (c := 29979602789903722819741500) b133_09_checked (by decide +kernel)).append (c := 1147455515035847194496867250) (b133_10_checked.append (c := 1117475912245943471677125750) b133_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 9847886611050124988350656510) ((b133_12_checked.append (c := 8617043317397400235685751660) b133_13_checked (by decide +kernel)).append (c := 8700431096014277793853789260) (b133_14_checked.append (c := 83387778616877558168037600) b133_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b134_00_rows : List Row := [(row3 31 33 52), (row3 31 33 53), (row3 31 33 54), (row3 31 33 55), (row3 31 33 56), (row3 31 33 57), (row3 31 33 58), (row3 31 33 59), (row3 31 33 60), (row3 31 33 61), (row3 31 33 62), (row3 31 33 63), (row3 31 34 35), (row3 31 34 36), (row3 31 34 37), (row3 31 34 38)]

def b134_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_00_rows b134_00_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_00_rows b134_00_labels]
    decide +kernel

def b134_01_rows : List Row := [(row3 31 34 39), (row3 31 34 40), (row3 31 34 41), (row3 31 34 42), (row3 31 34 43), (row3 31 34 44), (row3 31 34 45), (row3 31 34 46), (row3 31 34 47), (row3 31 34 48), (row3 31 34 49), (row3 31 34 50), (row3 31 34 51), (row3 31 34 52), (row3 31 34 53), (row3 31 34 54)]

def b134_01_labels : List Row := [(row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_01_rows b134_01_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_01_rows b134_01_labels]
    decide +kernel

def b134_02_rows : List Row := [(row3 31 34 55), (row3 31 34 56), (row3 31 34 57), (row3 31 34 58), (row3 31 34 59), (row3 31 34 60), (row3 31 34 61), (row3 31 34 62), (row3 31 34 63), (row3 31 35 36), (row3 31 35 37), (row3 31 35 38), (row3 31 35 39), (row3 31 35 40), (row3 31 35 41), (row3 31 35 42)]

def b134_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462)]

theorem b134_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_02_rows b134_02_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_02_rows b134_02_labels]
    decide +kernel

def b134_03_rows : List Row := [(row3 31 35 43), (row3 31 35 44), (row3 31 35 45), (row3 31 35 46), (row3 31 35 47), (row3 31 35 48), (row3 31 35 49), (row3 31 35 50), (row3 31 35 51), (row3 31 35 52), (row3 31 35 53), (row3 31 35 54), (row3 31 35 55), (row3 31 35 56), (row3 31 35 57), (row3 31 35 58)]

def b134_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_03_rows b134_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_03_rows b134_03_labels]
    decide +kernel

def b134_04_rows : List Row := [(row3 31 35 59), (row3 31 35 60), (row3 31 35 61), (row3 31 35 62), (row3 31 35 63), (row3 31 36 37), (row3 31 36 38), (row3 31 36 39), (row3 31 36 40), (row3 31 36 41), (row3 31 36 42), (row3 31 36 43), (row3 31 36 44), (row3 31 36 45), (row3 31 36 46), (row3 31 36 47)]

def b134_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_04_rows b134_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_04_rows b134_04_labels]
    decide +kernel

def b134_05_rows : List Row := [(row3 31 36 48), (row3 31 36 49), (row3 31 36 50), (row3 31 36 51), (row3 31 36 52), (row3 31 36 53), (row3 31 36 54), (row3 31 36 55), (row3 31 36 56), (row3 31 36 57), (row3 31 36 58), (row3 31 36 59), (row3 31 36 60), (row3 31 36 61), (row3 31 36 62), (row3 31 36 63)]

def b134_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_05_rows b134_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_05_rows b134_05_labels]
    decide +kernel

def b134_06_rows : List Row := [(row3 31 37 38), (row3 31 37 39), (row3 31 37 40), (row3 31 37 41), (row3 31 37 42), (row3 31 37 43), (row3 31 37 44), (row3 31 37 45), (row3 31 37 46), (row3 31 37 47), (row3 31 37 48), (row3 31 37 49), (row3 31 37 50), (row3 31 37 51), (row3 31 37 52), (row3 31 37 53)]

def b134_06_labels : List Row := [(row3 462 232 232), (row3 462 284 284), (row3 462 247 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_06_rows b134_06_labels 65194622389040422337856000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_06_rows b134_06_labels]
    decide +kernel

def b134_07_rows : List Row := [(row3 31 37 54), (row3 31 37 55), (row3 31 37 56), (row3 31 37 57), (row3 31 37 58), (row3 31 37 59), (row3 31 37 60), (row3 31 37 61), (row3 31 37 62), (row3 31 37 63), (row3 31 38 39), (row3 31 38 40), (row3 31 38 41), (row3 31 38 42), (row3 31 38 43), (row3 31 38 44)]

def b134_07_labels : List Row := [(row3 462 462 462), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 234 226 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_07_rows b134_07_labels 1045779151985210358465754500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_07_rows b134_07_labels]
    decide +kernel

def b134_08_rows : List Row := [(row3 31 38 45), (row3 31 38 46), (row3 31 38 47), (row3 31 38 48), (row3 31 38 49), (row3 31 38 50), (row3 31 38 51), (row3 31 38 52), (row3 31 38 53), (row3 31 38 54), (row3 31 38 55), (row3 31 38 56), (row3 31 38 57), (row3 31 38 58), (row3 31 38 59), (row3 31 38 60)]

def b134_08_labels : List Row := [(row3 462 462 462), (row3 462 232 232), (row3 273 288 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 231 231), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_08_rows b134_08_labels 20107031991015763671141600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_08_rows b134_08_labels]
    decide +kernel

def b134_09_rows : List Row := [(row3 31 38 61), (row3 31 38 62), (row3 31 38 63), (row3 31 39 40), (row3 31 39 41), (row3 31 39 42), (row3 31 39 43), (row3 31 39 44), (row3 31 39 45), (row3 31 39 46), (row3 31 39 47), (row3 31 39 48), (row3 31 39 49), (row3 31 39 50), (row3 31 39 51), (row3 31 39 52)]

def b134_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 301 301), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 193 163 193), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_09_rows b134_09_labels 1251711139763577253940985600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_09_rows b134_09_labels]
    decide +kernel

def b134_10_rows : List Row := [(row3 31 39 53), (row3 31 39 54), (row3 31 39 55), (row3 31 39 56), (row3 31 39 57), (row3 31 39 58), (row3 31 39 59), (row3 31 39 60), (row3 31 39 61), (row3 31 39 62), (row3 31 39 63), (row3 31 40 41), (row3 31 40 42), (row3 31 40 43), (row3 31 40 44), (row3 31 40 45)]

def b134_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 265 277 277), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 180 154 154), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237)]

theorem b134_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_10_rows b134_10_labels 899045953432725946219644300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_10_rows b134_10_labels]
    decide +kernel

def b134_11_rows : List Row := [(row3 31 40 46), (row3 31 40 47), (row3 31 40 48), (row3 31 40 49), (row3 31 40 50), (row3 31 40 51), (row3 31 40 52), (row3 31 40 53), (row3 31 40 54), (row3 31 40 55), (row3 31 40 56), (row3 31 40 57), (row3 31 40 58), (row3 31 40 59), (row3 31 40 60), (row3 31 40 61)]

def b134_11_labels : List Row := [(row3 265 268 268), (row3 332 155 93), (row3 371 87 325), (row3 278 280 280), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 295 297 297), (row3 265 277 277), (row3 234 231 231), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_11_rows b134_11_labels 12948954418578201265899827100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_11_rows b134_11_labels]
    decide +kernel

def b134_12_rows : List Row := [(row3 31 40 62), (row3 31 40 63), (row3 31 41 42), (row3 31 41 43), (row3 31 41 44), (row3 31 41 45), (row3 31 41 46), (row3 31 41 47), (row3 31 41 48), (row3 31 41 49), (row3 31 41 50), (row3 31 41 51), (row3 31 41 52), (row3 31 41 53), (row3 31 41 54), (row3 31 41 55)]

def b134_12_labels : List Row := [(row3 462 245 245), (row3 229 231 227), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 261 462), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234)]

theorem b134_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_12_rows b134_12_labels 10541379961238882395731300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_12_rows b134_12_labels]
    decide +kernel

def b134_13_rows : List Row := [(row3 31 41 56), (row3 31 41 57), (row3 31 41 58), (row3 31 41 59), (row3 31 41 60), (row3 31 41 61), (row3 31 41 62), (row3 31 41 63), (row3 31 42 43), (row3 31 42 44), (row3 31 42 45), (row3 31 42 46), (row3 31 42 47), (row3 31 42 48), (row3 31 42 49), (row3 31 42 50)]

def b134_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b134_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_13_rows b134_13_labels 343803200111584190208000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_13_rows b134_13_labels]
    decide +kernel

def b134_14_rows : List Row := [(row3 31 42 51), (row3 31 42 52), (row3 31 42 53), (row3 31 42 54), (row3 31 42 55), (row3 31 42 56), (row3 31 42 57), (row3 31 42 58), (row3 31 42 59), (row3 31 42 60), (row3 31 42 61), (row3 31 42 62), (row3 31 42 63), (row3 31 43 44), (row3 31 43 45), (row3 31 43 46)]

def b134_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_14_rows b134_14_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_14_rows b134_14_labels]
    decide +kernel

def b134_15_rows : List Row := [(row3 31 43 47), (row3 31 43 48), (row3 31 43 49), (row3 31 43 50), (row3 31 43 51), (row3 31 43 52), (row3 31 43 53), (row3 31 43 54), (row3 31 43 55), (row3 31 43 56), (row3 31 43 57), (row3 31 43 58), (row3 31 43 59), (row3 31 43 60), (row3 31 43 61), (row3 31 43 62)]

def b134_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b134_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b134_15_rows b134_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b134_15_rows b134_15_labels]
    decide +kernel

theorem checked134 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_134 QuarticIntegerComputationalData.ids64_134 16242042629430542582442960900 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b134_00_rows ++ b134_01_rows) ++ (b134_02_rows ++ b134_03_rows)) ++ ((b134_04_rows ++ b134_05_rows) ++ (b134_06_rows ++ b134_07_rows))) ++ (((b134_08_rows ++ b134_09_rows) ++ (b134_10_rows ++ b134_11_rows)) ++ ((b134_12_rows ++ b134_13_rows) ++ (b134_14_rows ++ b134_15_rows))))
    ((((b134_00_labels ++ b134_01_labels) ++ (b134_02_labels ++ b134_03_labels)) ++ ((b134_04_labels ++ b134_05_labels) ++ (b134_06_labels ++ b134_07_labels))) ++ (((b134_08_labels ++ b134_09_labels) ++ (b134_10_labels ++ b134_11_labels)) ++ ((b134_12_labels ++ b134_13_labels) ++ (b134_14_labels ++ b134_15_labels)))) 16242042629430542582442960900
  exact ((((b134_00_checked.append (c := 349807928707298846362500) b134_01_checked (by decide +kernel)).append (c := 357468029064202084087500) (b134_02_checked.append (c := 7660100356903237725000) b134_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1111331242403314982887698000) ((b134_04_checked.append (c := 0) b134_05_checked (by decide +kernel)).append (c := 1110973774374250780803610500) (b134_06_checked.append (c := 1110973774374250780803610500) b134_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 16242042629430542582442960900) (((b134_08_checked.append (c := 1271818171754593017612127200) b134_09_checked (by decide +kernel)).append (c := 15119818543765520229731598600) (b134_10_checked.append (c := 13848000372010927212119471400) b134_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 15130711387027227599555262900) ((b134_12_checked.append (c := 10885183161350466585939300) b134_13_checked (by decide +kernel)).append (c := 10892843261707369823664300) (b134_14_checked.append (c := 7660100356903237725000) b134_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b135_00_rows : List Row := [(row3 31 43 63), (row3 31 44 45), (row3 31 44 46), (row3 31 44 47), (row3 31 44 48), (row3 31 44 49), (row3 31 44 50), (row3 31 44 51), (row3 31 44 52), (row3 31 44 53), (row3 31 44 54), (row3 31 44 55), (row3 31 44 56), (row3 31 44 57), (row3 31 44 58), (row3 31 44 59)]

def b135_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b135_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_00_rows b135_00_labels 89389896656442626817000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_00_rows b135_00_labels]
    decide +kernel

def b135_01_rows : List Row := [(row3 31 44 60), (row3 31 44 61), (row3 31 44 62), (row3 31 44 63), (row3 31 45 46), (row3 31 45 47), (row3 31 45 48), (row3 31 45 49), (row3 31 45 50), (row3 31 45 51), (row3 31 45 52), (row3 31 45 53), (row3 31 45 54), (row3 31 45 55), (row3 31 45 56), (row3 31 45 57)]

def b135_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462)]

theorem b135_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_01_rows b135_01_labels 2444384471852140836127200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_01_rows b135_01_labels]
    decide +kernel

def b135_02_rows : List Row := [(row3 31 45 58), (row3 31 45 59), (row3 31 45 60), (row3 31 45 61), (row3 31 45 62), (row3 31 45 63), (row3 31 46 47), (row3 31 46 48), (row3 31 46 49), (row3 31 46 50), (row3 31 46 51), (row3 31 46 52), (row3 31 46 53), (row3 31 46 54), (row3 31 46 55), (row3 31 46 56)]

def b135_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 191 235), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 280 280), (row3 462 462 462)]

theorem b135_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_02_rows b135_02_labels 360167757851809088843664600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_02_rows b135_02_labels]
    decide +kernel

def b135_03_rows : List Row := [(row3 31 46 57), (row3 31 46 58), (row3 31 46 59), (row3 31 46 60), (row3 31 46 61), (row3 31 46 62), (row3 31 46 63), (row3 31 47 48), (row3 31 47 49), (row3 31 47 50), (row3 31 47 51), (row3 31 47 52), (row3 31 47 53), (row3 31 47 54), (row3 31 47 55), (row3 31 47 56)]

def b135_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 371 87 325), (row3 235 462 235)]

theorem b135_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_03_rows b135_03_labels 9720350751198878958837221760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_03_rows b135_03_labels]
    decide +kernel

def b135_04_rows : List Row := [(row3 31 47 57), (row3 31 47 58), (row3 31 47 59), (row3 31 47 60), (row3 31 47 61), (row3 31 47 62), (row3 31 47 63), (row3 31 48 49), (row3 31 48 50), (row3 31 48 51), (row3 31 48 52), (row3 31 48 53), (row3 31 48 54), (row3 31 48 55), (row3 31 48 56), (row3 31 48 57)]

def b135_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 193 191 235), (row3 261 261 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 261 261 462), (row3 332 155 93), (row3 193 163 193), (row3 273 288 273)]

theorem b135_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_04_rows b135_04_labels 4547931488031044515153761360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_04_rows b135_04_labels]
    decide +kernel

def b135_05_rows : List Row := [(row3 31 48 58), (row3 31 48 59), (row3 31 48 60), (row3 31 48 61), (row3 31 48 62), (row3 31 48 63), (row3 31 49 50), (row3 31 49 51), (row3 31 49 52), (row3 31 49 53), (row3 31 49 54), (row3 31 49 55), (row3 31 49 56), (row3 31 49 57), (row3 31 49 58), (row3 31 49 59)]

def b135_05_labels : List Row := [(row3 235 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 232 235), (row3 288 288 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 268 268), (row3 462 284 284), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462)]

theorem b135_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_05_rows b135_05_labels 93791394426470737211879400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_05_rows b135_05_labels]
    decide +kernel

def b135_06_rows : List Row := [(row3 31 49 60), (row3 31 49 61), (row3 31 49 62), (row3 31 49 63), (row3 31 50 51), (row3 31 50 52), (row3 31 50 53), (row3 31 50 54), (row3 31 50 55), (row3 31 50 56), (row3 31 50 57), (row3 31 50 58), (row3 31 50 59), (row3 31 50 60), (row3 31 50 61), (row3 31 50 62)]

def b135_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 232 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b135_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_06_rows b135_06_labels 1373254239972587074281000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_06_rows b135_06_labels]
    decide +kernel

def b135_07_rows : List Row := [(row3 31 50 63), (row3 31 51 52), (row3 31 51 53), (row3 31 51 54), (row3 31 51 55), (row3 31 51 56), (row3 31 51 57), (row3 31 51 58), (row3 31 51 59), (row3 31 51 60), (row3 31 51 61), (row3 31 51 62), (row3 31 51 63), (row3 31 52 53), (row3 31 52 54), (row3 31 52 55)]

def b135_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237)]

theorem b135_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_07_rows b135_07_labels 101402565607521578812500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_07_rows b135_07_labels]
    decide +kernel

def b135_08_rows : List Row := [(row3 31 52 56), (row3 31 52 57), (row3 31 52 58), (row3 31 52 59), (row3 31 52 60), (row3 31 52 61), (row3 31 52 62), (row3 31 52 63), (row3 31 53 54), (row3 31 53 55), (row3 31 53 56), (row3 31 53 57), (row3 31 53 58), (row3 31 53 59), (row3 31 53 60), (row3 31 53 61)]

def b135_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b135_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_08_rows b135_08_labels 3223191543353527401284400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_08_rows b135_08_labels]
    decide +kernel

def b135_09_rows : List Row := [(row3 31 53 62), (row3 31 53 63), (row3 31 54 55), (row3 31 54 56), (row3 31 54 57), (row3 31 54 58), (row3 31 54 59), (row3 31 54 60), (row3 31 54 61), (row3 31 54 62), (row3 31 54 63), (row3 31 55 56), (row3 31 55 57), (row3 31 55 58), (row3 31 55 59), (row3 31 55 60)]

def b135_09_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 180 154 154), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 278 301 301), (row3 234 226 226), (row3 462 247 247), (row3 462 462 462), (row3 462 243 243)]

theorem b135_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_09_rows b135_09_labels 970565638238181897551492400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_09_rows b135_09_labels]
    decide +kernel

def b135_10_rows : List Row := [(row3 31 55 61), (row3 31 55 62), (row3 31 55 63), (row3 31 56 57), (row3 31 56 58), (row3 31 56 59), (row3 31 56 60), (row3 31 56 61), (row3 31 56 62), (row3 31 56 63), (row3 31 57 58), (row3 31 57 59), (row3 31 57 60), (row3 31 57 61), (row3 31 57 62), (row3 31 57 63)]

def b135_10_labels : List Row := [(row3 234 234 234), (row3 278 282 282), (row3 357 90 187), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 193 163 139), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 261 288 290)]

theorem b135_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_10_rows b135_10_labels 9313492645063156363244173800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_10_rows b135_10_labels]
    decide +kernel

def b135_11_rows : List Row := [(row3 31 58 59), (row3 31 58 60), (row3 31 58 61), (row3 31 58 62), (row3 31 58 63), (row3 31 59 60), (row3 31 59 61), (row3 31 59 62), (row3 31 59 63), (row3 31 60 61), (row3 31 60 62), (row3 31 60 63), (row3 31 61 62), (row3 31 61 63), (row3 31 62 63), (row3 32 33 34)]

def b135_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 238 232 230), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 261 462 261), (row3 193 232 189), (row3 462 208 208)]

theorem b135_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_11_rows b135_11_labels 624188657877834807920791800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_11_rows b135_11_labels]
    decide +kernel

def b135_12_rows : List Row := [(row3 32 33 35), (row3 32 33 36), (row3 32 33 37), (row3 32 33 38), (row3 32 33 39), (row3 32 33 40), (row3 32 33 41), (row3 32 33 42), (row3 32 33 43), (row3 32 33 44), (row3 32 33 45), (row3 32 33 46), (row3 32 33 47), (row3 32 33 48), (row3 32 33 49), (row3 32 33 50)]

def b135_12_labels : List Row := [(row3 462 257 257), (row3 462 462 462), (row3 462 257 257), (row3 462 208 208), (row3 462 337 337), (row3 429 71 341), (row3 163 139 193), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 232 189 193), (row3 178 174 174), (row3 289 299 299), (row3 462 462 462)]

theorem b135_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_12_rows b135_12_labels 121755124060819601620889656980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_12_rows b135_12_labels]
    decide +kernel

def b135_13_rows : List Row := [(row3 32 33 51), (row3 32 33 52), (row3 32 33 53), (row3 32 33 54), (row3 32 33 55), (row3 32 33 56), (row3 32 33 57), (row3 32 33 58), (row3 32 33 59), (row3 32 33 60), (row3 32 33 61), (row3 32 33 62), (row3 32 33 63), (row3 32 34 35), (row3 32 34 36), (row3 32 34 37)]

def b135_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 272 272), (row3 462 269 269), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 239 239)]

theorem b135_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_13_rows b135_13_labels 2263128937201298893979785500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_13_rows b135_13_labels]
    decide +kernel

def b135_14_rows : List Row := [(row3 32 34 38), (row3 32 34 39), (row3 32 34 40), (row3 32 34 41), (row3 32 34 42), (row3 32 34 43), (row3 32 34 44), (row3 32 34 45), (row3 32 34 46), (row3 32 34 47), (row3 32 34 48), (row3 32 34 49), (row3 32 34 50), (row3 32 34 51), (row3 32 34 52), (row3 32 34 53)]

def b135_14_labels : List Row := [(row3 462 255 255), (row3 462 208 208), (row3 94 333 168), (row3 288 290 261), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 261 261), (row3 462 273 273), (row3 224 223 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b135_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_14_rows b135_14_labels 3433631128239056572053726480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_14_rows b135_14_labels]
    decide +kernel

def b135_15_rows : List Row := [(row3 32 34 54), (row3 32 34 55), (row3 32 34 56), (row3 32 34 57), (row3 32 34 58), (row3 32 34 59), (row3 32 34 60), (row3 32 34 61), (row3 32 34 62), (row3 32 34 63), (row3 32 35 36), (row3 32 35 37), (row3 32 35 38), (row3 32 35 39), (row3 32 35 40), (row3 32 35 41)]

def b135_15_labels : List Row := [(row3 462 462 462), (row3 462 237 237), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 239 239), (row3 462 257 257), (row3 8 203 254), (row3 232 230 238)]

theorem b135_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b135_15_rows b135_15_labels 183603520291497450561073500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b135_15_rows b135_15_labels]
    decide +kernel

theorem checked135 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_135 QuarticIntegerComputationalData.ids64_135 153273207601956273125764549680 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b135_00_rows ++ b135_01_rows) ++ (b135_02_rows ++ b135_03_rows)) ++ ((b135_04_rows ++ b135_05_rows) ++ (b135_06_rows ++ b135_07_rows))) ++ (((b135_08_rows ++ b135_09_rows) ++ (b135_10_rows ++ b135_11_rows)) ++ ((b135_12_rows ++ b135_13_rows) ++ (b135_14_rows ++ b135_15_rows))))
    ((((b135_00_labels ++ b135_01_labels) ++ (b135_02_labels ++ b135_03_labels)) ++ ((b135_04_labels ++ b135_05_labels) ++ (b135_06_labels ++ b135_07_labels))) ++ (((b135_08_labels ++ b135_09_labels) ++ (b135_10_labels ++ b135_11_labels)) ++ ((b135_12_labels ++ b135_13_labels) ++ (b135_14_labels ++ b135_15_labels)))) 153273207601956273125764549680
  exact ((((b135_00_checked.append (c := 2533774368508583462944200) b135_01_checked (by decide +kernel)).append (c := 10083052283419196631143830560) (b135_02_checked.append (c := 10080518509050688047680886360) b135_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 14726249822682291992162564820) ((b135_04_checked.append (c := 4641722882457515252365640760) b135_05_checked (by decide +kernel)).append (c := 4643197539263095361018734260) (b135_06_checked.append (c := 1474656805580108653093500) b135_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 153273207601956273125764549680) (((b135_08_checked.append (c := 973788829781535424952776800) b135_09_checked (by decide +kernel)).append (c := 10911470132722526596117742400) (b135_10_checked.append (c := 9937681302940991171164965600) b135_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 138546957779273981133601984860) ((b135_12_checked.append (c := 124018252998020900514869442480) b135_13_checked (by decide +kernel)).append (c := 127635487646551454537484242460) (b135_14_checked.append (c := 3617234648530554022614799980) b135_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b136_00_rows : List Row := [(row3 32 35 42), (row3 32 35 43), (row3 32 35 44), (row3 32 35 45), (row3 32 35 46), (row3 32 35 47), (row3 32 35 48), (row3 32 35 49), (row3 32 35 50), (row3 32 35 51), (row3 32 35 52), (row3 32 35 53), (row3 32 35 54), (row3 32 35 55), (row3 32 35 56), (row3 32 35 57)]

def b136_00_labels : List Row := [(row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 238 238), (row3 462 239 239), (row3 462 249 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 240 240), (row3 462 462 462)]

theorem b136_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_00_rows b136_00_labels 298517856733489192644000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_00_rows b136_00_labels]
    decide +kernel

def b136_01_rows : List Row := [(row3 32 35 58), (row3 32 35 59), (row3 32 35 60), (row3 32 35 61), (row3 32 35 62), (row3 32 35 63), (row3 32 36 37), (row3 32 36 38), (row3 32 36 39), (row3 32 36 40), (row3 32 36 41), (row3 32 36 42), (row3 32 36 43), (row3 32 36 44), (row3 32 36 45), (row3 32 36 46)]

def b136_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_01_rows b136_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_01_rows b136_01_labels]
    decide +kernel

def b136_02_rows : List Row := [(row3 32 36 47), (row3 32 36 48), (row3 32 36 49), (row3 32 36 50), (row3 32 36 51), (row3 32 36 52), (row3 32 36 53), (row3 32 36 54), (row3 32 36 55), (row3 32 36 56), (row3 32 36 57), (row3 32 36 58), (row3 32 36 59), (row3 32 36 60), (row3 32 36 61), (row3 32 36 62)]

def b136_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_02_rows b136_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_02_rows b136_02_labels]
    decide +kernel

def b136_03_rows : List Row := [(row3 32 36 63), (row3 32 37 38), (row3 32 37 39), (row3 32 37 40), (row3 32 37 41), (row3 32 37 42), (row3 32 37 43), (row3 32 37 44), (row3 32 37 45), (row3 32 37 46), (row3 32 37 47), (row3 32 37 48), (row3 32 37 49), (row3 32 37 50), (row3 32 37 51), (row3 32 37 52)]

def b136_03_labels : List Row := [(row3 462 462 462), (row3 462 239 239), (row3 462 257 257), (row3 8 203 254), (row3 462 238 238), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 232 230 238), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_03_rows b136_03_labels 181813389649385894051785500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_03_rows b136_03_labels]
    decide +kernel

def b136_04_rows : List Row := [(row3 32 37 53), (row3 32 37 54), (row3 32 37 55), (row3 32 37 56), (row3 32 37 57), (row3 32 37 58), (row3 32 37 59), (row3 32 37 60), (row3 32 37 61), (row3 32 37 62), (row3 32 37 63), (row3 32 38 39), (row3 32 38 40), (row3 32 38 41), (row3 32 38 42), (row3 32 38 43)]

def b136_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 249 249), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 208 208), (row3 94 333 168), (row3 462 261 261), (row3 462 237 237), (row3 462 462 462)]

theorem b136_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_04_rows b136_04_labels 3476982830432477814700659300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_04_rows b136_04_labels]
    decide +kernel

def b136_05_rows : List Row := [(row3 32 38 44), (row3 32 38 45), (row3 32 38 46), (row3 32 38 47), (row3 32 38 48), (row3 32 38 49), (row3 32 38 50), (row3 32 38 51), (row3 32 38 52), (row3 32 38 53), (row3 32 38 54), (row3 32 38 55), (row3 32 38 56), (row3 32 38 57), (row3 32 38 58), (row3 32 38 59)]

def b136_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 288 290 261), (row3 462 273 273), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 223 223), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_05_rows b136_05_labels 37807367202500612705488080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_05_rows b136_05_labels]
    decide +kernel

def b136_06_rows : List Row := [(row3 32 38 60), (row3 32 38 61), (row3 32 38 62), (row3 32 38 63), (row3 32 39 40), (row3 32 39 41), (row3 32 39 42), (row3 32 39 43), (row3 32 39 44), (row3 32 39 45), (row3 32 39 46), (row3 32 39 47), (row3 32 39 48), (row3 32 39 49), (row3 32 39 50), (row3 32 39 51)]

def b136_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 429 71 341), (row3 232 189 193), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 163 139 193), (row3 178 174 174), (row3 462 272 272), (row3 462 462 462), (row3 462 462 462)]

theorem b136_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_06_rows b136_06_labels 114792195034346773317959415780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_06_rows b136_06_labels]
    decide +kernel

def b136_07_rows : List Row := [(row3 32 39 52), (row3 32 39 53), (row3 32 39 54), (row3 32 39 55), (row3 32 39 56), (row3 32 39 57), (row3 32 39 58), (row3 32 39 59), (row3 32 39 60), (row3 32 39 61), (row3 32 39 62), (row3 32 39 63), (row3 32 40 41), (row3 32 40 42), (row3 32 40 43), (row3 32 40 44)]

def b136_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 299 299), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 64 55 66), (row3 339 342 328), (row3 201 201 208), (row3 462 257 257)]

theorem b136_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_07_rows b136_07_labels 267404091936551158800853331250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_07_rows b136_07_labels]
    decide +kernel

def b136_08_rows : List Row := [(row3 32 40 45), (row3 32 40 46), (row3 32 40 47), (row3 32 40 48), (row3 32 40 49), (row3 32 40 50), (row3 32 40 51), (row3 32 40 52), (row3 32 40 53), (row3 32 40 54), (row3 32 40 55), (row3 32 40 56), (row3 32 40 57), (row3 32 40 58), (row3 32 40 59), (row3 32 40 60)]

def b136_08_labels : List Row := [(row3 201 201 208), (row3 339 342 328), (row3 64 55 66), (row3 446 30 80), (row3 366 375 353), (row3 154 154 180), (row3 462 263 263), (row3 462 462 462), (row3 462 263 263), (row3 154 154 180), (row3 366 375 353), (row3 364 374 355), (row3 151 153 179), (row3 462 270 270), (row3 462 462 462), (row3 462 462 462)]

theorem b136_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_08_rows b136_08_labels 4754585819041611627698365056750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_08_rows b136_08_labels]
    decide +kernel

def b136_09_rows : List Row := [(row3 32 40 61), (row3 32 40 62), (row3 32 40 63), (row3 32 41 42), (row3 32 41 43), (row3 32 41 44), (row3 32 41 45), (row3 32 41 46), (row3 32 41 47), (row3 32 41 48), (row3 32 41 49), (row3 32 41 50), (row3 32 41 51), (row3 32 41 52), (row3 32 41 53), (row3 32 41 54)]

def b136_09_labels : List Row := [(row3 462 462 462), (row3 462 270 270), (row3 151 153 179), (row3 163 235 162), (row3 273 462 273), (row3 236 462 236), (row3 462 462 462), (row3 236 235 233), (row3 288 288 288), (row3 350 346 349), (row3 399 82 156), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_09_rows b136_09_labels 32540023743491537035802135640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_09_rows b136_09_labels]
    decide +kernel

def b136_10_rows : List Row := [(row3 32 41 55), (row3 32 41 56), (row3 32 41 57), (row3 32 41 58), (row3 32 41 59), (row3 32 41 60), (row3 32 41 61), (row3 32 41 62), (row3 32 41 63), (row3 32 42 43), (row3 32 42 44), (row3 32 42 45), (row3 32 42 46), (row3 32 42 47), (row3 32 42 48), (row3 32 42 49)]

def b136_10_labels : List Row := [(row3 221 222 220), (row3 151 153 179), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 236 233 235), (row3 178 183 183), (row3 306 311 311)]

theorem b136_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_10_rows b136_10_labels 6762624648375571098351888600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_10_rows b136_10_labels]
    decide +kernel

def b136_11_rows : List Row := [(row3 32 42 50), (row3 32 42 51), (row3 32 42 52), (row3 32 42 53), (row3 32 42 54), (row3 32 42 55), (row3 32 42 56), (row3 32 42 57), (row3 32 42 58), (row3 32 42 59), (row3 32 42 60), (row3 32 42 61), (row3 32 42 62), (row3 32 42 63), (row3 32 43 44), (row3 32 43 45)]

def b136_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 270 270), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_11_rows b136_11_labels 50290129866452707373647500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_11_rows b136_11_labels]
    decide +kernel

def b136_12_rows : List Row := [(row3 32 43 46), (row3 32 43 47), (row3 32 43 48), (row3 32 43 49), (row3 32 43 50), (row3 32 43 51), (row3 32 43 52), (row3 32 43 53), (row3 32 43 54), (row3 32 43 55), (row3 32 43 56), (row3 32 43 57), (row3 32 43 58), (row3 32 43 59), (row3 32 43 60), (row3 32 43 61)]

def b136_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_12_rows b136_12_labels 3188107204239935288077200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_12_rows b136_12_labels]
    decide +kernel

def b136_13_rows : List Row := [(row3 32 43 62), (row3 32 43 63), (row3 32 44 45), (row3 32 44 46), (row3 32 44 47), (row3 32 44 48), (row3 32 44 49), (row3 32 44 50), (row3 32 44 51), (row3 32 44 52), (row3 32 44 53), (row3 32 44 54), (row3 32 44 55), (row3 32 44 56), (row3 32 44 57), (row3 32 44 58)]

def b136_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b136_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_13_rows b136_13_labels 310000683581911151838000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_13_rows b136_13_labels]
    decide +kernel

def b136_14_rows : List Row := [(row3 32 44 59), (row3 32 44 60), (row3 32 44 61), (row3 32 44 62), (row3 32 44 63), (row3 32 45 46), (row3 32 45 47), (row3 32 45 48), (row3 32 45 49), (row3 32 45 50), (row3 32 45 51), (row3 32 45 52), (row3 32 45 53), (row3 32 45 54), (row3 32 45 55), (row3 32 45 56)]

def b136_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 462 261 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 462 462)]

theorem b136_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_14_rows b136_14_labels 9016574122499625035398800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_14_rows b136_14_labels]
    decide +kernel

def b136_15_rows : List Row := [(row3 32 45 57), (row3 32 45 58), (row3 32 45 59), (row3 32 45 60), (row3 32 45 61), (row3 32 45 62), (row3 32 45 63), (row3 32 46 47), (row3 32 46 48), (row3 32 46 49), (row3 32 46 50), (row3 32 46 51), (row3 32 46 52), (row3 32 46 53), (row3 32 46 54), (row3 32 46 55)]

def b136_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 162 235), (row3 178 183 183), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 306 311 311)]

theorem b136_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b136_15_rows b136_15_labels 870635129463736959205791360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b136_15_rows b136_15_labels]
    decide +kernel

theorem checked136 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_136 QuarticIntegerComputationalData.ids64_136 5180715096450858276900037157760 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b136_00_rows ++ b136_01_rows) ++ (b136_02_rows ++ b136_03_rows)) ++ ((b136_04_rows ++ b136_05_rows) ++ (b136_06_rows ++ b136_07_rows))) ++ (((b136_08_rows ++ b136_09_rows) ++ (b136_10_rows ++ b136_11_rows)) ++ ((b136_12_rows ++ b136_13_rows) ++ (b136_14_rows ++ b136_15_rows))))
    ((((b136_00_labels ++ b136_01_labels) ++ (b136_02_labels ++ b136_03_labels)) ++ ((b136_04_labels ++ b136_05_labels) ++ (b136_06_labels ++ b136_07_labels))) ++ (((b136_08_labels ++ b136_09_labels) ++ (b136_10_labels ++ b136_11_labels)) ++ ((b136_12_labels ++ b136_13_labels) ++ (b136_14_labels ++ b136_15_labels)))) 5180715096450858276900037157760
  exact ((((b136_00_checked.append (c := 298517856733489192644000) b136_01_checked (by decide +kernel)).append (c := 182111907506119383244429500) (b136_02_checked.append (c := 181813389649385894051785500) b136_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 385893189076039029929463323910) ((b136_04_checked.append (c := 3514790197634978427406147380) b136_05_checked (by decide +kernel)).append (c := 385711077168532910546218894410) (b136_06_checked.append (c := 382196286970897932118812747030) b136_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 5180715096450858276900037157760) (((b136_08_checked.append (c := 4787125842785103164734167192390) b136_09_checked (by decide +kernel)).append (c := 4793938757563345188539892728490) (b136_10_checked.append (c := 6812914778242023805725536100) b136_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4794821907374819246970573833850) ((b136_12_checked.append (c := 3498107887821846439915200) b136_13_checked (by decide +kernel)).append (c := 883149811474058430681105360) (b136_14_checked.append (c := 879651703586236584241190160) b136_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch012
import Dressed.QuarticIntegerComputationalData64.Batch013


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b105_00_rows : List Row := [(row3 20 32 39), (row3 20 32 40), (row3 20 32 41), (row3 20 32 42), (row3 20 32 43), (row3 20 32 44), (row3 20 32 45), (row3 20 32 46), (row3 20 32 47), (row3 20 32 48), (row3 20 32 49), (row3 20 32 50), (row3 20 32 51), (row3 20 32 52), (row3 20 32 53), (row3 20 32 54)]

def b105_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_00_rows b105_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_00_rows b105_00_labels]
    decide +kernel

def b105_01_rows : List Row := [(row3 20 32 55), (row3 20 32 56), (row3 20 32 57), (row3 20 32 58), (row3 20 32 59), (row3 20 32 60), (row3 20 32 61), (row3 20 32 62), (row3 20 32 63), (row3 20 33 34), (row3 20 33 35), (row3 20 33 36), (row3 20 33 37), (row3 20 33 38), (row3 20 33 39), (row3 20 33 40)]

def b105_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_01_rows b105_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_01_rows b105_01_labels]
    decide +kernel

def b105_02_rows : List Row := [(row3 20 33 41), (row3 20 33 42), (row3 20 33 43), (row3 20 33 44), (row3 20 33 45), (row3 20 33 46), (row3 20 33 47), (row3 20 33 48), (row3 20 33 49), (row3 20 33 50), (row3 20 33 51), (row3 20 33 52), (row3 20 33 53), (row3 20 33 54), (row3 20 33 55), (row3 20 33 56)]

def b105_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_02_rows b105_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_02_rows b105_02_labels]
    decide +kernel

def b105_03_rows : List Row := [(row3 20 33 57), (row3 20 33 58), (row3 20 33 59), (row3 20 33 60), (row3 20 33 61), (row3 20 33 62), (row3 20 33 63), (row3 20 34 35), (row3 20 34 36), (row3 20 34 37), (row3 20 34 38), (row3 20 34 39), (row3 20 34 40), (row3 20 34 41), (row3 20 34 42), (row3 20 34 43)]

def b105_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_03_rows b105_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_03_rows b105_03_labels]
    decide +kernel

def b105_04_rows : List Row := [(row3 20 34 44), (row3 20 34 45), (row3 20 34 46), (row3 20 34 47), (row3 20 34 48), (row3 20 34 49), (row3 20 34 50), (row3 20 34 51), (row3 20 34 52), (row3 20 34 53), (row3 20 34 54), (row3 20 34 55), (row3 20 34 56), (row3 20 34 57), (row3 20 34 58), (row3 20 34 59)]

def b105_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_04_rows b105_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_04_rows b105_04_labels]
    decide +kernel

def b105_05_rows : List Row := [(row3 20 34 60), (row3 20 34 61), (row3 20 34 62), (row3 20 34 63), (row3 20 35 36), (row3 20 35 37), (row3 20 35 38), (row3 20 35 39), (row3 20 35 40), (row3 20 35 41), (row3 20 35 42), (row3 20 35 43), (row3 20 35 44), (row3 20 35 45), (row3 20 35 46), (row3 20 35 47)]

def b105_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_05_rows b105_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_05_rows b105_05_labels]
    decide +kernel

def b105_06_rows : List Row := [(row3 20 35 48), (row3 20 35 49), (row3 20 35 50), (row3 20 35 51), (row3 20 35 52), (row3 20 35 53), (row3 20 35 54), (row3 20 35 55), (row3 20 35 56), (row3 20 35 57), (row3 20 35 58), (row3 20 35 59), (row3 20 35 60), (row3 20 35 61), (row3 20 35 62), (row3 20 35 63)]

def b105_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_06_rows b105_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_06_rows b105_06_labels]
    decide +kernel

def b105_07_rows : List Row := [(row3 20 36 37), (row3 20 36 38), (row3 20 36 39), (row3 20 36 40), (row3 20 36 41), (row3 20 36 42), (row3 20 36 43), (row3 20 36 44), (row3 20 36 45), (row3 20 36 46), (row3 20 36 47), (row3 20 36 48), (row3 20 36 49), (row3 20 36 50), (row3 20 36 51), (row3 20 36 52)]

def b105_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_07_rows b105_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_07_rows b105_07_labels]
    decide +kernel

def b105_08_rows : List Row := [(row3 20 36 53), (row3 20 36 54), (row3 20 36 55), (row3 20 36 56), (row3 20 36 57), (row3 20 36 58), (row3 20 36 59), (row3 20 36 60), (row3 20 36 61), (row3 20 36 62), (row3 20 36 63), (row3 20 37 38), (row3 20 37 39), (row3 20 37 40), (row3 20 37 41), (row3 20 37 42)]

def b105_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_08_rows b105_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_08_rows b105_08_labels]
    decide +kernel

def b105_09_rows : List Row := [(row3 20 37 43), (row3 20 37 44), (row3 20 37 45), (row3 20 37 46), (row3 20 37 47), (row3 20 37 48), (row3 20 37 49), (row3 20 37 50), (row3 20 37 51), (row3 20 37 52), (row3 20 37 53), (row3 20 37 54), (row3 20 37 55), (row3 20 37 56), (row3 20 37 57), (row3 20 37 58)]

def b105_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_09_rows b105_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_09_rows b105_09_labels]
    decide +kernel

def b105_10_rows : List Row := [(row3 20 37 59), (row3 20 37 60), (row3 20 37 61), (row3 20 37 62), (row3 20 37 63), (row3 20 38 39), (row3 20 38 40), (row3 20 38 41), (row3 20 38 42), (row3 20 38 43), (row3 20 38 44), (row3 20 38 45), (row3 20 38 46), (row3 20 38 47), (row3 20 38 48), (row3 20 38 49)]

def b105_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_10_rows b105_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_10_rows b105_10_labels]
    decide +kernel

def b105_11_rows : List Row := [(row3 20 38 50), (row3 20 38 51), (row3 20 38 52), (row3 20 38 53), (row3 20 38 54), (row3 20 38 55), (row3 20 38 56), (row3 20 38 57), (row3 20 38 58), (row3 20 38 59), (row3 20 38 60), (row3 20 38 61), (row3 20 38 62), (row3 20 38 63), (row3 20 39 40), (row3 20 39 41)]

def b105_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_11_rows b105_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_11_rows b105_11_labels]
    decide +kernel

def b105_12_rows : List Row := [(row3 20 39 42), (row3 20 39 43), (row3 20 39 44), (row3 20 39 45), (row3 20 39 46), (row3 20 39 47), (row3 20 39 48), (row3 20 39 49), (row3 20 39 50), (row3 20 39 51), (row3 20 39 52), (row3 20 39 53), (row3 20 39 54), (row3 20 39 55), (row3 20 39 56), (row3 20 39 57)]

def b105_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_12_rows b105_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_12_rows b105_12_labels]
    decide +kernel

def b105_13_rows : List Row := [(row3 20 39 58), (row3 20 39 59), (row3 20 39 60), (row3 20 39 61), (row3 20 39 62), (row3 20 39 63), (row3 20 40 41), (row3 20 40 42), (row3 20 40 43), (row3 20 40 44), (row3 20 40 45), (row3 20 40 46), (row3 20 40 47), (row3 20 40 48), (row3 20 40 49), (row3 20 40 50)]

def b105_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_13_rows b105_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_13_rows b105_13_labels]
    decide +kernel

def b105_14_rows : List Row := [(row3 20 40 51), (row3 20 40 52), (row3 20 40 53), (row3 20 40 54), (row3 20 40 55), (row3 20 40 56), (row3 20 40 57), (row3 20 40 58), (row3 20 40 59), (row3 20 40 60), (row3 20 40 61), (row3 20 40 62), (row3 20 40 63), (row3 20 41 42), (row3 20 41 43), (row3 20 41 44)]

def b105_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_14_rows b105_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_14_rows b105_14_labels]
    decide +kernel

def b105_15_rows : List Row := [(row3 20 41 45), (row3 20 41 46), (row3 20 41 47), (row3 20 41 48), (row3 20 41 49), (row3 20 41 50), (row3 20 41 51), (row3 20 41 52), (row3 20 41 53), (row3 20 41 54), (row3 20 41 55), (row3 20 41 56), (row3 20 41 57), (row3 20 41 58), (row3 20 41 59), (row3 20 41 60)]

def b105_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b105_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b105_15_rows b105_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b105_15_rows b105_15_labels]
    decide +kernel

theorem checked105 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_105 QuarticIntegerComputationalData.ids64_105 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b105_00_rows ++ b105_01_rows) ++ (b105_02_rows ++ b105_03_rows)) ++ ((b105_04_rows ++ b105_05_rows) ++ (b105_06_rows ++ b105_07_rows))) ++ (((b105_08_rows ++ b105_09_rows) ++ (b105_10_rows ++ b105_11_rows)) ++ ((b105_12_rows ++ b105_13_rows) ++ (b105_14_rows ++ b105_15_rows))))
    ((((b105_00_labels ++ b105_01_labels) ++ (b105_02_labels ++ b105_03_labels)) ++ ((b105_04_labels ++ b105_05_labels) ++ (b105_06_labels ++ b105_07_labels))) ++ (((b105_08_labels ++ b105_09_labels) ++ (b105_10_labels ++ b105_11_labels)) ++ ((b105_12_labels ++ b105_13_labels) ++ (b105_14_labels ++ b105_15_labels)))) 0
  exact ((((b105_00_checked.append (c := 0) b105_01_checked (by decide +kernel)).append (c := 0) (b105_02_checked.append (c := 0) b105_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b105_04_checked.append (c := 0) b105_05_checked (by decide +kernel)).append (c := 0) (b105_06_checked.append (c := 0) b105_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b105_08_checked.append (c := 0) b105_09_checked (by decide +kernel)).append (c := 0) (b105_10_checked.append (c := 0) b105_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b105_12_checked.append (c := 0) b105_13_checked (by decide +kernel)).append (c := 0) (b105_14_checked.append (c := 0) b105_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b106_00_rows : List Row := [(row3 20 41 61), (row3 20 41 62), (row3 20 41 63), (row3 20 42 43), (row3 20 42 44), (row3 20 42 45), (row3 20 42 46), (row3 20 42 47), (row3 20 42 48), (row3 20 42 49), (row3 20 42 50), (row3 20 42 51), (row3 20 42 52), (row3 20 42 53), (row3 20 42 54), (row3 20 42 55)]

def b106_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_00_rows b106_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_00_rows b106_00_labels]
    decide +kernel

def b106_01_rows : List Row := [(row3 20 42 56), (row3 20 42 57), (row3 20 42 58), (row3 20 42 59), (row3 20 42 60), (row3 20 42 61), (row3 20 42 62), (row3 20 42 63), (row3 20 43 44), (row3 20 43 45), (row3 20 43 46), (row3 20 43 47), (row3 20 43 48), (row3 20 43 49), (row3 20 43 50), (row3 20 43 51)]

def b106_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_01_rows b106_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_01_rows b106_01_labels]
    decide +kernel

def b106_02_rows : List Row := [(row3 20 43 52), (row3 20 43 53), (row3 20 43 54), (row3 20 43 55), (row3 20 43 56), (row3 20 43 57), (row3 20 43 58), (row3 20 43 59), (row3 20 43 60), (row3 20 43 61), (row3 20 43 62), (row3 20 43 63), (row3 20 44 45), (row3 20 44 46), (row3 20 44 47), (row3 20 44 48)]

def b106_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_02_rows b106_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_02_rows b106_02_labels]
    decide +kernel

def b106_03_rows : List Row := [(row3 20 44 49), (row3 20 44 50), (row3 20 44 51), (row3 20 44 52), (row3 20 44 53), (row3 20 44 54), (row3 20 44 55), (row3 20 44 56), (row3 20 44 57), (row3 20 44 58), (row3 20 44 59), (row3 20 44 60), (row3 20 44 61), (row3 20 44 62), (row3 20 44 63), (row3 20 45 46)]

def b106_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_03_rows b106_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_03_rows b106_03_labels]
    decide +kernel

def b106_04_rows : List Row := [(row3 20 45 47), (row3 20 45 48), (row3 20 45 49), (row3 20 45 50), (row3 20 45 51), (row3 20 45 52), (row3 20 45 53), (row3 20 45 54), (row3 20 45 55), (row3 20 45 56), (row3 20 45 57), (row3 20 45 58), (row3 20 45 59), (row3 20 45 60), (row3 20 45 61), (row3 20 45 62)]

def b106_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_04_rows b106_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_04_rows b106_04_labels]
    decide +kernel

def b106_05_rows : List Row := [(row3 20 45 63), (row3 20 46 47), (row3 20 46 48), (row3 20 46 49), (row3 20 46 50), (row3 20 46 51), (row3 20 46 52), (row3 20 46 53), (row3 20 46 54), (row3 20 46 55), (row3 20 46 56), (row3 20 46 57), (row3 20 46 58), (row3 20 46 59), (row3 20 46 60), (row3 20 46 61)]

def b106_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_05_rows b106_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_05_rows b106_05_labels]
    decide +kernel

def b106_06_rows : List Row := [(row3 20 46 62), (row3 20 46 63), (row3 20 47 48), (row3 20 47 49), (row3 20 47 50), (row3 20 47 51), (row3 20 47 52), (row3 20 47 53), (row3 20 47 54), (row3 20 47 55), (row3 20 47 56), (row3 20 47 57), (row3 20 47 58), (row3 20 47 59), (row3 20 47 60), (row3 20 47 61)]

def b106_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_06_rows b106_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_06_rows b106_06_labels]
    decide +kernel

def b106_07_rows : List Row := [(row3 20 47 62), (row3 20 47 63), (row3 20 48 49), (row3 20 48 50), (row3 20 48 51), (row3 20 48 52), (row3 20 48 53), (row3 20 48 54), (row3 20 48 55), (row3 20 48 56), (row3 20 48 57), (row3 20 48 58), (row3 20 48 59), (row3 20 48 60), (row3 20 48 61), (row3 20 48 62)]

def b106_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_07_rows b106_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_07_rows b106_07_labels]
    decide +kernel

def b106_08_rows : List Row := [(row3 20 48 63), (row3 20 49 50), (row3 20 49 51), (row3 20 49 52), (row3 20 49 53), (row3 20 49 54), (row3 20 49 55), (row3 20 49 56), (row3 20 49 57), (row3 20 49 58), (row3 20 49 59), (row3 20 49 60), (row3 20 49 61), (row3 20 49 62), (row3 20 49 63), (row3 20 50 51)]

def b106_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_08_rows b106_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_08_rows b106_08_labels]
    decide +kernel

def b106_09_rows : List Row := [(row3 20 50 52), (row3 20 50 53), (row3 20 50 54), (row3 20 50 55), (row3 20 50 56), (row3 20 50 57), (row3 20 50 58), (row3 20 50 59), (row3 20 50 60), (row3 20 50 61), (row3 20 50 62), (row3 20 50 63), (row3 20 51 52), (row3 20 51 53), (row3 20 51 54), (row3 20 51 55)]

def b106_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_09_rows b106_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_09_rows b106_09_labels]
    decide +kernel

def b106_10_rows : List Row := [(row3 20 51 56), (row3 20 51 57), (row3 20 51 58), (row3 20 51 59), (row3 20 51 60), (row3 20 51 61), (row3 20 51 62), (row3 20 51 63), (row3 20 52 53), (row3 20 52 54), (row3 20 52 55), (row3 20 52 56), (row3 20 52 57), (row3 20 52 58), (row3 20 52 59), (row3 20 52 60)]

def b106_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_10_rows b106_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_10_rows b106_10_labels]
    decide +kernel

def b106_11_rows : List Row := [(row3 20 52 61), (row3 20 52 62), (row3 20 52 63), (row3 20 53 54), (row3 20 53 55), (row3 20 53 56), (row3 20 53 57), (row3 20 53 58), (row3 20 53 59), (row3 20 53 60), (row3 20 53 61), (row3 20 53 62), (row3 20 53 63), (row3 20 54 55), (row3 20 54 56), (row3 20 54 57)]

def b106_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_11_rows b106_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_11_rows b106_11_labels]
    decide +kernel

def b106_12_rows : List Row := [(row3 20 54 58), (row3 20 54 59), (row3 20 54 60), (row3 20 54 61), (row3 20 54 62), (row3 20 54 63), (row3 20 55 56), (row3 20 55 57), (row3 20 55 58), (row3 20 55 59), (row3 20 55 60), (row3 20 55 61), (row3 20 55 62), (row3 20 55 63), (row3 20 56 57), (row3 20 56 58)]

def b106_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_12_rows b106_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_12_rows b106_12_labels]
    decide +kernel

def b106_13_rows : List Row := [(row3 20 56 59), (row3 20 56 60), (row3 20 56 61), (row3 20 56 62), (row3 20 56 63), (row3 20 57 58), (row3 20 57 59), (row3 20 57 60), (row3 20 57 61), (row3 20 57 62), (row3 20 57 63), (row3 20 58 59), (row3 20 58 60), (row3 20 58 61), (row3 20 58 62), (row3 20 58 63)]

def b106_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_13_rows b106_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_13_rows b106_13_labels]
    decide +kernel

def b106_14_rows : List Row := [(row3 20 59 60), (row3 20 59 61), (row3 20 59 62), (row3 20 59 63), (row3 20 60 61), (row3 20 60 62), (row3 20 60 63), (row3 20 61 62), (row3 20 61 63), (row3 20 62 63), (row3 21 22 23), (row3 21 22 24), (row3 21 22 25), (row3 21 22 26), (row3 21 22 27), (row3 21 22 28)]

def b106_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 42 435 181), (row3 294 462 294), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293)]

theorem b106_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_14_rows b106_14_labels 344659792352447811362805252450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_14_rows b106_14_labels]
    decide +kernel

def b106_15_rows : List Row := [(row3 21 22 29), (row3 21 22 30), (row3 21 22 31), (row3 21 22 32), (row3 21 22 33), (row3 21 22 34), (row3 21 22 35), (row3 21 22 36), (row3 21 22 37), (row3 21 22 38), (row3 21 22 39), (row3 21 22 40), (row3 21 22 41), (row3 21 22 42), (row3 21 22 43), (row3 21 22 44)]

def b106_15_labels : List Row := [(row3 139 462 139), (row3 377 462 377), (row3 138 232 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 180 462 180), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b106_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b106_15_rows b106_15_labels 23394219184062453942783445500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b106_15_rows b106_15_labels]
    decide +kernel

theorem checked106 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_106 QuarticIntegerComputationalData.ids64_106 368054011536510265305588697950 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b106_00_rows ++ b106_01_rows) ++ (b106_02_rows ++ b106_03_rows)) ++ ((b106_04_rows ++ b106_05_rows) ++ (b106_06_rows ++ b106_07_rows))) ++ (((b106_08_rows ++ b106_09_rows) ++ (b106_10_rows ++ b106_11_rows)) ++ ((b106_12_rows ++ b106_13_rows) ++ (b106_14_rows ++ b106_15_rows))))
    ((((b106_00_labels ++ b106_01_labels) ++ (b106_02_labels ++ b106_03_labels)) ++ ((b106_04_labels ++ b106_05_labels) ++ (b106_06_labels ++ b106_07_labels))) ++ (((b106_08_labels ++ b106_09_labels) ++ (b106_10_labels ++ b106_11_labels)) ++ ((b106_12_labels ++ b106_13_labels) ++ (b106_14_labels ++ b106_15_labels)))) 368054011536510265305588697950
  exact ((((b106_00_checked.append (c := 0) b106_01_checked (by decide +kernel)).append (c := 0) (b106_02_checked.append (c := 0) b106_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b106_04_checked.append (c := 0) b106_05_checked (by decide +kernel)).append (c := 0) (b106_06_checked.append (c := 0) b106_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 368054011536510265305588697950) (((b106_08_checked.append (c := 0) b106_09_checked (by decide +kernel)).append (c := 0) (b106_10_checked.append (c := 0) b106_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 368054011536510265305588697950) ((b106_12_checked.append (c := 0) b106_13_checked (by decide +kernel)).append (c := 368054011536510265305588697950) (b106_14_checked.append (c := 368054011536510265305588697950) b106_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b107_00_rows : List Row := [(row3 21 22 45), (row3 21 22 46), (row3 21 22 47), (row3 21 22 48), (row3 21 22 49), (row3 21 22 50), (row3 21 22 51), (row3 21 22 52), (row3 21 22 53), (row3 21 22 54), (row3 21 22 55), (row3 21 22 56), (row3 21 22 57), (row3 21 22 58), (row3 21 22 59), (row3 21 22 60)]

def b107_00_labels : List Row := [(row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_00_rows b107_00_labels 29570949389683955255512500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_00_rows b107_00_labels]
    decide +kernel

def b107_01_rows : List Row := [(row3 21 22 61), (row3 21 22 62), (row3 21 22 63), (row3 21 23 24), (row3 21 23 25), (row3 21 23 26), (row3 21 23 27), (row3 21 23 28), (row3 21 23 29), (row3 21 23 30), (row3 21 23 31), (row3 21 23 32), (row3 21 23 33), (row3 21 23 34), (row3 21 23 35), (row3 21 23 36)]

def b107_01_labels : List Row := [(row3 462 462 462), (row3 271 462 271), (row3 462 462 462), (row3 145 137 148), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 291 289), (row3 146 137 149), (row3 360 390 387), (row3 291 291 289), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_01_rows b107_01_labels 15380545440819201813657467730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_01_rows b107_01_labels]
    decide +kernel

def b107_02_rows : List Row := [(row3 21 23 37), (row3 21 23 38), (row3 21 23 39), (row3 21 23 40), (row3 21 23 41), (row3 21 23 42), (row3 21 23 43), (row3 21 23 44), (row3 21 23 45), (row3 21 23 46), (row3 21 23 47), (row3 21 23 48), (row3 21 23 49), (row3 21 23 50), (row3 21 23 51), (row3 21 23 52)]

def b107_02_labels : List Row := [(row3 462 234 234), (row3 291 291 289), (row3 184 178 184), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 266 266 265), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_02_rows b107_02_labels 101108601258179496579591120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_02_rows b107_02_labels]
    decide +kernel

def b107_03_rows : List Row := [(row3 21 23 53), (row3 21 23 54), (row3 21 23 55), (row3 21 23 56), (row3 21 23 57), (row3 21 23 58), (row3 21 23 59), (row3 21 23 60), (row3 21 23 61), (row3 21 23 62), (row3 21 23 63), (row3 21 24 25), (row3 21 24 26), (row3 21 24 27), (row3 21 24 28), (row3 21 24 29)]

def b107_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 266 266 265), (row3 263 263 462), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462)]

theorem b107_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_03_rows b107_03_labels 52120505377856186985138120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_03_rows b107_03_labels]
    decide +kernel

def b107_04_rows : List Row := [(row3 21 24 30), (row3 21 24 31), (row3 21 24 32), (row3 21 24 33), (row3 21 24 34), (row3 21 24 35), (row3 21 24 36), (row3 21 24 37), (row3 21 24 38), (row3 21 24 39), (row3 21 24 40), (row3 21 24 41), (row3 21 24 42), (row3 21 24 43), (row3 21 24 44), (row3 21 24 45)]

def b107_04_labels : List Row := [(row3 238 238 462), (row3 171 254 10), (row3 263 263 462), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_04_rows b107_04_labels 537968433329499944403343500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_04_rows b107_04_labels]
    decide +kernel

def b107_05_rows : List Row := [(row3 21 24 46), (row3 21 24 47), (row3 21 24 48), (row3 21 24 49), (row3 21 24 50), (row3 21 24 51), (row3 21 24 52), (row3 21 24 53), (row3 21 24 54), (row3 21 24 55), (row3 21 24 56), (row3 21 24 57), (row3 21 24 58), (row3 21 24 59), (row3 21 24 60), (row3 21 24 61)]

def b107_05_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_05_rows b107_05_labels 11285468089421881020000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_05_rows b107_05_labels]
    decide +kernel

def b107_06_rows : List Row := [(row3 21 24 62), (row3 21 24 63), (row3 21 25 26), (row3 21 25 27), (row3 21 25 28), (row3 21 25 29), (row3 21 25 30), (row3 21 25 31), (row3 21 25 32), (row3 21 25 33), (row3 21 25 34), (row3 21 25 35), (row3 21 25 36), (row3 21 25 37), (row3 21 25 38), (row3 21 25 39)]

def b107_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_06_rows b107_06_labels 262073403812044801116000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_06_rows b107_06_labels]
    decide +kernel

def b107_07_rows : List Row := [(row3 21 25 40), (row3 21 25 41), (row3 21 25 42), (row3 21 25 43), (row3 21 25 44), (row3 21 25 45), (row3 21 25 46), (row3 21 25 47), (row3 21 25 48), (row3 21 25 49), (row3 21 25 50), (row3 21 25 51), (row3 21 25 52), (row3 21 25 53), (row3 21 25 54), (row3 21 25 55)]

def b107_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_07_rows b107_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_07_rows b107_07_labels]
    decide +kernel

def b107_08_rows : List Row := [(row3 21 25 56), (row3 21 25 57), (row3 21 25 58), (row3 21 25 59), (row3 21 25 60), (row3 21 25 61), (row3 21 25 62), (row3 21 25 63), (row3 21 26 27), (row3 21 26 28), (row3 21 26 29), (row3 21 26 30), (row3 21 26 31), (row3 21 26 32), (row3 21 26 33), (row3 21 26 34)]

def b107_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_08_rows b107_08_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_08_rows b107_08_labels]
    decide +kernel

def b107_09_rows : List Row := [(row3 21 26 35), (row3 21 26 36), (row3 21 26 37), (row3 21 26 38), (row3 21 26 39), (row3 21 26 40), (row3 21 26 41), (row3 21 26 42), (row3 21 26 43), (row3 21 26 44), (row3 21 26 45), (row3 21 26 46), (row3 21 26 47), (row3 21 26 48), (row3 21 26 49), (row3 21 26 50)]

def b107_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_09_rows b107_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_09_rows b107_09_labels]
    decide +kernel

def b107_10_rows : List Row := [(row3 21 26 51), (row3 21 26 52), (row3 21 26 53), (row3 21 26 54), (row3 21 26 55), (row3 21 26 56), (row3 21 26 57), (row3 21 26 58), (row3 21 26 59), (row3 21 26 60), (row3 21 26 61), (row3 21 26 62), (row3 21 26 63), (row3 21 27 28), (row3 21 27 29), (row3 21 27 30)]

def b107_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_10_rows b107_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_10_rows b107_10_labels]
    decide +kernel

def b107_11_rows : List Row := [(row3 21 27 31), (row3 21 27 32), (row3 21 27 33), (row3 21 27 34), (row3 21 27 35), (row3 21 27 36), (row3 21 27 37), (row3 21 27 38), (row3 21 27 39), (row3 21 27 40), (row3 21 27 41), (row3 21 27 42), (row3 21 27 43), (row3 21 27 44), (row3 21 27 45), (row3 21 27 46)]

def b107_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_11_rows b107_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_11_rows b107_11_labels]
    decide +kernel

def b107_12_rows : List Row := [(row3 21 27 47), (row3 21 27 48), (row3 21 27 49), (row3 21 27 50), (row3 21 27 51), (row3 21 27 52), (row3 21 27 53), (row3 21 27 54), (row3 21 27 55), (row3 21 27 56), (row3 21 27 57), (row3 21 27 58), (row3 21 27 59), (row3 21 27 60), (row3 21 27 61), (row3 21 27 62)]

def b107_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_12_rows b107_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_12_rows b107_12_labels]
    decide +kernel

def b107_13_rows : List Row := [(row3 21 27 63), (row3 21 28 29), (row3 21 28 30), (row3 21 28 31), (row3 21 28 32), (row3 21 28 33), (row3 21 28 34), (row3 21 28 35), (row3 21 28 36), (row3 21 28 37), (row3 21 28 38), (row3 21 28 39), (row3 21 28 40), (row3 21 28 41), (row3 21 28 42), (row3 21 28 43)]

def b107_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_13_rows b107_13_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_13_rows b107_13_labels]
    decide +kernel

def b107_14_rows : List Row := [(row3 21 28 44), (row3 21 28 45), (row3 21 28 46), (row3 21 28 47), (row3 21 28 48), (row3 21 28 49), (row3 21 28 50), (row3 21 28 51), (row3 21 28 52), (row3 21 28 53), (row3 21 28 54), (row3 21 28 55), (row3 21 28 56), (row3 21 28 57), (row3 21 28 58), (row3 21 28 59)]

def b107_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_14_rows b107_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_14_rows b107_14_labels]
    decide +kernel

def b107_15_rows : List Row := [(row3 21 28 60), (row3 21 28 61), (row3 21 28 62), (row3 21 28 63), (row3 21 29 30), (row3 21 29 31), (row3 21 29 32), (row3 21 29 33), (row3 21 29 34), (row3 21 29 35), (row3 21 29 36), (row3 21 29 37), (row3 21 29 38), (row3 21 29 39), (row3 21 29 40), (row3 21 29 41)]

def b107_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b107_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b107_15_rows b107_15_labels 1684551660268238702136000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b107_15_rows b107_15_labels]
    decide +kernel

theorem checked107 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_107 QuarticIntegerComputationalData.ids64_107 16103295602914761622057694970 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b107_00_rows ++ b107_01_rows) ++ (b107_02_rows ++ b107_03_rows)) ++ ((b107_04_rows ++ b107_05_rows) ++ (b107_06_rows ++ b107_07_rows))) ++ (((b107_08_rows ++ b107_09_rows) ++ (b107_10_rows ++ b107_11_rows)) ++ ((b107_12_rows ++ b107_13_rows) ++ (b107_14_rows ++ b107_15_rows))))
    ((((b107_00_labels ++ b107_01_labels) ++ (b107_02_labels ++ b107_03_labels)) ++ ((b107_04_labels ++ b107_05_labels) ++ (b107_06_labels ++ b107_07_labels))) ++ (((b107_08_labels ++ b107_09_labels) ++ (b107_10_labels ++ b107_11_labels)) ++ ((b107_12_labels ++ b107_13_labels) ++ (b107_14_labels ++ b107_15_labels)))) 16103295602914761622057694970
  exact ((((b107_00_checked.append (c := 15410116390208885768912980230) b107_01_checked (by decide +kernel)).append (c := 15563345496844921452477709470) (b107_02_checked.append (c := 153229106636035683564729240) b107_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 16101587289046322863563188970) ((b107_04_checked.append (c := 537979718797589366284363500) b107_05_checked (by decide +kernel)).append (c := 538241792201401411085479500) (b107_06_checked.append (c := 262073403812044801116000) b107_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 16103295602914761622057694970) (((b107_08_checked.append (c := 7660100356903237725000) b107_09_checked (by decide +kernel)).append (c := 7660100356903237725000) (b107_10_checked.append (c := 0) b107_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1708313868438758494506000) ((b107_12_checked.append (c := 16102107813616554645000) b107_13_checked (by decide +kernel)).append (c := 1700653768081855256781000) (b107_14_checked.append (c := 1684551660268238702136000) b107_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b108_00_rows : List Row := [(row3 21 29 42), (row3 21 29 43), (row3 21 29 44), (row3 21 29 45), (row3 21 29 46), (row3 21 29 47), (row3 21 29 48), (row3 21 29 49), (row3 21 29 50), (row3 21 29 51), (row3 21 29 52), (row3 21 29 53), (row3 21 29 54), (row3 21 29 55), (row3 21 29 56), (row3 21 29 57)]

def b108_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_00_rows b108_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_00_rows b108_00_labels]
    decide +kernel

def b108_01_rows : List Row := [(row3 21 29 58), (row3 21 29 59), (row3 21 29 60), (row3 21 29 61), (row3 21 29 62), (row3 21 29 63), (row3 21 30 31), (row3 21 30 32), (row3 21 30 33), (row3 21 30 34), (row3 21 30 35), (row3 21 30 36), (row3 21 30 37), (row3 21 30 38), (row3 21 30 39), (row3 21 30 40)]

def b108_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_01_rows b108_01_labels 62325540591436534956165000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_01_rows b108_01_labels]
    decide +kernel

def b108_02_rows : List Row := [(row3 21 30 41), (row3 21 30 42), (row3 21 30 43), (row3 21 30 44), (row3 21 30 45), (row3 21 30 46), (row3 21 30 47), (row3 21 30 48), (row3 21 30 49), (row3 21 30 50), (row3 21 30 51), (row3 21 30 52), (row3 21 30 53), (row3 21 30 54), (row3 21 30 55), (row3 21 30 56)]

def b108_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_02_rows b108_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_02_rows b108_02_labels]
    decide +kernel

def b108_03_rows : List Row := [(row3 21 30 57), (row3 21 30 58), (row3 21 30 59), (row3 21 30 60), (row3 21 30 61), (row3 21 30 62), (row3 21 30 63), (row3 21 31 32), (row3 21 31 33), (row3 21 31 34), (row3 21 31 35), (row3 21 31 36), (row3 21 31 37), (row3 21 31 38), (row3 21 31 39), (row3 21 31 40)]

def b108_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 284 462 284), (row3 246 462 246)]

theorem b108_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_03_rows b108_03_labels 61214668581046198391478000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_03_rows b108_03_labels]
    decide +kernel

def b108_04_rows : List Row := [(row3 21 31 41), (row3 21 31 42), (row3 21 31 43), (row3 21 31 44), (row3 21 31 45), (row3 21 31 46), (row3 21 31 47), (row3 21 31 48), (row3 21 31 49), (row3 21 31 50), (row3 21 31 51), (row3 21 31 52), (row3 21 31 53), (row3 21 31 54), (row3 21 31 55), (row3 21 31 56)]

def b108_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462)]

theorem b108_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_04_rows b108_04_labels 298241849328832024416000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_04_rows b108_04_labels]
    decide +kernel

def b108_05_rows : List Row := [(row3 21 31 57), (row3 21 31 58), (row3 21 31 59), (row3 21 31 60), (row3 21 31 61), (row3 21 31 62), (row3 21 31 63), (row3 21 32 33), (row3 21 32 34), (row3 21 32 35), (row3 21 32 36), (row3 21 32 37), (row3 21 32 38), (row3 21 32 39), (row3 21 32 40), (row3 21 32 41)]

def b108_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_05_rows b108_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_05_rows b108_05_labels]
    decide +kernel

def b108_06_rows : List Row := [(row3 21 32 42), (row3 21 32 43), (row3 21 32 44), (row3 21 32 45), (row3 21 32 46), (row3 21 32 47), (row3 21 32 48), (row3 21 32 49), (row3 21 32 50), (row3 21 32 51), (row3 21 32 52), (row3 21 32 53), (row3 21 32 54), (row3 21 32 55), (row3 21 32 56), (row3 21 32 57)]

def b108_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_06_rows b108_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_06_rows b108_06_labels]
    decide +kernel

def b108_07_rows : List Row := [(row3 21 32 58), (row3 21 32 59), (row3 21 32 60), (row3 21 32 61), (row3 21 32 62), (row3 21 32 63), (row3 21 33 34), (row3 21 33 35), (row3 21 33 36), (row3 21 33 37), (row3 21 33 38), (row3 21 33 39), (row3 21 33 40), (row3 21 33 41), (row3 21 33 42), (row3 21 33 43)]

def b108_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_07_rows b108_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_07_rows b108_07_labels]
    decide +kernel

def b108_08_rows : List Row := [(row3 21 33 44), (row3 21 33 45), (row3 21 33 46), (row3 21 33 47), (row3 21 33 48), (row3 21 33 49), (row3 21 33 50), (row3 21 33 51), (row3 21 33 52), (row3 21 33 53), (row3 21 33 54), (row3 21 33 55), (row3 21 33 56), (row3 21 33 57), (row3 21 33 58), (row3 21 33 59)]

def b108_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_08_rows b108_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_08_rows b108_08_labels]
    decide +kernel

def b108_09_rows : List Row := [(row3 21 33 60), (row3 21 33 61), (row3 21 33 62), (row3 21 33 63), (row3 21 34 35), (row3 21 34 36), (row3 21 34 37), (row3 21 34 38), (row3 21 34 39), (row3 21 34 40), (row3 21 34 41), (row3 21 34 42), (row3 21 34 43), (row3 21 34 44), (row3 21 34 45), (row3 21 34 46)]

def b108_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_09_rows b108_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_09_rows b108_09_labels]
    decide +kernel

def b108_10_rows : List Row := [(row3 21 34 47), (row3 21 34 48), (row3 21 34 49), (row3 21 34 50), (row3 21 34 51), (row3 21 34 52), (row3 21 34 53), (row3 21 34 54), (row3 21 34 55), (row3 21 34 56), (row3 21 34 57), (row3 21 34 58), (row3 21 34 59), (row3 21 34 60), (row3 21 34 61), (row3 21 34 62)]

def b108_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_10_rows b108_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_10_rows b108_10_labels]
    decide +kernel

def b108_11_rows : List Row := [(row3 21 34 63), (row3 21 35 36), (row3 21 35 37), (row3 21 35 38), (row3 21 35 39), (row3 21 35 40), (row3 21 35 41), (row3 21 35 42), (row3 21 35 43), (row3 21 35 44), (row3 21 35 45), (row3 21 35 46), (row3 21 35 47), (row3 21 35 48), (row3 21 35 49), (row3 21 35 50)]

def b108_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_11_rows b108_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_11_rows b108_11_labels]
    decide +kernel

def b108_12_rows : List Row := [(row3 21 35 51), (row3 21 35 52), (row3 21 35 53), (row3 21 35 54), (row3 21 35 55), (row3 21 35 56), (row3 21 35 57), (row3 21 35 58), (row3 21 35 59), (row3 21 35 60), (row3 21 35 61), (row3 21 35 62), (row3 21 35 63), (row3 21 36 37), (row3 21 36 38), (row3 21 36 39)]

def b108_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_12_rows b108_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_12_rows b108_12_labels]
    decide +kernel

def b108_13_rows : List Row := [(row3 21 36 40), (row3 21 36 41), (row3 21 36 42), (row3 21 36 43), (row3 21 36 44), (row3 21 36 45), (row3 21 36 46), (row3 21 36 47), (row3 21 36 48), (row3 21 36 49), (row3 21 36 50), (row3 21 36 51), (row3 21 36 52), (row3 21 36 53), (row3 21 36 54), (row3 21 36 55)]

def b108_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_13_rows b108_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_13_rows b108_13_labels]
    decide +kernel

def b108_14_rows : List Row := [(row3 21 36 56), (row3 21 36 57), (row3 21 36 58), (row3 21 36 59), (row3 21 36 60), (row3 21 36 61), (row3 21 36 62), (row3 21 36 63), (row3 21 37 38), (row3 21 37 39), (row3 21 37 40), (row3 21 37 41), (row3 21 37 42), (row3 21 37 43), (row3 21 37 44), (row3 21 37 45)]

def b108_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b108_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_14_rows b108_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_14_rows b108_14_labels]
    decide +kernel

def b108_15_rows : List Row := [(row3 21 37 46), (row3 21 37 47), (row3 21 37 48), (row3 21 37 49), (row3 21 37 50), (row3 21 37 51), (row3 21 37 52), (row3 21 37 53), (row3 21 37 54), (row3 21 37 55), (row3 21 37 56), (row3 21 37 57), (row3 21 37 58), (row3 21 37 59), (row3 21 37 60), (row3 21 37 61)]

def b108_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462)]

theorem b108_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b108_15_rows b108_15_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b108_15_rows b108_15_labels]
    decide +kernel

theorem checked108 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_108 QuarticIntegerComputationalData.ids64_108 123842076389544084015354000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b108_00_rows ++ b108_01_rows) ++ (b108_02_rows ++ b108_03_rows)) ++ ((b108_04_rows ++ b108_05_rows) ++ (b108_06_rows ++ b108_07_rows))) ++ (((b108_08_rows ++ b108_09_rows) ++ (b108_10_rows ++ b108_11_rows)) ++ ((b108_12_rows ++ b108_13_rows) ++ (b108_14_rows ++ b108_15_rows))))
    ((((b108_00_labels ++ b108_01_labels) ++ (b108_02_labels ++ b108_03_labels)) ++ ((b108_04_labels ++ b108_05_labels) ++ (b108_06_labels ++ b108_07_labels))) ++ (((b108_08_labels ++ b108_09_labels) ++ (b108_10_labels ++ b108_11_labels)) ++ ((b108_12_labels ++ b108_13_labels) ++ (b108_14_labels ++ b108_15_labels)))) 123842076389544084015354000
  exact ((((b108_00_checked.append (c := 62325540591436534956165000) b108_01_checked (by decide +kernel)).append (c := 123540209172482733347643000) (b108_02_checked.append (c := 61214668581046198391478000) b108_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 123838451021811565372059000) ((b108_04_checked.append (c := 298241849328832024416000) b108_05_checked (by decide +kernel)).append (c := 298241849328832024416000) (b108_06_checked.append (c := 0) b108_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 123842076389544084015354000) (((b108_08_checked.append (c := 0) b108_09_checked (by decide +kernel)).append (c := 0) (b108_10_checked.append (c := 0) b108_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 3625367732518643295000) ((b108_12_checked.append (c := 0) b108_13_checked (by decide +kernel)).append (c := 3625367732518643295000) (b108_14_checked.append (c := 3625367732518643295000) b108_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b109_00_rows : List Row := [(row3 21 37 62), (row3 21 37 63), (row3 21 38 39), (row3 21 38 40), (row3 21 38 41), (row3 21 38 42), (row3 21 38 43), (row3 21 38 44), (row3 21 38 45), (row3 21 38 46), (row3 21 38 47), (row3 21 38 48), (row3 21 38 49), (row3 21 38 50), (row3 21 38 51), (row3 21 38 52)]

def b109_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_00_rows b109_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_00_rows b109_00_labels]
    decide +kernel

def b109_01_rows : List Row := [(row3 21 38 53), (row3 21 38 54), (row3 21 38 55), (row3 21 38 56), (row3 21 38 57), (row3 21 38 58), (row3 21 38 59), (row3 21 38 60), (row3 21 38 61), (row3 21 38 62), (row3 21 38 63), (row3 21 39 40), (row3 21 39 41), (row3 21 39 42), (row3 21 39 43), (row3 21 39 44)]

def b109_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_01_rows b109_01_labels 10173141782965611225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_01_rows b109_01_labels]
    decide +kernel

def b109_02_rows : List Row := [(row3 21 39 45), (row3 21 39 46), (row3 21 39 47), (row3 21 39 48), (row3 21 39 49), (row3 21 39 50), (row3 21 39 51), (row3 21 39 52), (row3 21 39 53), (row3 21 39 54), (row3 21 39 55), (row3 21 39 56), (row3 21 39 57), (row3 21 39 58), (row3 21 39 59), (row3 21 39 60)]

def b109_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_02_rows b109_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_02_rows b109_02_labels]
    decide +kernel

def b109_03_rows : List Row := [(row3 21 39 61), (row3 21 39 62), (row3 21 39 63), (row3 21 40 41), (row3 21 40 42), (row3 21 40 43), (row3 21 40 44), (row3 21 40 45), (row3 21 40 46), (row3 21 40 47), (row3 21 40 48), (row3 21 40 49), (row3 21 40 50), (row3 21 40 51), (row3 21 40 52), (row3 21 40 53)]

def b109_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_03_rows b109_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_03_rows b109_03_labels]
    decide +kernel

def b109_04_rows : List Row := [(row3 21 40 54), (row3 21 40 55), (row3 21 40 56), (row3 21 40 57), (row3 21 40 58), (row3 21 40 59), (row3 21 40 60), (row3 21 40 61), (row3 21 40 62), (row3 21 40 63), (row3 21 41 42), (row3 21 41 43), (row3 21 41 44), (row3 21 41 45), (row3 21 41 46), (row3 21 41 47)]

def b109_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_04_rows b109_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_04_rows b109_04_labels]
    decide +kernel

def b109_05_rows : List Row := [(row3 21 41 48), (row3 21 41 49), (row3 21 41 50), (row3 21 41 51), (row3 21 41 52), (row3 21 41 53), (row3 21 41 54), (row3 21 41 55), (row3 21 41 56), (row3 21 41 57), (row3 21 41 58), (row3 21 41 59), (row3 21 41 60), (row3 21 41 61), (row3 21 41 62), (row3 21 41 63)]

def b109_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_05_rows b109_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_05_rows b109_05_labels]
    decide +kernel

def b109_06_rows : List Row := [(row3 21 42 43), (row3 21 42 44), (row3 21 42 45), (row3 21 42 46), (row3 21 42 47), (row3 21 42 48), (row3 21 42 49), (row3 21 42 50), (row3 21 42 51), (row3 21 42 52), (row3 21 42 53), (row3 21 42 54), (row3 21 42 55), (row3 21 42 56), (row3 21 42 57), (row3 21 42 58)]

def b109_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_06_rows b109_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_06_rows b109_06_labels]
    decide +kernel

def b109_07_rows : List Row := [(row3 21 42 59), (row3 21 42 60), (row3 21 42 61), (row3 21 42 62), (row3 21 42 63), (row3 21 43 44), (row3 21 43 45), (row3 21 43 46), (row3 21 43 47), (row3 21 43 48), (row3 21 43 49), (row3 21 43 50), (row3 21 43 51), (row3 21 43 52), (row3 21 43 53), (row3 21 43 54)]

def b109_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_07_rows b109_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_07_rows b109_07_labels]
    decide +kernel

def b109_08_rows : List Row := [(row3 21 43 55), (row3 21 43 56), (row3 21 43 57), (row3 21 43 58), (row3 21 43 59), (row3 21 43 60), (row3 21 43 61), (row3 21 43 62), (row3 21 43 63), (row3 21 44 45), (row3 21 44 46), (row3 21 44 47), (row3 21 44 48), (row3 21 44 49), (row3 21 44 50), (row3 21 44 51)]

def b109_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_08_rows b109_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_08_rows b109_08_labels]
    decide +kernel

def b109_09_rows : List Row := [(row3 21 44 52), (row3 21 44 53), (row3 21 44 54), (row3 21 44 55), (row3 21 44 56), (row3 21 44 57), (row3 21 44 58), (row3 21 44 59), (row3 21 44 60), (row3 21 44 61), (row3 21 44 62), (row3 21 44 63), (row3 21 45 46), (row3 21 45 47), (row3 21 45 48), (row3 21 45 49)]

def b109_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_09_rows b109_09_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_09_rows b109_09_labels]
    decide +kernel

def b109_10_rows : List Row := [(row3 21 45 50), (row3 21 45 51), (row3 21 45 52), (row3 21 45 53), (row3 21 45 54), (row3 21 45 55), (row3 21 45 56), (row3 21 45 57), (row3 21 45 58), (row3 21 45 59), (row3 21 45 60), (row3 21 45 61), (row3 21 45 62), (row3 21 45 63), (row3 21 46 47), (row3 21 46 48)]

def b109_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_10_rows b109_10_labels 111645142702208927487000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_10_rows b109_10_labels]
    decide +kernel

def b109_11_rows : List Row := [(row3 21 46 49), (row3 21 46 50), (row3 21 46 51), (row3 21 46 52), (row3 21 46 53), (row3 21 46 54), (row3 21 46 55), (row3 21 46 56), (row3 21 46 57), (row3 21 46 58), (row3 21 46 59), (row3 21 46 60), (row3 21 46 61), (row3 21 46 62), (row3 21 46 63), (row3 21 47 48)]

def b109_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b109_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_11_rows b109_11_labels 269733504168948038841000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_11_rows b109_11_labels]
    decide +kernel

def b109_12_rows : List Row := [(row3 21 47 49), (row3 21 47 50), (row3 21 47 51), (row3 21 47 52), (row3 21 47 53), (row3 21 47 54), (row3 21 47 55), (row3 21 47 56), (row3 21 47 57), (row3 21 47 58), (row3 21 47 59), (row3 21 47 60), (row3 21 47 61), (row3 21 47 62), (row3 21 47 63), (row3 21 48 49)]

def b109_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462)]

theorem b109_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_12_rows b109_12_labels 25995303733821612075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_12_rows b109_12_labels]
    decide +kernel

def b109_13_rows : List Row := [(row3 21 48 50), (row3 21 48 51), (row3 21 48 52), (row3 21 48 53), (row3 21 48 54), (row3 21 48 55), (row3 21 48 56), (row3 21 48 57), (row3 21 48 58), (row3 21 48 59), (row3 21 48 60), (row3 21 48 61), (row3 21 48 62), (row3 21 48 63), (row3 21 49 50), (row3 21 49 51)]

def b109_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_13_rows b109_13_labels 38658314918891587455000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_13_rows b109_13_labels]
    decide +kernel

def b109_14_rows : List Row := [(row3 21 49 52), (row3 21 49 53), (row3 21 49 54), (row3 21 49 55), (row3 21 49 56), (row3 21 49 57), (row3 21 49 58), (row3 21 49 59), (row3 21 49 60), (row3 21 49 61), (row3 21 49 62), (row3 21 49 63), (row3 21 50 51), (row3 21 50 52), (row3 21 50 53), (row3 21 50 54)]

def b109_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_14_rows b109_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_14_rows b109_14_labels]
    decide +kernel

def b109_15_rows : List Row := [(row3 21 50 55), (row3 21 50 56), (row3 21 50 57), (row3 21 50 58), (row3 21 50 59), (row3 21 50 60), (row3 21 50 61), (row3 21 50 62), (row3 21 50 63), (row3 21 51 52), (row3 21 51 53), (row3 21 51 54), (row3 21 51 55), (row3 21 51 56), (row3 21 51 57), (row3 21 51 58)]

def b109_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b109_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b109_15_rows b109_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b109_15_rows b109_15_labels]
    decide +kernel

theorem checked109 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_109 QuarticIntegerComputationalData.ids64_109 463865507663739014808000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b109_00_rows ++ b109_01_rows) ++ (b109_02_rows ++ b109_03_rows)) ++ ((b109_04_rows ++ b109_05_rows) ++ (b109_06_rows ++ b109_07_rows))) ++ (((b109_08_rows ++ b109_09_rows) ++ (b109_10_rows ++ b109_11_rows)) ++ ((b109_12_rows ++ b109_13_rows) ++ (b109_14_rows ++ b109_15_rows))))
    ((((b109_00_labels ++ b109_01_labels) ++ (b109_02_labels ++ b109_03_labels)) ++ ((b109_04_labels ++ b109_05_labels) ++ (b109_06_labels ++ b109_07_labels))) ++ (((b109_08_labels ++ b109_09_labels) ++ (b109_10_labels ++ b109_11_labels)) ++ ((b109_12_labels ++ b109_13_labels) ++ (b109_14_labels ++ b109_15_labels)))) 463865507663739014808000
  exact ((((b109_00_checked.append (c := 10173141782965611225000) b109_01_checked (by decide +kernel)).append (c := 10173141782965611225000) (b109_02_checked.append (c := 0) b109_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 10173141782965611225000) ((b109_04_checked.append (c := 0) b109_05_checked (by decide +kernel)).append (c := 0) (b109_06_checked.append (c := 0) b109_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 463865507663739014808000) (((b109_08_checked.append (c := 7660100356903237725000) b109_09_checked (by decide +kernel)).append (c := 389038747228060204053000) (b109_10_checked.append (c := 381378646871156966328000) b109_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 453692365880773403583000) ((b109_12_checked.append (c := 64653618652713199530000) b109_13_checked (by decide +kernel)).append (c := 64653618652713199530000) (b109_14_checked.append (c := 0) b109_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b110_00_rows : List Row := [(row3 21 51 59), (row3 21 51 60), (row3 21 51 61), (row3 21 51 62), (row3 21 51 63), (row3 21 52 53), (row3 21 52 54), (row3 21 52 55), (row3 21 52 56), (row3 21 52 57), (row3 21 52 58), (row3 21 52 59), (row3 21 52 60), (row3 21 52 61), (row3 21 52 62), (row3 21 52 63)]

def b110_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 246 462 246), (row3 462 462 462)]

theorem b110_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_00_rows b110_00_labels 291665480204992777488000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_00_rows b110_00_labels]
    decide +kernel

def b110_01_rows : List Row := [(row3 21 53 54), (row3 21 53 55), (row3 21 53 56), (row3 21 53 57), (row3 21 53 58), (row3 21 53 59), (row3 21 53 60), (row3 21 53 61), (row3 21 53 62), (row3 21 53 63), (row3 21 54 55), (row3 21 54 56), (row3 21 54 57), (row3 21 54 58), (row3 21 54 59), (row3 21 54 60)]

def b110_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_01_rows b110_01_labels 20521764517958960554419000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_01_rows b110_01_labels]
    decide +kernel

def b110_02_rows : List Row := [(row3 21 54 61), (row3 21 54 62), (row3 21 54 63), (row3 21 55 56), (row3 21 55 57), (row3 21 55 58), (row3 21 55 59), (row3 21 55 60), (row3 21 55 61), (row3 21 55 62), (row3 21 55 63), (row3 21 56 57), (row3 21 56 58), (row3 21 56 59), (row3 21 56 60), (row3 21 56 61)]

def b110_02_labels : List Row := [(row3 236 236 462), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462)]

theorem b110_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_02_rows b110_02_labels 60652437763315748346717000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_02_rows b110_02_labels]
    decide +kernel

def b110_03_rows : List Row := [(row3 21 56 62), (row3 21 56 63), (row3 21 57 58), (row3 21 57 59), (row3 21 57 60), (row3 21 57 61), (row3 21 57 62), (row3 21 57 63), (row3 21 58 59), (row3 21 58 60), (row3 21 58 61), (row3 21 58 62), (row3 21 58 63), (row3 21 59 60), (row3 21 59 61), (row3 21 59 62)]

def b110_03_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 243 462 243)]

theorem b110_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_03_rows b110_03_labels 1792876258349050337673000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_03_rows b110_03_labels]
    decide +kernel

def b110_04_rows : List Row := [(row3 21 59 63), (row3 21 60 61), (row3 21 60 62), (row3 21 60 63), (row3 21 61 62), (row3 21 61 63), (row3 21 62 63), (row3 22 23 24), (row3 22 23 25), (row3 22 23 26), (row3 22 23 27), (row3 22 23 28), (row3 22 23 29), (row3 22 23 30), (row3 22 23 31), (row3 22 23 32)]

def b110_04_labels : List Row := [(row3 462 462 462), (row3 263 263 462), (row3 235 462 235), (row3 462 462 462), (row3 171 10 254), (row3 238 462 238), (row3 284 284 462), (row3 407 415 395), (row3 105 105 131), (row3 462 284 284), (row3 462 462 462), (row3 11 214 117), (row3 83 135 398), (row3 436 389 45), (row3 36 31 35), (row3 105 105 131)]

theorem b110_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_04_rows b110_04_labels 1236256250417454170424498616500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_04_rows b110_04_labels]
    decide +kernel

def b110_05_rows : List Row := [(row3 22 23 33), (row3 22 23 34), (row3 22 23 35), (row3 22 23 36), (row3 22 23 37), (row3 22 23 38), (row3 22 23 39), (row3 22 23 40), (row3 22 23 41), (row3 22 23 42), (row3 22 23 43), (row3 22 23 44), (row3 22 23 45), (row3 22 23 46), (row3 22 23 47), (row3 22 23 48)]

def b110_05_labels : List Row := [(row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 11 215 118), (row3 86 114 368), (row3 387 391 361), (row3 462 285 285), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 10 258 172), (row3 154 154 180), (row3 462 234 234)]

theorem b110_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_05_rows b110_05_labels 27439461695928662193195329400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_05_rows b110_05_labels]
    decide +kernel

def b110_06_rows : List Row := [(row3 22 23 49), (row3 22 23 50), (row3 22 23 51), (row3 22 23 52), (row3 22 23 53), (row3 22 23 54), (row3 22 23 55), (row3 22 23 56), (row3 22 23 57), (row3 22 23 58), (row3 22 23 59), (row3 22 23 60), (row3 22 23 61), (row3 22 23 62), (row3 22 23 63), (row3 22 24 25)]

def b110_06_labels : List Row := [(row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 272 272), (row3 462 307 307), (row3 462 228 228), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 10 260 173), (row3 152 150 177), (row3 180 154 154)]

theorem b110_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_06_rows b110_06_labels 19330170458026068163645614000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_06_rows b110_06_labels]
    decide +kernel

def b110_07_rows : List Row := [(row3 22 24 26), (row3 22 24 27), (row3 22 24 28), (row3 22 24 29), (row3 22 24 30), (row3 22 24 31), (row3 22 24 32), (row3 22 24 33), (row3 22 24 34), (row3 22 24 35), (row3 22 24 36), (row3 22 24 37), (row3 22 24 38), (row3 22 24 39), (row3 22 24 40), (row3 22 24 41)]

def b110_07_labels : List Row := [(row3 265 266 266), (row3 237 237 237), (row3 462 249 249), (row3 237 226 226), (row3 265 302 302), (row3 356 158 89), (row3 180 154 154), (row3 278 279 279), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 250 250), (row3 234 228 228), (row3 278 283 283), (row3 265 267 267), (row3 234 234 234)]

theorem b110_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_07_rows b110_07_labels 7389811753572000222637376400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_07_rows b110_07_labels]
    decide +kernel

def b110_08_rows : List Row := [(row3 22 24 42), (row3 22 24 43), (row3 22 24 44), (row3 22 24 45), (row3 22 24 46), (row3 22 24 47), (row3 22 24 48), (row3 22 24 49), (row3 22 24 50), (row3 22 24 51), (row3 22 24 52), (row3 22 24 53), (row3 22 24 54), (row3 22 24 55), (row3 22 24 56), (row3 22 24 57)]

def b110_08_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 234 234 234), (row3 237 235 235), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 462 270 270), (row3 462 235 235)]

theorem b110_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_08_rows b110_08_labels 50446078714843483047862500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_08_rows b110_08_labels]
    decide +kernel

def b110_09_rows : List Row := [(row3 22 24 58), (row3 22 24 59), (row3 22 24 60), (row3 22 24 61), (row3 22 24 62), (row3 22 24 63), (row3 22 25 26), (row3 22 25 27), (row3 22 25 28), (row3 22 25 29), (row3 22 25 30), (row3 22 25 31), (row3 22 25 32), (row3 22 25 33), (row3 22 25 34), (row3 22 25 35)]

def b110_09_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_09_rows b110_09_labels 6477632298369963680174100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_09_rows b110_09_labels]
    decide +kernel

def b110_10_rows : List Row := [(row3 22 25 36), (row3 22 25 37), (row3 22 25 38), (row3 22 25 39), (row3 22 25 40), (row3 22 25 41), (row3 22 25 42), (row3 22 25 43), (row3 22 25 44), (row3 22 25 45), (row3 22 25 46), (row3 22 25 47), (row3 22 25 48), (row3 22 25 49), (row3 22 25 50), (row3 22 25 51)]

def b110_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_10_rows b110_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_10_rows b110_10_labels]
    decide +kernel

def b110_11_rows : List Row := [(row3 22 25 52), (row3 22 25 53), (row3 22 25 54), (row3 22 25 55), (row3 22 25 56), (row3 22 25 57), (row3 22 25 58), (row3 22 25 59), (row3 22 25 60), (row3 22 25 61), (row3 22 25 62), (row3 22 25 63), (row3 22 26 27), (row3 22 26 28), (row3 22 26 29), (row3 22 26 30)]

def b110_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_11_rows b110_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_11_rows b110_11_labels]
    decide +kernel

def b110_12_rows : List Row := [(row3 22 26 31), (row3 22 26 32), (row3 22 26 33), (row3 22 26 34), (row3 22 26 35), (row3 22 26 36), (row3 22 26 37), (row3 22 26 38), (row3 22 26 39), (row3 22 26 40), (row3 22 26 41), (row3 22 26 42), (row3 22 26 43), (row3 22 26 44), (row3 22 26 45), (row3 22 26 46)]

def b110_12_labels : List Row := [(row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_12_rows b110_12_labels 258010076114267927688000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_12_rows b110_12_labels]
    decide +kernel

def b110_13_rows : List Row := [(row3 22 26 47), (row3 22 26 48), (row3 22 26 49), (row3 22 26 50), (row3 22 26 51), (row3 22 26 52), (row3 22 26 53), (row3 22 26 54), (row3 22 26 55), (row3 22 26 56), (row3 22 26 57), (row3 22 26 58), (row3 22 26 59), (row3 22 26 60), (row3 22 26 61), (row3 22 26 62)]

def b110_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_13_rows b110_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_13_rows b110_13_labels]
    decide +kernel

def b110_14_rows : List Row := [(row3 22 26 63), (row3 22 27 28), (row3 22 27 29), (row3 22 27 30), (row3 22 27 31), (row3 22 27 32), (row3 22 27 33), (row3 22 27 34), (row3 22 27 35), (row3 22 27 36), (row3 22 27 37), (row3 22 27 38), (row3 22 27 39), (row3 22 27 40), (row3 22 27 41), (row3 22 27 42)]

def b110_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_14_rows b110_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_14_rows b110_14_labels]
    decide +kernel

def b110_15_rows : List Row := [(row3 22 27 43), (row3 22 27 44), (row3 22 27 45), (row3 22 27 46), (row3 22 27 47), (row3 22 27 48), (row3 22 27 49), (row3 22 27 50), (row3 22 27 51), (row3 22 27 52), (row3 22 27 53), (row3 22 27 54), (row3 22 27 55), (row3 22 27 56), (row3 22 27 57), (row3 22 27 58)]

def b110_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b110_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b110_15_rows b110_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b110_15_rows b110_15_labels]
    decide +kernel

theorem checked110 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_110 QuarticIntegerComputationalData.ids64_110 1290556134790090057470648957900 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b110_00_rows ++ b110_01_rows) ++ (b110_02_rows ++ b110_03_rows)) ++ ((b110_04_rows ++ b110_05_rows) ++ (b110_06_rows ++ b110_07_rows))) ++ (((b110_08_rows ++ b110_09_rows) ++ (b110_10_rows ++ b110_11_rows)) ++ ((b110_12_rows ++ b110_13_rows) ++ (b110_14_rows ++ b110_15_rows))))
    ((((b110_00_labels ++ b110_01_labels) ++ (b110_02_labels ++ b110_03_labels)) ++ ((b110_04_labels ++ b110_05_labels) ++ (b110_06_labels ++ b110_07_labels))) ++ (((b110_08_labels ++ b110_09_labels) ++ (b110_10_labels ++ b110_11_labels)) ++ ((b110_12_labels ++ b110_13_labels) ++ (b110_14_labels ++ b110_15_labels)))) 1290556134790090057470648957900
  exact ((((b110_00_checked.append (c := 20813429998163953331907000) b110_01_checked (by decide +kernel)).append (c := 83258744019828752016297000) (b110_02_checked.append (c := 62445314021664798684390000) b110_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1290498953069000729755993233300) ((b110_04_checked.append (c := 1263695712113382832617693945900) b110_05_checked (by decide +kernel)).append (c := 1290415694324980901003976936300) (b110_06_checked.append (c := 26719982211598068386282990400) b110_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1290556134790090057470648957900) (((b110_08_checked.append (c := 56923711013213446728036600) b110_09_checked (by decide +kernel)).append (c := 56923711013213446728036600) (b110_10_checked.append (c := 0) b110_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 57181721089327714655724600) ((b110_12_checked.append (c := 258010076114267927688000) b110_13_checked (by decide +kernel)).append (c := 258010076114267927688000) (b110_14_checked.append (c := 0) b110_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b111_00_rows : List Row := [(row3 22 27 59), (row3 22 27 60), (row3 22 27 61), (row3 22 27 62), (row3 22 27 63), (row3 22 28 29), (row3 22 28 30), (row3 22 28 31), (row3 22 28 32), (row3 22 28 33), (row3 22 28 34), (row3 22 28 35), (row3 22 28 36), (row3 22 28 37), (row3 22 28 38), (row3 22 28 39)]

def b111_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 462 293 293), (row3 236 225 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 234 234), (row3 462 248 248)]

theorem b111_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_00_rows b111_00_labels 98852617708356462585106500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_00_rows b111_00_labels]
    decide +kernel

def b111_01_rows : List Row := [(row3 22 28 40), (row3 22 28 41), (row3 22 28 42), (row3 22 28 43), (row3 22 28 44), (row3 22 28 45), (row3 22 28 46), (row3 22 28 47), (row3 22 28 48), (row3 22 28 49), (row3 22 28 50), (row3 22 28 51), (row3 22 28 52), (row3 22 28 53), (row3 22 28 54), (row3 22 28 55)]

def b111_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_01_rows b111_01_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_01_rows b111_01_labels]
    decide +kernel

def b111_02_rows : List Row := [(row3 22 28 56), (row3 22 28 57), (row3 22 28 58), (row3 22 28 59), (row3 22 28 60), (row3 22 28 61), (row3 22 28 62), (row3 22 28 63), (row3 22 29 30), (row3 22 29 31), (row3 22 29 32), (row3 22 29 33), (row3 22 29 34), (row3 22 29 35), (row3 22 29 36), (row3 22 29 37)]

def b111_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 139 139), (row3 273 304 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228)]

theorem b111_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_02_rows b111_02_labels 1603249378459201835674933500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_02_rows b111_02_labels]
    decide +kernel

def b111_03_rows : List Row := [(row3 22 29 38), (row3 22 29 39), (row3 22 29 40), (row3 22 29 41), (row3 22 29 42), (row3 22 29 43), (row3 22 29 44), (row3 22 29 45), (row3 22 29 46), (row3 22 29 47), (row3 22 29 48), (row3 22 29 49), (row3 22 29 50), (row3 22 29 51), (row3 22 29 52), (row3 22 29 53)]

def b111_03_labels : List Row := [(row3 462 278 278), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_03_rows b111_03_labels 12774737108138468557651200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_03_rows b111_03_labels]
    decide +kernel

def b111_04_rows : List Row := [(row3 22 29 54), (row3 22 29 55), (row3 22 29 56), (row3 22 29 57), (row3 22 29 58), (row3 22 29 59), (row3 22 29 60), (row3 22 29 61), (row3 22 29 62), (row3 22 29 63), (row3 22 30 31), (row3 22 30 32), (row3 22 30 33), (row3 22 30 34), (row3 22 30 35), (row3 22 30 36)]

def b111_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 163 124 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_04_rows b111_04_labels 2610109300627494009883980000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_04_rows b111_04_labels]
    decide +kernel

def b111_05_rows : List Row := [(row3 22 30 37), (row3 22 30 38), (row3 22 30 39), (row3 22 30 40), (row3 22 30 41), (row3 22 30 42), (row3 22 30 43), (row3 22 30 44), (row3 22 30 45), (row3 22 30 46), (row3 22 30 47), (row3 22 30 48), (row3 22 30 49), (row3 22 30 50), (row3 22 30 51), (row3 22 30 52)]

def b111_05_labels : List Row := [(row3 462 293 293), (row3 462 180 180), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_05_rows b111_05_labels 976213502703788641325113500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_05_rows b111_05_labels]
    decide +kernel

def b111_06_rows : List Row := [(row3 22 30 53), (row3 22 30 54), (row3 22 30 55), (row3 22 30 56), (row3 22 30 57), (row3 22 30 58), (row3 22 30 59), (row3 22 30 60), (row3 22 30 61), (row3 22 30 62), (row3 22 30 63), (row3 22 31 32), (row3 22 31 33), (row3 22 31 34), (row3 22 31 35), (row3 22 31 36)]

def b111_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 270 270), (row3 462 462 462), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_06_rows b111_06_labels 64644601413959491792746600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_06_rows b111_06_labels]
    decide +kernel

def b111_07_rows : List Row := [(row3 22 31 37), (row3 22 31 38), (row3 22 31 39), (row3 22 31 40), (row3 22 31 41), (row3 22 31 42), (row3 22 31 43), (row3 22 31 44), (row3 22 31 45), (row3 22 31 46), (row3 22 31 47), (row3 22 31 48), (row3 22 31 49), (row3 22 31 50), (row3 22 31 51), (row3 22 31 52)]

def b111_07_labels : List Row := [(row3 232 228 223), (row3 288 278 300), (row3 163 228 160), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 235 228), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_07_rows b111_07_labels 770169407213205822190233600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_07_rows b111_07_labels]
    decide +kernel

def b111_08_rows : List Row := [(row3 22 31 53), (row3 22 31 54), (row3 22 31 55), (row3 22 31 56), (row3 22 31 57), (row3 22 31 58), (row3 22 31 59), (row3 22 31 60), (row3 22 31 61), (row3 22 31 62), (row3 22 31 63), (row3 22 32 33), (row3 22 32 34), (row3 22 32 35), (row3 22 32 36), (row3 22 32 37)]

def b111_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_08_rows b111_08_labels 1002572601206450985900000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_08_rows b111_08_labels]
    decide +kernel

def b111_09_rows : List Row := [(row3 22 32 38), (row3 22 32 39), (row3 22 32 40), (row3 22 32 41), (row3 22 32 42), (row3 22 32 43), (row3 22 32 44), (row3 22 32 45), (row3 22 32 46), (row3 22 32 47), (row3 22 32 48), (row3 22 32 49), (row3 22 32 50), (row3 22 32 51), (row3 22 32 52), (row3 22 32 53)]

def b111_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_09_rows b111_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_09_rows b111_09_labels]
    decide +kernel

def b111_10_rows : List Row := [(row3 22 32 54), (row3 22 32 55), (row3 22 32 56), (row3 22 32 57), (row3 22 32 58), (row3 22 32 59), (row3 22 32 60), (row3 22 32 61), (row3 22 32 62), (row3 22 32 63), (row3 22 33 34), (row3 22 33 35), (row3 22 33 36), (row3 22 33 37), (row3 22 33 38), (row3 22 33 39)]

def b111_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_10_rows b111_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_10_rows b111_10_labels]
    decide +kernel

def b111_11_rows : List Row := [(row3 22 33 40), (row3 22 33 41), (row3 22 33 42), (row3 22 33 43), (row3 22 33 44), (row3 22 33 45), (row3 22 33 46), (row3 22 33 47), (row3 22 33 48), (row3 22 33 49), (row3 22 33 50), (row3 22 33 51), (row3 22 33 52), (row3 22 33 53), (row3 22 33 54), (row3 22 33 55)]

def b111_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_11_rows b111_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_11_rows b111_11_labels]
    decide +kernel

def b111_12_rows : List Row := [(row3 22 33 56), (row3 22 33 57), (row3 22 33 58), (row3 22 33 59), (row3 22 33 60), (row3 22 33 61), (row3 22 33 62), (row3 22 33 63), (row3 22 34 35), (row3 22 34 36), (row3 22 34 37), (row3 22 34 38), (row3 22 34 39), (row3 22 34 40), (row3 22 34 41), (row3 22 34 42)]

def b111_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_12_rows b111_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_12_rows b111_12_labels]
    decide +kernel

def b111_13_rows : List Row := [(row3 22 34 43), (row3 22 34 44), (row3 22 34 45), (row3 22 34 46), (row3 22 34 47), (row3 22 34 48), (row3 22 34 49), (row3 22 34 50), (row3 22 34 51), (row3 22 34 52), (row3 22 34 53), (row3 22 34 54), (row3 22 34 55), (row3 22 34 56), (row3 22 34 57), (row3 22 34 58)]

def b111_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_13_rows b111_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_13_rows b111_13_labels]
    decide +kernel

def b111_14_rows : List Row := [(row3 22 34 59), (row3 22 34 60), (row3 22 34 61), (row3 22 34 62), (row3 22 34 63), (row3 22 35 36), (row3 22 35 37), (row3 22 35 38), (row3 22 35 39), (row3 22 35 40), (row3 22 35 41), (row3 22 35 42), (row3 22 35 43), (row3 22 35 44), (row3 22 35 45), (row3 22 35 46)]

def b111_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_14_rows b111_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_14_rows b111_14_labels]
    decide +kernel

def b111_15_rows : List Row := [(row3 22 35 47), (row3 22 35 48), (row3 22 35 49), (row3 22 35 50), (row3 22 35 51), (row3 22 35 52), (row3 22 35 53), (row3 22 35 54), (row3 22 35 55), (row3 22 35 56), (row3 22 35 57), (row3 22 35 58), (row3 22 35 59), (row3 22 35 60), (row3 22 35 61), (row3 22 35 62)]

def b111_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b111_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b111_15_rows b111_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b111_15_rows b111_15_labels]
    decide +kernel

theorem checked111 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_111 QuarticIntegerComputationalData.ids64_111 6137027607985886537852252400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b111_00_rows ++ b111_01_rows) ++ (b111_02_rows ++ b111_03_rows)) ++ ((b111_04_rows ++ b111_05_rows) ++ (b111_06_rows ++ b111_07_rows))) ++ (((b111_08_rows ++ b111_09_rows) ++ (b111_10_rows ++ b111_11_rows)) ++ ((b111_12_rows ++ b111_13_rows) ++ (b111_14_rows ++ b111_15_rows))))
    ((((b111_00_labels ++ b111_01_labels) ++ (b111_02_labels ++ b111_03_labels)) ++ ((b111_04_labels ++ b111_05_labels) ++ (b111_06_labels ++ b111_07_labels))) ++ (((b111_08_labels ++ b111_09_labels) ++ (b111_10_labels ++ b111_11_labels)) ++ ((b111_12_labels ++ b111_13_labels) ++ (b111_14_labels ++ b111_15_labels)))) 6137027607985886537852252400
  exact ((((b111_00_checked.append (c := 98864107858891817441694000) b111_01_checked (by decide +kernel)).append (c := 1714888223426232121674278700) (b111_02_checked.append (c := 1616024115567340304232584700) b111_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6136025035384680086866352400) ((b111_04_checked.append (c := 3586322803331282651209093500) b111_05_checked (by decide +kernel)).append (c := 4421136811958447965192073700) (b111_06_checked.append (c := 834814008627165313982980200) b111_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 6137027607985886537852252400) (((b111_08_checked.append (c := 1002572601206450985900000) b111_09_checked (by decide +kernel)).append (c := 1002572601206450985900000) (b111_10_checked.append (c := 0) b111_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1002572601206450985900000) ((b111_12_checked.append (c := 0) b111_13_checked (by decide +kernel)).append (c := 0) (b111_14_checked.append (c := 0) b111_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b112_00_rows : List Row := [(row3 22 35 63), (row3 22 36 37), (row3 22 36 38), (row3 22 36 39), (row3 22 36 40), (row3 22 36 41), (row3 22 36 42), (row3 22 36 43), (row3 22 36 44), (row3 22 36 45), (row3 22 36 46), (row3 22 36 47), (row3 22 36 48), (row3 22 36 49), (row3 22 36 50), (row3 22 36 51)]

def b112_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_00_rows b112_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_00_rows b112_00_labels]
    decide +kernel

def b112_01_rows : List Row := [(row3 22 36 52), (row3 22 36 53), (row3 22 36 54), (row3 22 36 55), (row3 22 36 56), (row3 22 36 57), (row3 22 36 58), (row3 22 36 59), (row3 22 36 60), (row3 22 36 61), (row3 22 36 62), (row3 22 36 63), (row3 22 37 38), (row3 22 37 39), (row3 22 37 40), (row3 22 37 41)]

def b112_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462)]

theorem b112_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_01_rows b112_01_labels 2584814962780695434386500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_01_rows b112_01_labels]
    decide +kernel

def b112_02_rows : List Row := [(row3 22 37 42), (row3 22 37 43), (row3 22 37 44), (row3 22 37 45), (row3 22 37 46), (row3 22 37 47), (row3 22 37 48), (row3 22 37 49), (row3 22 37 50), (row3 22 37 51), (row3 22 37 52), (row3 22 37 53), (row3 22 37 54), (row3 22 37 55), (row3 22 37 56), (row3 22 37 57)]

def b112_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_02_rows b112_02_labels 24153161720424831967500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_02_rows b112_02_labels]
    decide +kernel

def b112_03_rows : List Row := [(row3 22 37 58), (row3 22 37 59), (row3 22 37 60), (row3 22 37 61), (row3 22 37 62), (row3 22 37 63), (row3 22 38 39), (row3 22 38 40), (row3 22 38 41), (row3 22 38 42), (row3 22 38 43), (row3 22 38 44), (row3 22 38 45), (row3 22 38 46), (row3 22 38 47), (row3 22 38 48)]

def b112_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 462 462 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462)]

theorem b112_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_03_rows b112_03_labels 3386094167537178115414500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_03_rows b112_03_labels]
    decide +kernel

def b112_04_rows : List Row := [(row3 22 38 49), (row3 22 38 50), (row3 22 38 51), (row3 22 38 52), (row3 22 38 53), (row3 22 38 54), (row3 22 38 55), (row3 22 38 56), (row3 22 38 57), (row3 22 38 58), (row3 22 38 59), (row3 22 38 60), (row3 22 38 61), (row3 22 38 62), (row3 22 38 63), (row3 22 39 40)]

def b112_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 235 235), (row3 462 462 462), (row3 462 462 462)]

theorem b112_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_04_rows b112_04_labels 430008164825677097310000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_04_rows b112_04_labels]
    decide +kernel

def b112_05_rows : List Row := [(row3 22 39 41), (row3 22 39 42), (row3 22 39 43), (row3 22 39 44), (row3 22 39 45), (row3 22 39 46), (row3 22 39 47), (row3 22 39 48), (row3 22 39 49), (row3 22 39 50), (row3 22 39 51), (row3 22 39 52), (row3 22 39 53), (row3 22 39 54), (row3 22 39 55), (row3 22 39 56)]

def b112_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_05_rows b112_05_labels 24153161720424831967500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_05_rows b112_05_labels]
    decide +kernel

def b112_06_rows : List Row := [(row3 22 39 57), (row3 22 39 58), (row3 22 39 59), (row3 22 39 60), (row3 22 39 61), (row3 22 39 62), (row3 22 39 63), (row3 22 40 41), (row3 22 40 42), (row3 22 40 43), (row3 22 40 44), (row3 22 40 45), (row3 22 40 46), (row3 22 40 47), (row3 22 40 48), (row3 22 40 49)]

def b112_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244)]

theorem b112_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_06_rows b112_06_labels 1284448879337825288538000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_06_rows b112_06_labels]
    decide +kernel

def b112_07_rows : List Row := [(row3 22 40 50), (row3 22 40 51), (row3 22 40 52), (row3 22 40 53), (row3 22 40 54), (row3 22 40 55), (row3 22 40 56), (row3 22 40 57), (row3 22 40 58), (row3 22 40 59), (row3 22 40 60), (row3 22 40 61), (row3 22 40 62), (row3 22 40 63), (row3 22 41 42), (row3 22 41 43)]

def b112_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 269 269), (row3 462 235 235), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 232 235 228), (row3 462 462 462), (row3 462 462 462)]

theorem b112_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_07_rows b112_07_labels 31958251328940913800040500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_07_rows b112_07_labels]
    decide +kernel

def b112_08_rows : List Row := [(row3 22 41 44), (row3 22 41 45), (row3 22 41 46), (row3 22 41 47), (row3 22 41 48), (row3 22 41 49), (row3 22 41 50), (row3 22 41 51), (row3 22 41 52), (row3 22 41 53), (row3 22 41 54), (row3 22 41 55), (row3 22 41 56), (row3 22 41 57), (row3 22 41 58), (row3 22 41 59)]

def b112_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_08_rows b112_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_08_rows b112_08_labels]
    decide +kernel

def b112_09_rows : List Row := [(row3 22 41 60), (row3 22 41 61), (row3 22 41 62), (row3 22 41 63), (row3 22 42 43), (row3 22 42 44), (row3 22 42 45), (row3 22 42 46), (row3 22 42 47), (row3 22 42 48), (row3 22 42 49), (row3 22 42 50), (row3 22 42 51), (row3 22 42 52), (row3 22 42 53), (row3 22 42 54)]

def b112_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_09_rows b112_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_09_rows b112_09_labels]
    decide +kernel

def b112_10_rows : List Row := [(row3 22 42 55), (row3 22 42 56), (row3 22 42 57), (row3 22 42 58), (row3 22 42 59), (row3 22 42 60), (row3 22 42 61), (row3 22 42 62), (row3 22 42 63), (row3 22 43 44), (row3 22 43 45), (row3 22 43 46), (row3 22 43 47), (row3 22 43 48), (row3 22 43 49), (row3 22 43 50)]

def b112_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_10_rows b112_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_10_rows b112_10_labels]
    decide +kernel

def b112_11_rows : List Row := [(row3 22 43 51), (row3 22 43 52), (row3 22 43 53), (row3 22 43 54), (row3 22 43 55), (row3 22 43 56), (row3 22 43 57), (row3 22 43 58), (row3 22 43 59), (row3 22 43 60), (row3 22 43 61), (row3 22 43 62), (row3 22 43 63), (row3 22 44 45), (row3 22 44 46), (row3 22 44 47)]

def b112_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_11_rows b112_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_11_rows b112_11_labels]
    decide +kernel

def b112_12_rows : List Row := [(row3 22 44 48), (row3 22 44 49), (row3 22 44 50), (row3 22 44 51), (row3 22 44 52), (row3 22 44 53), (row3 22 44 54), (row3 22 44 55), (row3 22 44 56), (row3 22 44 57), (row3 22 44 58), (row3 22 44 59), (row3 22 44 60), (row3 22 44 61), (row3 22 44 62), (row3 22 44 63)]

def b112_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462)]

theorem b112_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_12_rows b112_12_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_12_rows b112_12_labels]
    decide +kernel

def b112_13_rows : List Row := [(row3 22 45 46), (row3 22 45 47), (row3 22 45 48), (row3 22 45 49), (row3 22 45 50), (row3 22 45 51), (row3 22 45 52), (row3 22 45 53), (row3 22 45 54), (row3 22 45 55), (row3 22 45 56), (row3 22 45 57), (row3 22 45 58), (row3 22 45 59), (row3 22 45 60), (row3 22 45 61)]

def b112_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_13_rows b112_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_13_rows b112_13_labels]
    decide +kernel

def b112_14_rows : List Row := [(row3 22 45 62), (row3 22 45 63), (row3 22 46 47), (row3 22 46 48), (row3 22 46 49), (row3 22 46 50), (row3 22 46 51), (row3 22 46 52), (row3 22 46 53), (row3 22 46 54), (row3 22 46 55), (row3 22 46 56), (row3 22 46 57), (row3 22 46 58), (row3 22 46 59), (row3 22 46 60)]

def b112_14_labels : List Row := [(row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_14_rows b112_14_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_14_rows b112_14_labels]
    decide +kernel

def b112_15_rows : List Row := [(row3 22 46 61), (row3 22 46 62), (row3 22 46 63), (row3 22 47 48), (row3 22 47 49), (row3 22 47 50), (row3 22 47 51), (row3 22 47 52), (row3 22 47 53), (row3 22 47 54), (row3 22 47 55), (row3 22 47 56), (row3 22 47 57), (row3 22 47 58), (row3 22 47 59), (row3 22 47 60)]

def b112_15_labels : List Row := [(row3 462 462 462), (row3 265 267 267), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b112_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b112_15_rows b112_15_labels 4341068780563739173122900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b112_15_rows b112_15_labels]
    decide +kernel

theorem checked112 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_112 QuarticIntegerComputationalData.ids64_112 44368857832212118247634900 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b112_00_rows ++ b112_01_rows) ++ (b112_02_rows ++ b112_03_rows)) ++ ((b112_04_rows ++ b112_05_rows) ++ (b112_06_rows ++ b112_07_rows))) ++ (((b112_08_rows ++ b112_09_rows) ++ (b112_10_rows ++ b112_11_rows)) ++ ((b112_12_rows ++ b112_13_rows) ++ (b112_14_rows ++ b112_15_rows))))
    ((((b112_00_labels ++ b112_01_labels) ++ (b112_02_labels ++ b112_03_labels)) ++ ((b112_04_labels ++ b112_05_labels) ++ (b112_06_labels ++ b112_07_labels))) ++ (((b112_08_labels ++ b112_09_labels) ++ (b112_10_labels ++ b112_11_labels)) ++ ((b112_12_labels ++ b112_13_labels) ++ (b112_14_labels ++ b112_15_labels)))) 44368857832212118247634900
  exact ((((b112_00_checked.append (c := 2584814962780695434386500) b112_01_checked (by decide +kernel)).append (c := 5995062292038298381768500) (b112_02_checked.append (c := 3410247329257602947382000) b112_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 39691923826863139399624500) ((b112_04_checked.append (c := 454161326546101929277500) b112_05_checked (by decide +kernel)).append (c := 33696861534824841017856000) (b112_06_checked.append (c := 33242700208278739088578500) b112_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 44368857832212118247634900) (((b112_08_checked.append (c := 0) b112_09_checked (by decide +kernel)).append (c := 0) (b112_10_checked.append (c := 0) b112_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4676934005348978848010400) ((b112_12_checked.append (c := 11490150535354856587500) b112_13_checked (by decide +kernel)).append (c := 4676934005348978848010400) (b112_14_checked.append (c := 4665443854813623991422900) b112_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
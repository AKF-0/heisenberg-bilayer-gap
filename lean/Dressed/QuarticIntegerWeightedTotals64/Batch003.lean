import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch002
import Dressed.QuarticIntegerComputationalData64.Batch003


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b025_00_rows : List Row := [(row3 4 23 42), (row3 4 23 43), (row3 4 23 44), (row3 4 23 45), (row3 4 23 46), (row3 4 23 47), (row3 4 23 48), (row3 4 23 49), (row3 4 23 50), (row3 4 23 51), (row3 4 23 52), (row3 4 23 53), (row3 4 23 54), (row3 4 23 55), (row3 4 23 56), (row3 4 23 57)]

def b025_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 269 269), (row3 462 235 235)]

theorem b025_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_00_rows b025_00_labels 30301223173986746115067500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_00_rows b025_00_labels]
    decide +kernel

def b025_01_rows : List Row := [(row3 4 23 58), (row3 4 23 59), (row3 4 23 60), (row3 4 23 61), (row3 4 23 62), (row3 4 23 63), (row3 4 24 25), (row3 4 24 26), (row3 4 24 27), (row3 4 24 28), (row3 4 24 29), (row3 4 24 30), (row3 4 24 31), (row3 4 24 32), (row3 4 24 33), (row3 4 24 34)]

def b025_01_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 236 235 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_01_rows b025_01_labels 741641072408183893590000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_01_rows b025_01_labels]
    decide +kernel

def b025_02_rows : List Row := [(row3 4 24 35), (row3 4 24 36), (row3 4 24 37), (row3 4 24 38), (row3 4 24 39), (row3 4 24 40), (row3 4 24 41), (row3 4 24 42), (row3 4 24 43), (row3 4 24 44), (row3 4 24 45), (row3 4 24 46), (row3 4 24 47), (row3 4 24 48), (row3 4 24 49), (row3 4 24 50)]

def b025_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462)]

theorem b025_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_02_rows b025_02_labels 47211132815873411466000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_02_rows b025_02_labels]
    decide +kernel

def b025_03_rows : List Row := [(row3 4 24 51), (row3 4 24 52), (row3 4 24 53), (row3 4 24 54), (row3 4 24 55), (row3 4 24 56), (row3 4 24 57), (row3 4 24 58), (row3 4 24 59), (row3 4 24 60), (row3 4 24 61), (row3 4 24 62), (row3 4 24 63), (row3 4 25 26), (row3 4 25 27), (row3 4 25 28)]

def b025_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 257 257), (row3 462 238 238), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_03_rows b025_03_labels 10128326037907332626913000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_03_rows b025_03_labels]
    decide +kernel

def b025_04_rows : List Row := [(row3 4 25 29), (row3 4 25 30), (row3 4 25 31), (row3 4 25 32), (row3 4 25 33), (row3 4 25 34), (row3 4 25 35), (row3 4 25 36), (row3 4 25 37), (row3 4 25 38), (row3 4 25 39), (row3 4 25 40), (row3 4 25 41), (row3 4 25 42), (row3 4 25 43), (row3 4 25 44)]

def b025_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_04_rows b025_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_04_rows b025_04_labels]
    decide +kernel

def b025_05_rows : List Row := [(row3 4 25 45), (row3 4 25 46), (row3 4 25 47), (row3 4 25 48), (row3 4 25 49), (row3 4 25 50), (row3 4 25 51), (row3 4 25 52), (row3 4 25 53), (row3 4 25 54), (row3 4 25 55), (row3 4 25 56), (row3 4 25 57), (row3 4 25 58), (row3 4 25 59), (row3 4 25 60)]

def b025_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_05_rows b025_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_05_rows b025_05_labels]
    decide +kernel

def b025_06_rows : List Row := [(row3 4 25 61), (row3 4 25 62), (row3 4 25 63), (row3 4 26 27), (row3 4 26 28), (row3 4 26 29), (row3 4 26 30), (row3 4 26 31), (row3 4 26 32), (row3 4 26 33), (row3 4 26 34), (row3 4 26 35), (row3 4 26 36), (row3 4 26 37), (row3 4 26 38), (row3 4 26 39)]

def b025_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_06_rows b025_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_06_rows b025_06_labels]
    decide +kernel

def b025_07_rows : List Row := [(row3 4 26 40), (row3 4 26 41), (row3 4 26 42), (row3 4 26 43), (row3 4 26 44), (row3 4 26 45), (row3 4 26 46), (row3 4 26 47), (row3 4 26 48), (row3 4 26 49), (row3 4 26 50), (row3 4 26 51), (row3 4 26 52), (row3 4 26 53), (row3 4 26 54), (row3 4 26 55)]

def b025_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_07_rows b025_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_07_rows b025_07_labels]
    decide +kernel

def b025_08_rows : List Row := [(row3 4 26 56), (row3 4 26 57), (row3 4 26 58), (row3 4 26 59), (row3 4 26 60), (row3 4 26 61), (row3 4 26 62), (row3 4 26 63), (row3 4 27 28), (row3 4 27 29), (row3 4 27 30), (row3 4 27 31), (row3 4 27 32), (row3 4 27 33), (row3 4 27 34), (row3 4 27 35)]

def b025_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_08_rows b025_08_labels 12997651866910806037500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_08_rows b025_08_labels]
    decide +kernel

def b025_09_rows : List Row := [(row3 4 27 36), (row3 4 27 37), (row3 4 27 38), (row3 4 27 39), (row3 4 27 40), (row3 4 27 41), (row3 4 27 42), (row3 4 27 43), (row3 4 27 44), (row3 4 27 45), (row3 4 27 46), (row3 4 27 47), (row3 4 27 48), (row3 4 27 49), (row3 4 27 50), (row3 4 27 51)]

def b025_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_09_rows b025_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_09_rows b025_09_labels]
    decide +kernel

def b025_10_rows : List Row := [(row3 4 27 52), (row3 4 27 53), (row3 4 27 54), (row3 4 27 55), (row3 4 27 56), (row3 4 27 57), (row3 4 27 58), (row3 4 27 59), (row3 4 27 60), (row3 4 27 61), (row3 4 27 62), (row3 4 27 63), (row3 4 28 29), (row3 4 28 30), (row3 4 28 31), (row3 4 28 32)]

def b025_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_10_rows b025_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_10_rows b025_10_labels]
    decide +kernel

def b025_11_rows : List Row := [(row3 4 28 33), (row3 4 28 34), (row3 4 28 35), (row3 4 28 36), (row3 4 28 37), (row3 4 28 38), (row3 4 28 39), (row3 4 28 40), (row3 4 28 41), (row3 4 28 42), (row3 4 28 43), (row3 4 28 44), (row3 4 28 45), (row3 4 28 46), (row3 4 28 47), (row3 4 28 48)]

def b025_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_11_rows b025_11_labels 1812683866259321647500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_11_rows b025_11_labels]
    decide +kernel

def b025_12_rows : List Row := [(row3 4 28 49), (row3 4 28 50), (row3 4 28 51), (row3 4 28 52), (row3 4 28 53), (row3 4 28 54), (row3 4 28 55), (row3 4 28 56), (row3 4 28 57), (row3 4 28 58), (row3 4 28 59), (row3 4 28 60), (row3 4 28 61), (row3 4 28 62), (row3 4 28 63), (row3 4 29 30)]

def b025_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 238 238), (row3 462 257 257), (row3 462 238 238), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462)]

theorem b025_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_12_rows b025_12_labels 10173724486856946716731500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_12_rows b025_12_labels]
    decide +kernel

def b025_13_rows : List Row := [(row3 4 29 31), (row3 4 29 32), (row3 4 29 33), (row3 4 29 34), (row3 4 29 35), (row3 4 29 36), (row3 4 29 37), (row3 4 29 38), (row3 4 29 39), (row3 4 29 40), (row3 4 29 41), (row3 4 29 42), (row3 4 29 43), (row3 4 29 44), (row3 4 29 45), (row3 4 29 46)]

def b025_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_13_rows b025_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_13_rows b025_13_labels]
    decide +kernel

def b025_14_rows : List Row := [(row3 4 29 47), (row3 4 29 48), (row3 4 29 49), (row3 4 29 50), (row3 4 29 51), (row3 4 29 52), (row3 4 29 53), (row3 4 29 54), (row3 4 29 55), (row3 4 29 56), (row3 4 29 57), (row3 4 29 58), (row3 4 29 59), (row3 4 29 60), (row3 4 29 61), (row3 4 29 62)]

def b025_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_14_rows b025_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_14_rows b025_14_labels]
    decide +kernel

def b025_15_rows : List Row := [(row3 4 29 63), (row3 4 30 31), (row3 4 30 32), (row3 4 30 33), (row3 4 30 34), (row3 4 30 35), (row3 4 30 36), (row3 4 30 37), (row3 4 30 38), (row3 4 30 39), (row3 4 30 40), (row3 4 30 41), (row3 4 30 42), (row3 4 30 43), (row3 4 30 44), (row3 4 30 45)]

def b025_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b025_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b025_15_rows b025_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b025_15_rows b025_15_labels]
    decide +kernel

theorem checked025 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_025 QuarticIntegerComputationalData.ids64_025 51406936239708252891453000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b025_00_rows ++ b025_01_rows) ++ (b025_02_rows ++ b025_03_rows)) ++ ((b025_04_rows ++ b025_05_rows) ++ (b025_06_rows ++ b025_07_rows))) ++ (((b025_08_rows ++ b025_09_rows) ++ (b025_10_rows ++ b025_11_rows)) ++ ((b025_12_rows ++ b025_13_rows) ++ (b025_14_rows ++ b025_15_rows))))
    ((((b025_00_labels ++ b025_01_labels) ++ (b025_02_labels ++ b025_03_labels)) ++ ((b025_04_labels ++ b025_05_labels) ++ (b025_06_labels ++ b025_07_labels))) ++ (((b025_08_labels ++ b025_09_labels) ++ (b025_10_labels ++ b025_11_labels)) ++ ((b025_12_labels ++ b025_13_labels) ++ (b025_14_labels ++ b025_15_labels)))) 51406936239708252891453000
  exact ((((b025_00_checked.append (c := 31042864246394930008657500) b025_01_checked (by decide +kernel)).append (c := 41218401417118136047036500) (b025_02_checked.append (c := 10175537170723206038379000) b025_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 41218401417118136047036500) ((b025_04_checked.append (c := 0) b025_05_checked (by decide +kernel)).append (c := 0) (b025_06_checked.append (c := 0) b025_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 51406936239708252891453000) (((b025_08_checked.append (c := 12997651866910806037500) b025_09_checked (by decide +kernel)).append (c := 14810335733170127685000) (b025_10_checked.append (c := 1812683866259321647500) b025_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 10188534822590116844416500) ((b025_12_checked.append (c := 10173724486856946716731500) b025_13_checked (by decide +kernel)).append (c := 10173724486856946716731500) (b025_14_checked.append (c := 0) b025_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b026_00_rows : List Row := [(row3 4 30 46), (row3 4 30 47), (row3 4 30 48), (row3 4 30 49), (row3 4 30 50), (row3 4 30 51), (row3 4 30 52), (row3 4 30 53), (row3 4 30 54), (row3 4 30 55), (row3 4 30 56), (row3 4 30 57), (row3 4 30 58), (row3 4 30 59), (row3 4 30 60), (row3 4 30 61)]

def b026_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_00_rows b026_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_00_rows b026_00_labels]
    decide +kernel

def b026_01_rows : List Row := [(row3 4 30 62), (row3 4 30 63), (row3 4 31 32), (row3 4 31 33), (row3 4 31 34), (row3 4 31 35), (row3 4 31 36), (row3 4 31 37), (row3 4 31 38), (row3 4 31 39), (row3 4 31 40), (row3 4 31 41), (row3 4 31 42), (row3 4 31 43), (row3 4 31 44), (row3 4 31 45)]

def b026_01_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_01_rows b026_01_labels 12997651866910806037500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_01_rows b026_01_labels]
    decide +kernel

def b026_02_rows : List Row := [(row3 4 31 46), (row3 4 31 47), (row3 4 31 48), (row3 4 31 49), (row3 4 31 50), (row3 4 31 51), (row3 4 31 52), (row3 4 31 53), (row3 4 31 54), (row3 4 31 55), (row3 4 31 56), (row3 4 31 57), (row3 4 31 58), (row3 4 31 59), (row3 4 31 60), (row3 4 31 61)]

def b026_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_02_rows b026_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_02_rows b026_02_labels]
    decide +kernel

def b026_03_rows : List Row := [(row3 4 31 62), (row3 4 31 63), (row3 4 32 33), (row3 4 32 34), (row3 4 32 35), (row3 4 32 36), (row3 4 32 37), (row3 4 32 38), (row3 4 32 39), (row3 4 32 40), (row3 4 32 41), (row3 4 32 42), (row3 4 32 43), (row3 4 32 44), (row3 4 32 45), (row3 4 32 46)]

def b026_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_03_rows b026_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_03_rows b026_03_labels]
    decide +kernel

def b026_04_rows : List Row := [(row3 4 32 47), (row3 4 32 48), (row3 4 32 49), (row3 4 32 50), (row3 4 32 51), (row3 4 32 52), (row3 4 32 53), (row3 4 32 54), (row3 4 32 55), (row3 4 32 56), (row3 4 32 57), (row3 4 32 58), (row3 4 32 59), (row3 4 32 60), (row3 4 32 61), (row3 4 32 62)]

def b026_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_04_rows b026_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_04_rows b026_04_labels]
    decide +kernel

def b026_05_rows : List Row := [(row3 4 32 63), (row3 4 33 34), (row3 4 33 35), (row3 4 33 36), (row3 4 33 37), (row3 4 33 38), (row3 4 33 39), (row3 4 33 40), (row3 4 33 41), (row3 4 33 42), (row3 4 33 43), (row3 4 33 44), (row3 4 33 45), (row3 4 33 46), (row3 4 33 47), (row3 4 33 48)]

def b026_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_05_rows b026_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_05_rows b026_05_labels]
    decide +kernel

def b026_06_rows : List Row := [(row3 4 33 49), (row3 4 33 50), (row3 4 33 51), (row3 4 33 52), (row3 4 33 53), (row3 4 33 54), (row3 4 33 55), (row3 4 33 56), (row3 4 33 57), (row3 4 33 58), (row3 4 33 59), (row3 4 33 60), (row3 4 33 61), (row3 4 33 62), (row3 4 33 63), (row3 4 34 35)]

def b026_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_06_rows b026_06_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_06_rows b026_06_labels]
    decide +kernel

def b026_07_rows : List Row := [(row3 4 34 36), (row3 4 34 37), (row3 4 34 38), (row3 4 34 39), (row3 4 34 40), (row3 4 34 41), (row3 4 34 42), (row3 4 34 43), (row3 4 34 44), (row3 4 34 45), (row3 4 34 46), (row3 4 34 47), (row3 4 34 48), (row3 4 34 49), (row3 4 34 50), (row3 4 34 51)]

def b026_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_07_rows b026_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_07_rows b026_07_labels]
    decide +kernel

def b026_08_rows : List Row := [(row3 4 34 52), (row3 4 34 53), (row3 4 34 54), (row3 4 34 55), (row3 4 34 56), (row3 4 34 57), (row3 4 34 58), (row3 4 34 59), (row3 4 34 60), (row3 4 34 61), (row3 4 34 62), (row3 4 34 63), (row3 4 35 36), (row3 4 35 37), (row3 4 35 38), (row3 4 35 39)]

def b026_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_08_rows b026_08_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_08_rows b026_08_labels]
    decide +kernel

def b026_09_rows : List Row := [(row3 4 35 40), (row3 4 35 41), (row3 4 35 42), (row3 4 35 43), (row3 4 35 44), (row3 4 35 45), (row3 4 35 46), (row3 4 35 47), (row3 4 35 48), (row3 4 35 49), (row3 4 35 50), (row3 4 35 51), (row3 4 35 52), (row3 4 35 53), (row3 4 35 54), (row3 4 35 55)]

def b026_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_09_rows b026_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_09_rows b026_09_labels]
    decide +kernel

def b026_10_rows : List Row := [(row3 4 35 56), (row3 4 35 57), (row3 4 35 58), (row3 4 35 59), (row3 4 35 60), (row3 4 35 61), (row3 4 35 62), (row3 4 35 63), (row3 4 36 37), (row3 4 36 38), (row3 4 36 39), (row3 4 36 40), (row3 4 36 41), (row3 4 36 42), (row3 4 36 43), (row3 4 36 44)]

def b026_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_10_rows b026_10_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_10_rows b026_10_labels]
    decide +kernel

def b026_11_rows : List Row := [(row3 4 36 45), (row3 4 36 46), (row3 4 36 47), (row3 4 36 48), (row3 4 36 49), (row3 4 36 50), (row3 4 36 51), (row3 4 36 52), (row3 4 36 53), (row3 4 36 54), (row3 4 36 55), (row3 4 36 56), (row3 4 36 57), (row3 4 36 58), (row3 4 36 59), (row3 4 36 60)]

def b026_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_11_rows b026_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_11_rows b026_11_labels]
    decide +kernel

def b026_12_rows : List Row := [(row3 4 36 61), (row3 4 36 62), (row3 4 36 63), (row3 4 37 38), (row3 4 37 39), (row3 4 37 40), (row3 4 37 41), (row3 4 37 42), (row3 4 37 43), (row3 4 37 44), (row3 4 37 45), (row3 4 37 46), (row3 4 37 47), (row3 4 37 48), (row3 4 37 49), (row3 4 37 50)]

def b026_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_12_rows b026_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_12_rows b026_12_labels]
    decide +kernel

def b026_13_rows : List Row := [(row3 4 37 51), (row3 4 37 52), (row3 4 37 53), (row3 4 37 54), (row3 4 37 55), (row3 4 37 56), (row3 4 37 57), (row3 4 37 58), (row3 4 37 59), (row3 4 37 60), (row3 4 37 61), (row3 4 37 62), (row3 4 37 63), (row3 4 38 39), (row3 4 38 40), (row3 4 38 41)]

def b026_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_13_rows b026_13_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_13_rows b026_13_labels]
    decide +kernel

def b026_14_rows : List Row := [(row3 4 38 42), (row3 4 38 43), (row3 4 38 44), (row3 4 38 45), (row3 4 38 46), (row3 4 38 47), (row3 4 38 48), (row3 4 38 49), (row3 4 38 50), (row3 4 38 51), (row3 4 38 52), (row3 4 38 53), (row3 4 38 54), (row3 4 38 55), (row3 4 38 56), (row3 4 38 57)]

def b026_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_14_rows b026_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_14_rows b026_14_labels]
    decide +kernel

def b026_15_rows : List Row := [(row3 4 38 58), (row3 4 38 59), (row3 4 38 60), (row3 4 38 61), (row3 4 38 62), (row3 4 38 63), (row3 4 39 40), (row3 4 39 41), (row3 4 39 42), (row3 4 39 43), (row3 4 39 44), (row3 4 39 45), (row3 4 39 46), (row3 4 39 47), (row3 4 39 48), (row3 4 39 49)]

def b026_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b026_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b026_15_rows b026_15_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b026_15_rows b026_15_labels]
    decide +kernel

theorem checked026 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_026 QuarticIntegerComputationalData.ids64_026 1513763939910949061926500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b026_00_rows ++ b026_01_rows) ++ (b026_02_rows ++ b026_03_rows)) ++ ((b026_04_rows ++ b026_05_rows) ++ (b026_06_rows ++ b026_07_rows))) ++ (((b026_08_rows ++ b026_09_rows) ++ (b026_10_rows ++ b026_11_rows)) ++ ((b026_12_rows ++ b026_13_rows) ++ (b026_14_rows ++ b026_15_rows))))
    ((((b026_00_labels ++ b026_01_labels) ++ (b026_02_labels ++ b026_03_labels)) ++ ((b026_04_labels ++ b026_05_labels) ++ (b026_06_labels ++ b026_07_labels))) ++ (((b026_08_labels ++ b026_09_labels) ++ (b026_10_labels ++ b026_11_labels)) ++ ((b026_12_labels ++ b026_13_labels) ++ (b026_14_labels ++ b026_15_labels)))) 1513763939910949061926500
  exact ((((b026_00_checked.append (c := 12997651866910806037500) b026_01_checked (by decide +kernel)).append (c := 12997651866910806037500) (b026_02_checked.append (c := 0) b026_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 297003031715000345800500) ((b026_04_checked.append (c := 0) b026_05_checked (by decide +kernel)).append (c := 284005379848089539763000) (b026_06_checked.append (c := 284005379848089539763000) b026_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1513763939910949061926500) (((b026_08_checked.append (c := 324375074249884818300000) b026_09_checked (by decide +kernel)).append (c := 608380454097974358063000) (b026_10_checked.append (c := 284005379848089539763000) b026_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1216760908195948716126000) ((b026_12_checked.append (c := 284005379848089539763000) b026_13_checked (by decide +kernel)).append (c := 608380454097974358063000) (b026_14_checked.append (c := 324375074249884818300000) b026_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b027_00_rows : List Row := [(row3 4 39 50), (row3 4 39 51), (row3 4 39 52), (row3 4 39 53), (row3 4 39 54), (row3 4 39 55), (row3 4 39 56), (row3 4 39 57), (row3 4 39 58), (row3 4 39 59), (row3 4 39 60), (row3 4 39 61), (row3 4 39 62), (row3 4 39 63), (row3 4 40 41), (row3 4 40 42)]

def b027_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462)]

theorem b027_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_00_rows b027_00_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_00_rows b027_00_labels]
    decide +kernel

def b027_01_rows : List Row := [(row3 4 40 43), (row3 4 40 44), (row3 4 40 45), (row3 4 40 46), (row3 4 40 47), (row3 4 40 48), (row3 4 40 49), (row3 4 40 50), (row3 4 40 51), (row3 4 40 52), (row3 4 40 53), (row3 4 40 54), (row3 4 40 55), (row3 4 40 56), (row3 4 40 57), (row3 4 40 58)]

def b027_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 257 257), (row3 232 238 230), (row3 462 249 249)]

theorem b027_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_01_rows b027_01_labels 11385089770688436933961500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_01_rows b027_01_labels]
    decide +kernel

def b027_02_rows : List Row := [(row3 4 40 59), (row3 4 40 60), (row3 4 40 61), (row3 4 40 62), (row3 4 40 63), (row3 4 41 42), (row3 4 41 43), (row3 4 41 44), (row3 4 41 45), (row3 4 41 46), (row3 4 41 47), (row3 4 41 48), (row3 4 41 49), (row3 4 41 50), (row3 4 41 51), (row3 4 41 52)]

def b027_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 249 249), (row3 232 238 230), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_02_rows b027_02_labels 996980216011667632593000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_02_rows b027_02_labels]
    decide +kernel

def b027_03_rows : List Row := [(row3 4 41 53), (row3 4 41 54), (row3 4 41 55), (row3 4 41 56), (row3 4 41 57), (row3 4 41 58), (row3 4 41 59), (row3 4 41 60), (row3 4 41 61), (row3 4 41 62), (row3 4 41 63), (row3 4 42 43), (row3 4 42 44), (row3 4 42 45), (row3 4 42 46), (row3 4 42 47)]

def b027_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_03_rows b027_03_labels 6896564724897369017571600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_03_rows b027_03_labels]
    decide +kernel

def b027_04_rows : List Row := [(row3 4 42 48), (row3 4 42 49), (row3 4 42 50), (row3 4 42 51), (row3 4 42 52), (row3 4 42 53), (row3 4 42 54), (row3 4 42 55), (row3 4 42 56), (row3 4 42 57), (row3 4 42 58), (row3 4 42 59), (row3 4 42 60), (row3 4 42 61), (row3 4 42 62), (row3 4 42 63)]

def b027_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 289 291 291), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_04_rows b027_04_labels 11863569257291282990317200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_04_rows b027_04_labels]
    decide +kernel

def b027_05_rows : List Row := [(row3 4 43 44), (row3 4 43 45), (row3 4 43 46), (row3 4 43 47), (row3 4 43 48), (row3 4 43 49), (row3 4 43 50), (row3 4 43 51), (row3 4 43 52), (row3 4 43 53), (row3 4 43 54), (row3 4 43 55), (row3 4 43 56), (row3 4 43 57), (row3 4 43 58), (row3 4 43 59)]

def b027_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 273 273 462)]

theorem b027_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_05_rows b027_05_labels 6896564724897369017571600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_05_rows b027_05_labels]
    decide +kernel

def b027_06_rows : List Row := [(row3 4 43 60), (row3 4 43 61), (row3 4 43 62), (row3 4 43 63), (row3 4 44 45), (row3 4 44 46), (row3 4 44 47), (row3 4 44 48), (row3 4 44 49), (row3 4 44 50), (row3 4 44 51), (row3 4 44 52), (row3 4 44 53), (row3 4 44 54), (row3 4 44 55), (row3 4 44 56)]

def b027_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_06_rows b027_06_labels 294046715372751899361000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_06_rows b027_06_labels]
    decide +kernel

def b027_07_rows : List Row := [(row3 4 44 57), (row3 4 44 58), (row3 4 44 59), (row3 4 44 60), (row3 4 44 61), (row3 4 44 62), (row3 4 44 63), (row3 4 45 46), (row3 4 45 47), (row3 4 45 48), (row3 4 45 49), (row3 4 45 50), (row3 4 45 51), (row3 4 45 52), (row3 4 45 53), (row3 4 45 54)]

def b027_07_labels : List Row := [(row3 462 462 462), (row3 462 249 249), (row3 232 230 238), (row3 462 257 257), (row3 232 230 238), (row3 462 249 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_07_rows b027_07_labels 12088023271327352667193500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_07_rows b027_07_labels]
    decide +kernel

def b027_08_rows : List Row := [(row3 4 45 55), (row3 4 45 56), (row3 4 45 57), (row3 4 45 58), (row3 4 45 59), (row3 4 45 60), (row3 4 45 61), (row3 4 45 62), (row3 4 45 63), (row3 4 46 47), (row3 4 46 48), (row3 4 46 49), (row3 4 46 50), (row3 4 46 51), (row3 4 46 52), (row3 4 46 53)]

def b027_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 273 462), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_08_rows b027_08_labels 6896564724897369017571600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_08_rows b027_08_labels]
    decide +kernel

def b027_09_rows : List Row := [(row3 4 46 54), (row3 4 46 55), (row3 4 46 56), (row3 4 46 57), (row3 4 46 58), (row3 4 46 59), (row3 4 46 60), (row3 4 46 61), (row3 4 46 62), (row3 4 46 63), (row3 4 47 48), (row3 4 47 49), (row3 4 47 50), (row3 4 47 51), (row3 4 47 52), (row3 4 47 53)]

def b027_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 289 291 291), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_09_rows b027_09_labels 11863569257291282990317200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_09_rows b027_09_labels]
    decide +kernel

def b027_10_rows : List Row := [(row3 4 47 54), (row3 4 47 55), (row3 4 47 56), (row3 4 47 57), (row3 4 47 58), (row3 4 47 59), (row3 4 47 60), (row3 4 47 61), (row3 4 47 62), (row3 4 47 63), (row3 4 48 49), (row3 4 48 50), (row3 4 48 51), (row3 4 48 52), (row3 4 48 53), (row3 4 48 54)]

def b027_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 273 462 273), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b027_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_10_rows b027_10_labels 7738840555031488368639600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_10_rows b027_10_labels]
    decide +kernel

def b027_11_rows : List Row := [(row3 4 48 55), (row3 4 48 56), (row3 4 48 57), (row3 4 48 58), (row3 4 48 59), (row3 4 48 60), (row3 4 48 61), (row3 4 48 62), (row3 4 48 63), (row3 4 49 50), (row3 4 49 51), (row3 4 49 52), (row3 4 49 53), (row3 4 49 54), (row3 4 49 55), (row3 4 49 56)]

def b027_11_labels : List Row := [(row3 462 237 237), (row3 462 208 208), (row3 288 261 290), (row3 224 223 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 223 223), (row3 288 261 290), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 269 269)]

theorem b027_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_11_rows b027_11_labels 330461406514597047179468400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_11_rows b027_11_labels]
    decide +kernel

def b027_12_rows : List Row := [(row3 4 49 57), (row3 4 49 58), (row3 4 49 59), (row3 4 49 60), (row3 4 49 61), (row3 4 49 62), (row3 4 49 63), (row3 4 50 51), (row3 4 50 52), (row3 4 50 53), (row3 4 50 54), (row3 4 50 55), (row3 4 50 56), (row3 4 50 57), (row3 4 50 58), (row3 4 50 59)]

def b027_12_labels : List Row := [(row3 163 235 162), (row3 306 311 311), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 232 235 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 131 105 105), (row3 288 288 462)]

theorem b027_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_12_rows b027_12_labels 3200943568003843690918980000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_12_rows b027_12_labels]
    decide +kernel

def b027_13_rows : List Row := [(row3 4 50 60), (row3 4 50 61), (row3 4 50 62), (row3 4 50 63), (row3 4 51 52), (row3 4 51 53), (row3 4 51 54), (row3 4 51 55), (row3 4 51 56), (row3 4 51 57), (row3 4 51 58), (row3 4 51 59), (row3 4 51 60), (row3 4 51 61), (row3 4 51 62), (row3 4 51 63)]

def b027_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 306 311 311), (row3 163 162 235), (row3 462 269 269), (row3 232 228 235), (row3 462 248 248), (row3 462 462 462)]

theorem b027_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_13_rows b027_13_labels 796078527425716589804962800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_13_rows b027_13_labels]
    decide +kernel

def b027_14_rows : List Row := [(row3 4 52 53), (row3 4 52 54), (row3 4 52 55), (row3 4 52 56), (row3 4 52 57), (row3 4 52 58), (row3 4 52 59), (row3 4 52 60), (row3 4 52 61), (row3 4 52 62), (row3 4 52 63), (row3 4 53 54), (row3 4 53 55), (row3 4 53 56), (row3 4 53 57), (row3 4 53 58)]

def b027_14_labels : List Row := [(row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 223 223), (row3 288 290 261), (row3 462 208 208), (row3 288 290 261), (row3 224 223 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248)]

theorem b027_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_14_rows b027_14_labels 299329608703437347006520900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_14_rows b027_14_labels]
    decide +kernel

def b027_15_rows : List Row := [(row3 4 53 59), (row3 4 53 60), (row3 4 53 61), (row3 4 53 62), (row3 4 53 63), (row3 4 54 55), (row3 4 54 56), (row3 4 54 57), (row3 4 54 58), (row3 4 54 59), (row3 4 54 60), (row3 4 54 61), (row3 4 54 62), (row3 4 54 63), (row3 4 55 56), (row3 4 55 57)]

def b027_15_labels : List Row := [(row3 232 228 235), (row3 462 269 269), (row3 163 162 235), (row3 306 311 311), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 288 462), (row3 131 105 105), (row3 288 462 288), (row3 462 269 269), (row3 232 235 228)]

theorem b027_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b027_15_rows b027_15_labels 3264468493374071908278538500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b027_15_rows b027_15_labels]
    decide +kernel

theorem checked027 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_027 QuarticIntegerComputationalData.ids64_027 7968485422619221043263331400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b027_00_rows ++ b027_01_rows) ++ (b027_02_rows ++ b027_03_rows)) ++ ((b027_04_rows ++ b027_05_rows) ++ (b027_06_rows ++ b027_07_rows))) ++ (((b027_08_rows ++ b027_09_rows) ++ (b027_10_rows ++ b027_11_rows)) ++ ((b027_12_rows ++ b027_13_rows) ++ (b027_14_rows ++ b027_15_rows))))
    ((((b027_00_labels ++ b027_01_labels) ++ (b027_02_labels ++ b027_03_labels)) ++ ((b027_04_labels ++ b027_05_labels) ++ (b027_06_labels ++ b027_07_labels))) ++ (((b027_08_labels ++ b027_09_labels) ++ (b027_10_labels ++ b027_11_labels)) ++ ((b027_12_labels ++ b027_13_labels) ++ (b027_14_labels ++ b027_15_labels)))) 7968485422619221043263331400
  exact ((((b027_00_checked.append (c := 11669095150536526473724500) b027_01_checked (by decide +kernel)).append (c := 19562640091445563123889100) (b027_02_checked.append (c := 7893544940909036650164600) b027_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 50704844060334319698332400) ((b027_04_checked.append (c := 18760133982188652007888800) b027_05_checked (by decide +kernel)).append (c := 31142203968888756574443300) (b027_06_checked.append (c := 12382069986700104566554500) b027_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7968485422619221043263331400) (((b027_08_checked.append (c := 18760133982188652007888800) b027_09_checked (by decide +kernel)).append (c := 356960381051817187555996800) (b027_10_checked.append (c := 338200247069628535548108000) b027_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 7917780578558886723564999000) ((b027_12_checked.append (c := 3997022095429560280723942800) b027_13_checked (by decide +kernel)).append (c := 7560820197507069536009002200) (b027_14_checked.append (c := 3563798102077509255285059400) b027_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b028_00_rows : List Row := [(row3 4 55 58), (row3 4 55 59), (row3 4 55 60), (row3 4 55 61), (row3 4 55 62), (row3 4 55 63), (row3 4 56 57), (row3 4 56 58), (row3 4 56 59), (row3 4 56 60), (row3 4 56 61), (row3 4 56 62), (row3 4 56 63), (row3 4 57 58), (row3 4 57 59), (row3 4 57 60)]

def b028_00_labels : List Row := [(row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 306 311 311), (row3 163 235 162), (row3 163 193 139), (row3 289 299 299), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 289 299 299), (row3 163 193 139), (row3 399 156 82), (row3 288 288 462), (row3 236 236 462)]

theorem b028_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_00_rows b028_00_labels 24714710332595941876073218440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_00_rows b028_00_labels]
    decide +kernel

def b028_01_rows : List Row := [(row3 4 57 61), (row3 4 57 62), (row3 4 57 63), (row3 4 58 59), (row3 4 58 60), (row3 4 58 61), (row3 4 58 62), (row3 4 58 63), (row3 4 59 60), (row3 4 59 61), (row3 4 59 62), (row3 4 59 63), (row3 4 60 61), (row3 4 60 62), (row3 4 60 63), (row3 4 61 62)]

def b028_01_labels : List Row := [(row3 462 462 462), (row3 231 227 229), (row3 288 288 288), (row3 399 156 82), (row3 289 299 299), (row3 231 227 229), (row3 462 251 251), (row3 231 229 227), (row3 163 193 139), (row3 288 288 288), (row3 231 229 227), (row3 462 462 462), (row3 163 139 193), (row3 289 299 299), (row3 236 462 236), (row3 399 82 156)]

theorem b028_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_01_rows b028_01_labels 44170062441988348769647937400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_01_rows b028_01_labels]
    decide +kernel

def b028_02_rows : List Row := [(row3 4 61 63), (row3 4 62 63), (row3 5 6 7), (row3 5 6 8), (row3 5 6 9), (row3 5 6 10), (row3 5 6 11), (row3 5 6 12), (row3 5 6 13), (row3 5 6 14), (row3 5 6 15), (row3 5 6 16), (row3 5 6 17), (row3 5 6 18), (row3 5 6 19), (row3 5 6 20)]

def b028_02_labels : List Row := [(row3 288 462 288), (row3 399 82 156), (row3 21 459 441), (row3 400 397 384), (row3 190 167 166), (row3 277 265 277), (row3 87 325 371), (row3 430 372 58), (row3 29 56 445), (row3 448 454 449), (row3 51 53 57), (row3 206 164 164), (row3 266 265 266), (row3 237 237 462), (row3 269 462 269), (row3 88 211 370)]

theorem b028_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_02_rows b028_02_labels 881557984729471317984917908968480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_02_rows b028_02_labels]
    decide +kernel

def b028_03_rows : List Row := [(row3 5 6 21), (row3 5 6 22), (row3 5 6 23), (row3 5 6 24), (row3 5 6 25), (row3 5 6 26), (row3 5 6 27), (row3 5 6 28), (row3 5 6 29), (row3 5 6 30), (row3 5 6 31), (row3 5 6 32), (row3 5 6 33), (row3 5 6 34), (row3 5 6 35), (row3 5 6 36)]

def b028_03_labels : List Row := [(row3 426 385 77), (row3 68 69 76), (row3 393 386 363), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 97 202 334), (row3 343 338 330), (row3 238 192 193), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b028_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_03_rows b028_03_labels 189621142096201952383657862220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_03_rows b028_03_labels]
    decide +kernel

def b028_04_rows : List Row := [(row3 5 6 37), (row3 5 6 38), (row3 5 6 39), (row3 5 6 40), (row3 5 6 41), (row3 5 6 42), (row3 5 6 43), (row3 5 6 44), (row3 5 6 45), (row3 5 6 46), (row3 5 6 47), (row3 5 6 48), (row3 5 6 49), (row3 5 6 50), (row3 5 6 51), (row3 5 6 52)]

def b028_04_labels : List Row := [(row3 257 462 257), (row3 462 208 208), (row3 462 462 462), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 97 202 334), (row3 343 338 330), (row3 238 192 193), (row3 206 164 164), (row3 266 265 266), (row3 237 237 462), (row3 269 462 269), (row3 88 211 370)]

theorem b028_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_04_rows b028_04_labels 21435211492531281780649142910 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_04_rows b028_04_labels]
    decide +kernel

def b028_05_rows : List Row := [(row3 5 6 53), (row3 5 6 54), (row3 5 6 55), (row3 5 6 56), (row3 5 6 57), (row3 5 6 58), (row3 5 6 59), (row3 5 6 60), (row3 5 6 61), (row3 5 6 62), (row3 5 6 63), (row3 5 7 8), (row3 5 7 9), (row3 5 7 10), (row3 5 7 11), (row3 5 7 12)]

def b028_05_labels : List Row := [(row3 426 385 77), (row3 68 69 76), (row3 393 386 363), (row3 400 397 384), (row3 190 167 166), (row3 277 265 277), (row3 87 325 371), (row3 430 372 58), (row3 29 56 445), (row3 448 454 449), (row3 51 53 57), (row3 29 445 56), (row3 430 58 372), (row3 87 371 325), (row3 277 277 265), (row3 190 166 167)]

theorem b028_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_05_rows b028_05_labels 18857300653319308118596080050610 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_05_rows b028_05_labels]
    decide +kernel

def b028_06_rows : List Row := [(row3 5 7 13), (row3 5 7 14), (row3 5 7 15), (row3 5 7 16), (row3 5 7 17), (row3 5 7 18), (row3 5 7 19), (row3 5 7 20), (row3 5 7 21), (row3 5 7 22), (row3 5 7 23), (row3 5 7 24), (row3 5 7 25), (row3 5 7 26), (row3 5 7 27), (row3 5 7 28)]

def b028_06_labels : List Row := [(row3 400 384 397), (row3 51 57 53), (row3 448 449 454), (row3 426 77 385), (row3 88 370 211), (row3 269 269 462), (row3 237 462 237), (row3 266 266 265), (row3 206 164 164), (row3 393 363 386), (row3 68 76 69), (row3 97 334 202), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238)]

theorem b028_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_06_rows b028_06_labels 10249670267246308608614146438230 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_06_rows b028_06_labels]
    decide +kernel

def b028_07_rows : List Row := [(row3 5 7 29), (row3 5 7 30), (row3 5 7 31), (row3 5 7 32), (row3 5 7 33), (row3 5 7 34), (row3 5 7 35), (row3 5 7 36), (row3 5 7 37), (row3 5 7 38), (row3 5 7 39), (row3 5 7 40), (row3 5 7 41), (row3 5 7 42), (row3 5 7 43), (row3 5 7 44)]

def b028_07_labels : List Row := [(row3 256 256 255), (row3 238 193 192), (row3 343 330 338), (row3 257 257 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 208 208), (row3 97 334 202), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238)]

theorem b028_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_07_rows b028_07_labels 8552734446049683410408159850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_07_rows b028_07_labels]
    decide +kernel

def b028_08_rows : List Row := [(row3 5 7 45), (row3 5 7 46), (row3 5 7 47), (row3 5 7 48), (row3 5 7 49), (row3 5 7 50), (row3 5 7 51), (row3 5 7 52), (row3 5 7 53), (row3 5 7 54), (row3 5 7 55), (row3 5 7 56), (row3 5 7 57), (row3 5 7 58), (row3 5 7 59), (row3 5 7 60)]

def b028_08_labels : List Row := [(row3 256 256 255), (row3 238 193 192), (row3 343 330 338), (row3 426 77 385), (row3 88 370 211), (row3 269 269 462), (row3 237 462 237), (row3 266 266 265), (row3 206 164 164), (row3 393 363 386), (row3 68 76 69), (row3 29 445 56), (row3 430 58 372), (row3 87 371 325), (row3 277 277 265), (row3 190 166 167)]

theorem b028_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_08_rows b028_08_labels 4511219428728158920871242789500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_08_rows b028_08_labels]
    decide +kernel

def b028_09_rows : List Row := [(row3 5 7 61), (row3 5 7 62), (row3 5 7 63), (row3 5 8 9), (row3 5 8 10), (row3 5 8 11), (row3 5 8 12), (row3 5 8 13), (row3 5 8 14), (row3 5 8 15), (row3 5 8 16), (row3 5 8 17), (row3 5 8 18), (row3 5 8 19), (row3 5 8 20), (row3 5 8 21)]

def b028_09_labels : List Row := [(row3 400 384 397), (row3 51 57 53), (row3 448 449 454), (row3 359 73 429), (row3 155 332 93), (row3 259 204 8), (row3 236 236 462), (row3 269 186 9), (row3 123 331 92), (row3 44 74 439), (row3 336 72 428), (row3 159 356 91), (row3 258 172 10), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462)]

theorem b028_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_09_rows b028_09_labels 10846296058391389450776429215100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_09_rows b028_09_labels]
    decide +kernel

def b028_10_rows : List Row := [(row3 5 8 22), (row3 5 8 23), (row3 5 8 24), (row3 5 8 25), (row3 5 8 26), (row3 5 8 27), (row3 5 8 28), (row3 5 8 29), (row3 5 8 30), (row3 5 8 31), (row3 5 8 32), (row3 5 8 33), (row3 5 8 34), (row3 5 8 35), (row3 5 8 36), (row3 5 8 37)]

def b028_10_labels : List Row := [(row3 260 173 10), (row3 158 356 89), (row3 202 334 97), (row3 254 171 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 254 171 10), (row3 254 203 8), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b028_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_10_rows b028_10_labels 11519520141450938097894048000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_10_rows b028_10_labels]
    decide +kernel

def b028_11_rows : List Row := [(row3 5 8 38), (row3 5 8 39), (row3 5 8 40), (row3 5 8 41), (row3 5 8 42), (row3 5 8 43), (row3 5 8 44), (row3 5 8 45), (row3 5 8 46), (row3 5 8 47), (row3 5 8 48), (row3 5 8 49), (row3 5 8 50), (row3 5 8 51), (row3 5 8 52), (row3 5 8 53)]

def b028_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 201 208 201), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 263 263 462), (row3 343 330 338), (row3 154 180 154), (row3 269 269 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462)]

theorem b028_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_11_rows b028_11_labels 6060916925160169479299575050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_11_rows b028_11_labels]
    decide +kernel

def b028_12_rows : List Row := [(row3 5 8 54), (row3 5 8 55), (row3 5 8 56), (row3 5 8 57), (row3 5 8 58), (row3 5 8 59), (row3 5 8 60), (row3 5 8 61), (row3 5 8 62), (row3 5 8 63), (row3 5 9 10), (row3 5 9 11), (row3 5 9 12), (row3 5 9 13), (row3 5 9 14), (row3 5 9 15)]

def b028_12_labels : List Row := [(row3 271 271 462), (row3 154 180 154), (row3 54 65 65), (row3 373 352 365), (row3 154 180 154), (row3 264 264 462), (row3 236 236 462), (row3 274 274 462), (row3 152 177 150), (row3 376 354 366), (row3 301 278 301), (row3 233 233 462), (row3 462 462 462), (row3 236 236 462), (row3 296 295 296), (row3 126 125 128)]

theorem b028_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_12_rows b028_12_labels 290928045917556075134179495200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_12_rows b028_12_labels]
    decide +kernel

def b028_13_rows : List Row := [(row3 5 9 16), (row3 5 9 17), (row3 5 9 18), (row3 5 9 19), (row3 5 9 20), (row3 5 9 21), (row3 5 9 22), (row3 5 9 23), (row3 5 9 24), (row3 5 9 25), (row3 5 9 26), (row3 5 9 27), (row3 5 9 28), (row3 5 9 29), (row3 5 9 30), (row3 5 9 31)]

def b028_13_labels : List Row := [(row3 190 198 199), (row3 279 278 279), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 283 278 283), (row3 262 261 262), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462)]

theorem b028_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_13_rows b028_13_labels 224627500915791723222254580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_13_rows b028_13_labels]
    decide +kernel

def b028_14_rows : List Row := [(row3 5 9 32), (row3 5 9 33), (row3 5 9 34), (row3 5 9 35), (row3 5 9 36), (row3 5 9 37), (row3 5 9 38), (row3 5 9 39), (row3 5 9 40), (row3 5 9 41), (row3 5 9 42), (row3 5 9 43), (row3 5 9 44), (row3 5 9 45), (row3 5 9 46), (row3 5 9 47)]

def b028_14_labels : List Row := [(row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 262 261 262), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462)]

theorem b028_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_14_rows b028_14_labels 3691450176326031038725200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_14_rows b028_14_labels]
    decide +kernel

def b028_15_rows : List Row := [(row3 5 9 48), (row3 5 9 49), (row3 5 9 50), (row3 5 9 51), (row3 5 9 52), (row3 5 9 53), (row3 5 9 54), (row3 5 9 55), (row3 5 9 56), (row3 5 9 57), (row3 5 9 58), (row3 5 9 59), (row3 5 9 60), (row3 5 9 61), (row3 5 9 62), (row3 5 9 63)]

def b028_15_labels : List Row := [(row3 190 198 199), (row3 279 278 279), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 279 278 279), (row3 373 365 352), (row3 161 176 176), (row3 282 278 282), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 279 278 279), (row3 161 175 175)]

theorem b028_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b028_15_rows b028_15_labels 11000003816351057008034407890 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b028_15_rows b028_15_labels]
    decide +kernel

theorem checked028 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_028 QuarticIntegerComputationalData.ids64_028 926630701803717460649469912288660 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b028_00_rows ++ b028_01_rows) ++ (b028_02_rows ++ b028_03_rows)) ++ ((b028_04_rows ++ b028_05_rows) ++ (b028_06_rows ++ b028_07_rows))) ++ (((b028_08_rows ++ b028_09_rows) ++ (b028_10_rows ++ b028_11_rows)) ++ ((b028_12_rows ++ b028_13_rows) ++ (b028_14_rows ++ b028_15_rows))))
    ((((b028_00_labels ++ b028_01_labels) ++ (b028_02_labels ++ b028_03_labels)) ++ ((b028_04_labels ++ b028_05_labels) ++ (b028_06_labels ++ b028_07_labels))) ++ (((b028_08_labels ++ b028_09_labels) ++ (b028_10_labels ++ b028_11_labels)) ++ ((b028_12_labels ++ b028_13_labels) ++ (b028_14_labels ++ b028_15_labels)))) 926630701803717460649469912288660
  exact ((((b028_00_checked.append (c := 68884772774584290645721155840) b028_01_checked (by decide +kernel)).append (c := 881816490644342104227947287986540) (b028_02_checked.append (c := 881747605871567519937301566830700) b028_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 910953449510846301920348571778140) ((b028_04_checked.append (c := 18878735864811839400376729193520) b028_05_checked (by decide +kernel)).append (c := 29136958866504197692401283791600) (b028_06_checked.append (c := 10258223001692358292024554598080) b028_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 926630701803717460649469912288660) (((b028_08_checked.append (c := 15357515487119548371647672004600) b028_09_checked (by decide +kernel)).append (c := 15375095924186159479224865627650) (b028_10_checked.append (c := 17580437066611107577193623050) b028_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 15677252292871158729121340510520) ((b028_12_checked.append (c := 291152673418471866857401749780) b028_13_checked (by decide +kernel)).append (c := 302156368684999249896474882870) (b028_14_checked.append (c := 11003695266527383039073133090) b028_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b029_00_rows : List Row := [(row3 5 10 11), (row3 5 10 12), (row3 5 10 13), (row3 5 10 14), (row3 5 10 15), (row3 5 10 16), (row3 5 10 17), (row3 5 10 18), (row3 5 10 19), (row3 5 10 20), (row3 5 10 21), (row3 5 10 22), (row3 5 10 23), (row3 5 10 24), (row3 5 10 25), (row3 5 10 26)]

def b029_00_labels : List Row := [(row3 116 213 11), (row3 233 233 462), (row3 259 204 8), (row3 231 227 229), (row3 297 297 295), (row3 268 268 265), (row3 226 226 234), (row3 285 285 462), (row3 232 232 462), (row3 247 247 462), (row3 238 238 462), (row3 245 245 462), (row3 234 234 234), (row3 237 237 237), (row3 247 247 462), (row3 235 235 462)]

theorem b029_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_00_rows b029_00_labels 2409985868361021417301606350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_00_rows b029_00_labels]
    decide +kernel

def b029_01_rows : List Row := [(row3 5 10 27), (row3 5 10 28), (row3 5 10 29), (row3 5 10 30), (row3 5 10 31), (row3 5 10 32), (row3 5 10 33), (row3 5 10 34), (row3 5 10 35), (row3 5 10 36), (row3 5 10 37), (row3 5 10 38), (row3 5 10 39), (row3 5 10 40), (row3 5 10 41), (row3 5 10 42)]

def b029_01_labels : List Row := [(row3 246 246 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 243 243 462), (row3 242 242 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462)]

theorem b029_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_01_rows b029_01_labels 156338032569887095237500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_01_rows b029_01_labels]
    decide +kernel

def b029_02_rows : List Row := [(row3 5 10 43), (row3 5 10 44), (row3 5 10 45), (row3 5 10 46), (row3 5 10 47), (row3 5 10 48), (row3 5 10 49), (row3 5 10 50), (row3 5 10 51), (row3 5 10 52), (row3 5 10 53), (row3 5 10 54), (row3 5 10 55), (row3 5 10 56), (row3 5 10 57), (row3 5 10 58)]

def b029_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 245 245 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462), (row3 245 245 462), (row3 234 234 234), (row3 154 154 180), (row3 282 282 278), (row3 226 229 229)]

theorem b029_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_02_rows b029_02_labels 812655719470074235387101000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_02_rows b029_02_labels]
    decide +kernel

def b029_03_rows : List Row := [(row3 5 10 59), (row3 5 10 60), (row3 5 10 61), (row3 5 10 62), (row3 5 10 63), (row3 5 11 12), (row3 5 11 13), (row3 5 11 14), (row3 5 11 15), (row3 5 11 16), (row3 5 11 17), (row3 5 11 18), (row3 5 11 19), (row3 5 11 20), (row3 5 11 21), (row3 5 11 22)]

def b029_03_labels : List Row := [(row3 252 252 462), (row3 236 236 462), (row3 264 264 462), (row3 231 231 234), (row3 280 280 278), (row3 301 278 301), (row3 155 332 93), (row3 297 295 297), (row3 231 229 227), (row3 238 462 238), (row3 247 462 247), (row3 232 462 232), (row3 285 462 285), (row3 226 234 226), (row3 268 265 268), (row3 234 234 234)]

theorem b029_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_03_rows b029_03_labels 3460384670305719664563600300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_03_rows b029_03_labels]
    decide +kernel

def b029_04_rows : List Row := [(row3 5 11 23), (row3 5 11 24), (row3 5 11 25), (row3 5 11 26), (row3 5 11 27), (row3 5 11 28), (row3 5 11 29), (row3 5 11 30), (row3 5 11 31), (row3 5 11 32), (row3 5 11 33), (row3 5 11 34), (row3 5 11 35), (row3 5 11 36), (row3 5 11 37), (row3 5 11 38)]

def b029_04_labels : List Row := [(row3 245 462 245), (row3 241 462 241), (row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 247 462 247), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462)]

theorem b029_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_04_rows b029_04_labels 514171062182722775919000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_04_rows b029_04_labels]
    decide +kernel

def b029_05_rows : List Row := [(row3 5 11 39), (row3 5 11 40), (row3 5 11 41), (row3 5 11 42), (row3 5 11 43), (row3 5 11 44), (row3 5 11 45), (row3 5 11 46), (row3 5 11 47), (row3 5 11 48), (row3 5 11 49), (row3 5 11 50), (row3 5 11 51), (row3 5 11 52), (row3 5 11 53), (row3 5 11 54)]

def b029_05_labels : List Row := [(row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 245 462 245), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234)]

theorem b029_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_05_rows b029_05_labels 4140231503204672206116900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_05_rows b029_05_labels]
    decide +kernel

def b029_06_rows : List Row := [(row3 5 11 55), (row3 5 11 56), (row3 5 11 57), (row3 5 11 58), (row3 5 11 59), (row3 5 11 60), (row3 5 11 61), (row3 5 11 62), (row3 5 11 63), (row3 5 12 13), (row3 5 12 14), (row3 5 12 15), (row3 5 12 16), (row3 5 12 17), (row3 5 12 18), (row3 5 12 19)]

def b029_06_labels : List Row := [(row3 245 462 245), (row3 264 462 264), (row3 236 462 236), (row3 252 462 252), (row3 226 229 229), (row3 282 278 282), (row3 154 180 154), (row3 280 278 280), (row3 231 234 231), (row3 359 73 429), (row3 126 128 125), (row3 296 296 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b029_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_06_rows b029_06_labels 111259780979840794175891296200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_06_rows b029_06_labels]
    decide +kernel

def b029_07_rows : List Row := [(row3 5 12 20), (row3 5 12 21), (row3 5 12 22), (row3 5 12 23), (row3 5 12 24), (row3 5 12 25), (row3 5 12 26), (row3 5 12 27), (row3 5 12 28), (row3 5 12 29), (row3 5 12 30), (row3 5 12 31), (row3 5 12 32), (row3 5 12 33), (row3 5 12 34), (row3 5 12 35)]

def b029_07_labels : List Row := [(row3 279 279 278), (row3 190 199 198), (row3 283 283 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 262 262 261), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b029_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_07_rows b029_07_labels 223893766876347310965794580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_07_rows b029_07_labels]
    decide +kernel

def b029_08_rows : List Row := [(row3 5 12 36), (row3 5 12 37), (row3 5 12 38), (row3 5 12 39), (row3 5 12 40), (row3 5 12 41), (row3 5 12 42), (row3 5 12 43), (row3 5 12 44), (row3 5 12 45), (row3 5 12 46), (row3 5 12 47), (row3 5 12 48), (row3 5 12 49), (row3 5 12 50), (row3 5 12 51)]

def b029_08_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 262 262 261), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b029_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_08_rows b029_08_labels 4078465290497432930257200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_08_rows b029_08_labels]
    decide +kernel

def b029_09_rows : List Row := [(row3 5 12 52), (row3 5 12 53), (row3 5 12 54), (row3 5 12 55), (row3 5 12 56), (row3 5 12 57), (row3 5 12 58), (row3 5 12 59), (row3 5 12 60), (row3 5 12 61), (row3 5 12 62), (row3 5 12 63), (row3 5 13 14), (row3 5 13 15), (row3 5 13 16), (row3 5 13 17)]

def b029_09_labels : List Row := [(row3 279 279 278), (row3 190 199 198), (row3 279 279 278), (row3 235 462 235), (row3 236 462 236), (row3 462 462 462), (row3 236 462 236), (row3 282 282 278), (row3 161 176 176), (row3 373 352 365), (row3 161 175 175), (row3 279 279 278), (row3 44 439 74), (row3 123 92 331), (row3 238 462 238), (row3 243 462 243)]

theorem b029_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_09_rows b029_09_labels 559255033992943933968292344690 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_09_rows b029_09_labels]
    decide +kernel

def b029_10_rows : List Row := [(row3 5 13 18), (row3 5 13 19), (row3 5 13 20), (row3 5 13 21), (row3 5 13 22), (row3 5 13 23), (row3 5 13 24), (row3 5 13 25), (row3 5 13 26), (row3 5 13 27), (row3 5 13 28), (row3 5 13 29), (row3 5 13 30), (row3 5 13 31), (row3 5 13 32), (row3 5 13 33)]

def b029_10_labels : List Row := [(row3 462 462 462), (row3 258 10 172), (row3 159 91 356), (row3 336 428 72), (row3 158 89 356), (row3 260 10 173), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 10 171), (row3 202 97 334), (row3 254 10 171), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b029_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_10_rows b029_10_labels 119429792747990704942003179900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_10_rows b029_10_labels]
    decide +kernel

def b029_11_rows : List Row := [(row3 5 13 34), (row3 5 13 35), (row3 5 13 36), (row3 5 13 37), (row3 5 13 38), (row3 5 13 39), (row3 5 13 40), (row3 5 13 41), (row3 5 13 42), (row3 5 13 43), (row3 5 13 44), (row3 5 13 45), (row3 5 13 46), (row3 5 13 47), (row3 5 13 48), (row3 5 13 49)]

def b029_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 8 203), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 201 201 208), (row3 263 462 263), (row3 462 462 462), (row3 238 462 238), (row3 243 462 243)]

theorem b029_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_11_rows b029_11_labels 478526499974784774617206500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_11_rows b029_11_labels]
    decide +kernel

def b029_12_rows : List Row := [(row3 5 13 50), (row3 5 13 51), (row3 5 13 52), (row3 5 13 53), (row3 5 13 54), (row3 5 13 55), (row3 5 13 56), (row3 5 13 57), (row3 5 13 58), (row3 5 13 59), (row3 5 13 60), (row3 5 13 61), (row3 5 13 62), (row3 5 13 63), (row3 5 14 15), (row3 5 14 16)]

def b029_12_labels : List Row := [(row3 462 462 462), (row3 269 462 269), (row3 154 154 180), (row3 343 338 330), (row3 154 154 180), (row3 271 462 271), (row3 274 462 274), (row3 236 462 236), (row3 264 462 264), (row3 154 154 180), (row3 373 365 352), (row3 54 65 65), (row3 376 366 354), (row3 152 150 177), (row3 40 438 413), (row3 318 318 315)]

theorem b029_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_12_rows b029_12_labels 680861989856668628707981050270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_12_rows b029_12_labels]
    decide +kernel

def b029_13_rows : List Row := [(row3 5 14 17), (row3 5 14 18), (row3 5 14 19), (row3 5 14 20), (row3 5 14 21), (row3 5 14 22), (row3 5 14 23), (row3 5 14 24), (row3 5 14 25), (row3 5 14 26), (row3 5 14 27), (row3 5 14 28), (row3 5 14 29), (row3 5 14 30), (row3 5 14 31), (row3 5 14 32)]

def b029_13_labels : List Row := [(row3 234 226 226), (row3 244 244 462), (row3 235 232 228), (row3 320 320 319), (row3 110 109 111), (row3 395 415 407), (row3 120 112 120), (row3 237 226 226), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 236 228 225), (row3 317 317 308), (row3 148 137 145), (row3 310 310 306), (row3 242 242 462)]

theorem b029_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_13_rows b029_13_labels 39333941735169889300538808030 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_13_rows b029_13_labels]
    decide +kernel

def b029_14_rows : List Row := [(row3 5 14 33), (row3 5 14 34), (row3 5 14 35), (row3 5 14 36), (row3 5 14 37), (row3 5 14 38), (row3 5 14 39), (row3 5 14 40), (row3 5 14 41), (row3 5 14 42), (row3 5 14 43), (row3 5 14 44), (row3 5 14 45), (row3 5 14 46), (row3 5 14 47), (row3 5 14 48)]

def b029_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 232 230), (row3 279 279 278), (row3 462 232 232), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 262 262 261), (row3 236 235 233), (row3 243 243 462), (row3 266 266 265)]

theorem b029_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_14_rows b029_14_labels 34035231846457378705519920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_14_rows b029_14_labels]
    decide +kernel

def b029_15_rows : List Row := [(row3 5 14 49), (row3 5 14 50), (row3 5 14 51), (row3 5 14 52), (row3 5 14 53), (row3 5 14 54), (row3 5 14 55), (row3 5 14 56), (row3 5 14 57), (row3 5 14 58), (row3 5 14 59), (row3 5 14 60), (row3 5 14 61), (row3 5 14 62), (row3 5 14 63), (row3 5 15 16)]

def b029_15_labels : List Row := [(row3 234 234 234), (row3 244 244 462), (row3 235 462 235), (row3 279 279 278), (row3 190 197 196), (row3 298 298 295), (row3 229 226 224), (row3 152 150 177), (row3 279 279 278), (row3 231 234 231), (row3 280 280 278), (row3 161 175 175), (row3 376 354 366), (row3 107 106 106), (row3 324 324 323), (row3 110 111 109)]

theorem b029_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b029_15_rows b029_15_labels 26472681961419967572681635070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b029_15_rows b029_15_labels]
    decide +kernel

theorem checked029 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_029 QuarticIntegerComputationalData.ids64_029 1544041592236756778163936673410 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b029_00_rows ++ b029_01_rows) ++ (b029_02_rows ++ b029_03_rows)) ++ ((b029_04_rows ++ b029_05_rows) ++ (b029_06_rows ++ b029_07_rows))) ++ (((b029_08_rows ++ b029_09_rows) ++ (b029_10_rows ++ b029_11_rows)) ++ ((b029_12_rows ++ b029_13_rows) ++ (b029_14_rows ++ b029_15_rows))))
    ((((b029_00_labels ++ b029_01_labels) ++ (b029_02_labels ++ b029_03_labels)) ++ ((b029_04_labels ++ b029_05_labels) ++ (b029_06_labels ++ b029_07_labels))) ++ (((b029_08_labels ++ b029_09_labels) ++ (b029_10_labels ++ b029_11_labels)) ++ ((b029_12_labels ++ b029_13_labels) ++ (b029_14_labels ++ b029_15_labels)))) 1544041592236756778163936673410
  exact ((((b029_00_checked.append (c := 2410142206393591304396843850) b029_01_checked (by decide +kernel)).append (c := 6683182596169385204347545150) (b029_02_checked.append (c := 4273040389775793899950701300) b029_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 118171511745451914086186671830) ((b029_04_checked.append (c := 4654402565387394982035900) b029_05_checked (by decide +kernel)).append (c := 111488329149282528881839126680) (b029_06_checked.append (c := 111483674746717141486857090780) b029_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1544041592236756778163936673410) (((b029_08_checked.append (c := 559259112458234431401222601890) b029_09_checked (by decide +kernel)).append (c := 679167431706199921117842988290) (b029_10_checked.append (c := 119908319247965489716620386400) b029_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1425870080491304864077750001580) ((b029_12_checked.append (c := 720195931591838518008519858300) b029_13_checked (by decide +kernel)).append (c := 746702648785104942959907013290) (b029_14_checked.append (c := 26506717193266424951387154990) b029_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b030_00_rows : List Row := [(row3 5 15 17), (row3 5 15 18), (row3 5 15 19), (row3 5 15 20), (row3 5 15 21), (row3 5 15 22), (row3 5 15 23), (row3 5 15 24), (row3 5 15 25), (row3 5 15 26), (row3 5 15 27), (row3 5 15 28), (row3 5 15 29), (row3 5 15 30), (row3 5 15 31), (row3 5 15 32)]

def b030_00_labels : List Row := [(row3 320 319 320), (row3 235 228 232), (row3 244 462 244), (row3 234 226 226), (row3 318 315 318), (row3 120 120 112), (row3 395 407 415), (row3 317 308 317), (row3 236 225 228), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 226 226), (row3 310 306 310), (row3 148 145 137), (row3 238 230 232)]

theorem b030_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_00_rows b030_00_labels 38513862279382371165298187130 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_00_rows b030_00_labels]
    decide +kernel

def b030_01_rows : List Row := [(row3 5 15 33), (row3 5 15 34), (row3 5 15 35), (row3 5 15 36), (row3 5 15 37), (row3 5 15 38), (row3 5 15 39), (row3 5 15 40), (row3 5 15 41), (row3 5 15 42), (row3 5 15 43), (row3 5 15 44), (row3 5 15 45), (row3 5 15 46), (row3 5 15 47), (row3 5 15 48)]

def b030_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 232 232), (row3 279 278 279), (row3 262 261 262), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 236 233 235), (row3 190 196 197)]

theorem b030_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_01_rows b030_01_labels 105177729579132764678739780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_01_rows b030_01_labels]
    decide +kernel

def b030_02_rows : List Row := [(row3 5 15 49), (row3 5 15 50), (row3 5 15 51), (row3 5 15 52), (row3 5 15 53), (row3 5 15 54), (row3 5 15 55), (row3 5 15 56), (row3 5 15 57), (row3 5 15 58), (row3 5 15 59), (row3 5 15 60), (row3 5 15 61), (row3 5 15 62), (row3 5 15 63), (row3 5 16 17)]

def b030_02_labels : List Row := [(row3 279 278 279), (row3 235 235 462), (row3 244 462 244), (row3 234 234 234), (row3 266 265 266), (row3 229 224 226), (row3 298 295 298), (row3 376 366 354), (row3 161 175 175), (row3 280 278 280), (row3 231 231 234), (row3 279 278 279), (row3 152 177 150), (row3 324 323 324), (row3 107 106 106), (row3 266 265 266)]

theorem b030_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_02_rows b030_02_labels 25494750879968765076371115870 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_02_rows b030_02_labels]
    decide +kernel

def b030_03_rows : List Row := [(row3 5 16 18), (row3 5 16 19), (row3 5 16 20), (row3 5 16 21), (row3 5 16 22), (row3 5 16 23), (row3 5 16 24), (row3 5 16 25), (row3 5 16 26), (row3 5 16 27), (row3 5 16 28), (row3 5 16 29), (row3 5 16 30), (row3 5 16 31), (row3 5 16 32), (row3 5 16 33)]

def b030_03_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 302 265 302), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 239 239 462), (row3 462 462 462)]

theorem b030_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_03_rows b030_03_labels 169571993875269435781160700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_03_rows b030_03_labels]
    decide +kernel

def b030_04_rows : List Row := [(row3 5 16 34), (row3 5 16 35), (row3 5 16 36), (row3 5 16 37), (row3 5 16 38), (row3 5 16 39), (row3 5 16 40), (row3 5 16 41), (row3 5 16 42), (row3 5 16 43), (row3 5 16 44), (row3 5 16 45), (row3 5 16 46), (row3 5 16 47), (row3 5 16 48), (row3 5 16 49)]

def b030_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 206 210 210), (row3 266 265 266)]

theorem b030_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_04_rows b030_04_labels 31562572869564522820256640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_04_rows b030_04_labels]
    decide +kernel

def b030_05_rows : List Row := [(row3 5 16 50), (row3 5 16 51), (row3 5 16 52), (row3 5 16 53), (row3 5 16 54), (row3 5 16 55), (row3 5 16 56), (row3 5 16 57), (row3 5 16 58), (row3 5 16 59), (row3 5 16 60), (row3 5 16 61), (row3 5 16 62), (row3 5 16 63), (row3 5 17 18), (row3 5 17 19)]

def b030_05_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 266 265 266), (row3 343 338 330), (row3 190 199 198), (row3 266 265 266), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 266 265 266), (row3 190 197 196), (row3 244 244 462), (row3 462 462 462)]

theorem b030_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_05_rows b030_05_labels 5118662274916774507801899570 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_05_rows b030_05_labels]
    decide +kernel

def b030_06_rows : List Row := [(row3 5 17 20), (row3 5 17 21), (row3 5 17 22), (row3 5 17 23), (row3 5 17 24), (row3 5 17 25), (row3 5 17 26), (row3 5 17 27), (row3 5 17 28), (row3 5 17 29), (row3 5 17 30), (row3 5 17 31), (row3 5 17 32), (row3 5 17 33), (row3 5 17 34), (row3 5 17 35)]

def b030_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 228 234 228), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_06_rows b030_06_labels 1697035069576683489073500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_06_rows b030_06_labels]
    decide +kernel

def b030_07_rows : List Row := [(row3 5 17 36), (row3 5 17 37), (row3 5 17 38), (row3 5 17 39), (row3 5 17 40), (row3 5 17 41), (row3 5 17 42), (row3 5 17 43), (row3 5 17 44), (row3 5 17 45), (row3 5 17 46), (row3 5 17 47), (row3 5 17 48), (row3 5 17 49), (row3 5 17 50), (row3 5 17 51)]

def b030_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 244 244 462), (row3 462 462 462)]

theorem b030_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_07_rows b030_07_labels 3672563711402662875171900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_07_rows b030_07_labels]
    decide +kernel

def b030_08_rows : List Row := [(row3 5 17 52), (row3 5 17 53), (row3 5 17 54), (row3 5 17 55), (row3 5 17 56), (row3 5 17 57), (row3 5 17 58), (row3 5 17 59), (row3 5 17 60), (row3 5 17 61), (row3 5 17 62), (row3 5 17 63), (row3 5 18 19), (row3 5 18 20), (row3 5 18 21), (row3 5 18 22)]

def b030_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 234), (row3 154 154 180), (row3 279 279 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 279 279 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_08_rows b030_08_labels 819450887420550863159264700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_08_rows b030_08_labels]
    decide +kernel

def b030_09_rows : List Row := [(row3 5 18 23), (row3 5 18 24), (row3 5 18 25), (row3 5 18 26), (row3 5 18 27), (row3 5 18 28), (row3 5 18 29), (row3 5 18 30), (row3 5 18 31), (row3 5 18 32), (row3 5 18 33), (row3 5 18 34), (row3 5 18 35), (row3 5 18 36), (row3 5 18 37), (row3 5 18 38)]

def b030_09_labels : List Row := [(row3 246 462 246), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_09_rows b030_09_labels 29071872849896485087500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_09_rows b030_09_labels]
    decide +kernel

def b030_10_rows : List Row := [(row3 5 18 39), (row3 5 18 40), (row3 5 18 41), (row3 5 18 42), (row3 5 18 43), (row3 5 18 44), (row3 5 18 45), (row3 5 18 46), (row3 5 18 47), (row3 5 18 48), (row3 5 18 49), (row3 5 18 50), (row3 5 18 51), (row3 5 18 52), (row3 5 18 53), (row3 5 18 54)]

def b030_10_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_10_rows b030_10_labels 137412394719263575938000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_10_rows b030_10_labels]
    decide +kernel

def b030_11_rows : List Row := [(row3 5 18 55), (row3 5 18 56), (row3 5 18 57), (row3 5 18 58), (row3 5 18 59), (row3 5 18 60), (row3 5 18 61), (row3 5 18 62), (row3 5 18 63), (row3 5 19 20), (row3 5 19 21), (row3 5 19 22), (row3 5 19 23), (row3 5 19 24), (row3 5 19 25), (row3 5 19 26)]

def b030_11_labels : List Row := [(row3 244 462 244), (row3 269 462 269), (row3 235 462 235), (row3 245 462 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 244 244 462), (row3 237 237 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_11_rows b030_11_labels 30970051128574387841056500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_11_rows b030_11_labels]
    decide +kernel

def b030_12_rows : List Row := [(row3 5 19 27), (row3 5 19 28), (row3 5 19 29), (row3 5 19 30), (row3 5 19 31), (row3 5 19 32), (row3 5 19 33), (row3 5 19 34), (row3 5 19 35), (row3 5 19 36), (row3 5 19 37), (row3 5 19 38), (row3 5 19 39), (row3 5 19 40), (row3 5 19 41), (row3 5 19 42)]

def b030_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_12_rows b030_12_labels 4248890416128681112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_12_rows b030_12_labels]
    decide +kernel

def b030_13_rows : List Row := [(row3 5 19 43), (row3 5 19 44), (row3 5 19 45), (row3 5 19 46), (row3 5 19 47), (row3 5 19 48), (row3 5 19 49), (row3 5 19 50), (row3 5 19 51), (row3 5 19 52), (row3 5 19 53), (row3 5 19 54), (row3 5 19 55), (row3 5 19 56), (row3 5 19 57), (row3 5 19 58)]

def b030_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b030_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_13_rows b030_13_labels 148902545254618432525500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_13_rows b030_13_labels]
    decide +kernel

def b030_14_rows : List Row := [(row3 5 19 59), (row3 5 19 60), (row3 5 19 61), (row3 5 19 62), (row3 5 19 63), (row3 5 20 21), (row3 5 20 22), (row3 5 20 23), (row3 5 20 24), (row3 5 20 25), (row3 5 20 26), (row3 5 20 27), (row3 5 20 28), (row3 5 20 29), (row3 5 20 30), (row3 5 20 31)]

def b030_14_labels : List Row := [(row3 245 245 462), (row3 235 235 462), (row3 269 269 462), (row3 235 235 462), (row3 244 244 462), (row3 266 265 266), (row3 228 228 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462)]

theorem b030_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_14_rows b030_14_labels 75027789343768828864419900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_14_rows b030_14_labels]
    decide +kernel

def b030_15_rows : List Row := [(row3 5 20 32), (row3 5 20 33), (row3 5 20 34), (row3 5 20 35), (row3 5 20 36), (row3 5 20 37), (row3 5 20 38), (row3 5 20 39), (row3 5 20 40), (row3 5 20 41), (row3 5 20 42), (row3 5 20 43), (row3 5 20 44), (row3 5 20 45), (row3 5 20 46), (row3 5 20 47)]

def b030_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462)]

theorem b030_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b030_15_rows b030_15_labels 118258334123876463262500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b030_15_rows b030_15_labels]
    decide +kernel

theorem checked030 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_030 QuarticIntegerComputationalData.ids64_030 70364843951303114682618272190 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b030_00_rows ++ b030_01_rows) ++ (b030_02_rows ++ b030_03_rows)) ++ ((b030_04_rows ++ b030_05_rows) ++ (b030_06_rows ++ b030_07_rows))) ++ (((b030_08_rows ++ b030_09_rows) ++ (b030_10_rows ++ b030_11_rows)) ++ ((b030_12_rows ++ b030_13_rows) ++ (b030_14_rows ++ b030_15_rows))))
    ((((b030_00_labels ++ b030_01_labels) ++ (b030_02_labels ++ b030_03_labels)) ++ ((b030_04_labels ++ b030_05_labels) ++ (b030_06_labels ++ b030_07_labels))) ++ (((b030_08_labels ++ b030_09_labels) ++ (b030_10_labels ++ b030_11_labels)) ++ ((b030_12_labels ++ b030_13_labels) ++ (b030_14_labels ++ b030_15_labels)))) 70364843951303114682618272190
  exact ((((b030_00_checked.append (c := 38619040008961503929976926910) b030_01_checked (by decide +kernel)).append (c := 64283362882805538442129203480) (b030_02_checked.append (c := 25664322873844034512152276570) b030_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 69438957329372856819115605090) ((b030_04_checked.append (c := 5150224847786339030622156210) b030_05_checked (by decide +kernel)).append (c := 5155594446567318376986401610) (b030_06_checked.append (c := 5369598780979346364245400) b030_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 70364843951303114682618272190) (((b030_08_checked.append (c := 819479959293400759644352200) b030_09_checked (by decide +kernel)).append (c := 850587422816694411061346700) (b030_10_checked.append (c := 31107463523293651416994500) b030_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 925886621930257863502667100) ((b030_12_checked.append (c := 153151435670747113638000) b030_13_checked (by decide +kernel)).append (c := 75299199113563452441320400) (b030_14_checked.append (c := 75146047677892705327682400) b030_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b031_00_rows : List Row := [(row3 5 20 48), (row3 5 20 49), (row3 5 20 50), (row3 5 20 51), (row3 5 20 52), (row3 5 20 53), (row3 5 20 54), (row3 5 20 55), (row3 5 20 56), (row3 5 20 57), (row3 5 20 58), (row3 5 20 59), (row3 5 20 60), (row3 5 20 61), (row3 5 20 62), (row3 5 20 63)]

def b031_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234), (row3 244 462 244), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 234 234 234), (row3 279 278 279), (row3 154 180 154), (row3 279 278 279), (row3 234 234 234)]

theorem b031_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_00_rows b031_00_labels 823009944188689630235436600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_00_rows b031_00_labels]
    decide +kernel

def b031_01_rows : List Row := [(row3 5 21 22), (row3 5 21 23), (row3 5 21 24), (row3 5 21 25), (row3 5 21 26), (row3 5 21 27), (row3 5 21 28), (row3 5 21 29), (row3 5 21 30), (row3 5 21 31), (row3 5 21 32), (row3 5 21 33), (row3 5 21 34), (row3 5 21 35), (row3 5 21 36), (row3 5 21 37)]

def b031_01_labels : List Row := [(row3 302 302 265), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239)]

theorem b031_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_01_rows b031_01_labels 169362719449501874106290700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_01_rows b031_01_labels]
    decide +kernel

def b031_02_rows : List Row := [(row3 5 21 38), (row3 5 21 39), (row3 5 21 40), (row3 5 21 41), (row3 5 21 42), (row3 5 21 43), (row3 5 21 44), (row3 5 21 45), (row3 5 21 46), (row3 5 21 47), (row3 5 21 48), (row3 5 21 49), (row3 5 21 50), (row3 5 21 51), (row3 5 21 52), (row3 5 21 53)]

def b031_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 266 266 265), (row3 206 210 210)]

theorem b031_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_02_rows b031_02_labels 31685167564013831903894640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_02_rows b031_02_labels]
    decide +kernel

def b031_03_rows : List Row := [(row3 5 21 54), (row3 5 21 55), (row3 5 21 56), (row3 5 21 57), (row3 5 21 58), (row3 5 21 59), (row3 5 21 60), (row3 5 21 61), (row3 5 21 62), (row3 5 21 63), (row3 5 22 23), (row3 5 22 24), (row3 5 22 25), (row3 5 22 26), (row3 5 22 27), (row3 5 22 28)]

def b031_03_labels : List Row := [(row3 266 266 265), (row3 237 462 237), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 266 266 265), (row3 190 198 199), (row3 343 330 338), (row3 190 196 197), (row3 266 266 265), (row3 119 11 216), (row3 249 462 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 462 250)]

theorem b031_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_03_rows b031_03_labels 7076863484378186210135342820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_03_rows b031_03_labels]
    decide +kernel

def b031_04_rows : List Row := [(row3 5 22 29), (row3 5 22 30), (row3 5 22 31), (row3 5 22 32), (row3 5 22 33), (row3 5 22 34), (row3 5 22 35), (row3 5 22 36), (row3 5 22 37), (row3 5 22 38), (row3 5 22 39), (row3 5 22 40), (row3 5 22 41), (row3 5 22 42), (row3 5 22 43), (row3 5 22 44)]

def b031_04_labels : List Row := [(row3 226 237 226), (row3 294 462 294), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 462 249), (row3 234 462 234), (row3 248 462 248), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b031_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_04_rows b031_04_labels 112457220893712236343361500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_04_rows b031_04_labels]
    decide +kernel

def b031_05_rows : List Row := [(row3 5 22 45), (row3 5 22 46), (row3 5 22 47), (row3 5 22 48), (row3 5 22 49), (row3 5 22 50), (row3 5 22 51), (row3 5 22 52), (row3 5 22 53), (row3 5 22 54), (row3 5 22 55), (row3 5 22 56), (row3 5 22 57), (row3 5 22 58), (row3 5 22 59), (row3 5 22 60)]

def b031_05_labels : List Row := [(row3 237 237 237), (row3 245 462 245), (row3 462 462 462), (row3 237 462 237), (row3 244 462 244), (row3 462 462 462), (row3 244 462 244), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234), (row3 246 462 246), (row3 271 462 271), (row3 235 462 235), (row3 245 462 245), (row3 234 234 234), (row3 279 278 279)]

theorem b031_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_05_rows b031_05_labels 63852195096022659229516500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_05_rows b031_05_labels]
    decide +kernel

def b031_06_rows : List Row := [(row3 5 22 61), (row3 5 22 62), (row3 5 22 63), (row3 5 23 24), (row3 5 23 25), (row3 5 23 26), (row3 5 23 27), (row3 5 23 28), (row3 5 23 29), (row3 5 23 30), (row3 5 23 31), (row3 5 23 32), (row3 5 23 33), (row3 5 23 34), (row3 5 23 35), (row3 5 23 36)]

def b031_06_labels : List Row := [(row3 154 180 154), (row3 298 295 298), (row3 229 226 224), (row3 226 226 237), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 249 462), (row3 228 228 462), (row3 294 294 462), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_06_rows b031_06_labels 933650996988501960580348200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_06_rows b031_06_labels]
    decide +kernel

def b031_07_rows : List Row := [(row3 5 23 37), (row3 5 23 38), (row3 5 23 39), (row3 5 23 40), (row3 5 23 41), (row3 5 23 42), (row3 5 23 43), (row3 5 23 44), (row3 5 23 45), (row3 5 23 46), (row3 5 23 47), (row3 5 23 48), (row3 5 23 49), (row3 5 23 50), (row3 5 23 51), (row3 5 23 52)]

def b031_07_labels : List Row := [(row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 245 245 462), (row3 266 266 265), (row3 234 234 234), (row3 244 244 462), (row3 462 462 462), (row3 244 244 462)]

theorem b031_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_07_rows b031_07_labels 4200320046398669217837900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_07_rows b031_07_labels]
    decide +kernel

def b031_08_rows : List Row := [(row3 5 23 53), (row3 5 23 54), (row3 5 23 55), (row3 5 23 56), (row3 5 23 57), (row3 5 23 58), (row3 5 23 59), (row3 5 23 60), (row3 5 23 61), (row3 5 23 62), (row3 5 23 63), (row3 5 24 25), (row3 5 24 26), (row3 5 24 27), (row3 5 24 28), (row3 5 24 29)]

def b031_08_labels : List Row := [(row3 237 237 462), (row3 246 246 462), (row3 234 234 234), (row3 154 154 180), (row3 279 279 278), (row3 234 234 234), (row3 245 245 462), (row3 235 235 462), (row3 271 271 462), (row3 229 224 226), (row3 298 298 295), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_08_rows b031_08_labels 881828390543318079134659800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_08_rows b031_08_labels]
    decide +kernel

def b031_09_rows : List Row := [(row3 5 24 30), (row3 5 24 31), (row3 5 24 32), (row3 5 24 33), (row3 5 24 34), (row3 5 24 35), (row3 5 24 36), (row3 5 24 37), (row3 5 24 38), (row3 5 24 39), (row3 5 24 40), (row3 5 24 41), (row3 5 24 42), (row3 5 24 43), (row3 5 24 44), (row3 5 24 45)]

def b031_09_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 240 240 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 239), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_09_rows b031_09_labels 174780636655779540667500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_09_rows b031_09_labels]
    decide +kernel

def b031_10_rows : List Row := [(row3 5 24 46), (row3 5 24 47), (row3 5 24 48), (row3 5 24 49), (row3 5 24 50), (row3 5 24 51), (row3 5 24 52), (row3 5 24 53), (row3 5 24 54), (row3 5 24 55), (row3 5 24 56), (row3 5 24 57), (row3 5 24 58), (row3 5 24 59), (row3 5 24 60), (row3 5 24 61)]

def b031_10_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 256 256 255), (row3 237 237 237), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 237 237 237), (row3 201 201 208), (row3 262 262 261), (row3 237 237 237), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462)]

theorem b031_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_10_rows b031_10_labels 268361543011024615452084000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_10_rows b031_10_labels]
    decide +kernel

def b031_11_rows : List Row := [(row3 5 24 62), (row3 5 24 63), (row3 5 25 26), (row3 5 25 27), (row3 5 25 28), (row3 5 25 29), (row3 5 25 30), (row3 5 25 31), (row3 5 25 32), (row3 5 25 33), (row3 5 25 34), (row3 5 25 35), (row3 5 25 36), (row3 5 25 37), (row3 5 25 38), (row3 5 25 39)]

def b031_11_labels : List Row := [(row3 237 237 237), (row3 262 262 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_11_rows b031_11_labels 3595135037315733356383200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_11_rows b031_11_labels]
    decide +kernel

def b031_12_rows : List Row := [(row3 5 25 40), (row3 5 25 41), (row3 5 25 42), (row3 5 25 43), (row3 5 25 44), (row3 5 25 45), (row3 5 25 46), (row3 5 25 47), (row3 5 25 48), (row3 5 25 49), (row3 5 25 50), (row3 5 25 51), (row3 5 25 52), (row3 5 25 53), (row3 5 25 54), (row3 5 25 55)]

def b031_12_labels : List Row := [(row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b031_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_12_rows b031_12_labels 100496817745117682217000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_12_rows b031_12_labels]
    decide +kernel

def b031_13_rows : List Row := [(row3 5 25 56), (row3 5 25 57), (row3 5 25 58), (row3 5 25 59), (row3 5 25 60), (row3 5 25 61), (row3 5 25 62), (row3 5 25 63), (row3 5 26 27), (row3 5 26 28), (row3 5 26 29), (row3 5 26 30), (row3 5 26 31), (row3 5 26 32), (row3 5 26 33), (row3 5 26 34)]

def b031_13_labels : List Row := [(row3 263 462 263), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_13_rows b031_13_labels 20262190627645072468341000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_13_rows b031_13_labels]
    decide +kernel

def b031_14_rows : List Row := [(row3 5 26 35), (row3 5 26 36), (row3 5 26 37), (row3 5 26 38), (row3 5 26 39), (row3 5 26 40), (row3 5 26 41), (row3 5 26 42), (row3 5 26 43), (row3 5 26 44), (row3 5 26 45), (row3 5 26 46), (row3 5 26 47), (row3 5 26 48), (row3 5 26 49), (row3 5 26 50)]

def b031_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_14_rows b031_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_14_rows b031_14_labels]
    decide +kernel

def b031_15_rows : List Row := [(row3 5 26 51), (row3 5 26 52), (row3 5 26 53), (row3 5 26 54), (row3 5 26 55), (row3 5 26 56), (row3 5 26 57), (row3 5 26 58), (row3 5 26 59), (row3 5 26 60), (row3 5 26 61), (row3 5 26 62), (row3 5 26 63), (row3 5 27 28), (row3 5 27 29), (row3 5 27 30)]

def b031_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b031_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b031_15_rows b031_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b031_15_rows b031_15_labels]
    decide +kernel

theorem checked031 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_031 QuarticIntegerComputationalData.ids64_031 10389404585278731469386381360 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b031_00_rows ++ b031_01_rows) ++ (b031_02_rows ++ b031_03_rows)) ++ ((b031_04_rows ++ b031_05_rows) ++ (b031_06_rows ++ b031_07_rows))) ++ (((b031_08_rows ++ b031_09_rows) ++ (b031_10_rows ++ b031_11_rows)) ++ ((b031_12_rows ++ b031_13_rows) ++ (b031_14_rows ++ b031_15_rows))))
    ((((b031_00_labels ++ b031_01_labels) ++ (b031_02_labels ++ b031_03_labels)) ++ ((b031_04_labels ++ b031_05_labels) ++ (b031_06_labels ++ b031_07_labels))) ++ (((b031_08_labels ++ b031_09_labels) ++ (b031_10_labels ++ b031_11_labels)) ++ ((b031_12_labels ++ b031_13_labels) ++ (b031_14_labels ++ b031_15_labels)))) 10389404585278731469386381360
  exact ((((b031_00_checked.append (c := 992372663638191504341727300) b031_01_checked (by decide +kernel)).append (c := 8100921315580391546380964760) (b031_02_checked.append (c := 7108548651942200042039237460) b031_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 9215082048605027071752028860) ((b031_04_checked.append (c := 176309415989734895572878000) b031_05_checked (by decide +kernel)).append (c := 1114160733024635525371064100) (b031_06_checked.append (c := 937851317034900629798186100) b031_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 10389404585278731469386381360) (((b031_08_checked.append (c := 882003171179973858675327300) b031_09_checked (by decide +kernel)).append (c := 1153959849228314207483794500) (b031_10_checked.append (c := 271956678048340348808467200) b031_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1174322536673704397634352500) ((b031_12_checked.append (c := 20362687445390190150558000) b031_13_checked (by decide +kernel)).append (c := 20362687445390190150558000) (b031_14_checked.append (c := 0) b031_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b032_00_rows : List Row := [(row3 5 27 31), (row3 5 27 32), (row3 5 27 33), (row3 5 27 34), (row3 5 27 35), (row3 5 27 36), (row3 5 27 37), (row3 5 27 38), (row3 5 27 39), (row3 5 27 40), (row3 5 27 41), (row3 5 27 42), (row3 5 27 43), (row3 5 27 44), (row3 5 27 45), (row3 5 27 46)]

def b032_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_00_rows b032_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_00_rows b032_00_labels]
    decide +kernel

def b032_01_rows : List Row := [(row3 5 27 47), (row3 5 27 48), (row3 5 27 49), (row3 5 27 50), (row3 5 27 51), (row3 5 27 52), (row3 5 27 53), (row3 5 27 54), (row3 5 27 55), (row3 5 27 56), (row3 5 27 57), (row3 5 27 58), (row3 5 27 59), (row3 5 27 60), (row3 5 27 61), (row3 5 27 62)]

def b032_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_01_rows b032_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_01_rows b032_01_labels]
    decide +kernel

def b032_02_rows : List Row := [(row3 5 27 63), (row3 5 28 29), (row3 5 28 30), (row3 5 28 31), (row3 5 28 32), (row3 5 28 33), (row3 5 28 34), (row3 5 28 35), (row3 5 28 36), (row3 5 28 37), (row3 5 28 38), (row3 5 28 39), (row3 5 28 40), (row3 5 28 41), (row3 5 28 42), (row3 5 28 43)]

def b032_02_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_02_rows b032_02_labels 71216546417574934875000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_02_rows b032_02_labels]
    decide +kernel

def b032_03_rows : List Row := [(row3 5 28 44), (row3 5 28 45), (row3 5 28 46), (row3 5 28 47), (row3 5 28 48), (row3 5 28 49), (row3 5 28 50), (row3 5 28 51), (row3 5 28 52), (row3 5 28 53), (row3 5 28 54), (row3 5 28 55), (row3 5 28 56), (row3 5 28 57), (row3 5 28 58), (row3 5 28 59)]

def b032_03_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462)]

theorem b032_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_03_rows b032_03_labels 108156918102020919942000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_03_rows b032_03_labels]
    decide +kernel

def b032_04_rows : List Row := [(row3 5 28 60), (row3 5 28 61), (row3 5 28 62), (row3 5 28 63), (row3 5 29 30), (row3 5 29 31), (row3 5 29 32), (row3 5 29 33), (row3 5 29 34), (row3 5 29 35), (row3 5 29 36), (row3 5 29 37), (row3 5 29 38), (row3 5 29 39), (row3 5 29 40), (row3 5 29 41)]

def b032_04_labels : List Row := [(row3 236 236 462), (row3 263 263 462), (row3 236 236 462), (row3 243 243 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_04_rows b032_04_labels 20361355346914531632928500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_04_rows b032_04_labels]
    decide +kernel

def b032_05_rows : List Row := [(row3 5 29 42), (row3 5 29 43), (row3 5 29 44), (row3 5 29 45), (row3 5 29 46), (row3 5 29 47), (row3 5 29 48), (row3 5 29 49), (row3 5 29 50), (row3 5 29 51), (row3 5 29 52), (row3 5 29 53), (row3 5 29 54), (row3 5 29 55), (row3 5 29 56), (row3 5 29 57)]

def b032_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 239 239 239), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 237 237 237), (row3 256 255 256), (row3 237 237 237), (row3 242 462 242), (row3 241 462 241), (row3 462 462 462)]

theorem b032_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_05_rows b032_05_labels 1394134929384197170468800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_05_rows b032_05_labels]
    decide +kernel

def b032_06_rows : List Row := [(row3 5 29 58), (row3 5 29 59), (row3 5 29 60), (row3 5 29 61), (row3 5 29 62), (row3 5 29 63), (row3 5 30 31), (row3 5 30 32), (row3 5 30 33), (row3 5 30 34), (row3 5 30 35), (row3 5 30 36), (row3 5 30 37), (row3 5 30 38), (row3 5 30 39), (row3 5 30 40)]

def b032_06_labels : List Row := [(row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 201 208 201), (row3 262 261 262), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_06_rows b032_06_labels 270630498935985568776353400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_06_rows b032_06_labels]
    decide +kernel

def b032_07_rows : List Row := [(row3 5 30 41), (row3 5 30 42), (row3 5 30 43), (row3 5 30 44), (row3 5 30 45), (row3 5 30 46), (row3 5 30 47), (row3 5 30 48), (row3 5 30 49), (row3 5 30 50), (row3 5 30 51), (row3 5 30 52), (row3 5 30 53), (row3 5 30 54), (row3 5 30 55), (row3 5 30 56)]

def b032_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_07_rows b032_07_labels 112908308962001584204500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_07_rows b032_07_labels]
    decide +kernel

def b032_08_rows : List Row := [(row3 5 30 57), (row3 5 30 58), (row3 5 30 59), (row3 5 30 60), (row3 5 30 61), (row3 5 30 62), (row3 5 30 63), (row3 5 31 32), (row3 5 31 33), (row3 5 31 34), (row3 5 31 35), (row3 5 31 36), (row3 5 31 37), (row3 5 31 38), (row3 5 31 39), (row3 5 31 40)]

def b032_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 263 263 462), (row3 236 233 235), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241)]

theorem b032_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_08_rows b032_08_labels 20673143354069010106248000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_08_rows b032_08_labels]
    decide +kernel

def b032_09_rows : List Row := [(row3 5 31 41), (row3 5 31 42), (row3 5 31 43), (row3 5 31 44), (row3 5 31 45), (row3 5 31 46), (row3 5 31 47), (row3 5 31 48), (row3 5 31 49), (row3 5 31 50), (row3 5 31 51), (row3 5 31 52), (row3 5 31 53), (row3 5 31 54), (row3 5 31 55), (row3 5 31 56)]

def b032_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 462 245), (row3 263 462 263)]

theorem b032_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_09_rows b032_09_labels 19824041975140552633804500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_09_rows b032_09_labels]
    decide +kernel

def b032_10_rows : List Row := [(row3 5 31 57), (row3 5 31 58), (row3 5 31 59), (row3 5 31 60), (row3 5 31 61), (row3 5 31 62), (row3 5 31 63), (row3 5 32 33), (row3 5 32 34), (row3 5 32 35), (row3 5 32 36), (row3 5 32 37), (row3 5 32 38), (row3 5 32 39), (row3 5 32 40), (row3 5 32 41)]

def b032_10_labels : List Row := [(row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 235 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 462 462 462)]

theorem b032_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_10_rows b032_10_labels 991952773877741615935500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_10_rows b032_10_labels]
    decide +kernel

def b032_11_rows : List Row := [(row3 5 32 42), (row3 5 32 43), (row3 5 32 44), (row3 5 32 45), (row3 5 32 46), (row3 5 32 47), (row3 5 32 48), (row3 5 32 49), (row3 5 32 50), (row3 5 32 51), (row3 5 32 52), (row3 5 32 53), (row3 5 32 54), (row3 5 32 55), (row3 5 32 56), (row3 5 32 57)]

def b032_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 462 249), (row3 254 8 203), (row3 238 462 238)]

theorem b032_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_11_rows b032_11_labels 170527548699625427061534000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_11_rows b032_11_labels]
    decide +kernel

def b032_12_rows : List Row := [(row3 5 32 58), (row3 5 32 59), (row3 5 32 60), (row3 5 32 61), (row3 5 32 62), (row3 5 32 63), (row3 5 33 34), (row3 5 33 35), (row3 5 33 36), (row3 5 33 37), (row3 5 33 38), (row3 5 33 39), (row3 5 33 40), (row3 5 33 41), (row3 5 33 42), (row3 5 33 43)]

def b032_12_labels : List Row := [(row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 238 232 230), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_12_rows b032_12_labels 961347411497120886153000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_12_rows b032_12_labels]
    decide +kernel

def b032_13_rows : List Row := [(row3 5 33 44), (row3 5 33 45), (row3 5 33 46), (row3 5 33 47), (row3 5 33 48), (row3 5 33 49), (row3 5 33 50), (row3 5 33 51), (row3 5 33 52), (row3 5 33 53), (row3 5 33 54), (row3 5 33 55), (row3 5 33 56), (row3 5 33 57), (row3 5 33 58), (row3 5 33 59)]

def b032_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_13_rows b032_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_13_rows b032_13_labels]
    decide +kernel

def b032_14_rows : List Row := [(row3 5 33 60), (row3 5 33 61), (row3 5 33 62), (row3 5 33 63), (row3 5 34 35), (row3 5 34 36), (row3 5 34 37), (row3 5 34 38), (row3 5 34 39), (row3 5 34 40), (row3 5 34 41), (row3 5 34 42), (row3 5 34 43), (row3 5 34 44), (row3 5 34 45), (row3 5 34 46)]

def b032_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_14_rows b032_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_14_rows b032_14_labels]
    decide +kernel

def b032_15_rows : List Row := [(row3 5 34 47), (row3 5 34 48), (row3 5 34 49), (row3 5 34 50), (row3 5 34 51), (row3 5 34 52), (row3 5 34 53), (row3 5 34 54), (row3 5 34 55), (row3 5 34 56), (row3 5 34 57), (row3 5 34 58), (row3 5 34 59), (row3 5 34 60), (row3 5 34 61), (row3 5 34 62)]

def b032_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b032_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b032_15_rows b032_15_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b032_15_rows b032_15_labels]
    decide +kernel

theorem checked032 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_032 QuarticIntegerComputationalData.ids64_032 505664579527453669923772200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b032_00_rows ++ b032_01_rows) ++ (b032_02_rows ++ b032_03_rows)) ++ ((b032_04_rows ++ b032_05_rows) ++ (b032_06_rows ++ b032_07_rows))) ++ (((b032_08_rows ++ b032_09_rows) ++ (b032_10_rows ++ b032_11_rows)) ++ ((b032_12_rows ++ b032_13_rows) ++ (b032_14_rows ++ b032_15_rows))))
    ((((b032_00_labels ++ b032_01_labels) ++ (b032_02_labels ++ b032_03_labels)) ++ ((b032_04_labels ++ b032_05_labels) ++ (b032_06_labels ++ b032_07_labels))) ++ (((b032_08_labels ++ b032_09_labels) ++ (b032_10_labels ++ b032_11_labels)) ++ ((b032_12_labels ++ b032_13_labels) ++ (b032_14_labels ++ b032_15_labels)))) 505664579527453669923772200
  exact ((((b032_00_checked.append (c := 0) b032_01_checked (by decide +kernel)).append (c := 179373464519595854817000) (b032_02_checked.append (c := 179373464519595854817000) b032_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 292678270985765895018772200) ((b032_04_checked.append (c := 21755490276298728803397300) b032_05_checked (by decide +kernel)).append (c := 292498897521246299163955200) (b032_06_checked.append (c := 270743407244947570360557900) b032_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 505664579527453669923772200) (((b032_08_checked.append (c := 40497185329209562740052500) b032_09_checked (by decide +kernel)).append (c := 212016686802712731417522000) (b032_10_checked.append (c := 171519501473503168677469500) b032_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 212986308541687774905000000) ((b032_12_checked.append (c := 961347411497120886153000) b032_13_checked (by decide +kernel)).append (c := 969621738975043487478000) (b032_14_checked.append (c := 8274327477922601325000) b032_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
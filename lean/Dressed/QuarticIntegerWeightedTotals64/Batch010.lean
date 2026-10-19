import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch009
import Dressed.QuarticIntegerComputationalData64.Batch010


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b081_00_rows : List Row := [(row3 14 30 41), (row3 14 30 42), (row3 14 30 43), (row3 14 30 44), (row3 14 30 45), (row3 14 30 46), (row3 14 30 47), (row3 14 30 48), (row3 14 30 49), (row3 14 30 50), (row3 14 30 51), (row3 14 30 52), (row3 14 30 53), (row3 14 30 54), (row3 14 30 55), (row3 14 30 56)]

def b081_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 267 267 265), (row3 235 462 235), (row3 234 462 234)]

theorem b081_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_00_rows b081_00_labels 24884424883147006062198900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_00_rows b081_00_labels]
    decide +kernel

def b081_01_rows : List Row := [(row3 14 30 57), (row3 14 30 58), (row3 14 30 59), (row3 14 30 60), (row3 14 30 61), (row3 14 30 62), (row3 14 30 63), (row3 14 31 32), (row3 14 31 33), (row3 14 31 34), (row3 14 31 35), (row3 14 31 36), (row3 14 31 37), (row3 14 31 38), (row3 14 31 39), (row3 14 31 40)]

def b081_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 291 291 289), (row3 178 183 183), (row3 291 291 289), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 462 251), (row3 226 234 226), (row3 286 462 286), (row3 247 462 247)]

theorem b081_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_01_rows b081_01_labels 276887937564301949727324120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_01_rows b081_01_labels]
    decide +kernel

def b081_02_rows : List Row := [(row3 14 31 41), (row3 14 31 42), (row3 14 31 43), (row3 14 31 44), (row3 14 31 45), (row3 14 31 46), (row3 14 31 47), (row3 14 31 48), (row3 14 31 49), (row3 14 31 50), (row3 14 31 51), (row3 14 31 52), (row3 14 31 53), (row3 14 31 54), (row3 14 31 55), (row3 14 31 56)]

def b081_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 235 462 235), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 252 462 252), (row3 287 462 287)]

theorem b081_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_02_rows b081_02_labels 100658342731129071450300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_02_rows b081_02_labels]
    decide +kernel

def b081_03_rows : List Row := [(row3 14 31 57), (row3 14 31 58), (row3 14 31 59), (row3 14 31 60), (row3 14 31 61), (row3 14 31 62), (row3 14 31 63), (row3 14 32 33), (row3 14 32 34), (row3 14 32 35), (row3 14 32 36), (row3 14 32 37), (row3 14 32 38), (row3 14 32 39), (row3 14 32 40), (row3 14 32 41)]

def b081_03_labels : List Row := [(row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 292 289 292), (row3 221 222 220), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462)]

theorem b081_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_03_rows b081_03_labels 19884107945926298247244200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_03_rows b081_03_labels]
    decide +kernel

def b081_04_rows : List Row := [(row3 14 32 42), (row3 14 32 43), (row3 14 32 44), (row3 14 32 45), (row3 14 32 46), (row3 14 32 47), (row3 14 32 48), (row3 14 32 49), (row3 14 32 50), (row3 14 32 51), (row3 14 32 52), (row3 14 32 53), (row3 14 32 54), (row3 14 32 55), (row3 14 32 56), (row3 14 32 57)]

def b081_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 218 10 170), (row3 235 462 235)]

theorem b081_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_04_rows b081_04_labels 535439045898112649482563750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_04_rows b081_04_labels]
    decide +kernel

def b081_05_rows : List Row := [(row3 14 32 58), (row3 14 32 59), (row3 14 32 60), (row3 14 32 61), (row3 14 32 62), (row3 14 32 63), (row3 14 33 34), (row3 14 33 35), (row3 14 33 36), (row3 14 33 37), (row3 14 33 38), (row3 14 33 39), (row3 14 33 40), (row3 14 33 41), (row3 14 33 42), (row3 14 33 43)]

def b081_05_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 232 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_05_rows b081_05_labels 1282013230136052102021000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_05_rows b081_05_labels]
    decide +kernel

def b081_06_rows : List Row := [(row3 14 33 44), (row3 14 33 45), (row3 14 33 46), (row3 14 33 47), (row3 14 33 48), (row3 14 33 49), (row3 14 33 50), (row3 14 33 51), (row3 14 33 52), (row3 14 33 53), (row3 14 33 54), (row3 14 33 55), (row3 14 33 56), (row3 14 33 57), (row3 14 33 58), (row3 14 33 59)]

def b081_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_06_rows b081_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_06_rows b081_06_labels]
    decide +kernel

def b081_07_rows : List Row := [(row3 14 33 60), (row3 14 33 61), (row3 14 33 62), (row3 14 33 63), (row3 14 34 35), (row3 14 34 36), (row3 14 34 37), (row3 14 34 38), (row3 14 34 39), (row3 14 34 40), (row3 14 34 41), (row3 14 34 42), (row3 14 34 43), (row3 14 34 44), (row3 14 34 45), (row3 14 34 46)]

def b081_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_07_rows b081_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_07_rows b081_07_labels]
    decide +kernel

def b081_08_rows : List Row := [(row3 14 34 47), (row3 14 34 48), (row3 14 34 49), (row3 14 34 50), (row3 14 34 51), (row3 14 34 52), (row3 14 34 53), (row3 14 34 54), (row3 14 34 55), (row3 14 34 56), (row3 14 34 57), (row3 14 34 58), (row3 14 34 59), (row3 14 34 60), (row3 14 34 61), (row3 14 34 62)]

def b081_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_08_rows b081_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_08_rows b081_08_labels]
    decide +kernel

def b081_09_rows : List Row := [(row3 14 34 63), (row3 14 35 36), (row3 14 35 37), (row3 14 35 38), (row3 14 35 39), (row3 14 35 40), (row3 14 35 41), (row3 14 35 42), (row3 14 35 43), (row3 14 35 44), (row3 14 35 45), (row3 14 35 46), (row3 14 35 47), (row3 14 35 48), (row3 14 35 49), (row3 14 35 50)]

def b081_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_09_rows b081_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_09_rows b081_09_labels]
    decide +kernel

def b081_10_rows : List Row := [(row3 14 35 51), (row3 14 35 52), (row3 14 35 53), (row3 14 35 54), (row3 14 35 55), (row3 14 35 56), (row3 14 35 57), (row3 14 35 58), (row3 14 35 59), (row3 14 35 60), (row3 14 35 61), (row3 14 35 62), (row3 14 35 63), (row3 14 36 37), (row3 14 36 38), (row3 14 36 39)]

def b081_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_10_rows b081_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_10_rows b081_10_labels]
    decide +kernel

def b081_11_rows : List Row := [(row3 14 36 40), (row3 14 36 41), (row3 14 36 42), (row3 14 36 43), (row3 14 36 44), (row3 14 36 45), (row3 14 36 46), (row3 14 36 47), (row3 14 36 48), (row3 14 36 49), (row3 14 36 50), (row3 14 36 51), (row3 14 36 52), (row3 14 36 53), (row3 14 36 54), (row3 14 36 55)]

def b081_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_11_rows b081_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_11_rows b081_11_labels]
    decide +kernel

def b081_12_rows : List Row := [(row3 14 36 56), (row3 14 36 57), (row3 14 36 58), (row3 14 36 59), (row3 14 36 60), (row3 14 36 61), (row3 14 36 62), (row3 14 36 63), (row3 14 37 38), (row3 14 37 39), (row3 14 37 40), (row3 14 37 41), (row3 14 37 42), (row3 14 37 43), (row3 14 37 44), (row3 14 37 45)]

def b081_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_12_rows b081_12_labels 289958420551243194225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_12_rows b081_12_labels]
    decide +kernel

def b081_13_rows : List Row := [(row3 14 37 46), (row3 14 37 47), (row3 14 37 48), (row3 14 37 49), (row3 14 37 50), (row3 14 37 51), (row3 14 37 52), (row3 14 37 53), (row3 14 37 54), (row3 14 37 55), (row3 14 37 56), (row3 14 37 57), (row3 14 37 58), (row3 14 37 59), (row3 14 37 60), (row3 14 37 61)]

def b081_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 247 462)]

theorem b081_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_13_rows b081_13_labels 63443981337259342162500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_13_rows b081_13_labels]
    decide +kernel

def b081_14_rows : List Row := [(row3 14 37 62), (row3 14 37 63), (row3 14 38 39), (row3 14 38 40), (row3 14 38 41), (row3 14 38 42), (row3 14 38 43), (row3 14 38 44), (row3 14 38 45), (row3 14 38 46), (row3 14 38 47), (row3 14 38 48), (row3 14 38 49), (row3 14 38 50), (row3 14 38 51), (row3 14 38 52)]

def b081_14_labels : List Row := [(row3 235 232 235), (row3 246 246 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_14_rows b081_14_labels 1035731786925055907164500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_14_rows b081_14_labels]
    decide +kernel

def b081_15_rows : List Row := [(row3 14 38 53), (row3 14 38 54), (row3 14 38 55), (row3 14 38 56), (row3 14 38 57), (row3 14 38 58), (row3 14 38 59), (row3 14 38 60), (row3 14 38 61), (row3 14 38 62), (row3 14 38 63), (row3 14 39 40), (row3 14 39 41), (row3 14 39 42), (row3 14 39 43), (row3 14 39 44)]

def b081_15_labels : List Row := [(row3 243 462 243), (row3 235 235 237), (row3 247 462 247), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 234 234 234), (row3 281 278 281), (row3 234 226 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b081_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b081_15_rows b081_15_labels 10571492405102562637498800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b081_15_rows b081_15_labels]
    decide +kernel

theorem checked081 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_081 QuarticIntegerComputationalData.ids64_081 970996498846669148152702770 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b081_00_rows ++ b081_01_rows) ++ (b081_02_rows ++ b081_03_rows)) ++ ((b081_04_rows ++ b081_05_rows) ++ (b081_06_rows ++ b081_07_rows))) ++ (((b081_08_rows ++ b081_09_rows) ++ (b081_10_rows ++ b081_11_rows)) ++ ((b081_12_rows ++ b081_13_rows) ++ (b081_14_rows ++ b081_15_rows))))
    ((((b081_00_labels ++ b081_01_labels) ++ (b081_02_labels ++ b081_03_labels)) ++ ((b081_04_labels ++ b081_05_labels) ++ (b081_06_labels ++ b081_07_labels))) ++ (((b081_08_labels ++ b081_09_labels) ++ (b081_10_labels ++ b081_11_labels)) ++ ((b081_12_labels ++ b081_13_labels) ++ (b081_14_labels ++ b081_15_labels)))) 970996498846669148152702770
  exact ((((b081_00_checked.append (c := 301772362447448955789523020) b081_01_checked (by decide +kernel)).append (c := 422314813124504325487067220) (b081_02_checked.append (c := 120542450677055369697544200) b081_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 959035872252753027071651970) ((b081_04_checked.append (c := 536721059128248701584584750) b081_05_checked (by decide +kernel)).append (c := 536721059128248701584584750) (b081_06_checked.append (c := 0) b081_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 970996498846669148152702770) (((b081_08_checked.append (c := 0) b081_09_checked (by decide +kernel)).append (c := 0) (b081_10_checked.append (c := 0) b081_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 11960626593916121081050800) ((b081_12_checked.append (c := 353402401888502536387500) b081_13_checked (by decide +kernel)).append (c := 11960626593916121081050800) (b081_14_checked.append (c := 11607224192027618544663300) b081_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b082_00_rows : List Row := [(row3 14 39 45), (row3 14 39 46), (row3 14 39 47), (row3 14 39 48), (row3 14 39 49), (row3 14 39 50), (row3 14 39 51), (row3 14 39 52), (row3 14 39 53), (row3 14 39 54), (row3 14 39 55), (row3 14 39 56), (row3 14 39 57), (row3 14 39 58), (row3 14 39 59), (row3 14 39 60)]

def b082_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_00_rows b082_00_labels 407433492730763154562500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_00_rows b082_00_labels]
    decide +kernel

def b082_01_rows : List Row := [(row3 14 39 61), (row3 14 39 62), (row3 14 39 63), (row3 14 40 41), (row3 14 40 42), (row3 14 40 43), (row3 14 40 44), (row3 14 40 45), (row3 14 40 46), (row3 14 40 47), (row3 14 40 48), (row3 14 40 49), (row3 14 40 50), (row3 14 40 51), (row3 14 40 52), (row3 14 40 53)]

def b082_01_labels : List Row := [(row3 246 246 462), (row3 235 232 235), (row3 282 282 278), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_01_rows b082_01_labels 70040934753427350364477500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_01_rows b082_01_labels]
    decide +kernel

def b082_02_rows : List Row := [(row3 14 40 54), (row3 14 40 55), (row3 14 40 56), (row3 14 40 57), (row3 14 40 58), (row3 14 40 59), (row3 14 40 60), (row3 14 40 61), (row3 14 40 62), (row3 14 40 63), (row3 14 41 42), (row3 14 41 43), (row3 14 41 44), (row3 14 41 45), (row3 14 41 46), (row3 14 41 47)]

def b082_02_labels : List Row := [(row3 246 246 462), (row3 226 234 226), (row3 211 88 370), (row3 279 279 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 228 228), (row3 320 320 319), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_02_rows b082_02_labels 9595658929893122650217715000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_02_rows b082_02_labels]
    decide +kernel

def b082_03_rows : List Row := [(row3 14 41 48), (row3 14 41 49), (row3 14 41 50), (row3 14 41 51), (row3 14 41 52), (row3 14 41 53), (row3 14 41 54), (row3 14 41 55), (row3 14 41 56), (row3 14 41 57), (row3 14 41 58), (row3 14 41 59), (row3 14 41 60), (row3 14 41 61), (row3 14 41 62), (row3 14 41 63)]

def b082_03_labels : List Row := [(row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 462 251), (row3 214 11 117), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 228 223)]

theorem b082_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_03_rows b082_03_labels 1647472497286259345855838750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_03_rows b082_03_labels]
    decide +kernel

def b082_04_rows : List Row := [(row3 14 42 43), (row3 14 42 44), (row3 14 42 45), (row3 14 42 46), (row3 14 42 47), (row3 14 42 48), (row3 14 42 49), (row3 14 42 50), (row3 14 42 51), (row3 14 42 52), (row3 14 42 53), (row3 14 42 54), (row3 14 42 55), (row3 14 42 56), (row3 14 42 57), (row3 14 42 58)]

def b082_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_04_rows b082_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_04_rows b082_04_labels]
    decide +kernel

def b082_05_rows : List Row := [(row3 14 42 59), (row3 14 42 60), (row3 14 42 61), (row3 14 42 62), (row3 14 42 63), (row3 14 43 44), (row3 14 43 45), (row3 14 43 46), (row3 14 43 47), (row3 14 43 48), (row3 14 43 49), (row3 14 43 50), (row3 14 43 51), (row3 14 43 52), (row3 14 43 53), (row3 14 43 54)]

def b082_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_05_rows b082_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_05_rows b082_05_labels]
    decide +kernel

def b082_06_rows : List Row := [(row3 14 43 55), (row3 14 43 56), (row3 14 43 57), (row3 14 43 58), (row3 14 43 59), (row3 14 43 60), (row3 14 43 61), (row3 14 43 62), (row3 14 43 63), (row3 14 44 45), (row3 14 44 46), (row3 14 44 47), (row3 14 44 48), (row3 14 44 49), (row3 14 44 50), (row3 14 44 51)]

def b082_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_06_rows b082_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_06_rows b082_06_labels]
    decide +kernel

def b082_07_rows : List Row := [(row3 14 44 52), (row3 14 44 53), (row3 14 44 54), (row3 14 44 55), (row3 14 44 56), (row3 14 44 57), (row3 14 44 58), (row3 14 44 59), (row3 14 44 60), (row3 14 44 61), (row3 14 44 62), (row3 14 44 63), (row3 14 45 46), (row3 14 45 47), (row3 14 45 48), (row3 14 45 49)]

def b082_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_07_rows b082_07_labels 460898763182129314156500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_07_rows b082_07_labels]
    decide +kernel

def b082_08_rows : List Row := [(row3 14 45 50), (row3 14 45 51), (row3 14 45 52), (row3 14 45 53), (row3 14 45 54), (row3 14 45 55), (row3 14 45 56), (row3 14 45 57), (row3 14 45 58), (row3 14 45 59), (row3 14 45 60), (row3 14 45 61), (row3 14 45 62), (row3 14 45 63), (row3 14 46 47), (row3 14 46 48)]

def b082_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 291 289 291), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462)]

theorem b082_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_08_rows b082_08_labels 13961043390298310038420200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_08_rows b082_08_labels]
    decide +kernel

def b082_09_rows : List Row := [(row3 14 46 49), (row3 14 46 50), (row3 14 46 51), (row3 14 46 52), (row3 14 46 53), (row3 14 46 54), (row3 14 46 55), (row3 14 46 56), (row3 14 46 57), (row3 14 46 58), (row3 14 46 59), (row3 14 46 60), (row3 14 46 61), (row3 14 46 62), (row3 14 46 63), (row3 14 47 48)]

def b082_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 270 270 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 183 183 178), (row3 311 311 306), (row3 235 462 235)]

theorem b082_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_09_rows b082_09_labels 192718896525375024963204360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_09_rows b082_09_labels]
    decide +kernel

def b082_10_rows : List Row := [(row3 14 47 49), (row3 14 47 50), (row3 14 47 51), (row3 14 47 52), (row3 14 47 53), (row3 14 47 54), (row3 14 47 55), (row3 14 47 56), (row3 14 47 57), (row3 14 47 58), (row3 14 47 59), (row3 14 47 60), (row3 14 47 61), (row3 14 47 62), (row3 14 47 63), (row3 14 48 49)]

def b082_10_labels : List Row := [(row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 286 462 286), (row3 214 11 117), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 292 289 292), (row3 146 137 143), (row3 291 289 291)]

theorem b082_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_10_rows b082_10_labels 2201702851244477746451466990 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_10_rows b082_10_labels]
    decide +kernel

def b082_11_rows : List Row := [(row3 14 48 50), (row3 14 48 51), (row3 14 48 52), (row3 14 48 53), (row3 14 48 54), (row3 14 48 55), (row3 14 48 56), (row3 14 48 57), (row3 14 48 58), (row3 14 48 59), (row3 14 48 60), (row3 14 48 61), (row3 14 48 62), (row3 14 48 63), (row3 14 49 50), (row3 14 49 51)]

def b082_11_labels : List Row := [(row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 305 289 305), (row3 181 435 42), (row3 137 149 146), (row3 291 289 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 313 306 313), (row3 99 98 101), (row3 248 248 462), (row3 462 462 462)]

theorem b082_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_11_rows b082_11_labels 346627363039266808372649372190 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_11_rows b082_11_labels]
    decide +kernel

def b082_12_rows : List Row := [(row3 14 49 52), (row3 14 49 53), (row3 14 49 54), (row3 14 49 55), (row3 14 49 56), (row3 14 49 57), (row3 14 49 58), (row3 14 49 59), (row3 14 49 60), (row3 14 49 61), (row3 14 49 62), (row3 14 49 63), (row3 14 50 51), (row3 14 50 52), (row3 14 50 53), (row3 14 50 54)]

def b082_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 249 249 462), (row3 222 224 222), (row3 135 83 398), (row3 309 309 306), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 222 222), (row3 322 322 321), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_12_rows b082_12_labels 20560629095944380402330137400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_12_rows b082_12_labels]
    decide +kernel

def b082_13_rows : List Row := [(row3 14 50 55), (row3 14 50 56), (row3 14 50 57), (row3 14 50 58), (row3 14 50 59), (row3 14 50 60), (row3 14 50 61), (row3 14 50 62), (row3 14 50 63), (row3 14 51 52), (row3 14 51 53), (row3 14 51 54), (row3 14 51 55), (row3 14 51 56), (row3 14 51 57), (row3 14 51 58)]

def b082_13_labels : List Row := [(row3 250 462 250), (row3 215 11 118), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 232 223), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b082_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_13_rows b082_13_labels 1618335122562164198590832250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_13_rows b082_13_labels]
    decide +kernel

def b082_14_rows : List Row := [(row3 14 51 59), (row3 14 51 60), (row3 14 51 61), (row3 14 51 62), (row3 14 51 63), (row3 14 52 53), (row3 14 52 54), (row3 14 52 55), (row3 14 52 56), (row3 14 52 57), (row3 14 52 58), (row3 14 52 59), (row3 14 52 60), (row3 14 52 61), (row3 14 52 62), (row3 14 52 63)]

def b082_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 291 289 291), (row3 462 232 232)]

theorem b082_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_14_rows b082_14_labels 14264589710702823621739200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_14_rows b082_14_labels]
    decide +kernel

def b082_15_rows : List Row := [(row3 14 53 54), (row3 14 53 55), (row3 14 53 56), (row3 14 53 57), (row3 14 53 58), (row3 14 53 59), (row3 14 53 60), (row3 14 53 61), (row3 14 53 62), (row3 14 53 63), (row3 14 54 55), (row3 14 54 56), (row3 14 54 57), (row3 14 54 58), (row3 14 54 59), (row3 14 54 60)]

def b082_15_labels : List Row := [(row3 271 271 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 286 462), (row3 144 147 137), (row3 312 312 306), (row3 173 10 260), (row3 216 11 119), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 246 462 246)]

theorem b082_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b082_15_rows b082_15_labels 3297365594924246984374227270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b082_15_rows b082_15_labels]
    decide +kernel

theorem checked082 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_082 QuarticIntegerComputationalData.ids64_082 385840380927757176101926150110 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b082_00_rows ++ b082_01_rows) ++ (b082_02_rows ++ b082_03_rows)) ++ ((b082_04_rows ++ b082_05_rows) ++ (b082_06_rows ++ b082_07_rows))) ++ (((b082_08_rows ++ b082_09_rows) ++ (b082_10_rows ++ b082_11_rows)) ++ ((b082_12_rows ++ b082_13_rows) ++ (b082_14_rows ++ b082_15_rows))))
    ((((b082_00_labels ++ b082_01_labels) ++ (b082_02_labels ++ b082_03_labels)) ++ ((b082_04_labels ++ b082_05_labels) ++ (b082_06_labels ++ b082_07_labels))) ++ (((b082_08_labels ++ b082_09_labels) ++ (b082_10_labels ++ b082_11_labels)) ++ ((b082_12_labels ++ b082_13_labels) ++ (b082_14_labels ++ b082_15_labels)))) 385840380927757176101926150110
  exact ((((b082_00_checked.append (c := 70448368246158113519040000) b082_01_checked (by decide +kernel)).append (c := 11313579795425540109592593750) (b082_02_checked.append (c := 11243131427179381996073553750) b082_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 11314040694188722238906750250) ((b082_04_checked.append (c := 0) b082_05_checked (by decide +kernel)).append (c := 460898763182129314156500) (b082_06_checked.append (c := 460898763182129314156500) b082_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 385840380927757176101926150110) (((b082_08_checked.append (c := 206679939915673335001624560) b082_09_checked (by decide +kernel)).append (c := 349035745830426959454102463740) (b082_10_checked.append (c := 348829065890511286119100839180) b082_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 374526340233568453863019399860) ((b082_12_checked.append (c := 22178964218506544600920969650) b082_13_checked (by decide +kernel)).append (c := 25490594403141494408916936120) (b082_14_checked.append (c := 3311630184634949807995966470) b082_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b083_00_rows : List Row := [(row3 14 54 61), (row3 14 54 62), (row3 14 54 63), (row3 14 55 56), (row3 14 55 57), (row3 14 55 58), (row3 14 55 59), (row3 14 55 60), (row3 14 55 61), (row3 14 55 62), (row3 14 55 63), (row3 14 56 57), (row3 14 56 58), (row3 14 56 59), (row3 14 56 60), (row3 14 56 61)]

def b083_00_labels : List Row := [(row3 224 226 229), (row3 363 386 393), (row3 120 112 120), (row3 134 81 398), (row3 312 312 306), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 253 253 462), (row3 141 142 136), (row3 396 416 408), (row3 389 45 436), (row3 114 368 86), (row3 258 172 10), (row3 462 462 462), (row3 260 173 10)]

theorem b083_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_00_rows b083_00_labels 479365558526635371333973216620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_00_rows b083_00_labels]
    decide +kernel

def b083_01_rows : List Row := [(row3 14 56 62), (row3 14 56 63), (row3 14 57 58), (row3 14 57 59), (row3 14 57 60), (row3 14 57 61), (row3 14 57 62), (row3 14 57 63), (row3 14 58 59), (row3 14 58 60), (row3 14 58 61), (row3 14 58 62), (row3 14 58 63), (row3 14 59 60), (row3 14 59 61), (row3 14 59 62)]

def b083_01_labels : List Row := [(row3 108 367 84), (row3 46 46 440), (row3 309 306 309), (row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 318 315 318), (row3 98 99 101), (row3 246 246 462), (row3 462 462 462), (row3 247 247 462), (row3 224 223 223), (row3 320 320 319), (row3 462 462 462), (row3 235 235 462), (row3 268 265 268)]

theorem b083_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_01_rows b083_01_labels 969383742273272979805865976900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_01_rows b083_01_labels]
    decide +kernel

def b083_02_rows : List Row := [(row3 14 59 63), (row3 14 60 61), (row3 14 60 62), (row3 14 60 63), (row3 14 61 62), (row3 14 61 63), (row3 14 62 63), (row3 15 16 17), (row3 15 16 18), (row3 15 16 19), (row3 15 16 20), (row3 15 16 21), (row3 15 16 22), (row3 15 16 23), (row3 15 16 24), (row3 15 16 25)]

def b083_02_labels : List Row := [(row3 232 235 228), (row3 287 287 462), (row3 182 182 178), (row3 283 283 278), (row3 362 388 392), (row3 142 136 141), (row3 60 432 411), (row3 61 48 50), (row3 351 348 350), (row3 190 199 198), (row3 288 261 290), (row3 110 109 111), (row3 406 406 405), (row3 442 451 24), (row3 57 53 51), (row3 382 378 381)]

theorem b083_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_02_rows b083_02_labels 30734102377486642746693436728570 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_02_rows b083_02_labels]
    decide +kernel

def b083_03_rows : List Row := [(row3 15 16 26), (row3 15 16 27), (row3 15 16 28), (row3 15 16 29), (row3 15 16 30), (row3 15 16 31), (row3 15 16 32), (row3 15 16 33), (row3 15 16 34), (row3 15 16 35), (row3 15 16 36), (row3 15 16 37), (row3 15 16 38), (row3 15 16 39), (row3 15 16 40), (row3 15 16 41)]

def b083_03_labels : List Row := [(row3 137 149 146), (row3 462 273 273), (row3 462 462 462), (row3 295 273 304), (row3 99 98 101), (row3 404 402 403), (row3 349 346 350), (row3 137 149 146), (row3 462 278 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 278 300), (row3 125 126 128), (row3 165 176 165), (row3 273 288 273)]

theorem b083_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_03_rows b083_03_labels 45561025251454629097519228800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_03_rows b083_03_labels]
    decide +kernel

def b083_04_rows : List Row := [(row3 15 16 42), (row3 15 16 43), (row3 15 16 44), (row3 15 16 45), (row3 15 16 46), (row3 15 16 47), (row3 15 16 48), (row3 15 16 49), (row3 15 16 50), (row3 15 16 51), (row3 15 16 52), (row3 15 16 53), (row3 15 16 54), (row3 15 16 55), (row3 15 16 56), (row3 15 16 57)]

def b083_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 288 288), (row3 350 346 349), (row3 146 149 137), (row3 278 278 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 300 278 288), (row3 128 126 125), (row3 51 53 57), (row3 381 378 382)]

theorem b083_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_04_rows b083_04_labels 1403925310604150153224749095760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_04_rows b083_04_labels]
    decide +kernel

def b083_05_rows : List Row := [(row3 15 16 58), (row3 15 16 59), (row3 15 16 60), (row3 15 16 61), (row3 15 16 62), (row3 15 16 63), (row3 15 17 18), (row3 15 17 19), (row3 15 17 20), (row3 15 17 21), (row3 15 17 22), (row3 15 17 23), (row3 15 17 24), (row3 15 17 25), (row3 15 17 26), (row3 15 17 27)]

def b083_05_labels : List Row := [(row3 146 149 137), (row3 273 273 462), (row3 462 462 462), (row3 304 273 295), (row3 101 98 99), (row3 403 402 404), (row3 129 102 103), (row3 289 291 291), (row3 226 234 226), (row3 306 311 311), (row3 120 120 112), (row3 411 60 432), (row3 323 324 324), (row3 129 103 102), (row3 306 309 309), (row3 224 224 224)]

theorem b083_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_05_rows b083_05_labels 299403600831113047436255666040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_05_rows b083_05_labels]
    decide +kernel

def b083_06_rows : List Row := [(row3 15 17 28), (row3 15 17 29), (row3 15 17 30), (row3 15 17 31), (row3 15 17 32), (row3 15 17 33), (row3 15 17 34), (row3 15 17 35), (row3 15 17 36), (row3 15 17 37), (row3 15 17 38), (row3 15 17 39), (row3 15 17 40), (row3 15 17 41), (row3 15 17 42), (row3 15 17 43)]

def b083_06_labels : List Row := [(row3 462 246 246), (row3 228 462 228), (row3 306 312 312), (row3 141 142 136), (row3 220 222 221), (row3 289 291 291), (row3 224 224 224), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 283 283), (row3 278 282 282), (row3 226 226 234), (row3 462 246 246), (row3 462 462 462)]

theorem b083_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_06_rows b083_06_labels 487464921207273306338129160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_06_rows b083_06_labels]
    decide +kernel

def b083_07_rows : List Row := [(row3 15 17 44), (row3 15 17 45), (row3 15 17 46), (row3 15 17 47), (row3 15 17 48), (row3 15 17 49), (row3 15 17 50), (row3 15 17 51), (row3 15 17 52), (row3 15 17 53), (row3 15 17 54), (row3 15 17 55), (row3 15 17 56), (row3 15 17 57), (row3 15 17 58), (row3 15 17 59)]

def b083_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 232 235), (row3 143 137 146), (row3 306 311 311), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 228 232), (row3 319 320 320), (row3 408 416 396), (row3 120 112 120), (row3 306 312 312), (row3 232 232 462)]

theorem b083_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_07_rows b083_07_labels 50395545404681658070548752010 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_07_rows b083_07_labels]
    decide +kernel

def b083_08_rows : List Row := [(row3 15 17 60), (row3 15 17 61), (row3 15 17 62), (row3 15 17 63), (row3 15 18 19), (row3 15 18 20), (row3 15 18 21), (row3 15 18 22), (row3 15 18 23), (row3 15 18 24), (row3 15 18 25), (row3 15 18 26), (row3 15 18 27), (row3 15 18 28), (row3 15 18 29), (row3 15 18 30)]

def b083_08_labels : List Row := [(row3 462 462 462), (row3 223 232 228), (row3 321 322 322), (row3 101 98 99), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 288 288 462), (row3 158 356 89), (row3 224 226 229), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462)]

theorem b083_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_08_rows b083_08_labels 7895651967088898759327751120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_08_rows b083_08_labels]
    decide +kernel

def b083_09_rows : List Row := [(row3 15 18 31), (row3 15 18 32), (row3 15 18 33), (row3 15 18 34), (row3 15 18 35), (row3 15 18 36), (row3 15 18 37), (row3 15 18 38), (row3 15 18 39), (row3 15 18 40), (row3 15 18 41), (row3 15 18 42), (row3 15 18 43), (row3 15 18 44), (row3 15 18 45), (row3 15 18 46)]

def b083_09_labels : List Row := [(row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b083_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_09_rows b083_09_labels 6473492108545359566541600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_09_rows b083_09_labels]
    decide +kernel

def b083_10_rows : List Row := [(row3 15 18 47), (row3 15 18 48), (row3 15 18 49), (row3 15 18 50), (row3 15 18 51), (row3 15 18 52), (row3 15 18 53), (row3 15 18 54), (row3 15 18 55), (row3 15 18 56), (row3 15 18 57), (row3 15 18 58), (row3 15 18 59), (row3 15 18 60), (row3 15 18 61), (row3 15 18 62)]

def b083_10_labels : List Row := [(row3 462 462 462), (row3 278 462 278), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 225 236 228), (row3 138 232 139), (row3 295 462 295), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 232 228)]

theorem b083_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_10_rows b083_10_labels 1131454663260530971637620800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_10_rows b083_10_labels]
    decide +kernel

def b083_11_rows : List Row := [(row3 15 18 63), (row3 15 19 20), (row3 15 19 21), (row3 15 19 22), (row3 15 19 23), (row3 15 19 24), (row3 15 19 25), (row3 15 19 26), (row3 15 19 27), (row3 15 19 28), (row3 15 19 29), (row3 15 19 30), (row3 15 19 31), (row3 15 19 32), (row3 15 19 33), (row3 15 19 34)]

def b083_11_labels : List Row := [(row3 304 273 295), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 269 269), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b083_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_11_rows b083_11_labels 63962938792818532692643500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_11_rows b083_11_labels]
    decide +kernel

def b083_12_rows : List Row := [(row3 15 19 35), (row3 15 19 36), (row3 15 19 37), (row3 15 19 38), (row3 15 19 39), (row3 15 19 40), (row3 15 19 41), (row3 15 19 42), (row3 15 19 43), (row3 15 19 44), (row3 15 19 45), (row3 15 19 46), (row3 15 19 47), (row3 15 19 48), (row3 15 19 49), (row3 15 19 50)]

def b083_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b083_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_12_rows b083_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_12_rows b083_12_labels]
    decide +kernel

def b083_13_rows : List Row := [(row3 15 19 51), (row3 15 19 52), (row3 15 19 53), (row3 15 19 54), (row3 15 19 55), (row3 15 19 56), (row3 15 19 57), (row3 15 19 58), (row3 15 19 59), (row3 15 19 60), (row3 15 19 61), (row3 15 19 62), (row3 15 19 63), (row3 15 20 21), (row3 15 20 22), (row3 15 20 23)]

def b083_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 300 300 462), (row3 159 356 91)]

theorem b083_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_13_rows b083_13_labels 6525393029128383857275962960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_13_rows b083_13_labels]
    decide +kernel

def b083_14_rows : List Row := [(row3 15 20 24), (row3 15 20 25), (row3 15 20 26), (row3 15 20 27), (row3 15 20 28), (row3 15 20 29), (row3 15 20 30), (row3 15 20 31), (row3 15 20 32), (row3 15 20 33), (row3 15 20 34), (row3 15 20 35), (row3 15 20 36), (row3 15 20 37), (row3 15 20 38), (row3 15 20 39)]

def b083_14_labels : List Row := [(row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462)]

theorem b083_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_14_rows b083_14_labels 8139572411274922493433600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_14_rows b083_14_labels]
    decide +kernel

def b083_15_rows : List Row := [(row3 15 20 40), (row3 15 20 41), (row3 15 20 42), (row3 15 20 43), (row3 15 20 44), (row3 15 20 45), (row3 15 20 46), (row3 15 20 47), (row3 15 20 48), (row3 15 20 49), (row3 15 20 50), (row3 15 20 51), (row3 15 20 52), (row3 15 20 53), (row3 15 20 54), (row3 15 20 55)]

def b083_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462)]

theorem b083_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b083_15_rows b083_15_labels 266452083570981244608000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b083_15_rows b083_15_labels]
    decide +kernel

theorem checked083 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_083 QuarticIntegerComputationalData.ids64_083 33998255967414031882352925355440 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b083_00_rows ++ b083_01_rows) ++ (b083_02_rows ++ b083_03_rows)) ++ ((b083_04_rows ++ b083_05_rows) ++ (b083_06_rows ++ b083_07_rows))) ++ (((b083_08_rows ++ b083_09_rows) ++ (b083_10_rows ++ b083_11_rows)) ++ ((b083_12_rows ++ b083_13_rows) ++ (b083_14_rows ++ b083_15_rows))))
    ((((b083_00_labels ++ b083_01_labels) ++ (b083_02_labels ++ b083_03_labels)) ++ ((b083_04_labels ++ b083_05_labels) ++ (b083_06_labels ++ b083_07_labels))) ++ (((b083_08_labels ++ b083_09_labels) ++ (b083_10_labels ++ b083_11_labels)) ++ ((b083_12_labels ++ b083_13_labels) ++ (b083_14_labels ++ b083_15_labels)))) 33998255967414031882352925355440
  exact ((((b083_00_checked.append (c := 1448749300799908351139839193520) b083_01_checked (by decide +kernel)).append (c := 32228412703538005726930795150890) (b083_02_checked.append (c := 30779663402738097375790955957370) b083_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 33982624625299157858968686793860) ((b083_04_checked.append (c := 1703328911435263200661004761800) b083_05_checked (by decide +kernel)).append (c := 1754211921761152132037891642970) (b083_06_checked.append (c := 50883010325888931376886881170) b083_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 33998255967414031882352925355440) (((b083_08_checked.append (c := 7902125459197444118894292720) b083_09_checked (by decide +kernel)).append (c := 9097543061250793623224557020) (b083_10_checked.append (c := 1195417602053349504330264300) b083_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 15631342114874023384238561580) ((b083_12_checked.append (c := 6525393029128383857275962960) b083_13_checked (by decide +kernel)).append (c := 6533799053623229761014004560) (b083_14_checked.append (c := 8406024494845903738041600) b083_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b084_00_rows : List Row := [(row3 15 20 56), (row3 15 20 57), (row3 15 20 58), (row3 15 20 59), (row3 15 20 60), (row3 15 20 61), (row3 15 20 62), (row3 15 20 63), (row3 15 21 22), (row3 15 21 23), (row3 15 21 24), (row3 15 21 25), (row3 15 21 26), (row3 15 21 27), (row3 15 21 28), (row3 15 21 29)]

def b084_00_labels : List Row := [(row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 273 273 462), (row3 100 100 113), (row3 410 59 431), (row3 306 310 310), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228)]

theorem b084_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_00_rows b084_00_labels 178171463611291593292043211540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_00_rows b084_00_labels]
    decide +kernel

def b084_01_rows : List Row := [(row3 15 21 30), (row3 15 21 31), (row3 15 21 32), (row3 15 21 33), (row3 15 21 34), (row3 15 21 35), (row3 15 21 36), (row3 15 21 37), (row3 15 21 38), (row3 15 21 39), (row3 15 21 40), (row3 15 21 41), (row3 15 21 42), (row3 15 21 43), (row3 15 21 44), (row3 15 21 45)]

def b084_01_labels : List Row := [(row3 306 309 309), (row3 144 147 137), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_01_rows b084_01_labels 510565585097691517445688960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_01_rows b084_01_labels]
    decide +kernel

def b084_02_rows : List Row := [(row3 15 21 46), (row3 15 21 47), (row3 15 21 48), (row3 15 21 49), (row3 15 21 50), (row3 15 21 51), (row3 15 21 52), (row3 15 21 53), (row3 15 21 54), (row3 15 21 55), (row3 15 21 56), (row3 15 21 57), (row3 15 21 58), (row3 15 21 59), (row3 15 21 60), (row3 15 21 61)]

def b084_02_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 279 279), (row3 306 309 309), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228)]

theorem b084_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_02_rows b084_02_labels 369993101576439961414130400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_02_rows b084_02_labels]
    decide +kernel

def b084_03_rows : List Row := [(row3 15 21 62), (row3 15 21 63), (row3 15 22 23), (row3 15 22 24), (row3 15 22 25), (row3 15 22 26), (row3 15 22 27), (row3 15 22 28), (row3 15 22 29), (row3 15 22 30), (row3 15 22 31), (row3 15 22 32), (row3 15 22 33), (row3 15 22 34), (row3 15 22 35), (row3 15 22 36)]

def b084_03_labels : List Row := [(row3 306 312 312), (row3 146 149 137), (row3 32 452 25), (row3 120 112 120), (row3 295 462 295), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 319 462 319), (row3 100 113 100), (row3 382 378 381), (row3 288 462 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_03_rows b084_03_labels 13827819173207984766658207400760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_03_rows b084_03_labels]
    decide +kernel

def b084_04_rows : List Row := [(row3 15 22 37), (row3 15 22 38), (row3 15 22 39), (row3 15 22 40), (row3 15 22 41), (row3 15 22 42), (row3 15 22 43), (row3 15 22 44), (row3 15 22 45), (row3 15 22 46), (row3 15 22 47), (row3 15 22 48), (row3 15 22 49), (row3 15 22 50), (row3 15 22 51), (row3 15 22 52)]

def b084_04_labels : List Row := [(row3 228 462 228), (row3 300 462 300), (row3 175 161 175), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 300 462 300), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_04_rows b084_04_labels 402115258446703236346726080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_04_rows b084_04_labels]
    decide +kernel

def b084_05_rows : List Row := [(row3 15 22 53), (row3 15 22 54), (row3 15 22 55), (row3 15 22 56), (row3 15 22 57), (row3 15 22 58), (row3 15 22 59), (row3 15 22 60), (row3 15 22 61), (row3 15 22 62), (row3 15 22 63), (row3 15 23 24), (row3 15 23 25), (row3 15 23 26), (row3 15 23 27), (row3 15 23 28)]

def b084_05_labels : List Row := [(row3 462 462 462), (row3 288 462 288), (row3 175 161 175), (row3 100 113 100), (row3 319 462 319), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 295 462 295), (row3 120 112 120), (row3 381 378 382), (row3 413 438 40), (row3 134 81 398), (row3 462 284 284), (row3 462 462 462), (row3 462 284 284)]

theorem b084_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_05_rows b084_05_labels 450186782066988992055109098540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_05_rows b084_05_labels]
    decide +kernel

def b084_06_rows : List Row := [(row3 15 23 29), (row3 15 23 30), (row3 15 23 31), (row3 15 23 32), (row3 15 23 33), (row3 15 23 34), (row3 15 23 35), (row3 15 23 36), (row3 15 23 37), (row3 15 23 38), (row3 15 23 39), (row3 15 23 40), (row3 15 23 41), (row3 15 23 42), (row3 15 23 43), (row3 15 23 44)]

def b084_06_labels : List Row := [(row3 135 83 398), (row3 412 437 39), (row3 47 26 453), (row3 156 82 399), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 157 83 399), (row3 372 430 58), (row3 278 301 301), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_06_rows b084_06_labels 12990275098363885345798700524680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_06_rows b084_06_labels]
    decide +kernel

def b084_07_rows : List Row := [(row3 15 23 45), (row3 15 23 46), (row3 15 23 47), (row3 15 23 48), (row3 15 23 49), (row3 15 23 50), (row3 15 23 51), (row3 15 23 52), (row3 15 23 53), (row3 15 23 54), (row3 15 23 55), (row3 15 23 56), (row3 15 23 57), (row3 15 23 58), (row3 15 23 59), (row3 15 23 60)]

def b084_07_labels : List Row := [(row3 462 462 462), (row3 462 284 284), (row3 187 90 357), (row3 126 137 127), (row3 306 309 309), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 160 228 163), (row3 366 375 353), (row3 422 423 417), (row3 100 113 100), (row3 306 309 309), (row3 232 232 462), (row3 462 462 462)]

theorem b084_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_07_rows b084_07_labels 4083849555754624417711293402270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_07_rows b084_07_labels]
    decide +kernel

def b084_08_rows : List Row := [(row3 15 23 61), (row3 15 23 62), (row3 15 23 63), (row3 15 24 25), (row3 15 24 26), (row3 15 24 27), (row3 15 24 28), (row3 15 24 29), (row3 15 24 30), (row3 15 24 31), (row3 15 24 32), (row3 15 24 33), (row3 15 24 34), (row3 15 24 35), (row3 15 24 36), (row3 15 24 37)]

def b084_08_labels : List Row := [(row3 138 232 139), (row3 408 416 396), (row3 51 53 57), (row3 177 152 150), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 226 237 226), (row3 315 318 318), (row3 331 123 92), (row3 179 153 151), (row3 278 279 279), (row3 234 234 234), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243)]

theorem b084_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_08_rows b084_08_labels 1469063942514931293318715848090 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_08_rows b084_08_labels]
    decide +kernel

def b084_09_rows : List Row := [(row3 15 24 38), (row3 15 24 39), (row3 15 24 40), (row3 15 24 41), (row3 15 24 42), (row3 15 24 43), (row3 15 24 44), (row3 15 24 45), (row3 15 24 46), (row3 15 24 47), (row3 15 24 48), (row3 15 24 49), (row3 15 24 50), (row3 15 24 51), (row3 15 24 52), (row3 15 24 53)]

def b084_09_labels : List Row := [(row3 226 234 226), (row3 295 296 296), (row3 275 276 276), (row3 231 231 234), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 227 231 229), (row3 194 188 195), (row3 278 280 280), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_09_rows b084_09_labels 272328068497210836008832480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_09_rows b084_09_labels]
    decide +kernel

def b084_10_rows : List Row := [(row3 15 24 54), (row3 15 24 55), (row3 15 24 56), (row3 15 24 57), (row3 15 24 58), (row3 15 24 59), (row3 15 24 60), (row3 15 24 61), (row3 15 24 62), (row3 15 24 63), (row3 15 25 26), (row3 15 25 27), (row3 15 25 28), (row3 15 25 29), (row3 15 25 30), (row3 15 25 31)]

def b084_10_labels : List Row := [(row3 228 235 232), (row3 295 297 297), (row3 366 375 353), (row3 175 161 175), (row3 278 279 279), (row3 236 236 462), (row3 462 462 462), (row3 225 236 228), (row3 319 320 320), (row3 128 126 125), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 288 288 462)]

theorem b084_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_10_rows b084_10_labels 17635305519775167153941308170 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_10_rows b084_10_labels]
    decide +kernel

def b084_11_rows : List Row := [(row3 15 25 32), (row3 15 25 33), (row3 15 25 34), (row3 15 25 35), (row3 15 25 36), (row3 15 25 37), (row3 15 25 38), (row3 15 25 39), (row3 15 25 40), (row3 15 25 41), (row3 15 25 42), (row3 15 25 43), (row3 15 25 44), (row3 15 25 45), (row3 15 25 46), (row3 15 25 47)]

def b084_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_11_rows b084_11_labels 1002572601206450985900000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_11_rows b084_11_labels]
    decide +kernel

def b084_12_rows : List Row := [(row3 15 25 48), (row3 15 25 49), (row3 15 25 50), (row3 15 25 51), (row3 15 25 52), (row3 15 25 53), (row3 15 25 54), (row3 15 25 55), (row3 15 25 56), (row3 15 25 57), (row3 15 25 58), (row3 15 25 59), (row3 15 25 60), (row3 15 25 61), (row3 15 25 62), (row3 15 25 63)]

def b084_12_labels : List Row := [(row3 273 462 273), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 235 232), (row3 160 228 163), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 228 232), (row3 300 278 288)]

theorem b084_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_12_rows b084_12_labels 785811035554005214158955200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_12_rows b084_12_labels]
    decide +kernel

def b084_13_rows : List Row := [(row3 15 26 27), (row3 15 26 28), (row3 15 26 29), (row3 15 26 30), (row3 15 26 31), (row3 15 26 32), (row3 15 26 33), (row3 15 26 34), (row3 15 26 35), (row3 15 26 36), (row3 15 26 37), (row3 15 26 38), (row3 15 26 39), (row3 15 26 40), (row3 15 26 41), (row3 15 26 42)]

def b084_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_13_rows b084_13_labels 197302771390542844068000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_13_rows b084_13_labels]
    decide +kernel

def b084_14_rows : List Row := [(row3 15 26 43), (row3 15 26 44), (row3 15 26 45), (row3 15 26 46), (row3 15 26 47), (row3 15 26 48), (row3 15 26 49), (row3 15 26 50), (row3 15 26 51), (row3 15 26 52), (row3 15 26 53), (row3 15 26 54), (row3 15 26 55), (row3 15 26 56), (row3 15 26 57), (row3 15 26 58)]

def b084_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_14_rows b084_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_14_rows b084_14_labels]
    decide +kernel

def b084_15_rows : List Row := [(row3 15 26 59), (row3 15 26 60), (row3 15 26 61), (row3 15 26 62), (row3 15 26 63), (row3 15 27 28), (row3 15 27 29), (row3 15 27 30), (row3 15 27 31), (row3 15 27 32), (row3 15 27 33), (row3 15 27 34), (row3 15 27 35), (row3 15 27 36), (row3 15 27 37), (row3 15 27 38)]

def b084_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b084_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b084_15_rows b084_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b084_15_rows b084_15_labels]
    decide +kernel

theorem checked084 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_084 QuarticIntegerComputationalData.ids64_084 33019343333964026223747215095170 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b084_00_rows ++ b084_01_rows) ++ (b084_02_rows ++ b084_03_rows)) ++ ((b084_04_rows ++ b084_05_rows) ++ (b084_06_rows ++ b084_07_rows))) ++ (((b084_08_rows ++ b084_09_rows) ++ (b084_10_rows ++ b084_11_rows)) ++ ((b084_12_rows ++ b084_13_rows) ++ (b084_14_rows ++ b084_15_rows))))
    ((((b084_00_labels ++ b084_01_labels) ++ (b084_02_labels ++ b084_03_labels)) ++ ((b084_04_labels ++ b084_05_labels) ++ (b084_06_labels ++ b084_07_labels))) ++ (((b084_08_labels ++ b084_09_labels) ++ (b084_10_labels ++ b084_11_labels)) ++ ((b084_12_labels ++ b084_13_labels) ++ (b084_14_labels ++ b084_15_labels)))) 33019343333964026223747215095170
  exact ((((b084_00_checked.append (c := 178682029196389284809488900500) b084_01_checked (by decide +kernel)).append (c := 14006871195505950491429110431660) (b084_02_checked.append (c := 13828189166309561206619621531160) b084_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 31531584746949895950230560183230) ((b084_04_checked.append (c := 450588897325435695291455824620) b084_05_checked (by decide +kernel)).append (c := 17524713551443945458801449751570) (b084_06_checked.append (c := 17074124654118509763509993926950) b084_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 33019343333964026223747215095170) (((b084_08_checked.append (c := 1469336270583428504154724680570) b084_09_checked (by decide +kernel)).append (c := 1486972578675804877759651888740) (b084_10_checked.append (c := 17636308092376373604927208170) b084_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1487758587014130273516654911940) ((b084_12_checked.append (c := 786008338325395757003023200) b084_13_checked (by decide +kernel)).append (c := 786008338325395757003023200) (b084_14_checked.append (c := 0) b084_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b085_00_rows : List Row := [(row3 15 27 39), (row3 15 27 40), (row3 15 27 41), (row3 15 27 42), (row3 15 27 43), (row3 15 27 44), (row3 15 27 45), (row3 15 27 46), (row3 15 27 47), (row3 15 27 48), (row3 15 27 49), (row3 15 27 50), (row3 15 27 51), (row3 15 27 52), (row3 15 27 53), (row3 15 27 54)]

def b085_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_00_rows b085_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_00_rows b085_00_labels]
    decide +kernel

def b085_01_rows : List Row := [(row3 15 27 55), (row3 15 27 56), (row3 15 27 57), (row3 15 27 58), (row3 15 27 59), (row3 15 27 60), (row3 15 27 61), (row3 15 27 62), (row3 15 27 63), (row3 15 28 29), (row3 15 28 30), (row3 15 28 31), (row3 15 28 32), (row3 15 28 33), (row3 15 28 34), (row3 15 28 35)]

def b085_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_01_rows b085_01_labels 197302771390542844068000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_01_rows b085_01_labels]
    decide +kernel

def b085_02_rows : List Row := [(row3 15 28 36), (row3 15 28 37), (row3 15 28 38), (row3 15 28 39), (row3 15 28 40), (row3 15 28 41), (row3 15 28 42), (row3 15 28 43), (row3 15 28 44), (row3 15 28 45), (row3 15 28 46), (row3 15 28 47), (row3 15 28 48), (row3 15 28 49), (row3 15 28 50), (row3 15 28 51)]

def b085_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_02_rows b085_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_02_rows b085_02_labels]
    decide +kernel

def b085_03_rows : List Row := [(row3 15 28 52), (row3 15 28 53), (row3 15 28 54), (row3 15 28 55), (row3 15 28 56), (row3 15 28 57), (row3 15 28 58), (row3 15 28 59), (row3 15 28 60), (row3 15 28 61), (row3 15 28 62), (row3 15 28 63), (row3 15 29 30), (row3 15 29 31), (row3 15 29 32), (row3 15 29 33)]

def b085_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 288 288 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_03_rows b085_03_labels 112075166047497490702458720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_03_rows b085_03_labels]
    decide +kernel

def b085_04_rows : List Row := [(row3 15 29 34), (row3 15 29 35), (row3 15 29 36), (row3 15 29 37), (row3 15 29 38), (row3 15 29 39), (row3 15 29 40), (row3 15 29 41), (row3 15 29 42), (row3 15 29 43), (row3 15 29 44), (row3 15 29 45), (row3 15 29 46), (row3 15 29 47), (row3 15 29 48), (row3 15 29 49)]

def b085_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_04_rows b085_04_labels 601543560723870591540000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_04_rows b085_04_labels]
    decide +kernel

def b085_05_rows : List Row := [(row3 15 29 50), (row3 15 29 51), (row3 15 29 52), (row3 15 29 53), (row3 15 29 54), (row3 15 29 55), (row3 15 29 56), (row3 15 29 57), (row3 15 29 58), (row3 15 29 59), (row3 15 29 60), (row3 15 29 61), (row3 15 29 62), (row3 15 29 63), (row3 15 30 31), (row3 15 30 32)]

def b085_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 278 278 462), (row3 132 133 137), (row3 232 462 232)]

theorem b085_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_05_rows b085_05_labels 12606186984910544285879068800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_05_rows b085_05_labels]
    decide +kernel

def b085_06_rows : List Row := [(row3 15 30 33), (row3 15 30 34), (row3 15 30 35), (row3 15 30 36), (row3 15 30 37), (row3 15 30 38), (row3 15 30 39), (row3 15 30 40), (row3 15 30 41), (row3 15 30 42), (row3 15 30 43), (row3 15 30 44), (row3 15 30 45), (row3 15 30 46), (row3 15 30 47), (row3 15 30 48)]

def b085_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 232 462 232)]

theorem b085_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_06_rows b085_06_labels 112949417130384812569616880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_06_rows b085_06_labels]
    decide +kernel

def b085_07_rows : List Row := [(row3 15 30 49), (row3 15 30 50), (row3 15 30 51), (row3 15 30 52), (row3 15 30 53), (row3 15 30 54), (row3 15 30 55), (row3 15 30 56), (row3 15 30 57), (row3 15 30 58), (row3 15 30 59), (row3 15 30 60), (row3 15 30 61), (row3 15 30 62), (row3 15 30 63), (row3 15 31 32)]

def b085_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 280 280), (row3 306 309 309), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 306 311 311), (row3 146 149 137), (row3 288 462 288)]

theorem b085_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_07_rows b085_07_labels 886996603362802490954655300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_07_rows b085_07_labels]
    decide +kernel

def b085_08_rows : List Row := [(row3 15 31 33), (row3 15 31 34), (row3 15 31 35), (row3 15 31 36), (row3 15 31 37), (row3 15 31 38), (row3 15 31 39), (row3 15 31 40), (row3 15 31 41), (row3 15 31 42), (row3 15 31 43), (row3 15 31 44), (row3 15 31 45), (row3 15 31 46), (row3 15 31 47), (row3 15 31 48)]

def b085_08_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 288 462 288), (row3 166 190 167), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 288 462 288)]

theorem b085_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_08_rows b085_08_labels 6151898564707744591090004160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_08_rows b085_08_labels]
    decide +kernel

def b085_09_rows : List Row := [(row3 15 31 49), (row3 15 31 50), (row3 15 31 51), (row3 15 31 52), (row3 15 31 53), (row3 15 31 54), (row3 15 31 55), (row3 15 31 56), (row3 15 31 57), (row3 15 31 58), (row3 15 31 59), (row3 15 31 60), (row3 15 31 61), (row3 15 31 62), (row3 15 31 63), (row3 15 32 33)]

def b085_09_labels : List Row := [(row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 194 188 195), (row3 126 137 127), (row3 300 462 300), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 143 137 146), (row3 350 346 349), (row3 462 462 462)]

theorem b085_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_09_rows b085_09_labels 14094590360568851645108256240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_09_rows b085_09_labels]
    decide +kernel

def b085_10_rows : List Row := [(row3 15 32 34), (row3 15 32 35), (row3 15 32 36), (row3 15 32 37), (row3 15 32 38), (row3 15 32 39), (row3 15 32 40), (row3 15 32 41), (row3 15 32 42), (row3 15 32 43), (row3 15 32 44), (row3 15 32 45), (row3 15 32 46), (row3 15 32 47), (row3 15 32 48), (row3 15 32 49)]

def b085_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 235 462 235)]

theorem b085_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_10_rows b085_10_labels 44387829271899876362967360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_10_rows b085_10_labels]
    decide +kernel

def b085_11_rows : List Row := [(row3 15 32 50), (row3 15 32 51), (row3 15 32 52), (row3 15 32 53), (row3 15 32 54), (row3 15 32 55), (row3 15 32 56), (row3 15 32 57), (row3 15 32 58), (row3 15 32 59), (row3 15 32 60), (row3 15 32 61), (row3 15 32 62), (row3 15 32 63), (row3 15 33 34), (row3 15 33 35)]

def b085_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 227 231 229), (row3 187 90 357), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 232 235), (row3 288 288 288), (row3 462 462 462), (row3 462 462 462)]

theorem b085_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_11_rows b085_11_labels 6581333210295354146398414800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_11_rows b085_11_labels]
    decide +kernel

def b085_12_rows : List Row := [(row3 15 33 36), (row3 15 33 37), (row3 15 33 38), (row3 15 33 39), (row3 15 33 40), (row3 15 33 41), (row3 15 33 42), (row3 15 33 43), (row3 15 33 44), (row3 15 33 45), (row3 15 33 46), (row3 15 33 47), (row3 15 33 48), (row3 15 33 49), (row3 15 33 50), (row3 15 33 51)]

def b085_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_12_rows b085_12_labels 734927278539940998876000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_12_rows b085_12_labels]
    decide +kernel

def b085_13_rows : List Row := [(row3 15 33 52), (row3 15 33 53), (row3 15 33 54), (row3 15 33 55), (row3 15 33 56), (row3 15 33 57), (row3 15 33 58), (row3 15 33 59), (row3 15 33 60), (row3 15 33 61), (row3 15 33 62), (row3 15 33 63), (row3 15 34 35), (row3 15 34 36), (row3 15 34 37), (row3 15 34 38)]

def b085_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 284 284), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_13_rows b085_13_labels 63083427792601372044592500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_13_rows b085_13_labels]
    decide +kernel

def b085_14_rows : List Row := [(row3 15 34 39), (row3 15 34 40), (row3 15 34 41), (row3 15 34 42), (row3 15 34 43), (row3 15 34 44), (row3 15 34 45), (row3 15 34 46), (row3 15 34 47), (row3 15 34 48), (row3 15 34 49), (row3 15 34 50), (row3 15 34 51), (row3 15 34 52), (row3 15 34 53), (row3 15 34 54)]

def b085_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_14_rows b085_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_14_rows b085_14_labels]
    decide +kernel

def b085_15_rows : List Row := [(row3 15 34 55), (row3 15 34 56), (row3 15 34 57), (row3 15 34 58), (row3 15 34 59), (row3 15 34 60), (row3 15 34 61), (row3 15 34 62), (row3 15 34 63), (row3 15 35 36), (row3 15 35 37), (row3 15 35 38), (row3 15 35 39), (row3 15 35 40), (row3 15 35 41), (row3 15 35 42)]

def b085_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b085_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b085_15_rows b085_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b085_15_rows b085_15_labels]
    decide +kernel

theorem checked085 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_085 QuarticIntegerComputationalData.ids64_085 40655035337698335065544518760 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b085_00_rows ++ b085_01_rows) ++ (b085_02_rows ++ b085_03_rows)) ++ ((b085_04_rows ++ b085_05_rows) ++ (b085_06_rows ++ b085_07_rows))) ++ (((b085_08_rows ++ b085_09_rows) ++ (b085_10_rows ++ b085_11_rows)) ++ ((b085_12_rows ++ b085_13_rows) ++ (b085_14_rows ++ b085_15_rows))))
    ((((b085_00_labels ++ b085_01_labels) ++ (b085_02_labels ++ b085_03_labels)) ++ ((b085_04_labels ++ b085_05_labels) ++ (b085_06_labels ++ b085_07_labels))) ++ (((b085_08_labels ++ b085_09_labels) ++ (b085_10_labels ++ b085_11_labels)) ++ ((b085_12_labels ++ b085_13_labels) ++ (b085_14_labels ++ b085_15_labels)))) 40655035337698335065544518760
  exact ((((b085_00_checked.append (c := 197302771390542844068000) b085_01_checked (by decide +kernel)).append (c := 112272468818888033546526720) (b085_02_checked.append (c := 112075166047497490702458720) b085_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 13719007017783343493541407700) ((b085_04_checked.append (c := 12606788528471268156470608800) b085_05_checked (by decide +kernel)).append (c := 13606734548964455459994880980) (b085_06_checked.append (c := 999946020493187303524272180) b085_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 40655035337698335065544518760) (((b085_08_checked.append (c := 20246488925276596236198260400) b085_09_checked (by decide +kernel)).append (c := 26872209964843850258959642560) (b085_10_checked.append (c := 6625721039567254022761382160) b085_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 26936028319914991572003111060) ((b085_12_checked.append (c := 63818355071141313043468500) b085_13_checked (by decide +kernel)).append (c := 63818355071141313043468500) (b085_14_checked.append (c := 0) b085_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b086_00_rows : List Row := [(row3 15 35 43), (row3 15 35 44), (row3 15 35 45), (row3 15 35 46), (row3 15 35 47), (row3 15 35 48), (row3 15 35 49), (row3 15 35 50), (row3 15 35 51), (row3 15 35 52), (row3 15 35 53), (row3 15 35 54), (row3 15 35 55), (row3 15 35 56), (row3 15 35 57), (row3 15 35 58)]

def b086_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_00_rows b086_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_00_rows b086_00_labels]
    decide +kernel

def b086_01_rows : List Row := [(row3 15 35 59), (row3 15 35 60), (row3 15 35 61), (row3 15 35 62), (row3 15 35 63), (row3 15 36 37), (row3 15 36 38), (row3 15 36 39), (row3 15 36 40), (row3 15 36 41), (row3 15 36 42), (row3 15 36 43), (row3 15 36 44), (row3 15 36 45), (row3 15 36 46), (row3 15 36 47)]

def b086_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_01_rows b086_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_01_rows b086_01_labels]
    decide +kernel

def b086_02_rows : List Row := [(row3 15 36 48), (row3 15 36 49), (row3 15 36 50), (row3 15 36 51), (row3 15 36 52), (row3 15 36 53), (row3 15 36 54), (row3 15 36 55), (row3 15 36 56), (row3 15 36 57), (row3 15 36 58), (row3 15 36 59), (row3 15 36 60), (row3 15 36 61), (row3 15 36 62), (row3 15 36 63)]

def b086_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_02_rows b086_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_02_rows b086_02_labels]
    decide +kernel

def b086_03_rows : List Row := [(row3 15 37 38), (row3 15 37 39), (row3 15 37 40), (row3 15 37 41), (row3 15 37 42), (row3 15 37 43), (row3 15 37 44), (row3 15 37 45), (row3 15 37 46), (row3 15 37 47), (row3 15 37 48), (row3 15 37 49), (row3 15 37 50), (row3 15 37 51), (row3 15 37 52), (row3 15 37 53)]

def b086_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_03_rows b086_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_03_rows b086_03_labels]
    decide +kernel

def b086_04_rows : List Row := [(row3 15 37 54), (row3 15 37 55), (row3 15 37 56), (row3 15 37 57), (row3 15 37 58), (row3 15 37 59), (row3 15 37 60), (row3 15 37 61), (row3 15 37 62), (row3 15 37 63), (row3 15 38 39), (row3 15 38 40), (row3 15 38 41), (row3 15 38 42), (row3 15 38 43), (row3 15 38 44)]

def b086_04_labels : List Row := [(row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_04_rows b086_04_labels 16399281561312421411978500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_04_rows b086_04_labels]
    decide +kernel

def b086_05_rows : List Row := [(row3 15 38 45), (row3 15 38 46), (row3 15 38 47), (row3 15 38 48), (row3 15 38 49), (row3 15 38 50), (row3 15 38 51), (row3 15 38 52), (row3 15 38 53), (row3 15 38 54), (row3 15 38 55), (row3 15 38 56), (row3 15 38 57), (row3 15 38 58), (row3 15 38 59), (row3 15 38 60)]

def b086_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 231 231 234), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_05_rows b086_05_labels 5273201908386028753164000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_05_rows b086_05_labels]
    decide +kernel

def b086_06_rows : List Row := [(row3 15 38 61), (row3 15 38 62), (row3 15 38 63), (row3 15 39 40), (row3 15 39 41), (row3 15 39 42), (row3 15 39 43), (row3 15 39 44), (row3 15 39 45), (row3 15 39 46), (row3 15 39 47), (row3 15 39 48), (row3 15 39 49), (row3 15 39 50), (row3 15 39 51), (row3 15 39 52)]

def b086_06_labels : List Row := [(row3 462 462 462), (row3 226 226 234), (row3 273 288 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_06_rows b086_06_labels 26237854962352600770621600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_06_rows b086_06_labels]
    decide +kernel

def b086_07_rows : List Row := [(row3 15 39 53), (row3 15 39 54), (row3 15 39 55), (row3 15 39 56), (row3 15 39 57), (row3 15 39 58), (row3 15 39 59), (row3 15 39 60), (row3 15 39 61), (row3 15 39 62), (row3 15 39 63), (row3 15 40 41), (row3 15 40 42), (row3 15 40 43), (row3 15 40 44), (row3 15 40 45)]

def b086_07_labels : List Row := [(row3 462 462 462), (row3 236 462 236), (row3 275 276 276), (row3 278 301 301), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 278 282 282), (row3 165 176 165), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_07_rows b086_07_labels 482045010543635193219044640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_07_rows b086_07_labels]
    decide +kernel

def b086_08_rows : List Row := [(row3 15 40 46), (row3 15 40 47), (row3 15 40 48), (row3 15 40 49), (row3 15 40 50), (row3 15 40 51), (row3 15 40 52), (row3 15 40 53), (row3 15 40 54), (row3 15 40 55), (row3 15 40 56), (row3 15 40 57), (row3 15 40 58), (row3 15 40 59), (row3 15 40 60), (row3 15 40 61)]

def b086_08_labels : List Row := [(row3 462 462 462), (row3 236 236 462), (row3 166 190 167), (row3 278 279 279), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 295 296 296), (row3 372 430 58), (row3 175 161 175), (row3 278 279 279), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462)]

theorem b086_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_08_rows b086_08_labels 144959952566979344246198637420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_08_rows b086_08_labels]
    decide +kernel

def b086_09_rows : List Row := [(row3 15 40 62), (row3 15 40 63), (row3 15 41 42), (row3 15 41 43), (row3 15 41 44), (row3 15 41 45), (row3 15 41 46), (row3 15 41 47), (row3 15 41 48), (row3 15 41 49), (row3 15 41 50), (row3 15 41 51), (row3 15 41 52), (row3 15 41 53), (row3 15 41 54), (row3 15 41 55)]

def b086_09_labels : List Row := [(row3 278 283 283), (row3 125 126 128), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 226 234 226)]

theorem b086_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_09_rows b086_09_labels 850430288517450899799160980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_09_rows b086_09_labels]
    decide +kernel

def b086_10_rows : List Row := [(row3 15 41 56), (row3 15 41 57), (row3 15 41 58), (row3 15 41 59), (row3 15 41 60), (row3 15 41 61), (row3 15 41 62), (row3 15 41 63), (row3 15 42 43), (row3 15 42 44), (row3 15 42 45), (row3 15 42 46), (row3 15 42 47), (row3 15 42 48), (row3 15 42 49), (row3 15 42 50)]

def b086_10_labels : List Row := [(row3 157 83 399), (row3 300 462 300), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 278 300), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b086_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_10_rows b086_10_labels 20362501690304095447208004960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_10_rows b086_10_labels]
    decide +kernel

def b086_11_rows : List Row := [(row3 15 42 51), (row3 15 42 52), (row3 15 42 53), (row3 15 42 54), (row3 15 42 55), (row3 15 42 56), (row3 15 42 57), (row3 15 42 58), (row3 15 42 59), (row3 15 42 60), (row3 15 42 61), (row3 15 42 62), (row3 15 42 63), (row3 15 43 44), (row3 15 43 45), (row3 15 43 46)]

def b086_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 293 293), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_11_rows b086_11_labels 96134672006406593158288500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_11_rows b086_11_labels]
    decide +kernel

def b086_12_rows : List Row := [(row3 15 43 47), (row3 15 43 48), (row3 15 43 49), (row3 15 43 50), (row3 15 43 51), (row3 15 43 52), (row3 15 43 53), (row3 15 43 54), (row3 15 43 55), (row3 15 43 56), (row3 15 43 57), (row3 15 43 58), (row3 15 43 59), (row3 15 43 60), (row3 15 43 61), (row3 15 43 62)]

def b086_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_12_rows b086_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_12_rows b086_12_labels]
    decide +kernel

def b086_13_rows : List Row := [(row3 15 43 63), (row3 15 44 45), (row3 15 44 46), (row3 15 44 47), (row3 15 44 48), (row3 15 44 49), (row3 15 44 50), (row3 15 44 51), (row3 15 44 52), (row3 15 44 53), (row3 15 44 54), (row3 15 44 55), (row3 15 44 56), (row3 15 44 57), (row3 15 44 58), (row3 15 44 59)]

def b086_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b086_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_13_rows b086_13_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_13_rows b086_13_labels]
    decide +kernel

def b086_14_rows : List Row := [(row3 15 44 60), (row3 15 44 61), (row3 15 44 62), (row3 15 44 63), (row3 15 45 46), (row3 15 45 47), (row3 15 45 48), (row3 15 45 49), (row3 15 45 50), (row3 15 45 51), (row3 15 45 52), (row3 15 45 53), (row3 15 45 54), (row3 15 45 55), (row3 15 45 56), (row3 15 45 57)]

def b086_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462)]

theorem b086_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_14_rows b086_14_labels 1287958078520632533352500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_14_rows b086_14_labels]
    decide +kernel

def b086_15_rows : List Row := [(row3 15 45 58), (row3 15 45 59), (row3 15 45 60), (row3 15 45 61), (row3 15 45 62), (row3 15 45 63), (row3 15 46 47), (row3 15 46 48), (row3 15 46 49), (row3 15 46 50), (row3 15 46 51), (row3 15 46 52), (row3 15 46 53), (row3 15 46 54), (row3 15 46 55), (row3 15 46 56)]

def b086_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 278 278), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 279 279), (row3 462 293 293)]

theorem b086_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b086_15_rows b086_15_labels 171121659751208143780781580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b086_15_rows b086_15_labels]
    decide +kernel

theorem checked086 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_086 QuarticIntegerComputationalData.ids64_086 166971400286720525823387679680 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b086_00_rows ++ b086_01_rows) ++ (b086_02_rows ++ b086_03_rows)) ++ ((b086_04_rows ++ b086_05_rows) ++ (b086_06_rows ++ b086_07_rows))) ++ (((b086_08_rows ++ b086_09_rows) ++ (b086_10_rows ++ b086_11_rows)) ++ ((b086_12_rows ++ b086_13_rows) ++ (b086_14_rows ++ b086_15_rows))))
    ((((b086_00_labels ++ b086_01_labels) ++ (b086_02_labels ++ b086_03_labels)) ++ ((b086_04_labels ++ b086_05_labels) ++ (b086_06_labels ++ b086_07_labels))) ++ (((b086_08_labels ++ b086_09_labels) ++ (b086_10_labels ++ b086_11_labels)) ++ ((b086_12_labels ++ b086_13_labels) ++ (b086_14_labels ++ b086_15_labels)))) 166971400286720525823387679680
  exact ((((b086_00_checked.append (c := 0) b086_01_checked (by decide +kernel)).append (c := 0) (b086_02_checked.append (c := 0) b086_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 529955348975686244154808740) ((b086_04_checked.append (c := 21672483469698450165142500) b086_05_checked (by decide +kernel)).append (c := 529955348975686244154808740) (b086_06_checked.append (c := 508282865505987793989666240) b086_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 166971400286720525823387679680) (((b086_08_checked.append (c := 145810382855496795145997798400) b086_09_checked (by decide +kernel)).append (c := 166269019217807297186364091860) (b086_10_checked.append (c := 20458636362310502040366293460) b086_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 166441444937744839579232870940) ((b086_12_checked.append (c := 16102107813616554645000) b086_13_checked (by decide +kernel)).append (c := 172425719937542392868779080) (b086_14_checked.append (c := 172409617829728776314134080) b086_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b087_00_rows : List Row := [(row3 15 46 57), (row3 15 46 58), (row3 15 46 59), (row3 15 46 60), (row3 15 46 61), (row3 15 46 62), (row3 15 46 63), (row3 15 47 48), (row3 15 47 49), (row3 15 47 50), (row3 15 47 51), (row3 15 47 52), (row3 15 47 53), (row3 15 47 54), (row3 15 47 55), (row3 15 47 56)]

def b087_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291), (row3 137 149 146), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 179 153 151), (row3 156 82 399)]

theorem b087_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_00_rows b087_00_labels 27350806391886569325195936960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_00_rows b087_00_labels]
    decide +kernel

def b087_01_rows : List Row := [(row3 15 47 57), (row3 15 47 58), (row3 15 47 59), (row3 15 47 60), (row3 15 47 61), (row3 15 47 62), (row3 15 47 63), (row3 15 48 49), (row3 15 48 50), (row3 15 48 51), (row3 15 48 52), (row3 15 48 53), (row3 15 48 54), (row3 15 48 55), (row3 15 48 56), (row3 15 48 57)]

def b087_01_labels : List Row := [(row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 220 222 221), (row3 349 346 350), (row3 132 133 137), (row3 288 288 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 288 288 462), (row3 331 123 92), (row3 47 26 453), (row3 382 378 381)]

theorem b087_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_01_rows b087_01_labels 12507919889745560104295068075200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_01_rows b087_01_labels]
    decide +kernel

def b087_02_rows : List Row := [(row3 15 48 58), (row3 15 48 59), (row3 15 48 60), (row3 15 48 61), (row3 15 48 62), (row3 15 48 63), (row3 15 49 50), (row3 15 49 51), (row3 15 49 52), (row3 15 49 53), (row3 15 49 54), (row3 15 49 55), (row3 15 49 56), (row3 15 49 57), (row3 15 49 58), (row3 15 49 59)]

def b087_02_labels : List Row := [(row3 144 147 137), (row3 273 273 462), (row3 462 462 462), (row3 273 273 462), (row3 141 142 136), (row3 404 402 403), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 315 318 318), (row3 412 437 39), (row3 100 113 100), (row3 306 309 309), (row3 232 232 462)]

theorem b087_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_02_rows b087_02_labels 405639826381320310613121908940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_02_rows b087_02_labels]
    decide +kernel

def b087_03_rows : List Row := [(row3 15 49 60), (row3 15 49 61), (row3 15 49 62), (row3 15 49 63), (row3 15 50 51), (row3 15 50 52), (row3 15 50 53), (row3 15 50 54), (row3 15 50 55), (row3 15 50 56), (row3 15 50 57), (row3 15 50 58), (row3 15 50 59), (row3 15 50 60), (row3 15 50 61), (row3 15 50 62)]

def b087_03_labels : List Row := [(row3 462 462 462), (row3 232 232 462), (row3 306 312 312), (row3 99 98 101), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 226 237 226), (row3 135 83 398), (row3 319 462 319), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228)]

theorem b087_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_03_rows b087_03_labels 21837152757211331862566375640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_03_rows b087_03_labels]
    decide +kernel

def b087_04_rows : List Row := [(row3 15 50 63), (row3 15 51 52), (row3 15 51 53), (row3 15 51 54), (row3 15 51 55), (row3 15 51 56), (row3 15 51 57), (row3 15 51 58), (row3 15 51 59), (row3 15 51 60), (row3 15 51 61), (row3 15 51 62), (row3 15 51 63), (row3 15 52 53), (row3 15 52 54), (row3 15 52 55)]

def b087_04_labels : List Row := [(row3 295 273 304), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 284 284), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237)]

theorem b087_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_04_rows b087_04_labels 97379776176452416807204500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_04_rows b087_04_labels]
    decide +kernel

def b087_05_rows : List Row := [(row3 15 52 56), (row3 15 52 57), (row3 15 52 58), (row3 15 52 59), (row3 15 52 60), (row3 15 52 61), (row3 15 52 62), (row3 15 52 63), (row3 15 53 54), (row3 15 53 55), (row3 15 53 56), (row3 15 53 57), (row3 15 53 58), (row3 15 53 59), (row3 15 53 60), (row3 15 53 61)]

def b087_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 462 273 273), (row3 462 462 462), (row3 265 266 266), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b087_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_05_rows b087_05_labels 91414216300763926792222920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_05_rows b087_05_labels]
    decide +kernel

def b087_06_rows : List Row := [(row3 15 53 62), (row3 15 53 63), (row3 15 54 55), (row3 15 54 56), (row3 15 54 57), (row3 15 54 58), (row3 15 54 59), (row3 15 54 60), (row3 15 54 61), (row3 15 54 62), (row3 15 54 63), (row3 15 55 56), (row3 15 55 57), (row3 15 55 58), (row3 15 55 59), (row3 15 55 60)]

def b087_06_labels : List Row := [(row3 306 309 309), (row3 137 149 146), (row3 177 152 150), (row3 134 81 398), (row3 295 462 295), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 129 103 102), (row3 382 378 381), (row3 413 438 40), (row3 120 112 120), (row3 306 310 310), (row3 232 232 462), (row3 462 243 243)]

theorem b087_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_06_rows b087_06_labels 448426731639529320383600513820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_06_rows b087_06_labels]
    decide +kernel

def b087_07_rows : List Row := [(row3 15 55 61), (row3 15 55 62), (row3 15 55 63), (row3 15 56 57), (row3 15 56 58), (row3 15 56 59), (row3 15 56 60), (row3 15 56 61), (row3 15 56 62), (row3 15 56 63), (row3 15 57 58), (row3 15 57 59), (row3 15 57 60), (row3 15 57 61), (row3 15 57 62), (row3 15 57 63)]

def b087_07_labels : List Row := [(row3 224 226 229), (row3 323 324 324), (row3 57 53 51), (row3 32 452 25), (row3 410 59 431), (row3 159 356 91), (row3 462 269 269), (row3 158 356 89), (row3 411 60 432), (row3 442 451 24), (row3 100 100 113), (row3 300 300 462), (row3 235 235 462), (row3 288 288 462), (row3 120 120 112), (row3 406 406 405)]

theorem b087_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_07_rows b087_07_labels 43308959138815836066243585714540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_07_rows b087_07_labels]
    decide +kernel

def b087_08_rows : List Row := [(row3 15 58 59), (row3 15 58 60), (row3 15 58 61), (row3 15 58 62), (row3 15 58 63), (row3 15 59 60), (row3 15 59 61), (row3 15 59 62), (row3 15 59 63), (row3 15 60 61), (row3 15 60 62), (row3 15 60 63), (row3 15 61 62), (row3 15 61 63), (row3 15 62 63), (row3 16 17 18)]

def b087_08_labels : List Row := [(row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 306 311 311), (row3 110 109 111), (row3 462 462 462), (row3 462 462 462), (row3 226 234 226), (row3 288 261 290), (row3 462 462 462), (row3 289 291 291), (row3 190 199 198), (row3 129 102 103), (row3 351 348 350), (row3 61 48 50), (row3 37 28 444)]

theorem b087_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_08_rows b087_08_labels 5889261036610750770060812693820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_08_rows b087_08_labels]
    decide +kernel

def b087_09_rows : List Row := [(row3 16 17 19), (row3 16 17 20), (row3 16 17 21), (row3 16 17 22), (row3 16 17 23), (row3 16 17 24), (row3 16 17 25), (row3 16 17 26), (row3 16 17 27), (row3 16 17 28), (row3 16 17 29), (row3 16 17 30), (row3 16 17 31), (row3 16 17 32), (row3 16 17 33), (row3 16 17 34)]

def b087_09_labels : List Row := [(row3 385 426 77), (row3 168 94 333), (row3 339 342 328), (row3 68 69 76), (row3 455 447 447), (row3 454 449 448), (row3 34 27 443), (row3 410 431 59), (row3 122 86 369), (row3 462 284 284), (row3 193 462 193), (row3 387 390 360), (row3 49 52 62), (row3 67 67 79), (row3 401 427 78), (row3 114 86 368)]

theorem b087_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_09_rows b087_09_labels 20492019675329098934888696901900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_09_rows b087_09_labels]
    decide +kernel

def b087_10_rows : List Row := [(row3 16 17 35), (row3 16 17 36), (row3 16 17 37), (row3 16 17 38), (row3 16 17 39), (row3 16 17 40), (row3 16 17 41), (row3 16 17 42), (row3 16 17 43), (row3 16 17 44), (row3 16 17 45), (row3 16 17 46), (row3 16 17 47), (row3 16 17 48), (row3 16 17 49), (row3 16 17 50)]

def b087_10_labels : List Row := [(row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 180 462 180), (row3 387 391 361), (row3 340 344 329), (row3 155 93 332), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 191 235 193), (row3 174 178 174), (row3 289 299 299), (row3 234 234 462)]

theorem b087_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_10_rows b087_10_labels 28269485356971025907297029980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_10_rows b087_10_labels]
    decide +kernel

def b087_11_rows : List Row := [(row3 16 17 51), (row3 16 17 52), (row3 16 17 53), (row3 16 17 54), (row3 16 17 55), (row3 16 17 56), (row3 16 17 57), (row3 16 17 58), (row3 16 17 59), (row3 16 17 60), (row3 16 17 61), (row3 16 17 62), (row3 16 17 63), (row3 16 18 19), (row3 16 18 20), (row3 16 18 21)]

def b087_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 397 400 384), (row3 123 92 331), (row3 289 305 305), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 133 137 132), (row3 164 206 164), (row3 273 462 273), (row3 209 206 209)]

theorem b087_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_11_rows b087_11_labels 1388034074216737344875705093340 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_11_rows b087_11_labels]
    decide +kernel

def b087_12_rows : List Row := [(row3 16 18 22), (row3 16 18 23), (row3 16 18 24), (row3 16 18 25), (row3 16 18 26), (row3 16 18 27), (row3 16 18 28), (row3 16 18 29), (row3 16 18 30), (row3 16 18 31), (row3 16 18 32), (row3 16 18 33), (row3 16 18 34), (row3 16 18 35), (row3 16 18 36), (row3 16 18 37)]

def b087_12_labels : List Row := [(row3 327 327 327), (row3 68 76 69), (row3 69 76 68), (row3 351 350 348), (row3 140 178 140), (row3 288 462 288), (row3 234 462 234), (row3 261 462 261), (row3 184 178 184), (row3 345 347 345), (row3 327 327 327), (row3 182 178 182), (row3 278 462 278), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462)]

theorem b087_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_12_rows b087_12_labels 199384569953923239535168591200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_12_rows b087_12_labels]
    decide +kernel

def b087_13_rows : List Row := [(row3 16 18 38), (row3 16 18 39), (row3 16 18 40), (row3 16 18 41), (row3 16 18 42), (row3 16 18 43), (row3 16 18 44), (row3 16 18 45), (row3 16 18 46), (row3 16 18 47), (row3 16 18 48), (row3 16 18 49), (row3 16 18 50), (row3 16 18 51), (row3 16 18 52), (row3 16 18 53)]

def b087_13_labels : List Row := [(row3 265 462 265), (row3 184 178 184), (row3 209 206 209), (row3 261 462 261), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 273 462 273), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b087_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_13_rows b087_13_labels 135015255783276429256365600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_13_rows b087_13_labels]
    decide +kernel

def b087_14_rows : List Row := [(row3 16 18 54), (row3 16 18 55), (row3 16 18 56), (row3 16 18 57), (row3 16 18 58), (row3 16 18 59), (row3 16 18 60), (row3 16 18 61), (row3 16 18 62), (row3 16 18 63), (row3 16 19 20), (row3 16 19 21), (row3 16 19 22), (row3 16 19 23), (row3 16 19 24), (row3 16 19 25)]

def b087_14_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 164 206 164), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 288 462 288), (row3 239 462 239), (row3 255 256 256), (row3 209 209 206), (row3 339 328 342), (row3 338 330 343), (row3 197 196 190)]

theorem b087_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_14_rows b087_14_labels 13171628610905999262453410100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_14_rows b087_14_labels]
    decide +kernel

def b087_15_rows : List Row := [(row3 16 19 26), (row3 16 19 27), (row3 16 19 28), (row3 16 19 29), (row3 16 19 30), (row3 16 19 31), (row3 16 19 32), (row3 16 19 33), (row3 16 19 34), (row3 16 19 35), (row3 16 19 36), (row3 16 19 37), (row3 16 19 38), (row3 16 19 39), (row3 16 19 40), (row3 16 19 41)]

def b087_15_labels : List Row := [(row3 265 266 266), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 265 266 266), (row3 199 198 190), (row3 210 210 206), (row3 265 266 266), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 265 266 266), (row3 255 256 256), (row3 238 462 238)]

theorem b087_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b087_15_rows b087_15_labels 133733793866478967400173680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b087_15_rows b087_15_labels]
    decide +kernel

theorem checked087 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_087 QuarticIntegerComputationalData.ids64_087 84730731558851857988993528212140 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b087_00_rows ++ b087_01_rows) ++ (b087_02_rows ++ b087_03_rows)) ++ ((b087_04_rows ++ b087_05_rows) ++ (b087_06_rows ++ b087_07_rows))) ++ (((b087_08_rows ++ b087_09_rows) ++ (b087_10_rows ++ b087_11_rows)) ++ ((b087_12_rows ++ b087_13_rows) ++ (b087_14_rows ++ b087_15_rows))))
    ((((b087_00_labels ++ b087_01_labels) ++ (b087_02_labels ++ b087_03_labels)) ++ ((b087_04_labels ++ b087_05_labels) ++ (b087_06_labels ++ b087_07_labels))) ++ (((b087_08_labels ++ b087_09_labels) ++ (b087_10_labels ++ b087_11_labels)) ++ ((b087_12_labels ++ b087_13_labels) ++ (b087_14_labels ++ b087_15_labels)))) 84730731558851857988993528212140
  exact ((((b087_00_checked.append (c := 12535270696137446673620264012160) b087_01_checked (by decide +kernel)).append (c := 12962747675275978316095952296740) (b087_02_checked.append (c := 427476979138531642475688284580) b087_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 56720322339723820919066737952520) ((b087_04_checked.append (c := 188793992477216343599427420) b087_05_checked (by decide +kernel)).append (c := 43757574664447842602970785655780) (b087_06_checked.append (c := 43757385870455365386627186228360) b087_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 84730731558851857988993528212140) (((b087_08_checked.append (c := 26381280711939849704949509595720) b087_09_checked (by decide +kernel)).append (c := 27797584271513558075732511719040) (b087_10_checked.append (c := 1416303559573708370783002123320) b087_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 28010409219128037069926790259620) ((b087_12_checked.append (c := 199519585209706515964424956800) b087_13_checked (by decide +kernel)).append (c := 212824947614478994194278540580) (b087_14_checked.append (c := 13305362404772478229853583780) b087_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b088_00_rows : List Row := [(row3 16 19 42), (row3 16 19 43), (row3 16 19 44), (row3 16 19 45), (row3 16 19 46), (row3 16 19 47), (row3 16 19 48), (row3 16 19 49), (row3 16 19 50), (row3 16 19 51), (row3 16 19 52), (row3 16 19 53), (row3 16 19 54), (row3 16 19 55), (row3 16 19 56), (row3 16 19 57)]

def b088_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 238 462 238)]

theorem b088_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_00_rows b088_00_labels 14595532271321915056576800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_00_rows b088_00_labels]
    decide +kernel

def b088_01_rows : List Row := [(row3 16 19 58), (row3 16 19 59), (row3 16 19 60), (row3 16 19 61), (row3 16 19 62), (row3 16 19 63), (row3 16 20 21), (row3 16 20 22), (row3 16 20 23), (row3 16 20 24), (row3 16 20 25), (row3 16 20 26), (row3 16 20 27), (row3 16 20 28), (row3 16 20 29), (row3 16 20 30)]

def b088_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 239 239 462), (row3 273 273 462), (row3 168 333 94), (row3 208 208 462), (row3 261 261 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462)]

theorem b088_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_01_rows b088_01_labels 3411737216769728607258127680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_01_rows b088_01_labels]
    decide +kernel

def b088_02_rows : List Row := [(row3 16 20 31), (row3 16 20 32), (row3 16 20 33), (row3 16 20 34), (row3 16 20 35), (row3 16 20 36), (row3 16 20 37), (row3 16 20 38), (row3 16 20 39), (row3 16 20 40), (row3 16 20 41), (row3 16 20 42), (row3 16 20 43), (row3 16 20 44), (row3 16 20 45), (row3 16 20 46)]

def b088_02_labels : List Row := [(row3 261 261 462), (row3 255 255 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b088_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_02_rows b088_02_labels 4277879960514180154646400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_02_rows b088_02_labels]
    decide +kernel

def b088_03_rows : List Row := [(row3 16 20 47), (row3 16 20 48), (row3 16 20 49), (row3 16 20 50), (row3 16 20 51), (row3 16 20 52), (row3 16 20 53), (row3 16 20 54), (row3 16 20 55), (row3 16 20 56), (row3 16 20 57), (row3 16 20 58), (row3 16 20 59), (row3 16 20 60), (row3 16 20 61), (row3 16 20 62)]

def b088_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b088_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_03_rows b088_03_labels 277944607559135344716000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_03_rows b088_03_labels]
    decide +kernel

def b088_04_rows : List Row := [(row3 16 20 63), (row3 16 21 22), (row3 16 21 23), (row3 16 21 24), (row3 16 21 25), (row3 16 21 26), (row3 16 21 27), (row3 16 21 28), (row3 16 21 29), (row3 16 21 30), (row3 16 21 31), (row3 16 21 32), (row3 16 21 33), (row3 16 21 34), (row3 16 21 35), (row3 16 21 36)]

def b088_04_labels : List Row := [(row3 462 462 462), (row3 164 164 206), (row3 385 77 426), (row3 338 330 343), (row3 199 198 190), (row3 265 266 266), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 265 266 266), (row3 197 196 190), (row3 210 210 206), (row3 265 266 266), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b088_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_04_rows b088_04_labels 72698985176182223572215135090 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_04_rows b088_04_labels]
    decide +kernel

def b088_05_rows : List Row := [(row3 16 21 37), (row3 16 21 38), (row3 16 21 39), (row3 16 21 40), (row3 16 21 41), (row3 16 21 42), (row3 16 21 43), (row3 16 21 44), (row3 16 21 45), (row3 16 21 46), (row3 16 21 47), (row3 16 21 48), (row3 16 21 49), (row3 16 21 50), (row3 16 21 51), (row3 16 21 52)]

def b088_05_labels : List Row := [(row3 462 462 462), (row3 237 462 237), (row3 265 266 266), (row3 255 256 256), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b088_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_05_rows b088_05_labels 4688376090872672390527200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_05_rows b088_05_labels]
    decide +kernel

def b088_06_rows : List Row := [(row3 16 21 53), (row3 16 21 54), (row3 16 21 55), (row3 16 21 56), (row3 16 21 57), (row3 16 21 58), (row3 16 21 59), (row3 16 21 60), (row3 16 21 61), (row3 16 21 62), (row3 16 21 63), (row3 16 22 23), (row3 16 22 24), (row3 16 22 25), (row3 16 22 26), (row3 16 22 27)]

def b088_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 37 444 28), (row3 69 76 68), (row3 345 347 345), (row3 184 178 184), (row3 261 462 261)]

theorem b088_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_06_rows b088_06_labels 4603499332650272147021917097520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_06_rows b088_06_labels]
    decide +kernel

def b088_07_rows : List Row := [(row3 16 22 28), (row3 16 22 29), (row3 16 22 30), (row3 16 22 31), (row3 16 22 32), (row3 16 22 33), (row3 16 22 34), (row3 16 22 35), (row3 16 22 36), (row3 16 22 37), (row3 16 22 38), (row3 16 22 39), (row3 16 22 40), (row3 16 22 41), (row3 16 22 42), (row3 16 22 43)]

def b088_07_labels : List Row := [(row3 234 462 234), (row3 288 462 288), (row3 140 178 140), (row3 351 350 348), (row3 327 327 327), (row3 184 178 184), (row3 265 462 265), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 182 178 182), (row3 209 206 209), (row3 261 462 261), (row3 462 462 462), (row3 462 462 462)]

theorem b088_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_07_rows b088_07_labels 10974630208430922442528492800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_07_rows b088_07_labels]
    decide +kernel

def b088_08_rows : List Row := [(row3 16 22 44), (row3 16 22 45), (row3 16 22 46), (row3 16 22 47), (row3 16 22 48), (row3 16 22 49), (row3 16 22 50), (row3 16 22 51), (row3 16 22 52), (row3 16 22 53), (row3 16 22 54), (row3 16 22 55), (row3 16 22 56), (row3 16 22 57), (row3 16 22 58), (row3 16 22 59)]

def b088_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 261 462 261), (row3 273 462 273), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 164 206 164), (row3 288 462 288), (row3 234 462 234), (row3 462 462 462)]

theorem b088_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_08_rows b088_08_labels 3312677640887709558943368960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_08_rows b088_08_labels]
    decide +kernel

def b088_09_rows : List Row := [(row3 16 22 60), (row3 16 22 61), (row3 16 22 62), (row3 16 22 63), (row3 16 23 24), (row3 16 23 25), (row3 16 23 26), (row3 16 23 27), (row3 16 23 28), (row3 16 23 29), (row3 16 23 30), (row3 16 23 31), (row3 16 23 32), (row3 16 23 33), (row3 16 23 34), (row3 16 23 35)]

def b088_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 454 449 448), (row3 49 52 62), (row3 387 390 360), (row3 193 462 193), (row3 462 284 284), (row3 122 86 369), (row3 410 431 59), (row3 34 27 443), (row3 67 67 79), (row3 387 391 361), (row3 180 462 180), (row3 462 462 462)]

theorem b088_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_09_rows b088_09_labels 12749943362384145401120727214620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_09_rows b088_09_labels]
    decide +kernel

def b088_10_rows : List Row := [(row3 16 23 36), (row3 16 23 37), (row3 16 23 38), (row3 16 23 39), (row3 16 23 40), (row3 16 23 41), (row3 16 23 42), (row3 16 23 43), (row3 16 23 44), (row3 16 23 45), (row3 16 23 46), (row3 16 23 47), (row3 16 23 48), (row3 16 23 49), (row3 16 23 50), (row3 16 23 51)]

def b088_10_labels : List Row := [(row3 462 462 462), (row3 462 293 293), (row3 114 86 368), (row3 401 427 78), (row3 340 344 329), (row3 191 235 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 155 93 332), (row3 174 178 174), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462)]

theorem b088_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_10_rows b088_10_labels 91975841555239556243564327370 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_10_rows b088_10_labels]
    decide +kernel

def b088_11_rows : List Row := [(row3 16 23 52), (row3 16 23 53), (row3 16 23 54), (row3 16 23 55), (row3 16 23 56), (row3 16 23 57), (row3 16 23 58), (row3 16 23 59), (row3 16 23 60), (row3 16 23 61), (row3 16 23 62), (row3 16 23 63), (row3 16 24 25), (row3 16 24 26), (row3 16 24 27), (row3 16 24 28)]

def b088_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 299 299), (row3 397 400 384), (row3 133 137 132), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 305 305), (row3 123 92 331), (row3 56 29 445), (row3 385 426 77), (row3 202 97 334), (row3 462 257 257)]

theorem b088_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_11_rows b088_11_labels 5609681238644991610836507765720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_11_rows b088_11_labels]
    decide +kernel

def b088_12_rows : List Row := [(row3 16 24 29), (row3 16 24 30), (row3 16 24 31), (row3 16 24 32), (row3 16 24 33), (row3 16 24 34), (row3 16 24 35), (row3 16 24 36), (row3 16 24 37), (row3 16 24 38), (row3 16 24 39), (row3 16 24 40), (row3 16 24 41), (row3 16 24 42), (row3 16 24 43), (row3 16 24 44)]

def b088_12_labels : List Row := [(row3 202 97 334), (row3 385 426 77), (row3 56 29 445), (row3 80 30 446), (row3 372 430 58), (row3 211 88 370), (row3 462 263 263), (row3 462 462 462), (row3 462 263 263), (row3 211 88 370), (row3 372 430 58), (row3 326 425 75), (row3 325 87 371), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462)]

theorem b088_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_12_rows b088_12_labels 8370902907536752792383347022540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_12_rows b088_12_labels]
    decide +kernel

def b088_13_rows : List Row := [(row3 16 24 45), (row3 16 24 46), (row3 16 24 47), (row3 16 24 48), (row3 16 24 49), (row3 16 24 50), (row3 16 24 51), (row3 16 24 52), (row3 16 24 53), (row3 16 24 54), (row3 16 24 55), (row3 16 24 56), (row3 16 24 57), (row3 16 24 58), (row3 16 24 59), (row3 16 24 60)]

def b088_13_labels : List Row := [(row3 462 462 462), (row3 462 269 269), (row3 325 87 371), (row3 205 96 335), (row3 265 277 277), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 265 277 277), (row3 364 374 355), (row3 167 190 166), (row3 265 266 266), (row3 238 238 462), (row3 462 462 462)]

theorem b088_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_13_rows b088_13_labels 710350510982590874262323736120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_13_rows b088_13_labels]
    decide +kernel

def b088_14_rows : List Row := [(row3 16 24 61), (row3 16 24 62), (row3 16 24 63), (row3 16 25 26), (row3 16 25 27), (row3 16 25 28), (row3 16 25 29), (row3 16 25 30), (row3 16 25 31), (row3 16 25 32), (row3 16 25 33), (row3 16 25 34), (row3 16 25 35), (row3 16 25 36), (row3 16 25 37), (row3 16 25 38)]

def b088_14_labels : List Row := [(row3 238 238 462), (row3 265 266 266), (row3 167 190 166), (row3 127 137 126), (row3 288 462 288), (row3 236 462 236), (row3 273 462 273), (row3 148 137 145), (row3 379 380 380), (row3 349 346 350), (row3 127 137 126), (row3 300 462 300), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278)]

theorem b088_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_14_rows b088_14_labels 35972389603149244055662938480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_14_rows b088_14_labels]
    decide +kernel

def b088_15_rows : List Row := [(row3 16 25 39), (row3 16 25 40), (row3 16 25 41), (row3 16 25 42), (row3 16 25 43), (row3 16 25 44), (row3 16 25 45), (row3 16 25 46), (row3 16 25 47), (row3 16 25 48), (row3 16 25 49), (row3 16 25 50), (row3 16 25 51), (row3 16 25 52), (row3 16 25 53), (row3 16 25 54)]

def b088_15_labels : List Row := [(row3 146 137 143), (row3 195 188 194), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 273 462 273), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b088_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b088_15_rows b088_15_labels 429233905616316784093388880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b088_15_rows b088_15_labels]
    decide +kernel

theorem checked088 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_088 QuarticIntegerComputationalData.ids64_088 32263176687237958794792035082180 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b088_00_rows ++ b088_01_rows) ++ (b088_02_rows ++ b088_03_rows)) ++ ((b088_04_rows ++ b088_05_rows) ++ (b088_06_rows ++ b088_07_rows))) ++ (((b088_08_rows ++ b088_09_rows) ++ (b088_10_rows ++ b088_11_rows)) ++ ((b088_12_rows ++ b088_13_rows) ++ (b088_14_rows ++ b088_15_rows))))
    ((((b088_00_labels ++ b088_01_labels) ++ (b088_02_labels ++ b088_03_labels)) ++ ((b088_04_labels ++ b088_05_labels) ++ (b088_06_labels ++ b088_07_labels))) ++ (((b088_08_labels ++ b088_09_labels) ++ (b088_10_labels ++ b088_11_labels)) ++ ((b088_12_labels ++ b088_13_labels) ++ (b088_14_labels ++ b088_15_labels)))) 32263176687237958794792035082180
  exact ((((b088_00_checked.append (c := 3426332749041050522314704480) b088_01_checked (by decide +kernel)).append (c := 3430888573609123837814066880) (b088_02_checked.append (c := 4555824568073315499362400) b088_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4690608524984585289546865319490) ((b088_04_checked.append (c := 72703673552273096244605662290) b088_05_checked (by decide +kernel)).append (c := 4687177636410976165709051252610) (b088_06_checked.append (c := 4614473962858703069464445590320) b088_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 32263176687237958794792035082180) (((b088_08_checked.append (c := 12753256040025033110679670583580) b088_09_checked (by decide +kernel)).append (c := 18454913120225264277759742676670) (b088_10_checked.append (c := 5701657080200231167080072093090) b088_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 27572568162253373505245169762690) ((b088_12_checked.append (c := 9081253418519343666645670758660) b088_13_checked (by decide +kernel)).append (c := 9117655042028109227485427086020) (b088_14_checked.append (c := 36401623508765560839756327360) b088_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
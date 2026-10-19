import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch007
import Dressed.QuarticIntegerComputationalData64.Batch008


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b065_00_rows : List Row := [(row3 11 19 39), (row3 11 19 40), (row3 11 19 41), (row3 11 19 42), (row3 11 19 43), (row3 11 19 44), (row3 11 19 45), (row3 11 19 46), (row3 11 19 47), (row3 11 19 48), (row3 11 19 49), (row3 11 19 50), (row3 11 19 51), (row3 11 19 52), (row3 11 19 53), (row3 11 19 54)]

def b065_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_00_rows b065_00_labels 19713966259789303503675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_00_rows b065_00_labels]
    decide +kernel

def b065_01_rows : List Row := [(row3 11 19 55), (row3 11 19 56), (row3 11 19 57), (row3 11 19 58), (row3 11 19 59), (row3 11 19 60), (row3 11 19 61), (row3 11 19 62), (row3 11 19 63), (row3 11 20 21), (row3 11 20 22), (row3 11 20 23), (row3 11 20 24), (row3 11 20 25), (row3 11 20 26), (row3 11 20 27)]

def b065_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 286 286), (row3 238 192 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 273 273)]

theorem b065_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_01_rows b065_01_labels 517519060893772100988157800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_01_rows b065_01_labels]
    decide +kernel

def b065_02_rows : List Row := [(row3 11 20 28), (row3 11 20 29), (row3 11 20 30), (row3 11 20 31), (row3 11 20 32), (row3 11 20 33), (row3 11 20 34), (row3 11 20 35), (row3 11 20 36), (row3 11 20 37), (row3 11 20 38), (row3 11 20 39), (row3 11 20 40), (row3 11 20 41), (row3 11 20 42), (row3 11 20 43)]

def b065_02_labels : List Row := [(row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_02_rows b065_02_labels 3919206854653026097392000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_02_rows b065_02_labels]
    decide +kernel

def b065_03_rows : List Row := [(row3 11 20 44), (row3 11 20 45), (row3 11 20 46), (row3 11 20 47), (row3 11 20 48), (row3 11 20 49), (row3 11 20 50), (row3 11 20 51), (row3 11 20 52), (row3 11 20 53), (row3 11 20 54), (row3 11 20 55), (row3 11 20 56), (row3 11 20 57), (row3 11 20 58), (row3 11 20 59)]

def b065_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 273 273)]

theorem b065_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_03_rows b065_03_labels 7323332145648552125769600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_03_rows b065_03_labels]
    decide +kernel

def b065_04_rows : List Row := [(row3 11 20 60), (row3 11 20 61), (row3 11 20 62), (row3 11 20 63), (row3 11 21 22), (row3 11 21 23), (row3 11 21 24), (row3 11 21 25), (row3 11 21 26), (row3 11 21 27), (row3 11 21 28), (row3 11 21 29), (row3 11 21 30), (row3 11 21 31), (row3 11 21 32), (row3 11 21 33)]

def b065_04_labels : List Row := [(row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_04_rows b065_04_labels 1168293310461268319070000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_04_rows b065_04_labels]
    decide +kernel

def b065_05_rows : List Row := [(row3 11 21 34), (row3 11 21 35), (row3 11 21 36), (row3 11 21 37), (row3 11 21 38), (row3 11 21 39), (row3 11 21 40), (row3 11 21 41), (row3 11 21 42), (row3 11 21 43), (row3 11 21 44), (row3 11 21 45), (row3 11 21 46), (row3 11 21 47), (row3 11 21 48), (row3 11 21 49)]

def b065_05_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_05_rows b065_05_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_05_rows b065_05_labels]
    decide +kernel

def b065_06_rows : List Row := [(row3 11 21 50), (row3 11 21 51), (row3 11 21 52), (row3 11 21 53), (row3 11 21 54), (row3 11 21 55), (row3 11 21 56), (row3 11 21 57), (row3 11 21 58), (row3 11 21 59), (row3 11 21 60), (row3 11 21 61), (row3 11 21 62), (row3 11 21 63), (row3 11 22 23), (row3 11 22 24)]

def b065_06_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_06_rows b065_06_labels 329263235914778383491000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_06_rows b065_06_labels]
    decide +kernel

def b065_07_rows : List Row := [(row3 11 22 25), (row3 11 22 26), (row3 11 22 27), (row3 11 22 28), (row3 11 22 29), (row3 11 22 30), (row3 11 22 31), (row3 11 22 32), (row3 11 22 33), (row3 11 22 34), (row3 11 22 35), (row3 11 22 36), (row3 11 22 37), (row3 11 22 38), (row3 11 22 39), (row3 11 22 40)]

def b065_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_07_rows b065_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_07_rows b065_07_labels]
    decide +kernel

def b065_08_rows : List Row := [(row3 11 22 41), (row3 11 22 42), (row3 11 22 43), (row3 11 22 44), (row3 11 22 45), (row3 11 22 46), (row3 11 22 47), (row3 11 22 48), (row3 11 22 49), (row3 11 22 50), (row3 11 22 51), (row3 11 22 52), (row3 11 22 53), (row3 11 22 54), (row3 11 22 55), (row3 11 22 56)]

def b065_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_08_rows b065_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_08_rows b065_08_labels]
    decide +kernel

def b065_09_rows : List Row := [(row3 11 22 57), (row3 11 22 58), (row3 11 22 59), (row3 11 22 60), (row3 11 22 61), (row3 11 22 62), (row3 11 22 63), (row3 11 23 24), (row3 11 23 25), (row3 11 23 26), (row3 11 23 27), (row3 11 23 28), (row3 11 23 29), (row3 11 23 30), (row3 11 23 31), (row3 11 23 32)]

def b065_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_09_rows b065_09_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_09_rows b065_09_labels]
    decide +kernel

def b065_10_rows : List Row := [(row3 11 23 33), (row3 11 23 34), (row3 11 23 35), (row3 11 23 36), (row3 11 23 37), (row3 11 23 38), (row3 11 23 39), (row3 11 23 40), (row3 11 23 41), (row3 11 23 42), (row3 11 23 43), (row3 11 23 44), (row3 11 23 45), (row3 11 23 46), (row3 11 23 47), (row3 11 23 48)]

def b065_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235)]

theorem b065_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_10_rows b065_10_labels 269733504168948038841000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_10_rows b065_10_labels]
    decide +kernel

def b065_11_rows : List Row := [(row3 11 23 49), (row3 11 23 50), (row3 11 23 51), (row3 11 23 52), (row3 11 23 53), (row3 11 23 54), (row3 11 23 55), (row3 11 23 56), (row3 11 23 57), (row3 11 23 58), (row3 11 23 59), (row3 11 23 60), (row3 11 23 61), (row3 11 23 62), (row3 11 23 63), (row3 11 24 25)]

def b065_11_labels : List Row := [(row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 284 284), (row3 462 232 232), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232), (row3 462 462 462)]

theorem b065_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_11_rows b065_11_labels 61216142941533648141333000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_11_rows b065_11_labels]
    decide +kernel

def b065_12_rows : List Row := [(row3 11 24 26), (row3 11 24 27), (row3 11 24 28), (row3 11 24 29), (row3 11 24 30), (row3 11 24 31), (row3 11 24 32), (row3 11 24 33), (row3 11 24 34), (row3 11 24 35), (row3 11 24 36), (row3 11 24 37), (row3 11 24 38), (row3 11 24 39), (row3 11 24 40), (row3 11 24 41)]

def b065_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462)]

theorem b065_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_12_rows b065_12_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_12_rows b065_12_labels]
    decide +kernel

def b065_13_rows : List Row := [(row3 11 24 42), (row3 11 24 43), (row3 11 24 44), (row3 11 24 45), (row3 11 24 46), (row3 11 24 47), (row3 11 24 48), (row3 11 24 49), (row3 11 24 50), (row3 11 24 51), (row3 11 24 52), (row3 11 24 53), (row3 11 24 54), (row3 11 24 55), (row3 11 24 56), (row3 11 24 57)]

def b065_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 263 263), (row3 462 236 236)]

theorem b065_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_13_rows b065_13_labels 20070433334159702848725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_13_rows b065_13_labels]
    decide +kernel

def b065_14_rows : List Row := [(row3 11 24 58), (row3 11 24 59), (row3 11 24 60), (row3 11 24 61), (row3 11 24 62), (row3 11 24 63), (row3 11 25 26), (row3 11 25 27), (row3 11 25 28), (row3 11 25 29), (row3 11 25 30), (row3 11 25 31), (row3 11 25 32), (row3 11 25 33), (row3 11 25 34), (row3 11 25 35)]

def b065_14_labels : List Row := [(row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_14_rows b065_14_labels 275172958191132493938000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_14_rows b065_14_labels]
    decide +kernel

def b065_15_rows : List Row := [(row3 11 25 36), (row3 11 25 37), (row3 11 25 38), (row3 11 25 39), (row3 11 25 40), (row3 11 25 41), (row3 11 25 42), (row3 11 25 43), (row3 11 25 44), (row3 11 25 45), (row3 11 25 46), (row3 11 25 47), (row3 11 25 48), (row3 11 25 49), (row3 11 25 50), (row3 11 25 51)]

def b065_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b065_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b065_15_rows b065_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b065_15_rows b065_15_labels]
    decide +kernel

theorem checked065 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_065 QuarticIntegerComputationalData.ids64_065 631831993014195499376057400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b065_00_rows ++ b065_01_rows) ++ (b065_02_rows ++ b065_03_rows)) ++ ((b065_04_rows ++ b065_05_rows) ++ (b065_06_rows ++ b065_07_rows))) ++ (((b065_08_rows ++ b065_09_rows) ++ (b065_10_rows ++ b065_11_rows)) ++ ((b065_12_rows ++ b065_13_rows) ++ (b065_14_rows ++ b065_15_rows))))
    ((((b065_00_labels ++ b065_01_labels) ++ (b065_02_labels ++ b065_03_labels)) ++ ((b065_04_labels ++ b065_05_labels) ++ (b065_06_labels ++ b065_07_labels))) ++ (((b065_08_labels ++ b065_09_labels) ++ (b065_10_labels ++ b065_11_labels)) ++ ((b065_12_labels ++ b065_13_labels) ++ (b065_14_labels ++ b065_15_labels)))) 631831993014195499376057400
  exact ((((b065_00_checked.append (c := 537233027153561404491832800) b065_01_checked (by decide +kernel)).append (c := 548475566153862982714994400) (b065_02_checked.append (c := 11242539000301578223161600) b065_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 549980782800595932655280400) ((b065_04_checked.append (c := 1175953410818171556795000) b065_05_checked (by decide +kernel)).append (c := 1505216646732949940286000) (b065_06_checked.append (c := 329263235914778383491000) b065_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 631831993014195499376057400) (((b065_08_checked.append (c := 16102107813616554645000) b065_09_checked (by decide +kernel)).append (c := 61501978553516212734819000) (b065_10_checked.append (c := 61485876445702596180174000) b065_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 81851210213599566720777000) ((b065_12_checked.append (c := 20074058701892221492020000) b065_13_checked (by decide +kernel)).append (c := 20349231660083353985958000) (b065_14_checked.append (c := 275172958191132493938000) b065_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b066_00_rows : List Row := [(row3 11 25 52), (row3 11 25 53), (row3 11 25 54), (row3 11 25 55), (row3 11 25 56), (row3 11 25 57), (row3 11 25 58), (row3 11 25 59), (row3 11 25 60), (row3 11 25 61), (row3 11 25 62), (row3 11 25 63), (row3 11 26 27), (row3 11 26 28), (row3 11 26 29), (row3 11 26 30)]

def b066_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462)]

theorem b066_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_00_rows b066_00_labels 1723209975187130289591000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_00_rows b066_00_labels]
    decide +kernel

def b066_01_rows : List Row := [(row3 11 26 31), (row3 11 26 32), (row3 11 26 33), (row3 11 26 34), (row3 11 26 35), (row3 11 26 36), (row3 11 26 37), (row3 11 26 38), (row3 11 26 39), (row3 11 26 40), (row3 11 26 41), (row3 11 26 42), (row3 11 26 43), (row3 11 26 44), (row3 11 26 45), (row3 11 26 46)]

def b066_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_01_rows b066_01_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_01_rows b066_01_labels]
    decide +kernel

def b066_02_rows : List Row := [(row3 11 26 47), (row3 11 26 48), (row3 11 26 49), (row3 11 26 50), (row3 11 26 51), (row3 11 26 52), (row3 11 26 53), (row3 11 26 54), (row3 11 26 55), (row3 11 26 56), (row3 11 26 57), (row3 11 26 58), (row3 11 26 59), (row3 11 26 60), (row3 11 26 61), (row3 11 26 62)]

def b066_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462)]

theorem b066_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_02_rows b066_02_labels 346030449920782749778500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_02_rows b066_02_labels]
    decide +kernel

def b066_03_rows : List Row := [(row3 11 26 63), (row3 11 27 28), (row3 11 27 29), (row3 11 27 30), (row3 11 27 31), (row3 11 27 32), (row3 11 27 33), (row3 11 27 34), (row3 11 27 35), (row3 11 27 36), (row3 11 27 37), (row3 11 27 38), (row3 11 27 39), (row3 11 27 40), (row3 11 27 41), (row3 11 27 42)]

def b066_03_labels : List Row := [(row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_03_rows b066_03_labels 2240440875386509391568000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_03_rows b066_03_labels]
    decide +kernel

def b066_04_rows : List Row := [(row3 11 27 43), (row3 11 27 44), (row3 11 27 45), (row3 11 27 46), (row3 11 27 47), (row3 11 27 48), (row3 11 27 49), (row3 11 27 50), (row3 11 27 51), (row3 11 27 52), (row3 11 27 53), (row3 11 27 54), (row3 11 27 55), (row3 11 27 56), (row3 11 27 57), (row3 11 27 58)]

def b066_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235)]

theorem b066_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_04_rows b066_04_labels 465137435815674068412000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_04_rows b066_04_labels]
    decide +kernel

def b066_05_rows : List Row := [(row3 11 27 59), (row3 11 27 60), (row3 11 27 61), (row3 11 27 62), (row3 11 27 63), (row3 11 28 29), (row3 11 28 30), (row3 11 28 31), (row3 11 28 32), (row3 11 28 33), (row3 11 28 34), (row3 11 28 35), (row3 11 28 36), (row3 11 28 37), (row3 11 28 38), (row3 11 28 39)]

def b066_05_labels : List Row := [(row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_05_rows b066_05_labels 2398184909227917373588200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_05_rows b066_05_labels]
    decide +kernel

def b066_06_rows : List Row := [(row3 11 28 40), (row3 11 28 41), (row3 11 28 42), (row3 11 28 43), (row3 11 28 44), (row3 11 28 45), (row3 11 28 46), (row3 11 28 47), (row3 11 28 48), (row3 11 28 49), (row3 11 28 50), (row3 11 28 51), (row3 11 28 52), (row3 11 28 53), (row3 11 28 54), (row3 11 28 55)]

def b066_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_06_rows b066_06_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_06_rows b066_06_labels]
    decide +kernel

def b066_07_rows : List Row := [(row3 11 28 56), (row3 11 28 57), (row3 11 28 58), (row3 11 28 59), (row3 11 28 60), (row3 11 28 61), (row3 11 28 62), (row3 11 28 63), (row3 11 29 30), (row3 11 29 31), (row3 11 29 32), (row3 11 29 33), (row3 11 29 34), (row3 11 29 35), (row3 11 29 36), (row3 11 29 37)]

def b066_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_07_rows b066_07_labels 321603135557875145766000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_07_rows b066_07_labels]
    decide +kernel

def b066_08_rows : List Row := [(row3 11 29 38), (row3 11 29 39), (row3 11 29 40), (row3 11 29 41), (row3 11 29 42), (row3 11 29 43), (row3 11 29 44), (row3 11 29 45), (row3 11 29 46), (row3 11 29 47), (row3 11 29 48), (row3 11 29 49), (row3 11 29 50), (row3 11 29 51), (row3 11 29 52), (row3 11 29 53)]

def b066_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_08_rows b066_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_08_rows b066_08_labels]
    decide +kernel

def b066_09_rows : List Row := [(row3 11 29 54), (row3 11 29 55), (row3 11 29 56), (row3 11 29 57), (row3 11 29 58), (row3 11 29 59), (row3 11 29 60), (row3 11 29 61), (row3 11 29 62), (row3 11 29 63), (row3 11 30 31), (row3 11 30 32), (row3 11 30 33), (row3 11 30 34), (row3 11 30 35), (row3 11 30 36)]

def b066_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_09_rows b066_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_09_rows b066_09_labels]
    decide +kernel

def b066_10_rows : List Row := [(row3 11 30 37), (row3 11 30 38), (row3 11 30 39), (row3 11 30 40), (row3 11 30 41), (row3 11 30 42), (row3 11 30 43), (row3 11 30 44), (row3 11 30 45), (row3 11 30 46), (row3 11 30 47), (row3 11 30 48), (row3 11 30 49), (row3 11 30 50), (row3 11 30 51), (row3 11 30 52)]

def b066_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_10_rows b066_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_10_rows b066_10_labels]
    decide +kernel

def b066_11_rows : List Row := [(row3 11 30 53), (row3 11 30 54), (row3 11 30 55), (row3 11 30 56), (row3 11 30 57), (row3 11 30 58), (row3 11 30 59), (row3 11 30 60), (row3 11 30 61), (row3 11 30 62), (row3 11 30 63), (row3 11 31 32), (row3 11 31 33), (row3 11 31 34), (row3 11 31 35), (row3 11 31 36)]

def b066_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_11_rows b066_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_11_rows b066_11_labels]
    decide +kernel

def b066_12_rows : List Row := [(row3 11 31 37), (row3 11 31 38), (row3 11 31 39), (row3 11 31 40), (row3 11 31 41), (row3 11 31 42), (row3 11 31 43), (row3 11 31 44), (row3 11 31 45), (row3 11 31 46), (row3 11 31 47), (row3 11 31 48), (row3 11 31 49), (row3 11 31 50), (row3 11 31 51), (row3 11 31 52)]

def b066_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_12_rows b066_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_12_rows b066_12_labels]
    decide +kernel

def b066_13_rows : List Row := [(row3 11 31 53), (row3 11 31 54), (row3 11 31 55), (row3 11 31 56), (row3 11 31 57), (row3 11 31 58), (row3 11 31 59), (row3 11 31 60), (row3 11 31 61), (row3 11 31 62), (row3 11 31 63), (row3 11 32 33), (row3 11 32 34), (row3 11 32 35), (row3 11 32 36), (row3 11 32 37)]

def b066_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_13_rows b066_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_13_rows b066_13_labels]
    decide +kernel

def b066_14_rows : List Row := [(row3 11 32 38), (row3 11 32 39), (row3 11 32 40), (row3 11 32 41), (row3 11 32 42), (row3 11 32 43), (row3 11 32 44), (row3 11 32 45), (row3 11 32 46), (row3 11 32 47), (row3 11 32 48), (row3 11 32 49), (row3 11 32 50), (row3 11 32 51), (row3 11 32 52), (row3 11 32 53)]

def b066_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_14_rows b066_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_14_rows b066_14_labels]
    decide +kernel

def b066_15_rows : List Row := [(row3 11 32 54), (row3 11 32 55), (row3 11 32 56), (row3 11 32 57), (row3 11 32 58), (row3 11 32 59), (row3 11 32 60), (row3 11 32 61), (row3 11 32 62), (row3 11 32 63), (row3 11 33 34), (row3 11 33 35), (row3 11 33 36), (row3 11 33 37), (row3 11 33 38), (row3 11 33 39)]

def b066_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b066_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b066_15_rows b066_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b066_15_rows b066_15_labels]
    decide +kernel

theorem checked066 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_066 QuarticIntegerComputationalData.ids64_066 7518368989266408811073700 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b066_00_rows ++ b066_01_rows) ++ (b066_02_rows ++ b066_03_rows)) ++ ((b066_04_rows ++ b066_05_rows) ++ (b066_06_rows ++ b066_07_rows))) ++ (((b066_08_rows ++ b066_09_rows) ++ (b066_10_rows ++ b066_11_rows)) ++ ((b066_12_rows ++ b066_13_rows) ++ (b066_14_rows ++ b066_15_rows))))
    ((((b066_00_labels ++ b066_01_labels) ++ (b066_02_labels ++ b066_03_labels)) ++ ((b066_04_labels ++ b066_05_labels) ++ (b066_06_labels ++ b066_07_labels))) ++ (((b066_08_labels ++ b066_09_labels) ++ (b066_10_labels ++ b066_11_labels)) ++ ((b066_12_labels ++ b066_13_labels) ++ (b066_14_labels ++ b066_15_labels)))) 7518368989266408811073700
  exact ((((b066_00_checked.append (c := 1739312083000746844236000) b066_01_checked (by decide +kernel)).append (c := 4325783408308038985582500) (b066_02_checked.append (c := 2586471325307292141346500) b066_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 7518368989266408811073700) ((b066_04_checked.append (c := 2863322345043591442000200) b066_05_checked (by decide +kernel)).append (c := 3192585580958369825491200) (b066_06_checked.append (c := 329263235914778383491000) b066_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7518368989266408811073700) (((b066_08_checked.append (c := 0) b066_09_checked (by decide +kernel)).append (c := 0) (b066_10_checked.append (c := 0) b066_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b066_12_checked.append (c := 0) b066_13_checked (by decide +kernel)).append (c := 0) (b066_14_checked.append (c := 0) b066_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b067_00_rows : List Row := [(row3 11 33 40), (row3 11 33 41), (row3 11 33 42), (row3 11 33 43), (row3 11 33 44), (row3 11 33 45), (row3 11 33 46), (row3 11 33 47), (row3 11 33 48), (row3 11 33 49), (row3 11 33 50), (row3 11 33 51), (row3 11 33 52), (row3 11 33 53), (row3 11 33 54), (row3 11 33 55)]

def b067_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_00_rows b067_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_00_rows b067_00_labels]
    decide +kernel

def b067_01_rows : List Row := [(row3 11 33 56), (row3 11 33 57), (row3 11 33 58), (row3 11 33 59), (row3 11 33 60), (row3 11 33 61), (row3 11 33 62), (row3 11 33 63), (row3 11 34 35), (row3 11 34 36), (row3 11 34 37), (row3 11 34 38), (row3 11 34 39), (row3 11 34 40), (row3 11 34 41), (row3 11 34 42)]

def b067_01_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_01_rows b067_01_labels 413010417905223503607000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_01_rows b067_01_labels]
    decide +kernel

def b067_02_rows : List Row := [(row3 11 34 43), (row3 11 34 44), (row3 11 34 45), (row3 11 34 46), (row3 11 34 47), (row3 11 34 48), (row3 11 34 49), (row3 11 34 50), (row3 11 34 51), (row3 11 34 52), (row3 11 34 53), (row3 11 34 54), (row3 11 34 55), (row3 11 34 56), (row3 11 34 57), (row3 11 34 58)]

def b067_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234)]

theorem b067_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_02_rows b067_02_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_02_rows b067_02_labels]
    decide +kernel

def b067_03_rows : List Row := [(row3 11 34 59), (row3 11 34 60), (row3 11 34 61), (row3 11 34 62), (row3 11 34 63), (row3 11 35 36), (row3 11 35 37), (row3 11 35 38), (row3 11 35 39), (row3 11 35 40), (row3 11 35 41), (row3 11 35 42), (row3 11 35 43), (row3 11 35 44), (row3 11 35 45), (row3 11 35 46)]

def b067_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_03_rows b067_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_03_rows b067_03_labels]
    decide +kernel

def b067_04_rows : List Row := [(row3 11 35 47), (row3 11 35 48), (row3 11 35 49), (row3 11 35 50), (row3 11 35 51), (row3 11 35 52), (row3 11 35 53), (row3 11 35 54), (row3 11 35 55), (row3 11 35 56), (row3 11 35 57), (row3 11 35 58), (row3 11 35 59), (row3 11 35 60), (row3 11 35 61), (row3 11 35 62)]

def b067_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 247 247), (row3 238 236 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462)]

theorem b067_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_04_rows b067_04_labels 215570190053917078944000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_04_rows b067_04_labels]
    decide +kernel

def b067_05_rows : List Row := [(row3 11 35 63), (row3 11 36 37), (row3 11 36 38), (row3 11 36 39), (row3 11 36 40), (row3 11 36 41), (row3 11 36 42), (row3 11 36 43), (row3 11 36 44), (row3 11 36 45), (row3 11 36 46), (row3 11 36 47), (row3 11 36 48), (row3 11 36 49), (row3 11 36 50), (row3 11 36 51)]

def b067_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_05_rows b067_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_05_rows b067_05_labels]
    decide +kernel

def b067_06_rows : List Row := [(row3 11 36 52), (row3 11 36 53), (row3 11 36 54), (row3 11 36 55), (row3 11 36 56), (row3 11 36 57), (row3 11 36 58), (row3 11 36 59), (row3 11 36 60), (row3 11 36 61), (row3 11 36 62), (row3 11 36 63), (row3 11 37 38), (row3 11 37 39), (row3 11 37 40), (row3 11 37 41)]

def b067_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_06_rows b067_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_06_rows b067_06_labels]
    decide +kernel

def b067_07_rows : List Row := [(row3 11 37 42), (row3 11 37 43), (row3 11 37 44), (row3 11 37 45), (row3 11 37 46), (row3 11 37 47), (row3 11 37 48), (row3 11 37 49), (row3 11 37 50), (row3 11 37 51), (row3 11 37 52), (row3 11 37 53), (row3 11 37 54), (row3 11 37 55), (row3 11 37 56), (row3 11 37 57)]

def b067_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_07_rows b067_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_07_rows b067_07_labels]
    decide +kernel

def b067_08_rows : List Row := [(row3 11 37 58), (row3 11 37 59), (row3 11 37 60), (row3 11 37 61), (row3 11 37 62), (row3 11 37 63), (row3 11 38 39), (row3 11 38 40), (row3 11 38 41), (row3 11 38 42), (row3 11 38 43), (row3 11 38 44), (row3 11 38 45), (row3 11 38 46), (row3 11 38 47), (row3 11 38 48)]

def b067_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_08_rows b067_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_08_rows b067_08_labels]
    decide +kernel

def b067_09_rows : List Row := [(row3 11 38 49), (row3 11 38 50), (row3 11 38 51), (row3 11 38 52), (row3 11 38 53), (row3 11 38 54), (row3 11 38 55), (row3 11 38 56), (row3 11 38 57), (row3 11 38 58), (row3 11 38 59), (row3 11 38 60), (row3 11 38 61), (row3 11 38 62), (row3 11 38 63), (row3 11 39 40)]

def b067_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_09_rows b067_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_09_rows b067_09_labels]
    decide +kernel

def b067_10_rows : List Row := [(row3 11 39 41), (row3 11 39 42), (row3 11 39 43), (row3 11 39 44), (row3 11 39 45), (row3 11 39 46), (row3 11 39 47), (row3 11 39 48), (row3 11 39 49), (row3 11 39 50), (row3 11 39 51), (row3 11 39 52), (row3 11 39 53), (row3 11 39 54), (row3 11 39 55), (row3 11 39 56)]

def b067_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_10_rows b067_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_10_rows b067_10_labels]
    decide +kernel

def b067_11_rows : List Row := [(row3 11 39 57), (row3 11 39 58), (row3 11 39 59), (row3 11 39 60), (row3 11 39 61), (row3 11 39 62), (row3 11 39 63), (row3 11 40 41), (row3 11 40 42), (row3 11 40 43), (row3 11 40 44), (row3 11 40 45), (row3 11 40 46), (row3 11 40 47), (row3 11 40 48), (row3 11 40 49)]

def b067_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 243 243)]

theorem b067_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_11_rows b067_11_labels 571991322931887244077000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_11_rows b067_11_labels]
    decide +kernel

def b067_12_rows : List Row := [(row3 11 40 50), (row3 11 40 51), (row3 11 40 52), (row3 11 40 53), (row3 11 40 54), (row3 11 40 55), (row3 11 40 56), (row3 11 40 57), (row3 11 40 58), (row3 11 40 59), (row3 11 40 60), (row3 11 40 61), (row3 11 40 62), (row3 11 40 63), (row3 11 41 42), (row3 11 41 43)]

def b067_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 263 263), (row3 228 236 225), (row3 462 250 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462)]

theorem b067_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_12_rows b067_12_labels 22021417751819859943984500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_12_rows b067_12_labels]
    decide +kernel

def b067_13_rows : List Row := [(row3 11 41 44), (row3 11 41 45), (row3 11 41 46), (row3 11 41 47), (row3 11 41 48), (row3 11 41 49), (row3 11 41 50), (row3 11 41 51), (row3 11 41 52), (row3 11 41 53), (row3 11 41 54), (row3 11 41 55), (row3 11 41 56), (row3 11 41 57), (row3 11 41 58), (row3 11 41 59)]

def b067_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 224 224 224), (row3 462 462 462)]

theorem b067_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_13_rows b067_13_labels 9810798184027213891232400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_13_rows b067_13_labels]
    decide +kernel

def b067_14_rows : List Row := [(row3 11 41 60), (row3 11 41 61), (row3 11 41 62), (row3 11 41 63), (row3 11 42 43), (row3 11 42 44), (row3 11 42 45), (row3 11 42 46), (row3 11 42 47), (row3 11 42 48), (row3 11 42 49), (row3 11 42 50), (row3 11 42 51), (row3 11 42 52), (row3 11 42 53), (row3 11 42 54)]

def b067_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_14_rows b067_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_14_rows b067_14_labels]
    decide +kernel

def b067_15_rows : List Row := [(row3 11 42 55), (row3 11 42 56), (row3 11 42 57), (row3 11 42 58), (row3 11 42 59), (row3 11 42 60), (row3 11 42 61), (row3 11 42 62), (row3 11 42 63), (row3 11 43 44), (row3 11 43 45), (row3 11 43 46), (row3 11 43 47), (row3 11 43 48), (row3 11 43 49), (row3 11 43 50)]

def b067_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b067_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b067_15_rows b067_15_labels 11721743532018499266061200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b067_15_rows b067_15_labels]
    decide +kernel

theorem checked067 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_067 QuarticIntegerComputationalData.ids64_067 45078906473006485746206100 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b067_00_rows ++ b067_01_rows) ++ (b067_02_rows ++ b067_03_rows)) ++ ((b067_04_rows ++ b067_05_rows) ++ (b067_06_rows ++ b067_07_rows))) ++ (((b067_08_rows ++ b067_09_rows) ++ (b067_10_rows ++ b067_11_rows)) ++ ((b067_12_rows ++ b067_13_rows) ++ (b067_14_rows ++ b067_15_rows))))
    ((((b067_00_labels ++ b067_01_labels) ++ (b067_02_labels ++ b067_03_labels)) ++ ((b067_04_labels ++ b067_05_labels) ++ (b067_06_labels ++ b067_07_labels))) ++ (((b067_08_labels ++ b067_09_labels) ++ (b067_10_labels ++ b067_11_labels)) ++ ((b067_12_labels ++ b067_13_labels) ++ (b067_14_labels ++ b067_15_labels)))) 45078906473006485746206100
  exact ((((b067_00_checked.append (c := 413010417905223503607000) b067_01_checked (by decide +kernel)).append (c := 737385492155108321907000) (b067_02_checked.append (c := 324375074249884818300000) b067_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 952955682209025400851000) ((b067_04_checked.append (c := 215570190053917078944000) b067_05_checked (by decide +kernel)).append (c := 215570190053917078944000) (b067_06_checked.append (c := 0) b067_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 45078906473006485746206100) (((b067_08_checked.append (c := 0) b067_09_checked (by decide +kernel)).append (c := 571991322931887244077000) (b067_10_checked.append (c := 571991322931887244077000) b067_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 44125950790797460345355100) ((b067_12_checked.append (c := 31832215935847073835216900) b067_13_checked (by decide +kernel)).append (c := 43553959467865573101278100) (b067_14_checked.append (c := 11721743532018499266061200) b067_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b068_00_rows : List Row := [(row3 11 43 51), (row3 11 43 52), (row3 11 43 53), (row3 11 43 54), (row3 11 43 55), (row3 11 43 56), (row3 11 43 57), (row3 11 43 58), (row3 11 43 59), (row3 11 43 60), (row3 11 43 61), (row3 11 43 62), (row3 11 43 63), (row3 11 44 45), (row3 11 44 46), (row3 11 44 47)]

def b068_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_00_rows b068_00_labels 3188107204239935288077200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_00_rows b068_00_labels]
    decide +kernel

def b068_01_rows : List Row := [(row3 11 44 48), (row3 11 44 49), (row3 11 44 50), (row3 11 44 51), (row3 11 44 52), (row3 11 44 53), (row3 11 44 54), (row3 11 44 55), (row3 11 44 56), (row3 11 44 57), (row3 11 44 58), (row3 11 44 59), (row3 11 44 60), (row3 11 44 61), (row3 11 44 62), (row3 11 44 63)]

def b068_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_01_rows b068_01_labels 301066359412777219228500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_01_rows b068_01_labels]
    decide +kernel

def b068_02_rows : List Row := [(row3 11 45 46), (row3 11 45 47), (row3 11 45 48), (row3 11 45 49), (row3 11 45 50), (row3 11 45 51), (row3 11 45 52), (row3 11 45 53), (row3 11 45 54), (row3 11 45 55), (row3 11 45 56), (row3 11 45 57), (row3 11 45 58), (row3 11 45 59), (row3 11 45 60), (row3 11 45 61)]

def b068_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_02_rows b068_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_02_rows b068_02_labels]
    decide +kernel

def b068_03_rows : List Row := [(row3 11 45 62), (row3 11 45 63), (row3 11 46 47), (row3 11 46 48), (row3 11 46 49), (row3 11 46 50), (row3 11 46 51), (row3 11 46 52), (row3 11 46 53), (row3 11 46 54), (row3 11 46 55), (row3 11 46 56), (row3 11 46 57), (row3 11 46 58), (row3 11 46 59), (row3 11 46 60)]

def b068_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_03_rows b068_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_03_rows b068_03_labels]
    decide +kernel

def b068_04_rows : List Row := [(row3 11 46 61), (row3 11 46 62), (row3 11 46 63), (row3 11 47 48), (row3 11 47 49), (row3 11 47 50), (row3 11 47 51), (row3 11 47 52), (row3 11 47 53), (row3 11 47 54), (row3 11 47 55), (row3 11 47 56), (row3 11 47 57), (row3 11 47 58), (row3 11 47 59), (row3 11 47 60)]

def b068_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_04_rows b068_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_04_rows b068_04_labels]
    decide +kernel

def b068_05_rows : List Row := [(row3 11 47 61), (row3 11 47 62), (row3 11 47 63), (row3 11 48 49), (row3 11 48 50), (row3 11 48 51), (row3 11 48 52), (row3 11 48 53), (row3 11 48 54), (row3 11 48 55), (row3 11 48 56), (row3 11 48 57), (row3 11 48 58), (row3 11 48 59), (row3 11 48 60), (row3 11 48 61)]

def b068_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 193 193), (row3 295 273 304), (row3 224 222 222), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_05_rows b068_05_labels 544181893590191676403122000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_05_rows b068_05_labels]
    decide +kernel

def b068_06_rows : List Row := [(row3 11 48 62), (row3 11 48 63), (row3 11 49 50), (row3 11 49 51), (row3 11 49 52), (row3 11 49 53), (row3 11 49 54), (row3 11 49 55), (row3 11 49 56), (row3 11 49 57), (row3 11 49 58), (row3 11 49 59), (row3 11 49 60), (row3 11 49 61), (row3 11 49 62), (row3 11 49 63)]

def b068_06_labels : List Row := [(row3 462 235 235), (row3 462 273 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 284 284), (row3 139 232 138), (row3 306 312 312), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232)]

theorem b068_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_06_rows b068_06_labels 1198202392652146700962377600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_06_rows b068_06_labels]
    decide +kernel

def b068_07_rows : List Row := [(row3 11 50 51), (row3 11 50 52), (row3 11 50 53), (row3 11 50 54), (row3 11 50 55), (row3 11 50 56), (row3 11 50 57), (row3 11 50 58), (row3 11 50 59), (row3 11 50 60), (row3 11 50 61), (row3 11 50 62), (row3 11 50 63), (row3 11 51 52), (row3 11 51 53), (row3 11 51 54)]

def b068_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 295 462 295), (row3 131 105 105), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_07_rows b068_07_labels 2435300967738383756025228000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_07_rows b068_07_labels]
    decide +kernel

def b068_08_rows : List Row := [(row3 11 51 55), (row3 11 51 56), (row3 11 51 57), (row3 11 51 58), (row3 11 51 59), (row3 11 51 60), (row3 11 51 61), (row3 11 51 62), (row3 11 51 63), (row3 11 52 53), (row3 11 52 54), (row3 11 52 55), (row3 11 52 56), (row3 11 52 57), (row3 11 52 58), (row3 11 52 59)]

def b068_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 306 310 310), (row3 193 192 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 273 273 462)]

theorem b068_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_08_rows b068_08_labels 386243491847539661273372400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_08_rows b068_08_labels]
    decide +kernel

def b068_09_rows : List Row := [(row3 11 52 60), (row3 11 52 61), (row3 11 52 62), (row3 11 52 63), (row3 11 53 54), (row3 11 53 55), (row3 11 53 56), (row3 11 53 57), (row3 11 53 58), (row3 11 53 59), (row3 11 53 60), (row3 11 53 61), (row3 11 53 62), (row3 11 53 63), (row3 11 54 55), (row3 11 54 56)]

def b068_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_09_rows b068_09_labels 288068707545866413191000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_09_rows b068_09_labels]
    decide +kernel

def b068_10_rows : List Row := [(row3 11 54 57), (row3 11 54 58), (row3 11 54 59), (row3 11 54 60), (row3 11 54 61), (row3 11 54 62), (row3 11 54 63), (row3 11 55 56), (row3 11 55 57), (row3 11 55 58), (row3 11 55 59), (row3 11 55 60), (row3 11 55 61), (row3 11 55 62), (row3 11 55 63), (row3 11 56 57)]

def b068_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 228 232 223), (row3 462 251 251), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232), (row3 139 163 124)]

theorem b068_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_10_rows b068_10_labels 2677687253312766190633134000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_10_rows b068_10_labels]
    decide +kernel

def b068_11_rows : List Row := [(row3 11 56 58), (row3 11 56 59), (row3 11 56 60), (row3 11 56 61), (row3 11 56 62), (row3 11 56 63), (row3 11 57 58), (row3 11 57 59), (row3 11 57 60), (row3 11 57 61), (row3 11 57 62), (row3 11 57 63), (row3 11 58 59), (row3 11 58 60), (row3 11 58 61), (row3 11 58 62)]

def b068_11_labels : List Row := [(row3 289 305 305), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 163 163), (row3 398 134 81), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 235 228 232), (row3 278 300 288), (row3 369 121 85), (row3 289 292 292), (row3 234 234 234), (row3 462 248 248)]

theorem b068_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_11_rows b068_11_labels 31497018362835186972469366620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_11_rows b068_11_labels]
    decide +kernel

def b068_12_rows : List Row := [(row3 11 58 63), (row3 11 59 60), (row3 11 59 61), (row3 11 59 62), (row3 11 59 63), (row3 11 60 61), (row3 11 60 62), (row3 11 60 63), (row3 11 61 62), (row3 11 61 63), (row3 11 62 63), (row3 12 13 14), (row3 12 13 15), (row3 12 13 16), (row3 12 13 17), (row3 12 13 18)]

def b068_12_labels : List Row := [(row3 234 226 226), (row3 193 235 191), (row3 261 462 261), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 41 435 95), (row3 167 190 166), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_12_rows b068_12_labels 359616269115622060038168221550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_12_rows b068_12_labels]
    decide +kernel

def b068_13_rows : List Row := [(row3 12 13 19), (row3 12 13 20), (row3 12 13 21), (row3 12 13 22), (row3 12 13 23), (row3 12 13 24), (row3 12 13 25), (row3 12 13 26), (row3 12 13 27), (row3 12 13 28), (row3 12 13 29), (row3 12 13 30), (row3 12 13 31), (row3 12 13 32), (row3 12 13 33), (row3 12 13 34)]

def b068_13_labels : List Row := [(row3 284 462 284), (row3 163 462 163), (row3 358 462 358), (row3 160 228 163), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 193 462 193), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_13_rows b068_13_labels 15760443188898216235434282000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_13_rows b068_13_labels]
    decide +kernel

def b068_14_rows : List Row := [(row3 12 13 35), (row3 12 13 36), (row3 12 13 37), (row3 12 13 38), (row3 12 13 39), (row3 12 13 40), (row3 12 13 41), (row3 12 13 42), (row3 12 13 43), (row3 12 13 44), (row3 12 13 45), (row3 12 13 46), (row3 12 13 47), (row3 12 13 48), (row3 12 13 49), (row3 12 13 50)]

def b068_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b068_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_14_rows b068_14_labels 19713966259789303503675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_14_rows b068_14_labels]
    decide +kernel

def b068_15_rows : List Row := [(row3 12 13 51), (row3 12 13 52), (row3 12 13 53), (row3 12 13 54), (row3 12 13 55), (row3 12 13 56), (row3 12 13 57), (row3 12 13 58), (row3 12 13 59), (row3 12 13 60), (row3 12 13 61), (row3 12 13 62), (row3 12 13 63), (row3 12 14 15), (row3 12 14 16), (row3 12 14 17)]

def b068_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 191 235 193), (row3 287 462 287), (row3 462 462 462), (row3 58 430 372), (row3 291 291 289), (row3 462 235 235)]

theorem b068_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b068_15_rows b068_15_labels 139028954048573493632132272200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b068_15_rows b068_15_labels]
    decide +kernel

theorem checked068 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_068 QuarticIntegerComputationalData.ids64_068 553167791923600972745925548070 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b068_00_rows ++ b068_01_rows) ++ (b068_02_rows ++ b068_03_rows)) ++ ((b068_04_rows ++ b068_05_rows) ++ (b068_06_rows ++ b068_07_rows))) ++ (((b068_08_rows ++ b068_09_rows) ++ (b068_10_rows ++ b068_11_rows)) ++ ((b068_12_rows ++ b068_13_rows) ++ (b068_14_rows ++ b068_15_rows))))
    ((((b068_00_labels ++ b068_01_labels) ++ (b068_02_labels ++ b068_03_labels)) ++ ((b068_04_labels ++ b068_05_labels) ++ (b068_06_labels ++ b068_07_labels))) ++ (((b068_08_labels ++ b068_09_labels) ++ (b068_10_labels ++ b068_11_labels)) ++ ((b068_12_labels ++ b068_13_labels) ++ (b068_14_labels ++ b068_15_labels)))) 553167791923600972745925548070
  exact ((((b068_00_checked.append (c := 3489173563652712507305700) b068_01_checked (by decide +kernel)).append (c := 3489173563652712507305700) (b068_02_checked.append (c := 0) b068_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4181174427544374845898033300) ((b068_04_checked.append (c := 544181893590191676403122000) b068_05_checked (by decide +kernel)).append (c := 4177685253980722133390727600) (b068_06_checked.append (c := 3633503360390530456987605600) b068_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 553167791923600972745925548070) (((b068_08_checked.append (c := 386531560555085527686563400) b068_09_checked (by decide +kernel)).append (c := 34561237176703038690789064020) (b068_10_checked.append (c := 34174705616147953163102500620) b068_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 548986617496056597900027514770) ((b068_12_checked.append (c := 375376712304520276273602503550) b068_13_checked (by decide +kernel)).append (c := 514425380319353559209238450750) (b068_14_checked.append (c := 139048668014833282935635947200) b068_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b069_00_rows : List Row := [(row3 12 14 18), (row3 12 14 19), (row3 12 14 20), (row3 12 14 21), (row3 12 14 22), (row3 12 14 23), (row3 12 14 24), (row3 12 14 25), (row3 12 14 26), (row3 12 14 27), (row3 12 14 28), (row3 12 14 29), (row3 12 14 30), (row3 12 14 31), (row3 12 14 32), (row3 12 14 33)]

def b069_00_labels : List Row := [(row3 462 462 462), (row3 462 235 235), (row3 291 291 289), (row3 146 137 149), (row3 361 391 387), (row3 143 137 146), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 291 291 289), (row3 184 178 184), (row3 291 291 289), (row3 462 462 462), (row3 462 462 462)]

theorem b069_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_00_rows b069_00_labels 15481817960481183680269688970 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_00_rows b069_00_labels]
    decide +kernel

def b069_01_rows : List Row := [(row3 12 14 34), (row3 12 14 35), (row3 12 14 36), (row3 12 14 37), (row3 12 14 38), (row3 12 14 39), (row3 12 14 40), (row3 12 14 41), (row3 12 14 42), (row3 12 14 43), (row3 12 14 44), (row3 12 14 45), (row3 12 14 46), (row3 12 14 47), (row3 12 14 48), (row3 12 14 49)]

def b069_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 266 266 265), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_01_rows b069_01_labels 3878375052883639404074400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_01_rows b069_01_labels]
    decide +kernel

def b069_02_rows : List Row := [(row3 12 14 50), (row3 12 14 51), (row3 12 14 52), (row3 12 14 53), (row3 12 14 54), (row3 12 14 55), (row3 12 14 56), (row3 12 14 57), (row3 12 14 58), (row3 12 14 59), (row3 12 14 60), (row3 12 14 61), (row3 12 14 62), (row3 12 14 63), (row3 12 15 16), (row3 12 15 17)]

def b069_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 266 266 265), (row3 462 235 235), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 292 292 289), (row3 182 178 182), (row3 291 291 289), (row3 176 176 161), (row3 282 278 282)]

theorem b069_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_02_rows b069_02_labels 441244442788395885374036400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_02_rows b069_02_labels]
    decide +kernel

def b069_03_rows : List Row := [(row3 12 15 18), (row3 12 15 19), (row3 12 15 20), (row3 12 15 21), (row3 12 15 22), (row3 12 15 23), (row3 12 15 24), (row3 12 15 25), (row3 12 15 26), (row3 12 15 27), (row3 12 15 28), (row3 12 15 29), (row3 12 15 30), (row3 12 15 31), (row3 12 15 32), (row3 12 15 33)]

def b069_03_labels : List Row := [(row3 462 236 236), (row3 462 462 462), (row3 462 236 236), (row3 279 278 279), (row3 175 175 161), (row3 352 365 373), (row3 279 278 279), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 279 278 279), (row3 199 198 190), (row3 462 236 236), (row3 462 462 462)]

theorem b069_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_03_rows b069_03_labels 10759962384434862840609668010 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_03_rows b069_03_labels]
    decide +kernel

def b069_04_rows : List Row := [(row3 12 15 34), (row3 12 15 35), (row3 12 15 36), (row3 12 15 37), (row3 12 15 38), (row3 12 15 39), (row3 12 15 40), (row3 12 15 41), (row3 12 15 42), (row3 12 15 43), (row3 12 15 44), (row3 12 15 45), (row3 12 15 46), (row3 12 15 47), (row3 12 15 48), (row3 12 15 49)]

def b069_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 262 261 262), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 236 236), (row3 462 462 462)]

theorem b069_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_04_rows b069_04_labels 3807023151417034493701200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_04_rows b069_04_labels]
    decide +kernel

def b069_05_rows : List Row := [(row3 12 15 50), (row3 12 15 51), (row3 12 15 52), (row3 12 15 53), (row3 12 15 54), (row3 12 15 55), (row3 12 15 56), (row3 12 15 57), (row3 12 15 58), (row3 12 15 59), (row3 12 15 60), (row3 12 15 61), (row3 12 15 62), (row3 12 15 63), (row3 12 16 17), (row3 12 16 18)]

def b069_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 262 261 262), (row3 279 278 279), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 283 278 283), (row3 199 198 190), (row3 284 462 284), (row3 234 234 462)]

theorem b069_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_05_rows b069_05_labels 285904730711330782244729580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_05_rows b069_05_labels]
    decide +kernel

def b069_06_rows : List Row := [(row3 12 16 19), (row3 12 16 20), (row3 12 16 21), (row3 12 16 22), (row3 12 16 23), (row3 12 16 24), (row3 12 16 25), (row3 12 16 26), (row3 12 16 27), (row3 12 16 28), (row3 12 16 29), (row3 12 16 30), (row3 12 16 31), (row3 12 16 32), (row3 12 16 33), (row3 12 16 34)]

def b069_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_06_rows b069_06_labels 61650812846744330405139000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_06_rows b069_06_labels]
    decide +kernel

def b069_07_rows : List Row := [(row3 12 16 35), (row3 12 16 36), (row3 12 16 37), (row3 12 16 38), (row3 12 16 39), (row3 12 16 40), (row3 12 16 41), (row3 12 16 42), (row3 12 16 43), (row3 12 16 44), (row3 12 16 45), (row3 12 16 46), (row3 12 16 47), (row3 12 16 48), (row3 12 16 49), (row3 12 16 50)]

def b069_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_07_rows b069_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_07_rows b069_07_labels]
    decide +kernel

def b069_08_rows : List Row := [(row3 12 16 51), (row3 12 16 52), (row3 12 16 53), (row3 12 16 54), (row3 12 16 55), (row3 12 16 56), (row3 12 16 57), (row3 12 16 58), (row3 12 16 59), (row3 12 16 60), (row3 12 16 61), (row3 12 16 62), (row3 12 16 63), (row3 12 17 18), (row3 12 17 19), (row3 12 17 20)]

def b069_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 214 11), (row3 235 235 462), (row3 243 243 462)]

theorem b069_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_08_rows b069_08_labels 1643386841009291784031044750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_08_rows b069_08_labels]
    decide +kernel

def b069_09_rows : List Row := [(row3 12 17 21), (row3 12 17 22), (row3 12 17 23), (row3 12 17 24), (row3 12 17 25), (row3 12 17 26), (row3 12 17 27), (row3 12 17 28), (row3 12 17 29), (row3 12 17 30), (row3 12 17 31), (row3 12 17 32), (row3 12 17 33), (row3 12 17 34), (row3 12 17 35), (row3 12 17 36)]

def b069_09_labels : List Row := [(row3 462 462 462), (row3 245 245 462), (row3 232 235 235), (row3 232 232 462), (row3 284 284 462), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_09_rows b069_09_labels 62053122029797336523503500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_09_rows b069_09_labels]
    decide +kernel

def b069_10_rows : List Row := [(row3 12 17 37), (row3 12 17 38), (row3 12 17 39), (row3 12 17 40), (row3 12 17 41), (row3 12 17 42), (row3 12 17 43), (row3 12 17 44), (row3 12 17 45), (row3 12 17 46), (row3 12 17 47), (row3 12 17 48), (row3 12 17 49), (row3 12 17 50), (row3 12 17 51), (row3 12 17 52)]

def b069_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_10_rows b069_10_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_10_rows b069_10_labels]
    decide +kernel

def b069_11_rows : List Row := [(row3 12 17 53), (row3 12 17 54), (row3 12 17 55), (row3 12 17 56), (row3 12 17 57), (row3 12 17 58), (row3 12 17 59), (row3 12 17 60), (row3 12 17 61), (row3 12 17 62), (row3 12 17 63), (row3 12 18 19), (row3 12 18 20), (row3 12 18 21), (row3 12 18 22), (row3 12 18 23)]

def b069_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 245 462 245)]

theorem b069_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_11_rows b069_11_labels 96080826501548615902126500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_11_rows b069_11_labels]
    decide +kernel

def b069_12_rows : List Row := [(row3 12 18 24), (row3 12 18 25), (row3 12 18 26), (row3 12 18 27), (row3 12 18 28), (row3 12 18 29), (row3 12 18 30), (row3 12 18 31), (row3 12 18 32), (row3 12 18 33), (row3 12 18 34), (row3 12 18 35), (row3 12 18 36), (row3 12 18 37), (row3 12 18 38), (row3 12 18 39)]

def b069_12_labels : List Row := [(row3 248 462 248), (row3 228 462 228), (row3 293 462 293), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_12_rows b069_12_labels 92254105932888097207003500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_12_rows b069_12_labels]
    decide +kernel

def b069_13_rows : List Row := [(row3 12 18 40), (row3 12 18 41), (row3 12 18 42), (row3 12 18 43), (row3 12 18 44), (row3 12 18 45), (row3 12 18 46), (row3 12 18 47), (row3 12 18 48), (row3 12 18 49), (row3 12 18 50), (row3 12 18 51), (row3 12 18 52), (row3 12 18 53), (row3 12 18 54), (row3 12 18 55)]

def b069_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_13_rows b069_13_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_13_rows b069_13_labels]
    decide +kernel

def b069_14_rows : List Row := [(row3 12 18 56), (row3 12 18 57), (row3 12 18 58), (row3 12 18 59), (row3 12 18 60), (row3 12 18 61), (row3 12 18 62), (row3 12 18 63), (row3 12 19 20), (row3 12 19 21), (row3 12 19 22), (row3 12 19 23), (row3 12 19 24), (row3 12 19 25), (row3 12 19 26), (row3 12 19 27)]

def b069_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_14_rows b069_14_labels 54672587069321665642500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_14_rows b069_14_labels]
    decide +kernel

def b069_15_rows : List Row := [(row3 12 19 28), (row3 12 19 29), (row3 12 19 30), (row3 12 19 31), (row3 12 19 32), (row3 12 19 33), (row3 12 19 34), (row3 12 19 35), (row3 12 19 36), (row3 12 19 37), (row3 12 19 38), (row3 12 19 39), (row3 12 19 40), (row3 12 19 41), (row3 12 19 42), (row3 12 19 43)]

def b069_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b069_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b069_15_rows b069_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b069_15_rows b069_15_labels]
    decide +kernel

theorem checked069 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_069 QuarticIntegerComputationalData.ids64_069 28932114447778305606224670810 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b069_00_rows ++ b069_01_rows) ++ (b069_02_rows ++ b069_03_rows)) ++ ((b069_04_rows ++ b069_05_rows) ++ (b069_06_rows ++ b069_07_rows))) ++ (((b069_08_rows ++ b069_09_rows) ++ (b069_10_rows ++ b069_11_rows)) ++ ((b069_12_rows ++ b069_13_rows) ++ (b069_14_rows ++ b069_15_rows))))
    ((((b069_00_labels ++ b069_01_labels) ++ (b069_02_labels ++ b069_03_labels)) ++ ((b069_04_labels ++ b069_05_labels) ++ (b069_06_labels ++ b069_07_labels))) ++ (((b069_08_labels ++ b069_09_labels) ++ (b069_10_labels ++ b069_11_labels)) ++ ((b069_12_labels ++ b069_13_labels) ++ (b069_14_labels ++ b069_15_labels)))) 28932114447778305606224670810
  exact ((((b069_00_checked.append (c := 15485696335534067319673763370) b069_01_checked (by decide +kernel)).append (c := 26686903162757326045657467780) (b069_02_checked.append (c := 11201206827223258725983704410) b069_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 27038265729466818192801037560) ((b069_04_checked.append (c := 289711753862747816738430780) b069_05_checked (by decide +kernel)).append (c := 351362566709492147143569780) (b069_06_checked.append (c := 61650812846744330405139000) b069_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 28932114447778305606224670810) (((b069_08_checked.append (c := 1705439963039089120554548250) b069_09_checked (by decide +kernel)).append (c := 1801528449640994639694399750) (b069_10_checked.append (c := 96088486601905519139851500) b069_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1893848718311487413423633250) ((b069_12_checked.append (c := 92265596083423452063591000) b069_13_checked (by decide +kernel)).append (c := 92320268670492773729233500) (b069_14_checked.append (c := 54672587069321665642500) b069_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b070_00_rows : List Row := [(row3 12 19 44), (row3 12 19 45), (row3 12 19 46), (row3 12 19 47), (row3 12 19 48), (row3 12 19 49), (row3 12 19 50), (row3 12 19 51), (row3 12 19 52), (row3 12 19 53), (row3 12 19 54), (row3 12 19 55), (row3 12 19 56), (row3 12 19 57), (row3 12 19 58), (row3 12 19 59)]

def b070_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462)]

theorem b070_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_00_rows b070_00_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_00_rows b070_00_labels]
    decide +kernel

def b070_01_rows : List Row := [(row3 12 19 60), (row3 12 19 61), (row3 12 19 62), (row3 12 19 63), (row3 12 20 21), (row3 12 20 22), (row3 12 20 23), (row3 12 20 24), (row3 12 20 25), (row3 12 20 26), (row3 12 20 27), (row3 12 20 28), (row3 12 20 29), (row3 12 20 30), (row3 12 20 31), (row3 12 20 32)]

def b070_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_01_rows b070_01_labels 2816785910953601247429000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_01_rows b070_01_labels]
    decide +kernel

def b070_02_rows : List Row := [(row3 12 20 33), (row3 12 20 34), (row3 12 20 35), (row3 12 20 36), (row3 12 20 37), (row3 12 20 38), (row3 12 20 39), (row3 12 20 40), (row3 12 20 41), (row3 12 20 42), (row3 12 20 43), (row3 12 20 44), (row3 12 20 45), (row3 12 20 46), (row3 12 20 47), (row3 12 20 48)]

def b070_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_02_rows b070_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_02_rows b070_02_labels]
    decide +kernel

def b070_03_rows : List Row := [(row3 12 20 49), (row3 12 20 50), (row3 12 20 51), (row3 12 20 52), (row3 12 20 53), (row3 12 20 54), (row3 12 20 55), (row3 12 20 56), (row3 12 20 57), (row3 12 20 58), (row3 12 20 59), (row3 12 20 60), (row3 12 20 61), (row3 12 20 62), (row3 12 20 63), (row3 12 21 22)]

def b070_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462)]

theorem b070_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_03_rows b070_03_labels 93488310887154802434247500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_03_rows b070_03_labels]
    decide +kernel

def b070_04_rows : List Row := [(row3 12 21 23), (row3 12 21 24), (row3 12 21 25), (row3 12 21 26), (row3 12 21 27), (row3 12 21 28), (row3 12 21 29), (row3 12 21 30), (row3 12 21 31), (row3 12 21 32), (row3 12 21 33), (row3 12 21 34), (row3 12 21 35), (row3 12 21 36), (row3 12 21 37), (row3 12 21 38)]

def b070_04_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_04_rows b070_04_labels 734927278539940998876000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_04_rows b070_04_labels]
    decide +kernel

def b070_05_rows : List Row := [(row3 12 21 39), (row3 12 21 40), (row3 12 21 41), (row3 12 21 42), (row3 12 21 43), (row3 12 21 44), (row3 12 21 45), (row3 12 21 46), (row3 12 21 47), (row3 12 21 48), (row3 12 21 49), (row3 12 21 50), (row3 12 21 51), (row3 12 21 52), (row3 12 21 53), (row3 12 21 54)]

def b070_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_05_rows b070_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_05_rows b070_05_labels]
    decide +kernel

def b070_06_rows : List Row := [(row3 12 21 55), (row3 12 21 56), (row3 12 21 57), (row3 12 21 58), (row3 12 21 59), (row3 12 21 60), (row3 12 21 61), (row3 12 21 62), (row3 12 21 63), (row3 12 22 23), (row3 12 22 24), (row3 12 22 25), (row3 12 22 26), (row3 12 22 27), (row3 12 22 28), (row3 12 22 29)]

def b070_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228)]

theorem b070_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_06_rows b070_06_labels 1643728493828942075254389750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_06_rows b070_06_labels]
    decide +kernel

def b070_07_rows : List Row := [(row3 12 22 30), (row3 12 22 31), (row3 12 22 32), (row3 12 22 33), (row3 12 22 34), (row3 12 22 35), (row3 12 22 36), (row3 12 22 37), (row3 12 22 38), (row3 12 22 39), (row3 12 22 40), (row3 12 22 41), (row3 12 22 42), (row3 12 22 43), (row3 12 22 44), (row3 12 22 45)]

def b070_07_labels : List Row := [(row3 293 462 293), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_07_rows b070_07_labels 90903669521960238345202500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_07_rows b070_07_labels]
    decide +kernel

def b070_08_rows : List Row := [(row3 12 22 46), (row3 12 22 47), (row3 12 22 48), (row3 12 22 49), (row3 12 22 50), (row3 12 22 51), (row3 12 22 52), (row3 12 22 53), (row3 12 22 54), (row3 12 22 55), (row3 12 22 56), (row3 12 22 57), (row3 12 22 58), (row3 12 22 59), (row3 12 22 60), (row3 12 22 61)]

def b070_08_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_08_rows b070_08_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_08_rows b070_08_labels]
    decide +kernel

def b070_09_rows : List Row := [(row3 12 22 62), (row3 12 22 63), (row3 12 23 24), (row3 12 23 25), (row3 12 23 26), (row3 12 23 27), (row3 12 23 28), (row3 12 23 29), (row3 12 23 30), (row3 12 23 31), (row3 12 23 32), (row3 12 23 33), (row3 12 23 34), (row3 12 23 35), (row3 12 23 36), (row3 12 23 37)]

def b070_09_labels : List Row := [(row3 246 462 246), (row3 462 462 462), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 232 232 462), (row3 284 284 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_09_rows b070_09_labels 61220667063148723362933000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_09_rows b070_09_labels]
    decide +kernel

def b070_10_rows : List Row := [(row3 12 23 38), (row3 12 23 39), (row3 12 23 40), (row3 12 23 41), (row3 12 23 42), (row3 12 23 43), (row3 12 23 44), (row3 12 23 45), (row3 12 23 46), (row3 12 23 47), (row3 12 23 48), (row3 12 23 49), (row3 12 23 50), (row3 12 23 51), (row3 12 23 52), (row3 12 23 53)]

def b070_10_labels : List Row := [(row3 246 246 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_10_rows b070_10_labels 295728807902769650916000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_10_rows b070_10_labels]
    decide +kernel

def b070_11_rows : List Row := [(row3 12 23 54), (row3 12 23 55), (row3 12 23 56), (row3 12 23 57), (row3 12 23 58), (row3 12 23 59), (row3 12 23 60), (row3 12 23 61), (row3 12 23 62), (row3 12 23 63), (row3 12 24 25), (row3 12 24 26), (row3 12 24 27), (row3 12 24 28), (row3 12 24 29), (row3 12 24 30)]

def b070_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_11_rows b070_11_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_11_rows b070_11_labels]
    decide +kernel

def b070_12_rows : List Row := [(row3 12 24 31), (row3 12 24 32), (row3 12 24 33), (row3 12 24 34), (row3 12 24 35), (row3 12 24 36), (row3 12 24 37), (row3 12 24 38), (row3 12 24 39), (row3 12 24 40), (row3 12 24 41), (row3 12 24 42), (row3 12 24 43), (row3 12 24 44), (row3 12 24 45), (row3 12 24 46)]

def b070_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_12_rows b070_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_12_rows b070_12_labels]
    decide +kernel

def b070_13_rows : List Row := [(row3 12 24 47), (row3 12 24 48), (row3 12 24 49), (row3 12 24 50), (row3 12 24 51), (row3 12 24 52), (row3 12 24 53), (row3 12 24 54), (row3 12 24 55), (row3 12 24 56), (row3 12 24 57), (row3 12 24 58), (row3 12 24 59), (row3 12 24 60), (row3 12 24 61), (row3 12 24 62)]

def b070_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_13_rows b070_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_13_rows b070_13_labels]
    decide +kernel

def b070_14_rows : List Row := [(row3 12 24 63), (row3 12 25 26), (row3 12 25 27), (row3 12 25 28), (row3 12 25 29), (row3 12 25 30), (row3 12 25 31), (row3 12 25 32), (row3 12 25 33), (row3 12 25 34), (row3 12 25 35), (row3 12 25 36), (row3 12 25 37), (row3 12 25 38), (row3 12 25 39), (row3 12 25 40)]

def b070_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_14_rows b070_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_14_rows b070_14_labels]
    decide +kernel

def b070_15_rows : List Row := [(row3 12 25 41), (row3 12 25 42), (row3 12 25 43), (row3 12 25 44), (row3 12 25 45), (row3 12 25 46), (row3 12 25 47), (row3 12 25 48), (row3 12 25 49), (row3 12 25 50), (row3 12 25 51), (row3 12 25 52), (row3 12 25 53), (row3 12 25 54), (row3 12 25 55), (row3 12 25 56)]

def b070_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b070_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b070_15_rows b070_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b070_15_rows b070_15_labels]
    decide +kernel

theorem checked070 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_070 QuarticIntegerComputationalData.ids64_070 1893232277664764739259871250 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b070_00_rows ++ b070_01_rows) ++ (b070_02_rows ++ b070_03_rows)) ++ ((b070_04_rows ++ b070_05_rows) ++ (b070_06_rows ++ b070_07_rows))) ++ (((b070_08_rows ++ b070_09_rows) ++ (b070_10_rows ++ b070_11_rows)) ++ ((b070_12_rows ++ b070_13_rows) ++ (b070_14_rows ++ b070_15_rows))))
    ((((b070_00_labels ++ b070_01_labels) ++ (b070_02_labels ++ b070_03_labels)) ++ ((b070_04_labels ++ b070_05_labels) ++ (b070_06_labels ++ b070_07_labels))) ++ (((b070_08_labels ++ b070_09_labels) ++ (b070_10_labels ++ b070_11_labels)) ++ ((b070_12_labels ++ b070_13_labels) ++ (b070_14_labels ++ b070_15_labels)))) 1893232277664764739259871250
  exact ((((b070_00_checked.append (c := 2832888018767217802074000) b070_01_checked (by decide +kernel)).append (c := 96321198905922020236321500) (b070_02_checked.append (c := 93488310887154802434247500) b070_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1831688289535364274834789750) ((b070_04_checked.append (c := 734927278539940998876000) b070_05_checked (by decide +kernel)).append (c := 1735367090629442254598468250) (b070_06_checked.append (c := 1734632163350902313599592250) b070_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1893232277664764739259871250) (((b070_08_checked.append (c := 61232157213684078219520500) b070_09_checked (by decide +kernel)).append (c := 61543988129400464425081500) (b070_10_checked.append (c := 311830915716386205561000) b070_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 61543988129400464425081500) ((b070_12_checked.append (c := 0) b070_13_checked (by decide +kernel)).append (c := 0) (b070_14_checked.append (c := 0) b070_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b071_00_rows : List Row := [(row3 12 25 57), (row3 12 25 58), (row3 12 25 59), (row3 12 25 60), (row3 12 25 61), (row3 12 25 62), (row3 12 25 63), (row3 12 26 27), (row3 12 26 28), (row3 12 26 29), (row3 12 26 30), (row3 12 26 31), (row3 12 26 32), (row3 12 26 33), (row3 12 26 34), (row3 12 26 35)]

def b071_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_00_rows b071_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_00_rows b071_00_labels]
    decide +kernel

def b071_01_rows : List Row := [(row3 12 26 36), (row3 12 26 37), (row3 12 26 38), (row3 12 26 39), (row3 12 26 40), (row3 12 26 41), (row3 12 26 42), (row3 12 26 43), (row3 12 26 44), (row3 12 26 45), (row3 12 26 46), (row3 12 26 47), (row3 12 26 48), (row3 12 26 49), (row3 12 26 50), (row3 12 26 51)]

def b071_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_01_rows b071_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_01_rows b071_01_labels]
    decide +kernel

def b071_02_rows : List Row := [(row3 12 26 52), (row3 12 26 53), (row3 12 26 54), (row3 12 26 55), (row3 12 26 56), (row3 12 26 57), (row3 12 26 58), (row3 12 26 59), (row3 12 26 60), (row3 12 26 61), (row3 12 26 62), (row3 12 26 63), (row3 12 27 28), (row3 12 27 29), (row3 12 27 30), (row3 12 27 31)]

def b071_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_02_rows b071_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_02_rows b071_02_labels]
    decide +kernel

def b071_03_rows : List Row := [(row3 12 27 32), (row3 12 27 33), (row3 12 27 34), (row3 12 27 35), (row3 12 27 36), (row3 12 27 37), (row3 12 27 38), (row3 12 27 39), (row3 12 27 40), (row3 12 27 41), (row3 12 27 42), (row3 12 27 43), (row3 12 27 44), (row3 12 27 45), (row3 12 27 46), (row3 12 27 47)]

def b071_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_03_rows b071_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_03_rows b071_03_labels]
    decide +kernel

def b071_04_rows : List Row := [(row3 12 27 48), (row3 12 27 49), (row3 12 27 50), (row3 12 27 51), (row3 12 27 52), (row3 12 27 53), (row3 12 27 54), (row3 12 27 55), (row3 12 27 56), (row3 12 27 57), (row3 12 27 58), (row3 12 27 59), (row3 12 27 60), (row3 12 27 61), (row3 12 27 62), (row3 12 27 63)]

def b071_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_04_rows b071_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_04_rows b071_04_labels]
    decide +kernel

def b071_05_rows : List Row := [(row3 12 28 29), (row3 12 28 30), (row3 12 28 31), (row3 12 28 32), (row3 12 28 33), (row3 12 28 34), (row3 12 28 35), (row3 12 28 36), (row3 12 28 37), (row3 12 28 38), (row3 12 28 39), (row3 12 28 40), (row3 12 28 41), (row3 12 28 42), (row3 12 28 43), (row3 12 28 44)]

def b071_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_05_rows b071_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_05_rows b071_05_labels]
    decide +kernel

def b071_06_rows : List Row := [(row3 12 28 45), (row3 12 28 46), (row3 12 28 47), (row3 12 28 48), (row3 12 28 49), (row3 12 28 50), (row3 12 28 51), (row3 12 28 52), (row3 12 28 53), (row3 12 28 54), (row3 12 28 55), (row3 12 28 56), (row3 12 28 57), (row3 12 28 58), (row3 12 28 59), (row3 12 28 60)]

def b071_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_06_rows b071_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_06_rows b071_06_labels]
    decide +kernel

def b071_07_rows : List Row := [(row3 12 28 61), (row3 12 28 62), (row3 12 28 63), (row3 12 29 30), (row3 12 29 31), (row3 12 29 32), (row3 12 29 33), (row3 12 29 34), (row3 12 29 35), (row3 12 29 36), (row3 12 29 37), (row3 12 29 38), (row3 12 29 39), (row3 12 29 40), (row3 12 29 41), (row3 12 29 42)]

def b071_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_07_rows b071_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_07_rows b071_07_labels]
    decide +kernel

def b071_08_rows : List Row := [(row3 12 29 43), (row3 12 29 44), (row3 12 29 45), (row3 12 29 46), (row3 12 29 47), (row3 12 29 48), (row3 12 29 49), (row3 12 29 50), (row3 12 29 51), (row3 12 29 52), (row3 12 29 53), (row3 12 29 54), (row3 12 29 55), (row3 12 29 56), (row3 12 29 57), (row3 12 29 58)]

def b071_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_08_rows b071_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_08_rows b071_08_labels]
    decide +kernel

def b071_09_rows : List Row := [(row3 12 29 59), (row3 12 29 60), (row3 12 29 61), (row3 12 29 62), (row3 12 29 63), (row3 12 30 31), (row3 12 30 32), (row3 12 30 33), (row3 12 30 34), (row3 12 30 35), (row3 12 30 36), (row3 12 30 37), (row3 12 30 38), (row3 12 30 39), (row3 12 30 40), (row3 12 30 41)]

def b071_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_09_rows b071_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_09_rows b071_09_labels]
    decide +kernel

def b071_10_rows : List Row := [(row3 12 30 42), (row3 12 30 43), (row3 12 30 44), (row3 12 30 45), (row3 12 30 46), (row3 12 30 47), (row3 12 30 48), (row3 12 30 49), (row3 12 30 50), (row3 12 30 51), (row3 12 30 52), (row3 12 30 53), (row3 12 30 54), (row3 12 30 55), (row3 12 30 56), (row3 12 30 57)]

def b071_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_10_rows b071_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_10_rows b071_10_labels]
    decide +kernel

def b071_11_rows : List Row := [(row3 12 30 58), (row3 12 30 59), (row3 12 30 60), (row3 12 30 61), (row3 12 30 62), (row3 12 30 63), (row3 12 31 32), (row3 12 31 33), (row3 12 31 34), (row3 12 31 35), (row3 12 31 36), (row3 12 31 37), (row3 12 31 38), (row3 12 31 39), (row3 12 31 40), (row3 12 31 41)]

def b071_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_11_rows b071_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_11_rows b071_11_labels]
    decide +kernel

def b071_12_rows : List Row := [(row3 12 31 42), (row3 12 31 43), (row3 12 31 44), (row3 12 31 45), (row3 12 31 46), (row3 12 31 47), (row3 12 31 48), (row3 12 31 49), (row3 12 31 50), (row3 12 31 51), (row3 12 31 52), (row3 12 31 53), (row3 12 31 54), (row3 12 31 55), (row3 12 31 56), (row3 12 31 57)]

def b071_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_12_rows b071_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_12_rows b071_12_labels]
    decide +kernel

def b071_13_rows : List Row := [(row3 12 31 58), (row3 12 31 59), (row3 12 31 60), (row3 12 31 61), (row3 12 31 62), (row3 12 31 63), (row3 12 32 33), (row3 12 32 34), (row3 12 32 35), (row3 12 32 36), (row3 12 32 37), (row3 12 32 38), (row3 12 32 39), (row3 12 32 40), (row3 12 32 41), (row3 12 32 42)]

def b071_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_13_rows b071_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_13_rows b071_13_labels]
    decide +kernel

def b071_14_rows : List Row := [(row3 12 32 43), (row3 12 32 44), (row3 12 32 45), (row3 12 32 46), (row3 12 32 47), (row3 12 32 48), (row3 12 32 49), (row3 12 32 50), (row3 12 32 51), (row3 12 32 52), (row3 12 32 53), (row3 12 32 54), (row3 12 32 55), (row3 12 32 56), (row3 12 32 57), (row3 12 32 58)]

def b071_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_14_rows b071_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_14_rows b071_14_labels]
    decide +kernel

def b071_15_rows : List Row := [(row3 12 32 59), (row3 12 32 60), (row3 12 32 61), (row3 12 32 62), (row3 12 32 63), (row3 12 33 34), (row3 12 33 35), (row3 12 33 36), (row3 12 33 37), (row3 12 33 38), (row3 12 33 39), (row3 12 33 40), (row3 12 33 41), (row3 12 33 42), (row3 12 33 43), (row3 12 33 44)]

def b071_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b071_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b071_15_rows b071_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b071_15_rows b071_15_labels]
    decide +kernel

theorem checked071 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_071 QuarticIntegerComputationalData.ids64_071 0 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b071_00_rows ++ b071_01_rows) ++ (b071_02_rows ++ b071_03_rows)) ++ ((b071_04_rows ++ b071_05_rows) ++ (b071_06_rows ++ b071_07_rows))) ++ (((b071_08_rows ++ b071_09_rows) ++ (b071_10_rows ++ b071_11_rows)) ++ ((b071_12_rows ++ b071_13_rows) ++ (b071_14_rows ++ b071_15_rows))))
    ((((b071_00_labels ++ b071_01_labels) ++ (b071_02_labels ++ b071_03_labels)) ++ ((b071_04_labels ++ b071_05_labels) ++ (b071_06_labels ++ b071_07_labels))) ++ (((b071_08_labels ++ b071_09_labels) ++ (b071_10_labels ++ b071_11_labels)) ++ ((b071_12_labels ++ b071_13_labels) ++ (b071_14_labels ++ b071_15_labels)))) 0
  exact ((((b071_00_checked.append (c := 0) b071_01_checked (by decide +kernel)).append (c := 0) (b071_02_checked.append (c := 0) b071_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b071_04_checked.append (c := 0) b071_05_checked (by decide +kernel)).append (c := 0) (b071_06_checked.append (c := 0) b071_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 0) (((b071_08_checked.append (c := 0) b071_09_checked (by decide +kernel)).append (c := 0) (b071_10_checked.append (c := 0) b071_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b071_12_checked.append (c := 0) b071_13_checked (by decide +kernel)).append (c := 0) (b071_14_checked.append (c := 0) b071_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b072_00_rows : List Row := [(row3 12 33 45), (row3 12 33 46), (row3 12 33 47), (row3 12 33 48), (row3 12 33 49), (row3 12 33 50), (row3 12 33 51), (row3 12 33 52), (row3 12 33 53), (row3 12 33 54), (row3 12 33 55), (row3 12 33 56), (row3 12 33 57), (row3 12 33 58), (row3 12 33 59), (row3 12 33 60)]

def b072_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_00_rows b072_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_00_rows b072_00_labels]
    decide +kernel

def b072_01_rows : List Row := [(row3 12 33 61), (row3 12 33 62), (row3 12 33 63), (row3 12 34 35), (row3 12 34 36), (row3 12 34 37), (row3 12 34 38), (row3 12 34 39), (row3 12 34 40), (row3 12 34 41), (row3 12 34 42), (row3 12 34 43), (row3 12 34 44), (row3 12 34 45), (row3 12 34 46), (row3 12 34 47)]

def b072_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_01_rows b072_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_01_rows b072_01_labels]
    decide +kernel

def b072_02_rows : List Row := [(row3 12 34 48), (row3 12 34 49), (row3 12 34 50), (row3 12 34 51), (row3 12 34 52), (row3 12 34 53), (row3 12 34 54), (row3 12 34 55), (row3 12 34 56), (row3 12 34 57), (row3 12 34 58), (row3 12 34 59), (row3 12 34 60), (row3 12 34 61), (row3 12 34 62), (row3 12 34 63)]

def b072_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_02_rows b072_02_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_02_rows b072_02_labels]
    decide +kernel

def b072_03_rows : List Row := [(row3 12 35 36), (row3 12 35 37), (row3 12 35 38), (row3 12 35 39), (row3 12 35 40), (row3 12 35 41), (row3 12 35 42), (row3 12 35 43), (row3 12 35 44), (row3 12 35 45), (row3 12 35 46), (row3 12 35 47), (row3 12 35 48), (row3 12 35 49), (row3 12 35 50), (row3 12 35 51)]

def b072_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_03_rows b072_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_03_rows b072_03_labels]
    decide +kernel

def b072_04_rows : List Row := [(row3 12 35 52), (row3 12 35 53), (row3 12 35 54), (row3 12 35 55), (row3 12 35 56), (row3 12 35 57), (row3 12 35 58), (row3 12 35 59), (row3 12 35 60), (row3 12 35 61), (row3 12 35 62), (row3 12 35 63), (row3 12 36 37), (row3 12 36 38), (row3 12 36 39), (row3 12 36 40)]

def b072_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_04_rows b072_04_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_04_rows b072_04_labels]
    decide +kernel

def b072_05_rows : List Row := [(row3 12 36 41), (row3 12 36 42), (row3 12 36 43), (row3 12 36 44), (row3 12 36 45), (row3 12 36 46), (row3 12 36 47), (row3 12 36 48), (row3 12 36 49), (row3 12 36 50), (row3 12 36 51), (row3 12 36 52), (row3 12 36 53), (row3 12 36 54), (row3 12 36 55), (row3 12 36 56)]

def b072_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_05_rows b072_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_05_rows b072_05_labels]
    decide +kernel

def b072_06_rows : List Row := [(row3 12 36 57), (row3 12 36 58), (row3 12 36 59), (row3 12 36 60), (row3 12 36 61), (row3 12 36 62), (row3 12 36 63), (row3 12 37 38), (row3 12 37 39), (row3 12 37 40), (row3 12 37 41), (row3 12 37 42), (row3 12 37 43), (row3 12 37 44), (row3 12 37 45), (row3 12 37 46)]

def b072_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_06_rows b072_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_06_rows b072_06_labels]
    decide +kernel

def b072_07_rows : List Row := [(row3 12 37 47), (row3 12 37 48), (row3 12 37 49), (row3 12 37 50), (row3 12 37 51), (row3 12 37 52), (row3 12 37 53), (row3 12 37 54), (row3 12 37 55), (row3 12 37 56), (row3 12 37 57), (row3 12 37 58), (row3 12 37 59), (row3 12 37 60), (row3 12 37 61), (row3 12 37 62)]

def b072_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462)]

theorem b072_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_07_rows b072_07_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_07_rows b072_07_labels]
    decide +kernel

def b072_08_rows : List Row := [(row3 12 37 63), (row3 12 38 39), (row3 12 38 40), (row3 12 38 41), (row3 12 38 42), (row3 12 38 43), (row3 12 38 44), (row3 12 38 45), (row3 12 38 46), (row3 12 38 47), (row3 12 38 48), (row3 12 38 49), (row3 12 38 50), (row3 12 38 51), (row3 12 38 52), (row3 12 38 53)]

def b072_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_08_rows b072_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_08_rows b072_08_labels]
    decide +kernel

def b072_09_rows : List Row := [(row3 12 38 54), (row3 12 38 55), (row3 12 38 56), (row3 12 38 57), (row3 12 38 58), (row3 12 38 59), (row3 12 38 60), (row3 12 38 61), (row3 12 38 62), (row3 12 38 63), (row3 12 39 40), (row3 12 39 41), (row3 12 39 42), (row3 12 39 43), (row3 12 39 44), (row3 12 39 45)]

def b072_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_09_rows b072_09_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_09_rows b072_09_labels]
    decide +kernel

def b072_10_rows : List Row := [(row3 12 39 46), (row3 12 39 47), (row3 12 39 48), (row3 12 39 49), (row3 12 39 50), (row3 12 39 51), (row3 12 39 52), (row3 12 39 53), (row3 12 39 54), (row3 12 39 55), (row3 12 39 56), (row3 12 39 57), (row3 12 39 58), (row3 12 39 59), (row3 12 39 60), (row3 12 39 61)]

def b072_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_10_rows b072_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_10_rows b072_10_labels]
    decide +kernel

def b072_11_rows : List Row := [(row3 12 39 62), (row3 12 39 63), (row3 12 40 41), (row3 12 40 42), (row3 12 40 43), (row3 12 40 44), (row3 12 40 45), (row3 12 40 46), (row3 12 40 47), (row3 12 40 48), (row3 12 40 49), (row3 12 40 50), (row3 12 40 51), (row3 12 40 52), (row3 12 40 53), (row3 12 40 54)]

def b072_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_11_rows b072_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_11_rows b072_11_labels]
    decide +kernel

def b072_12_rows : List Row := [(row3 12 40 55), (row3 12 40 56), (row3 12 40 57), (row3 12 40 58), (row3 12 40 59), (row3 12 40 60), (row3 12 40 61), (row3 12 40 62), (row3 12 40 63), (row3 12 41 42), (row3 12 41 43), (row3 12 41 44), (row3 12 41 45), (row3 12 41 46), (row3 12 41 47), (row3 12 41 48)]

def b072_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_12_rows b072_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_12_rows b072_12_labels]
    decide +kernel

def b072_13_rows : List Row := [(row3 12 41 49), (row3 12 41 50), (row3 12 41 51), (row3 12 41 52), (row3 12 41 53), (row3 12 41 54), (row3 12 41 55), (row3 12 41 56), (row3 12 41 57), (row3 12 41 58), (row3 12 41 59), (row3 12 41 60), (row3 12 41 61), (row3 12 41 62), (row3 12 41 63), (row3 12 42 43)]

def b072_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_13_rows b072_13_labels 38992955600732418112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_13_rows b072_13_labels]
    decide +kernel

def b072_14_rows : List Row := [(row3 12 42 44), (row3 12 42 45), (row3 12 42 46), (row3 12 42 47), (row3 12 42 48), (row3 12 42 49), (row3 12 42 50), (row3 12 42 51), (row3 12 42 52), (row3 12 42 53), (row3 12 42 54), (row3 12 42 55), (row3 12 42 56), (row3 12 42 57), (row3 12 42 58), (row3 12 42 59)]

def b072_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 246 246 462)]

theorem b072_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_14_rows b072_14_labels 419105409451888813749000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_14_rows b072_14_labels]
    decide +kernel

def b072_15_rows : List Row := [(row3 12 42 60), (row3 12 42 61), (row3 12 42 62), (row3 12 42 63), (row3 12 43 44), (row3 12 43 45), (row3 12 43 46), (row3 12 43 47), (row3 12 43 48), (row3 12 43 49), (row3 12 43 50), (row3 12 43 51), (row3 12 43 52), (row3 12 43 53), (row3 12 43 54), (row3 12 43 55)]

def b072_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b072_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b072_15_rows b072_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b072_15_rows b072_15_labels]
    decide +kernel

theorem checked072 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_072 QuarticIntegerComputationalData.ids64_072 496398866837137420486500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b072_00_rows ++ b072_01_rows) ++ (b072_02_rows ++ b072_03_rows)) ++ ((b072_04_rows ++ b072_05_rows) ++ (b072_06_rows ++ b072_07_rows))) ++ (((b072_08_rows ++ b072_09_rows) ++ (b072_10_rows ++ b072_11_rows)) ++ ((b072_12_rows ++ b072_13_rows) ++ (b072_14_rows ++ b072_15_rows))))
    ((((b072_00_labels ++ b072_01_labels) ++ (b072_02_labels ++ b072_03_labels)) ++ ((b072_04_labels ++ b072_05_labels) ++ (b072_06_labels ++ b072_07_labels))) ++ (((b072_08_labels ++ b072_09_labels) ++ (b072_10_labels ++ b072_11_labels)) ++ ((b072_12_labels ++ b072_13_labels) ++ (b072_14_labels ++ b072_15_labels)))) 496398866837137420486500
  exact ((((b072_00_checked.append (c := 0) b072_01_checked (by decide +kernel)).append (c := 11490150535354856587500) (b072_02_checked.append (c := 11490150535354856587500) b072_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 26810351249161332037500) ((b072_04_checked.append (c := 7660100356903237725000) b072_05_checked (by decide +kernel)).append (c := 15320200713806475450000) (b072_06_checked.append (c := 7660100356903237725000) b072_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 496398866837137420486500) (((b072_08_checked.append (c := 11490150535354856587500) b072_09_checked (by decide +kernel)).append (c := 11490150535354856587500) (b072_10_checked.append (c := 0) b072_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 469588515587976088449000) ((b072_12_checked.append (c := 38992955600732418112500) b072_13_checked (by decide +kernel)).append (c := 458098365052621231861500) (b072_14_checked.append (c := 419105409451888813749000) b072_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
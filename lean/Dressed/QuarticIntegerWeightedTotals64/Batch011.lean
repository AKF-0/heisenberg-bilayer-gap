import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch010
import Dressed.QuarticIntegerComputationalData64.Batch011


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b089_00_rows : List Row := [(row3 16 25 55), (row3 16 25 56), (row3 16 25 57), (row3 16 25 58), (row3 16 25 59), (row3 16 25 60), (row3 16 25 61), (row3 16 25 62), (row3 16 25 63), (row3 16 26 27), (row3 16 26 28), (row3 16 26 29), (row3 16 26 30), (row3 16 26 31), (row3 16 26 32), (row3 16 26 33)]

def b089_00_labels : List Row := [(row3 235 462 235), (row3 167 190 166), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 289 291 291), (row3 148 145 137), (row3 183 183 178), (row3 289 291 291)]

theorem b089_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_00_rows b089_00_labels 6599675405384052580169493120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_00_rows b089_00_labels]
    decide +kernel

def b089_01_rows : List Row := [(row3 16 26 34), (row3 16 26 35), (row3 16 26 36), (row3 16 26 37), (row3 16 26 38), (row3 16 26 39), (row3 16 26 40), (row3 16 26 41), (row3 16 26 42), (row3 16 26 43), (row3 16 26 44), (row3 16 26 45), (row3 16 26 46), (row3 16 26 47), (row3 16 26 48), (row3 16 26 49)]

def b089_01_labels : List Row := [(row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 265 267 267), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 237 462 237), (row3 462 462 462)]

theorem b089_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_01_rows b089_01_labels 35525507729817042152702100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_01_rows b089_01_labels]
    decide +kernel

def b089_02_rows : List Row := [(row3 16 26 50), (row3 16 26 51), (row3 16 26 52), (row3 16 26 53), (row3 16 26 54), (row3 16 26 55), (row3 16 26 56), (row3 16 26 57), (row3 16 26 58), (row3 16 26 59), (row3 16 26 60), (row3 16 26 61), (row3 16 26 62), (row3 16 26 63), (row3 16 27 28), (row3 16 27 29)]

def b089_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b089_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_02_rows b089_02_labels 58849155846515586653996400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_02_rows b089_02_labels]
    decide +kernel

def b089_03_rows : List Row := [(row3 16 27 30), (row3 16 27 31), (row3 16 27 32), (row3 16 27 33), (row3 16 27 34), (row3 16 27 35), (row3 16 27 36), (row3 16 27 37), (row3 16 27 38), (row3 16 27 39), (row3 16 27 40), (row3 16 27 41), (row3 16 27 42), (row3 16 27 43), (row3 16 27 44), (row3 16 27 45)]

def b089_03_labels : List Row := [(row3 235 235 462), (row3 273 273 462), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b089_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_03_rows b089_03_labels 8977736304122144210920800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_03_rows b089_03_labels]
    decide +kernel

def b089_04_rows : List Row := [(row3 16 27 46), (row3 16 27 47), (row3 16 27 48), (row3 16 27 49), (row3 16 27 50), (row3 16 27 51), (row3 16 27 52), (row3 16 27 53), (row3 16 27 54), (row3 16 27 55), (row3 16 27 56), (row3 16 27 57), (row3 16 27 58), (row3 16 27 59), (row3 16 27 60), (row3 16 27 61)]

def b089_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b089_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_04_rows b089_04_labels 555889215118270689432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_04_rows b089_04_labels]
    decide +kernel

def b089_05_rows : List Row := [(row3 16 27 62), (row3 16 27 63), (row3 16 28 29), (row3 16 28 30), (row3 16 28 31), (row3 16 28 32), (row3 16 28 33), (row3 16 28 34), (row3 16 28 35), (row3 16 28 36), (row3 16 28 37), (row3 16 28 38), (row3 16 28 39), (row3 16 28 40), (row3 16 28 41), (row3 16 28 42)]

def b089_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b089_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_05_rows b089_05_labels 373583051205271382664000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_05_rows b089_05_labels]
    decide +kernel

def b089_06_rows : List Row := [(row3 16 28 43), (row3 16 28 44), (row3 16 28 45), (row3 16 28 46), (row3 16 28 47), (row3 16 28 48), (row3 16 28 49), (row3 16 28 50), (row3 16 28 51), (row3 16 28 52), (row3 16 28 53), (row3 16 28 54), (row3 16 28 55), (row3 16 28 56), (row3 16 28 57), (row3 16 28 58)]

def b089_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b089_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_06_rows b089_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_06_rows b089_06_labels]
    decide +kernel

def b089_07_rows : List Row := [(row3 16 28 59), (row3 16 28 60), (row3 16 28 61), (row3 16 28 62), (row3 16 28 63), (row3 16 29 30), (row3 16 29 31), (row3 16 29 32), (row3 16 29 33), (row3 16 29 34), (row3 16 29 35), (row3 16 29 36), (row3 16 29 37), (row3 16 29 38), (row3 16 29 39), (row3 16 29 40)]

def b089_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 288 288 462), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 238 238 462)]

theorem b089_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_07_rows b089_07_labels 43281725772873932977419360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_07_rows b089_07_labels]
    decide +kernel

def b089_08_rows : List Row := [(row3 16 29 41), (row3 16 29 42), (row3 16 29 43), (row3 16 29 44), (row3 16 29 45), (row3 16 29 46), (row3 16 29 47), (row3 16 29 48), (row3 16 29 49), (row3 16 29 50), (row3 16 29 51), (row3 16 29 52), (row3 16 29 53), (row3 16 29 54), (row3 16 29 55), (row3 16 29 56)]

def b089_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462)]

theorem b089_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_08_rows b089_08_labels 555889215118270689432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_08_rows b089_08_labels]
    decide +kernel

def b089_09_rows : List Row := [(row3 16 29 57), (row3 16 29 58), (row3 16 29 59), (row3 16 29 60), (row3 16 29 61), (row3 16 29 62), (row3 16 29 63), (row3 16 30 31), (row3 16 30 32), (row3 16 30 33), (row3 16 30 34), (row3 16 30 35), (row3 16 30 36), (row3 16 30 37), (row3 16 30 38), (row3 16 30 39)]

def b089_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 127 126 137), (row3 183 183 178), (row3 289 291 291), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291)]

theorem b089_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_09_rows b089_09_labels 8916638642916252629997895200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_09_rows b089_09_labels]
    decide +kernel

def b089_10_rows : List Row := [(row3 16 30 40), (row3 16 30 41), (row3 16 30 42), (row3 16 30 43), (row3 16 30 44), (row3 16 30 45), (row3 16 30 46), (row3 16 30 47), (row3 16 30 48), (row3 16 30 49), (row3 16 30 50), (row3 16 30 51), (row3 16 30 52), (row3 16 30 53), (row3 16 30 54), (row3 16 30 55)]

def b089_10_labels : List Row := [(row3 265 267 267), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b089_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_10_rows b089_10_labels 4283575770699160033320900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_10_rows b089_10_labels]
    decide +kernel

def b089_11_rows : List Row := [(row3 16 30 56), (row3 16 30 57), (row3 16 30 58), (row3 16 30 59), (row3 16 30 60), (row3 16 30 61), (row3 16 30 62), (row3 16 30 63), (row3 16 31 32), (row3 16 31 33), (row3 16 31 34), (row3 16 31 35), (row3 16 31 36), (row3 16 31 37), (row3 16 31 38), (row3 16 31 39)]

def b089_11_labels : List Row := [(row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 349 346 350), (row3 146 137 143), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 300 462 300), (row3 127 137 126)]

theorem b089_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_11_rows b089_11_labels 14045969096384881116575715120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_11_rows b089_11_labels]
    decide +kernel

def b089_12_rows : List Row := [(row3 16 31 40), (row3 16 31 41), (row3 16 31 42), (row3 16 31 43), (row3 16 31 44), (row3 16 31 45), (row3 16 31 46), (row3 16 31 47), (row3 16 31 48), (row3 16 31 49), (row3 16 31 50), (row3 16 31 51), (row3 16 31 52), (row3 16 31 53), (row3 16 31 54), (row3 16 31 55)]

def b089_12_labels : List Row := [(row3 195 188 194), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 233 462 233)]

theorem b089_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_12_rows b089_12_labels 155481149561335936491389040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_12_rows b089_12_labels]
    decide +kernel

def b089_13_rows : List Row := [(row3 16 31 56), (row3 16 31 57), (row3 16 31 58), (row3 16 31 59), (row3 16 31 60), (row3 16 31 61), (row3 16 31 62), (row3 16 31 63), (row3 16 32 33), (row3 16 32 34), (row3 16 32 35), (row3 16 32 36), (row3 16 32 37), (row3 16 32 38), (row3 16 32 39), (row3 16 32 40)]

def b089_13_labels : List Row := [(row3 167 190 166), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 288 462 288), (row3 174 178 174), (row3 273 462 273), (row3 239 462 239), (row3 462 462 462), (row3 239 462 239), (row3 273 462 273), (row3 174 178 174), (row3 335 96 205)]

theorem b089_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_13_rows b089_13_labels 27356395493194245977212621920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_13_rows b089_13_labels]
    decide +kernel

def b089_14_rows : List Row := [(row3 16 32 41), (row3 16 32 42), (row3 16 32 43), (row3 16 32 44), (row3 16 32 45), (row3 16 32 46), (row3 16 32 47), (row3 16 32 48), (row3 16 32 49), (row3 16 32 50), (row3 16 32 51), (row3 16 32 52), (row3 16 32 53), (row3 16 32 54), (row3 16 32 55), (row3 16 32 56)]

def b089_14_labels : List Row := [(row3 273 462 273), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 273 462 273), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 205 96 335)]

theorem b089_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_14_rows b089_14_labels 14119035340153549676204028000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_14_rows b089_14_labels]
    decide +kernel

def b089_15_rows : List Row := [(row3 16 32 57), (row3 16 32 58), (row3 16 32 59), (row3 16 32 60), (row3 16 32 61), (row3 16 32 62), (row3 16 32 63), (row3 16 33 34), (row3 16 33 35), (row3 16 33 36), (row3 16 33 37), (row3 16 33 38), (row3 16 33 39), (row3 16 33 40), (row3 16 33 41), (row3 16 33 42)]

def b089_15_labels : List Row := [(row3 273 462 273), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 273 462 273), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 275 276 276), (row3 235 462 235), (row3 462 462 462)]

theorem b089_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b089_15_rows b089_15_labels 136321817618016071348293200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b089_15_rows b089_15_labels]
    decide +kernel

theorem checked089 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_089 QuarticIntegerComputationalData.ids64_089 71481920008117803666789323160 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b089_00_rows ++ b089_01_rows) ++ (b089_02_rows ++ b089_03_rows)) ++ ((b089_04_rows ++ b089_05_rows) ++ (b089_06_rows ++ b089_07_rows))) ++ (((b089_08_rows ++ b089_09_rows) ++ (b089_10_rows ++ b089_11_rows)) ++ ((b089_12_rows ++ b089_13_rows) ++ (b089_14_rows ++ b089_15_rows))))
    ((((b089_00_labels ++ b089_01_labels) ++ (b089_02_labels ++ b089_03_labels)) ++ ((b089_04_labels ++ b089_05_labels) ++ (b089_06_labels ++ b089_07_labels))) ++ (((b089_08_labels ++ b089_09_labels) ++ (b089_10_labels ++ b089_11_labels)) ++ ((b089_12_labels ++ b089_13_labels) ++ (b089_14_labels ++ b089_15_labels)))) 71481920008117803666789323160
  exact ((((b089_00_checked.append (c := 6635200913113869622322195220) b089_01_checked (by decide +kernel)).append (c := 6703027805264507353187112420) (b089_02_checked.append (c := 67826892150637730864917200) b089_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6747239003303704828236627780) ((b089_04_checked.append (c := 929472266323542072096000) b089_05_checked (by decide +kernel)).append (c := 44211198039197475049515360) (b089_06_checked.append (c := 43281725772873932977419360) b089_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 71481920008117803666789323160) (((b089_08_checked.append (c := 8917194532131370900687327200) b089_09_checked (by decide +kernel)).append (c := 22967447204286951177296363220) (b089_10_checked.append (c := 14050252672155580276609036020) b089_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 64734681004814098838552695380) ((b089_12_checked.append (c := 27511876642755581913704010960) b089_13_checked (by decide +kernel)).append (c := 41767233800527147661256332160) (b089_14_checked.append (c := 14255357157771565747552321200) b089_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b090_00_rows : List Row := [(row3 16 33 43), (row3 16 33 44), (row3 16 33 45), (row3 16 33 46), (row3 16 33 47), (row3 16 33 48), (row3 16 33 49), (row3 16 33 50), (row3 16 33 51), (row3 16 33 52), (row3 16 33 53), (row3 16 33 54), (row3 16 33 55), (row3 16 33 56), (row3 16 33 57), (row3 16 33 58)]

def b090_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 277 277), (row3 233 462 233), (row3 462 462 462)]

theorem b090_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_00_rows b090_00_labels 92717389869688694083079400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_00_rows b090_00_labels]
    decide +kernel

def b090_01_rows : List Row := [(row3 16 33 59), (row3 16 33 60), (row3 16 33 61), (row3 16 33 62), (row3 16 33 63), (row3 16 34 35), (row3 16 34 36), (row3 16 34 37), (row3 16 34 38), (row3 16 34 39), (row3 16 34 40), (row3 16 34 41), (row3 16 34 42), (row3 16 34 43), (row3 16 34 44), (row3 16 34 45)]

def b090_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 235 235 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_01_rows b090_01_labels 1618009166314337460552000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_01_rows b090_01_labels]
    decide +kernel

def b090_02_rows : List Row := [(row3 16 34 46), (row3 16 34 47), (row3 16 34 48), (row3 16 34 49), (row3 16 34 50), (row3 16 34 51), (row3 16 34 52), (row3 16 34 53), (row3 16 34 54), (row3 16 34 55), (row3 16 34 56), (row3 16 34 57), (row3 16 34 58), (row3 16 34 59), (row3 16 34 60), (row3 16 34 61)]

def b090_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_02_rows b090_02_labels 833833822677406034148000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_02_rows b090_02_labels]
    decide +kernel

def b090_03_rows : List Row := [(row3 16 34 62), (row3 16 34 63), (row3 16 35 36), (row3 16 35 37), (row3 16 35 38), (row3 16 35 39), (row3 16 35 40), (row3 16 35 41), (row3 16 35 42), (row3 16 35 43), (row3 16 35 44), (row3 16 35 45), (row3 16 35 46), (row3 16 35 47), (row3 16 35 48), (row3 16 35 49)]

def b090_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_03_rows b090_03_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_03_rows b090_03_labels]
    decide +kernel

def b090_04_rows : List Row := [(row3 16 35 50), (row3 16 35 51), (row3 16 35 52), (row3 16 35 53), (row3 16 35 54), (row3 16 35 55), (row3 16 35 56), (row3 16 35 57), (row3 16 35 58), (row3 16 35 59), (row3 16 35 60), (row3 16 35 61), (row3 16 35 62), (row3 16 35 63), (row3 16 36 37), (row3 16 36 38)]

def b090_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_04_rows b090_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_04_rows b090_04_labels]
    decide +kernel

def b090_05_rows : List Row := [(row3 16 36 39), (row3 16 36 40), (row3 16 36 41), (row3 16 36 42), (row3 16 36 43), (row3 16 36 44), (row3 16 36 45), (row3 16 36 46), (row3 16 36 47), (row3 16 36 48), (row3 16 36 49), (row3 16 36 50), (row3 16 36 51), (row3 16 36 52), (row3 16 36 53), (row3 16 36 54)]

def b090_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_05_rows b090_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_05_rows b090_05_labels]
    decide +kernel

def b090_06_rows : List Row := [(row3 16 36 55), (row3 16 36 56), (row3 16 36 57), (row3 16 36 58), (row3 16 36 59), (row3 16 36 60), (row3 16 36 61), (row3 16 36 62), (row3 16 36 63), (row3 16 37 38), (row3 16 37 39), (row3 16 37 40), (row3 16 37 41), (row3 16 37 42), (row3 16 37 43), (row3 16 37 44)]

def b090_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_06_rows b090_06_labels 3625367732518643295000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_06_rows b090_06_labels]
    decide +kernel

def b090_07_rows : List Row := [(row3 16 37 45), (row3 16 37 46), (row3 16 37 47), (row3 16 37 48), (row3 16 37 49), (row3 16 37 50), (row3 16 37 51), (row3 16 37 52), (row3 16 37 53), (row3 16 37 54), (row3 16 37 55), (row3 16 37 56), (row3 16 37 57), (row3 16 37 58), (row3 16 37 59), (row3 16 37 60)]

def b090_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_07_rows b090_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_07_rows b090_07_labels]
    decide +kernel

def b090_08_rows : List Row := [(row3 16 37 61), (row3 16 37 62), (row3 16 37 63), (row3 16 38 39), (row3 16 38 40), (row3 16 38 41), (row3 16 38 42), (row3 16 38 43), (row3 16 38 44), (row3 16 38 45), (row3 16 38 46), (row3 16 38 47), (row3 16 38 48), (row3 16 38 49), (row3 16 38 50), (row3 16 38 51)]

def b090_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 235 235 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_08_rows b090_08_labels 21030857277273523126188000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_08_rows b090_08_labels]
    decide +kernel

def b090_09_rows : List Row := [(row3 16 38 52), (row3 16 38 53), (row3 16 38 54), (row3 16 38 55), (row3 16 38 56), (row3 16 38 57), (row3 16 38 58), (row3 16 38 59), (row3 16 38 60), (row3 16 38 61), (row3 16 38 62), (row3 16 38 63), (row3 16 39 40), (row3 16 39 41), (row3 16 39 42), (row3 16 39 43)]

def b090_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 275 276 276), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b090_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_09_rows b090_09_labels 31354972172067329694271200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_09_rows b090_09_labels]
    decide +kernel

def b090_10_rows : List Row := [(row3 16 39 44), (row3 16 39 45), (row3 16 39 46), (row3 16 39 47), (row3 16 39 48), (row3 16 39 49), (row3 16 39 50), (row3 16 39 51), (row3 16 39 52), (row3 16 39 53), (row3 16 39 54), (row3 16 39 55), (row3 16 39 56), (row3 16 39 57), (row3 16 39 58), (row3 16 39 59)]

def b090_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 277 277), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b090_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_10_rows b090_10_labels 105512710879319890351367400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_10_rows b090_10_labels]
    decide +kernel

def b090_11_rows : List Row := [(row3 16 39 60), (row3 16 39 61), (row3 16 39 62), (row3 16 39 63), (row3 16 40 41), (row3 16 40 42), (row3 16 40 43), (row3 16 40 44), (row3 16 40 45), (row3 16 40 46), (row3 16 40 47), (row3 16 40 48), (row3 16 40 49), (row3 16 40 50), (row3 16 40 51), (row3 16 40 52)]

def b090_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 233 462 233), (row3 207 200 200), (row3 255 256 256), (row3 239 239 239), (row3 462 240 240), (row3 239 239 239), (row3 255 256 256), (row3 207 200 200), (row3 335 96 205), (row3 275 276 276), (row3 235 235 237), (row3 462 241 241), (row3 462 462 462)]

theorem b090_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_11_rows b090_11_labels 16542341513293461475662881460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_11_rows b090_11_labels]
    decide +kernel

def b090_12_rows : List Row := [(row3 16 40 53), (row3 16 40 54), (row3 16 40 55), (row3 16 40 56), (row3 16 40 57), (row3 16 40 58), (row3 16 40 59), (row3 16 40 60), (row3 16 40 61), (row3 16 40 62), (row3 16 40 63), (row3 16 41 42), (row3 16 41 43), (row3 16 41 44), (row3 16 41 45), (row3 16 41 46)]

def b090_12_labels : List Row := [(row3 462 241 241), (row3 235 235 237), (row3 275 276 276), (row3 326 425 75), (row3 195 188 194), (row3 265 267 267), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 265 267 267), (row3 195 188 194), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_12_rows b090_12_labels 72519526803812978122474660020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_12_rows b090_12_labels]
    decide +kernel

def b090_13_rows : List Row := [(row3 16 41 47), (row3 16 41 48), (row3 16 41 49), (row3 16 41 50), (row3 16 41 51), (row3 16 41 52), (row3 16 41 53), (row3 16 41 54), (row3 16 41 55), (row3 16 41 56), (row3 16 41 57), (row3 16 41 58), (row3 16 41 59), (row3 16 41 60), (row3 16 41 61), (row3 16 41 62)]

def b090_13_labels : List Row := [(row3 462 462 462), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 325 87 371), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b090_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_13_rows b090_13_labels 9733569548429285847602843520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_13_rows b090_13_labels]
    decide +kernel

def b090_14_rows : List Row := [(row3 16 41 63), (row3 16 42 43), (row3 16 42 44), (row3 16 42 45), (row3 16 42 46), (row3 16 42 47), (row3 16 42 48), (row3 16 42 49), (row3 16 42 50), (row3 16 42 51), (row3 16 42 52), (row3 16 42 53), (row3 16 42 54), (row3 16 42 55), (row3 16 42 56), (row3 16 42 57)]

def b090_14_labels : List Row := [(row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 232 462 232)]

theorem b090_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_14_rows b090_14_labels 37640557739657291651846100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_14_rows b090_14_labels]
    decide +kernel

def b090_15_rows : List Row := [(row3 16 42 58), (row3 16 42 59), (row3 16 42 60), (row3 16 42 61), (row3 16 42 62), (row3 16 42 63), (row3 16 43 44), (row3 16 43 45), (row3 16 43 46), (row3 16 43 47), (row3 16 43 48), (row3 16 43 49), (row3 16 43 50), (row3 16 43 51), (row3 16 43 52), (row3 16 43 53)]

def b090_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b090_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b090_15_rows b090_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b090_15_rows b090_15_labels]
    decide +kernel

theorem checked090 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_090 QuarticIntegerComputationalData.ids64_090 99086153447198188955428427100 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b090_00_rows ++ b090_01_rows) ++ (b090_02_rows ++ b090_03_rows)) ++ ((b090_04_rows ++ b090_05_rows) ++ (b090_06_rows ++ b090_07_rows))) ++ (((b090_08_rows ++ b090_09_rows) ++ (b090_10_rows ++ b090_11_rows)) ++ ((b090_12_rows ++ b090_13_rows) ++ (b090_14_rows ++ b090_15_rows))))
    ((((b090_00_labels ++ b090_01_labels) ++ (b090_02_labels ++ b090_03_labels)) ++ ((b090_04_labels ++ b090_05_labels) ++ (b090_06_labels ++ b090_07_labels))) ++ (((b090_08_labels ++ b090_09_labels) ++ (b090_10_labels ++ b090_11_labels)) ++ ((b090_12_labels ++ b090_13_labels) ++ (b090_14_labels ++ b090_15_labels)))) 99086153447198188955428427100
  exact ((((b090_00_checked.append (c := 94335399036003031543631400) b090_01_checked (by decide +kernel)).append (c := 95172858226412956221074400) (b090_02_checked.append (c := 837459190409924677443000) b090_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 95176483594145474864369400) ((b090_04_checked.append (c := 0) b090_05_checked (by decide +kernel)).append (c := 3625367732518643295000) (b090_06_checked.append (c := 3625367732518643295000) b090_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 99086153447198188955428427100) (((b090_08_checked.append (c := 52385829449340852820459200) b090_09_checked (by decide +kernel)).append (c := 16700240053622122218834708060) (b090_10_checked.append (c := 16647854224172781366014248860) b090_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 98990976963604043480564057700) ((b090_12_checked.append (c := 82253096352242263970077503540) b090_13_checked (by decide +kernel)).append (c := 82290736909981921261729349640) (b090_14_checked.append (c := 37640557739657291651846100) b090_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b091_00_rows : List Row := [(row3 16 43 54), (row3 16 43 55), (row3 16 43 56), (row3 16 43 57), (row3 16 43 58), (row3 16 43 59), (row3 16 43 60), (row3 16 43 61), (row3 16 43 62), (row3 16 43 63), (row3 16 44 45), (row3 16 44 46), (row3 16 44 47), (row3 16 44 48), (row3 16 44 49), (row3 16 44 50)]

def b091_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b091_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_00_rows b091_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_00_rows b091_00_labels]
    decide +kernel

def b091_01_rows : List Row := [(row3 16 44 51), (row3 16 44 52), (row3 16 44 53), (row3 16 44 54), (row3 16 44 55), (row3 16 44 56), (row3 16 44 57), (row3 16 44 58), (row3 16 44 59), (row3 16 44 60), (row3 16 44 61), (row3 16 44 62), (row3 16 44 63), (row3 16 45 46), (row3 16 45 47), (row3 16 45 48)]

def b091_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b091_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_01_rows b091_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_01_rows b091_01_labels]
    decide +kernel

def b091_02_rows : List Row := [(row3 16 45 49), (row3 16 45 50), (row3 16 45 51), (row3 16 45 52), (row3 16 45 53), (row3 16 45 54), (row3 16 45 55), (row3 16 45 56), (row3 16 45 57), (row3 16 45 58), (row3 16 45 59), (row3 16 45 60), (row3 16 45 61), (row3 16 45 62), (row3 16 45 63), (row3 16 46 47)]

def b091_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b091_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_02_rows b091_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_02_rows b091_02_labels]
    decide +kernel

def b091_03_rows : List Row := [(row3 16 46 48), (row3 16 46 49), (row3 16 46 50), (row3 16 46 51), (row3 16 46 52), (row3 16 46 53), (row3 16 46 54), (row3 16 46 55), (row3 16 46 56), (row3 16 46 57), (row3 16 46 58), (row3 16 46 59), (row3 16 46 60), (row3 16 46 61), (row3 16 46 62), (row3 16 46 63)]

def b091_03_labels : List Row := [(row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232)]

theorem b091_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_03_rows b091_03_labels 31812090821397601904524500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_03_rows b091_03_labels]
    decide +kernel

def b091_04_rows : List Row := [(row3 16 47 48), (row3 16 47 49), (row3 16 47 50), (row3 16 47 51), (row3 16 47 52), (row3 16 47 53), (row3 16 47 54), (row3 16 47 55), (row3 16 47 56), (row3 16 47 57), (row3 16 47 58), (row3 16 47 59), (row3 16 47 60), (row3 16 47 61), (row3 16 47 62), (row3 16 47 63)]

def b091_04_labels : List Row := [(row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 325 87 371), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 288 462 288)]

theorem b091_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_04_rows b091_04_labels 9739398015347545537350165120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_04_rows b091_04_labels]
    decide +kernel

def b091_05_rows : List Row := [(row3 16 48 49), (row3 16 48 50), (row3 16 48 51), (row3 16 48 52), (row3 16 48 53), (row3 16 48 54), (row3 16 48 55), (row3 16 48 56), (row3 16 48 57), (row3 16 48 58), (row3 16 48 59), (row3 16 48 60), (row3 16 48 61), (row3 16 48 62), (row3 16 48 63), (row3 16 49 50)]

def b091_05_labels : List Row := [(row3 174 174 178), (row3 273 273 462), (row3 239 239 462), (row3 462 462 462), (row3 239 239 462), (row3 273 273 462), (row3 174 174 178), (row3 80 30 446), (row3 349 346 350), (row3 183 183 178), (row3 261 261 462), (row3 462 462 462), (row3 261 261 462), (row3 183 183 178), (row3 349 346 350), (row3 234 234 462)]

theorem b091_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_05_rows b091_05_labels 3785170182327539554658690871120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_05_rows b091_05_labels]
    decide +kernel

def b091_06_rows : List Row := [(row3 16 49 51), (row3 16 49 52), (row3 16 49 53), (row3 16 49 54), (row3 16 49 55), (row3 16 49 56), (row3 16 49 57), (row3 16 49 58), (row3 16 49 59), (row3 16 49 60), (row3 16 49 61), (row3 16 49 62), (row3 16 49 63), (row3 16 50 51), (row3 16 50 52), (row3 16 50 53)]

def b091_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 372 430 58), (row3 127 137 126), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 146 137 143), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b091_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_06_rows b091_06_labels 147561467906106418669255503180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_06_rows b091_06_labels]
    decide +kernel

def b091_07_rows : List Row := [(row3 16 50 54), (row3 16 50 55), (row3 16 50 56), (row3 16 50 57), (row3 16 50 58), (row3 16 50 59), (row3 16 50 60), (row3 16 50 61), (row3 16 50 62), (row3 16 50 63), (row3 16 51 52), (row3 16 51 53), (row3 16 51 54), (row3 16 51 55), (row3 16 51 56), (row3 16 51 57)]

def b091_07_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 211 88 370), (row3 300 462 300), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 232 462 232)]

theorem b091_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_07_rows b091_07_labels 9661194797404572862436616360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_07_rows b091_07_labels]
    decide +kernel

def b091_08_rows : List Row := [(row3 16 51 58), (row3 16 51 59), (row3 16 51 60), (row3 16 51 61), (row3 16 51 62), (row3 16 51 63), (row3 16 52 53), (row3 16 52 54), (row3 16 52 55), (row3 16 52 56), (row3 16 52 57), (row3 16 52 58), (row3 16 52 59), (row3 16 52 60), (row3 16 52 61), (row3 16 52 62)]

def b091_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b091_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_08_rows b091_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_08_rows b091_08_labels]
    decide +kernel

def b091_09_rows : List Row := [(row3 16 52 63), (row3 16 53 54), (row3 16 53 55), (row3 16 53 56), (row3 16 53 57), (row3 16 53 58), (row3 16 53 59), (row3 16 53 60), (row3 16 53 61), (row3 16 53 62), (row3 16 53 63), (row3 16 54 55), (row3 16 54 56), (row3 16 54 57), (row3 16 54 58), (row3 16 54 59)]

def b091_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 234 462 234), (row3 211 88 370), (row3 278 462 278), (row3 234 462 234), (row3 462 462 462)]

theorem b091_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_09_rows b091_09_labels 9587689236449824177940033400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_09_rows b091_09_labels]
    decide +kernel

def b091_10_rows : List Row := [(row3 16 54 60), (row3 16 54 61), (row3 16 54 62), (row3 16 54 63), (row3 16 55 56), (row3 16 55 57), (row3 16 55 58), (row3 16 55 59), (row3 16 55 60), (row3 16 55 61), (row3 16 55 62), (row3 16 55 63), (row3 16 56 57), (row3 16 56 58), (row3 16 56 59), (row3 16 56 60)]

def b091_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 300 462 300), (row3 372 430 58), (row3 146 137 143), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 127 137 126), (row3 56 445 29), (row3 385 77 426), (row3 202 334 97), (row3 462 257 257)]

theorem b091_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_10_rows b091_10_labels 4372519299854253693820534407780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_10_rows b091_10_labels]
    decide +kernel

def b091_11_rows : List Row := [(row3 16 56 61), (row3 16 56 62), (row3 16 56 63), (row3 16 57 58), (row3 16 57 59), (row3 16 57 60), (row3 16 57 61), (row3 16 57 62), (row3 16 57 63), (row3 16 58 59), (row3 16 58 60), (row3 16 58 61), (row3 16 58 62), (row3 16 58 63), (row3 16 59 60), (row3 16 59 61)]

def b091_11_labels : List Row := [(row3 202 334 97), (row3 385 77 426), (row3 56 445 29), (row3 127 126 137), (row3 288 288 462), (row3 236 236 462), (row3 273 273 462), (row3 148 145 137), (row3 379 380 380), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 148 137 145), (row3 462 462 462), (row3 462 462 462)]

theorem b091_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_11_rows b091_11_labels 4241317845919132888518308226540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_11_rows b091_11_labels]
    decide +kernel

def b091_12_rows : List Row := [(row3 16 59 62), (row3 16 59 63), (row3 16 60 61), (row3 16 60 62), (row3 16 60 63), (row3 16 61 62), (row3 16 61 63), (row3 16 62 63), (row3 17 18 19), (row3 17 18 20), (row3 17 18 21), (row3 17 18 22), (row3 17 18 23), (row3 17 18 24), (row3 17 18 25), (row3 17 18 26)]

def b091_12_labels : List Row := [(row3 235 462 235), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 235 462 235), (row3 288 462 288), (row3 127 137 126), (row3 181 435 42), (row3 211 88 370), (row3 218 10 170), (row3 154 154 180), (row3 393 386 363), (row3 415 407 395), (row3 31 36 35), (row3 389 436 45)]

theorem b091_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_12_rows b091_12_labels 1596983738891147549380123256340 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_12_rows b091_12_labels]
    decide +kernel

def b091_13_rows : List Row := [(row3 17 18 27), (row3 17 18 28), (row3 17 18 29), (row3 17 18 30), (row3 17 18 31), (row3 17 18 32), (row3 17 18 33), (row3 17 18 34), (row3 17 18 35), (row3 17 18 36), (row3 17 18 37), (row3 17 18 38), (row3 17 18 39), (row3 17 18 40), (row3 17 18 41), (row3 17 18 42)]

def b091_13_labels : List Row := [(row3 135 83 398), (row3 214 11 117), (row3 462 462 462), (row3 284 462 284), (row3 105 105 131), (row3 105 105 131), (row3 391 387 361), (row3 114 86 368), (row3 215 11 118), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 285 462 285), (row3 154 154 180), (row3 258 10 172)]

theorem b091_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_13_rows b091_13_labels 54062432923270009206560880150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_13_rows b091_13_labels]
    decide +kernel

def b091_14_rows : List Row := [(row3 17 18 43), (row3 17 18 44), (row3 17 18 45), (row3 17 18 46), (row3 17 18 47), (row3 17 18 48), (row3 17 18 49), (row3 17 18 50), (row3 17 18 51), (row3 17 18 52), (row3 17 18 53), (row3 17 18 54), (row3 17 18 55), (row3 17 18 56), (row3 17 18 57), (row3 17 18 58)]

def b091_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 272 462 272), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 307 462 307), (row3 150 152 177), (row3 260 10 173)]

theorem b091_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_14_rows b091_14_labels 18478917761211856588310167500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_14_rows b091_14_labels]
    decide +kernel

def b091_15_rows : List Row := [(row3 17 18 59), (row3 17 18 60), (row3 17 18 61), (row3 17 18 62), (row3 17 18 63), (row3 17 19 20), (row3 17 19 21), (row3 17 19 22), (row3 17 19 23), (row3 17 19 24), (row3 17 19 25), (row3 17 19 26), (row3 17 19 27), (row3 17 19 28), (row3 17 19 29), (row3 17 19 30)]

def b091_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 266 266 265), (row3 237 462 237), (row3 267 267 265), (row3 178 183 183), (row3 137 145 148), (row3 390 360 387), (row3 137 146 149), (row3 291 291 289), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235)]

theorem b091_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b091_15_rows b091_15_labels 15555411874131521749696844190 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b091_15_rows b091_15_labels]
    decide +kernel

theorem checked091 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_091 QuarticIntegerComputationalData.ids64_091 14260669391596816832771111496180 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b091_00_rows ++ b091_01_rows) ++ (b091_02_rows ++ b091_03_rows)) ++ ((b091_04_rows ++ b091_05_rows) ++ (b091_06_rows ++ b091_07_rows))) ++ (((b091_08_rows ++ b091_09_rows) ++ (b091_10_rows ++ b091_11_rows)) ++ ((b091_12_rows ++ b091_13_rows) ++ (b091_14_rows ++ b091_15_rows))))
    ((((b091_00_labels ++ b091_01_labels) ++ (b091_02_labels ++ b091_03_labels)) ++ ((b091_04_labels ++ b091_05_labels) ++ (b091_06_labels ++ b091_07_labels))) ++ (((b091_08_labels ++ b091_09_labels) ++ (b091_10_labels ++ b091_11_labels)) ++ ((b091_12_labels ++ b091_13_labels) ++ (b091_14_labels ++ b091_15_labels)))) 14260669391596816832771111496180
  exact ((((b091_00_checked.append (c := 0) b091_01_checked (by decide +kernel)).append (c := 31812090821397601904524500) (b091_02_checked.append (c := 31812090821397601904524500) b091_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3952164055137219489329637680280) ((b091_04_checked.append (c := 3794909580342887100196041036240) b091_05_checked (by decide +kernel)).append (c := 3952132243046398091727733155780) (b091_06_checked.append (c := 157222662703510991531692119540) b091_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 14260669391596816832771111496180) (((b091_08_checked.append (c := 9587689236449824177940033400) b091_09_checked (by decide +kernel)).append (c := 8623424835009836406516782667720) (b091_10_checked.append (c := 8613837145773386582338842634320) b091_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 10308505336459597343441473815900) ((b091_12_checked.append (c := 1651046171814417558586684136490) b091_13_checked (by decide +kernel)).append (c := 1685080501449760936924691148180) (b091_14_checked.append (c := 34034329635343378338007011690) b091_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b092_00_rows : List Row := [(row3 17 19 31), (row3 17 19 32), (row3 17 19 33), (row3 17 19 34), (row3 17 19 35), (row3 17 19 36), (row3 17 19 37), (row3 17 19 38), (row3 17 19 39), (row3 17 19 40), (row3 17 19 41), (row3 17 19 42), (row3 17 19 43), (row3 17 19 44), (row3 17 19 45), (row3 17 19 46)]

def b092_00_labels : List Row := [(row3 291 291 289), (row3 291 291 289), (row3 178 184 184), (row3 291 291 289), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b092_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_00_rows b092_00_labels 121997656845801501558923520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_00_rows b092_00_labels]
    decide +kernel

def b092_01_rows : List Row := [(row3 17 19 47), (row3 17 19 48), (row3 17 19 49), (row3 17 19 50), (row3 17 19 51), (row3 17 19 52), (row3 17 19 53), (row3 17 19 54), (row3 17 19 55), (row3 17 19 56), (row3 17 19 57), (row3 17 19 58), (row3 17 19 59), (row3 17 19 60), (row3 17 19 61), (row3 17 19 62)]

def b092_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b092_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_01_rows b092_01_labels 32250760181739016703421120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_01_rows b092_01_labels]
    decide +kernel

def b092_02_rows : List Row := [(row3 17 19 63), (row3 17 20 21), (row3 17 20 22), (row3 17 20 23), (row3 17 20 24), (row3 17 20 25), (row3 17 20 26), (row3 17 20 27), (row3 17 20 28), (row3 17 20 29), (row3 17 20 30), (row3 17 20 31), (row3 17 20 32), (row3 17 20 33), (row3 17 20 34), (row3 17 20 35)]

def b092_02_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 235 235 237), (row3 281 278 281), (row3 279 278 279), (row3 154 180 154), (row3 279 278 279), (row3 234 234 234), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 234 234 234), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234), (row3 244 462 244)]

theorem b092_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_02_rows b092_02_labels 831048225730124627642144400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_02_rows b092_02_labels]
    decide +kernel

def b092_03_rows : List Row := [(row3 17 20 36), (row3 17 20 37), (row3 17 20 38), (row3 17 20 39), (row3 17 20 40), (row3 17 20 41), (row3 17 20 42), (row3 17 20 43), (row3 17 20 44), (row3 17 20 45), (row3 17 20 46), (row3 17 20 47), (row3 17 20 48), (row3 17 20 49), (row3 17 20 50), (row3 17 20 51)]

def b092_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462)]

theorem b092_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_03_rows b092_03_labels 129748484659231319850000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_03_rows b092_03_labels]
    decide +kernel

def b092_04_rows : List Row := [(row3 17 20 52), (row3 17 20 53), (row3 17 20 54), (row3 17 20 55), (row3 17 20 56), (row3 17 20 57), (row3 17 20 58), (row3 17 20 59), (row3 17 20 60), (row3 17 20 61), (row3 17 20 62), (row3 17 20 63), (row3 17 21 22), (row3 17 21 23), (row3 17 21 24), (row3 17 21 25)]

def b092_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 270 270 462), (row3 183 183 178), (row3 235 233 236), (row3 269 269 462)]

theorem b092_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_04_rows b092_04_labels 189023785487807923343730060 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_04_rows b092_04_labels]
    decide +kernel

def b092_05_rows : List Row := [(row3 17 21 26), (row3 17 21 27), (row3 17 21 28), (row3 17 21 29), (row3 17 21 30), (row3 17 21 31), (row3 17 21 32), (row3 17 21 33), (row3 17 21 34), (row3 17 21 35), (row3 17 21 36), (row3 17 21 37), (row3 17 21 38), (row3 17 21 39), (row3 17 21 40), (row3 17 21 41)]

def b092_05_labels : List Row := [(row3 235 235 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 244 244 462), (row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462)]

theorem b092_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_05_rows b092_05_labels 631830040927141622017500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_05_rows b092_05_labels]
    decide +kernel

def b092_06_rows : List Row := [(row3 17 21 42), (row3 17 21 43), (row3 17 21 44), (row3 17 21 45), (row3 17 21 46), (row3 17 21 47), (row3 17 21 48), (row3 17 21 49), (row3 17 21 50), (row3 17 21 51), (row3 17 21 52), (row3 17 21 53), (row3 17 21 54), (row3 17 21 55), (row3 17 21 56), (row3 17 21 57)]

def b092_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462)]

theorem b092_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_06_rows b092_06_labels 8051053906808277322500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_06_rows b092_06_labels]
    decide +kernel

def b092_07_rows : List Row := [(row3 17 21 58), (row3 17 21 59), (row3 17 21 60), (row3 17 21 61), (row3 17 21 62), (row3 17 21 63), (row3 17 22 23), (row3 17 22 24), (row3 17 22 25), (row3 17 22 26), (row3 17 22 27), (row3 17 22 28), (row3 17 22 29), (row3 17 22 30), (row3 17 22 31), (row3 17 22 32)]

def b092_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 363 386 393), (row3 298 295 298), (row3 154 180 154), (row3 279 278 279), (row3 234 234 234), (row3 245 462 245), (row3 235 462 235), (row3 271 462 271), (row3 224 226 229), (row3 234 234 234)]

theorem b092_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_07_rows b092_07_labels 24757858374871656317029691850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_07_rows b092_07_labels]
    decide +kernel

def b092_08_rows : List Row := [(row3 17 22 33), (row3 17 22 34), (row3 17 22 35), (row3 17 22 36), (row3 17 22 37), (row3 17 22 38), (row3 17 22 39), (row3 17 22 40), (row3 17 22 41), (row3 17 22 42), (row3 17 22 43), (row3 17 22 44), (row3 17 22 45), (row3 17 22 46), (row3 17 22 47), (row3 17 22 48)]

def b092_08_labels : List Row := [(row3 266 265 266), (row3 234 234 234), (row3 244 462 244), (row3 462 462 462), (row3 244 462 244), (row3 237 462 237), (row3 246 462 246), (row3 245 462 245), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 234 462 234)]

theorem b092_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_08_rows b092_08_labels 4370635265687701319480400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_08_rows b092_08_labels]
    decide +kernel

def b092_09_rows : List Row := [(row3 17 22 49), (row3 17 22 50), (row3 17 22 51), (row3 17 22 52), (row3 17 22 53), (row3 17 22 54), (row3 17 22 55), (row3 17 22 56), (row3 17 22 57), (row3 17 22 58), (row3 17 22 59), (row3 17 22 60), (row3 17 22 61), (row3 17 22 62), (row3 17 22 63), (row3 17 23 24)]

def b092_09_labels : List Row := [(row3 249 462 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 294 462 294), (row3 226 237 226), (row3 250 462 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 462 249), (row3 228 462 228), (row3 106 106 107)]

theorem b092_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_09_rows b092_09_labels 1501683664146249474407064420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_09_rows b092_09_labels]
    decide +kernel

def b092_10_rows : List Row := [(row3 17 23 25), (row3 17 23 26), (row3 17 23 27), (row3 17 23 28), (row3 17 23 29), (row3 17 23 30), (row3 17 23 31), (row3 17 23 32), (row3 17 23 33), (row3 17 23 34), (row3 17 23 35), (row3 17 23 36), (row3 17 23 37), (row3 17 23 38), (row3 17 23 39), (row3 17 23 40)]

def b092_10_labels : List Row := [(row3 392 362 388), (row3 137 144 147), (row3 291 291 289), (row3 235 235 232), (row3 291 291 289), (row3 144 137 147), (row3 362 392 388), (row3 314 314 306), (row3 178 182 182), (row3 291 291 289), (row3 234 462 234), (row3 462 462 462), (row3 462 234 234), (row3 291 291 289), (row3 182 178 182), (row3 229 229 226)]

theorem b092_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_10_rows b092_10_labels 47351967827941643344810037460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_10_rows b092_10_labels]
    decide +kernel

def b092_11_rows : List Row := [(row3 17 23 41), (row3 17 23 42), (row3 17 23 43), (row3 17 23 44), (row3 17 23 45), (row3 17 23 46), (row3 17 23 47), (row3 17 23 48), (row3 17 23 49), (row3 17 23 50), (row3 17 23 51), (row3 17 23 52), (row3 17 23 53), (row3 17 23 54), (row3 17 23 55), (row3 17 23 56)]

def b092_11_labels : List Row := [(row3 268 268 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 268 268 265), (row3 291 291 289), (row3 223 224 223), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 224 223 223), (row3 104 104 130)]

theorem b092_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_11_rows b092_11_labels 11020672489156683280249591080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_11_rows b092_11_labels]
    decide +kernel

def b092_12_rows : List Row := [(row3 17 23 57), (row3 17 23 58), (row3 17 23 59), (row3 17 23 60), (row3 17 23 61), (row3 17 23 62), (row3 17 23 63), (row3 17 24 25), (row3 17 24 26), (row3 17 24 27), (row3 17 24 28), (row3 17 24 29), (row3 17 24 30), (row3 17 24 31), (row3 17 24 32), (row3 17 24 33)]

def b092_12_labels : List Row := [(row3 318 318 315), (row3 222 224 222), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 222 222), (row3 318 318 315), (row3 74 44 439), (row3 109 110 111), (row3 317 317 308), (row3 232 238 230), (row3 262 262 261), (row3 197 190 196), (row3 354 376 366), (row3 353 375 366), (row3 125 126 128)]

theorem b092_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_12_rows b092_12_labels 560294247513839421564604927140 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_12_rows b092_12_labels]
    decide +kernel

def b092_13_rows : List Row := [(row3 17 24 34), (row3 17 24 35), (row3 17 24 36), (row3 17 24 37), (row3 17 24 38), (row3 17 24 39), (row3 17 24 40), (row3 17 24 41), (row3 17 24 42), (row3 17 24 43), (row3 17 24 44), (row3 17 24 45), (row3 17 24 46), (row3 17 24 47), (row3 17 24 48), (row3 17 24 49)]

def b092_13_labels : List Row := [(row3 320 320 319), (row3 228 236 225), (row3 462 462 462), (row3 462 236 236), (row3 279 279 278), (row3 175 161 175), (row3 195 188 194), (row3 297 297 295), (row3 232 235 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 280 280 278), (row3 276 276 275), (row3 229 231 227)]

theorem b092_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_13_rows b092_13_labels 465177317924245009584890280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_13_rows b092_13_labels]
    decide +kernel

def b092_14_rows : List Row := [(row3 17 24 50), (row3 17 24 51), (row3 17 24 52), (row3 17 24 53), (row3 17 24 54), (row3 17 24 55), (row3 17 24 56), (row3 17 24 57), (row3 17 24 58), (row3 17 24 59), (row3 17 24 60), (row3 17 24 61), (row3 17 24 62), (row3 17 24 63), (row3 17 25 26), (row3 17 25 27)]

def b092_14_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 231 231), (row3 151 153 179), (row3 296 296 295), (row3 226 234 226), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 279 279 278), (row3 383 436 43), (row3 122 86 369)]

theorem b092_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_14_rows b092_14_labels 389320916143195160994294905940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_14_rows b092_14_labels]
    decide +kernel

def b092_15_rows : List Row := [(row3 17 25 28), (row3 17 25 29), (row3 17 25 30), (row3 17 25 31), (row3 17 25 32), (row3 17 25 33), (row3 17 25 34), (row3 17 25 35), (row3 17 25 36), (row3 17 25 37), (row3 17 25 38), (row3 17 25 39), (row3 17 25 40), (row3 17 25 41), (row3 17 25 42), (row3 17 25 43)]

def b092_15_labels : List Row := [(row3 254 10 171), (row3 462 462 462), (row3 254 10 171), (row3 121 85 369), (row3 156 82 399), (row3 95 435 41), (row3 157 83 399), (row3 214 11 117), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 214 11 117), (row3 213 11 116), (row3 325 87 371), (row3 212 11 115), (row3 462 462 462)]

theorem b092_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b092_15_rows b092_15_labels 421342943986263690031275874950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b092_15_rows b092_15_labels]
    decide +kernel

theorem checked092 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_092 QuarticIntegerComputationalData.ids64_092 1457234928010429403968043872620 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b092_00_rows ++ b092_01_rows) ++ (b092_02_rows ++ b092_03_rows)) ++ ((b092_04_rows ++ b092_05_rows) ++ (b092_06_rows ++ b092_07_rows))) ++ (((b092_08_rows ++ b092_09_rows) ++ (b092_10_rows ++ b092_11_rows)) ++ ((b092_12_rows ++ b092_13_rows) ++ (b092_14_rows ++ b092_15_rows))))
    ((((b092_00_labels ++ b092_01_labels) ++ (b092_02_labels ++ b092_03_labels)) ++ ((b092_04_labels ++ b092_05_labels) ++ (b092_06_labels ++ b092_07_labels))) ++ (((b092_08_labels ++ b092_09_labels) ++ (b092_10_labels ++ b092_11_labels)) ++ ((b092_12_labels ++ b092_13_labels) ++ (b092_14_labels ++ b092_15_labels)))) 1457234928010429403968043872620
  exact ((((b092_00_checked.append (c := 154248417027540518262344640) b092_01_checked (by decide +kernel)).append (c := 985426391242324377224339040) (b092_02_checked.append (c := 831177974214783858961994400) b092_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 25932948432696622567497100950) ((b092_04_checked.append (c := 189655615528735064965747560) b092_05_checked (by decide +kernel)).append (c := 24947522041454298190272761910) (b092_06_checked.append (c := 24757866425925563125307014350) b092_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1457234928010429403968043872620) (((b092_08_checked.append (c := 1506054299411937175726544820) b092_09_checked (by decide +kernel)).append (c := 59878694616510263800786173360) (b092_10_checked.append (c := 58372640317098326625059628540) b092_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1431301979577732781400546771670) ((b092_12_checked.append (c := 560759424831763666574189817420) b092_13_checked (by decide +kernel)).append (c := 1371423284961222517599760598310) (b092_14_checked.append (c := 810663860129458851025570780890) b092_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b093_00_rows : List Row := [(row3 17 25 44), (row3 17 25 45), (row3 17 25 46), (row3 17 25 47), (row3 17 25 48), (row3 17 25 49), (row3 17 25 50), (row3 17 25 51), (row3 17 25 52), (row3 17 25 53), (row3 17 25 54), (row3 17 25 55), (row3 17 25 56), (row3 17 25 57), (row3 17 25 58), (row3 17 25 59)]

def b093_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 217 10 169), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 303 462 303), (row3 151 153 179), (row3 286 462 286), (row3 462 462 462)]

theorem b093_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_00_rows b093_00_labels 16343797010135541937503660750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_00_rows b093_00_labels]
    decide +kernel

def b093_01_rows : List Row := [(row3 17 25 60), (row3 17 25 61), (row3 17 25 62), (row3 17 25 63), (row3 17 26 27), (row3 17 26 28), (row3 17 26 29), (row3 17 26 30), (row3 17 26 31), (row3 17 26 32), (row3 17 26 33), (row3 17 26 34), (row3 17 26 35), (row3 17 26 36), (row3 17 26 37), (row3 17 26 38)]

def b093_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 309 309 306), (row3 232 462 232), (row3 462 462 462), (row3 232 462 232), (row3 310 310 306), (row3 311 311 306), (row3 137 149 146), (row3 309 309 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_01_rows b093_01_labels 1244480837263959105240366060 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_01_rows b093_01_labels]
    decide +kernel

def b093_02_rows : List Row := [(row3 17 26 39), (row3 17 26 40), (row3 17 26 41), (row3 17 26 42), (row3 17 26 43), (row3 17 26 44), (row3 17 26 45), (row3 17 26 46), (row3 17 26 47), (row3 17 26 48), (row3 17 26 49), (row3 17 26 50), (row3 17 26 51), (row3 17 26 52), (row3 17 26 53), (row3 17 26 54)]

def b093_02_labels : List Row := [(row3 228 462 228), (row3 232 462 232), (row3 280 280 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_02_rows b093_02_labels 14562250816006404728940600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_02_rows b093_02_labels]
    decide +kernel

def b093_03_rows : List Row := [(row3 17 26 55), (row3 17 26 56), (row3 17 26 57), (row3 17 26 58), (row3 17 26 59), (row3 17 26 60), (row3 17 26 61), (row3 17 26 62), (row3 17 26 63), (row3 17 27 28), (row3 17 27 29), (row3 17 27 30), (row3 17 27 31), (row3 17 27 32), (row3 17 27 33), (row3 17 27 34)]

def b093_03_labels : List Row := [(row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 246 462 246), (row3 224 224 224), (row3 224 224 224), (row3 291 289 291), (row3 224 224 224)]

theorem b093_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_03_rows b093_03_labels 130746965990338122022342080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_03_rows b093_03_labels]
    decide +kernel

def b093_04_rows : List Row := [(row3 17 27 35), (row3 17 27 36), (row3 17 27 37), (row3 17 27 38), (row3 17 27 39), (row3 17 27 40), (row3 17 27 41), (row3 17 27 42), (row3 17 27 43), (row3 17 27 44), (row3 17 27 45), (row3 17 27 46), (row3 17 27 47), (row3 17 27 48), (row3 17 27 49), (row3 17 27 50)]

def b093_04_labels : List Row := [(row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462)]

theorem b093_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_04_rows b093_04_labels 1751513413503776543212500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_04_rows b093_04_labels]
    decide +kernel

def b093_05_rows : List Row := [(row3 17 27 51), (row3 17 27 52), (row3 17 27 53), (row3 17 27 54), (row3 17 27 55), (row3 17 27 56), (row3 17 27 57), (row3 17 27 58), (row3 17 27 59), (row3 17 27 60), (row3 17 27 61), (row3 17 27 62), (row3 17 27 63), (row3 17 28 29), (row3 17 28 30), (row3 17 28 31)]

def b093_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 247 462)]

theorem b093_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_05_rows b093_05_labels 2155411908573385717350000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_05_rows b093_05_labels]
    decide +kernel

def b093_06_rows : List Row := [(row3 17 28 32), (row3 17 28 33), (row3 17 28 34), (row3 17 28 35), (row3 17 28 36), (row3 17 28 37), (row3 17 28 38), (row3 17 28 39), (row3 17 28 40), (row3 17 28 41), (row3 17 28 42), (row3 17 28 43), (row3 17 28 44), (row3 17 28 45), (row3 17 28 46), (row3 17 28 47)]

def b093_06_labels : List Row := [(row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_06_rows b093_06_labels 329263235914778383491000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_06_rows b093_06_labels]
    decide +kernel

def b093_07_rows : List Row := [(row3 17 28 48), (row3 17 28 49), (row3 17 28 50), (row3 17 28 51), (row3 17 28 52), (row3 17 28 53), (row3 17 28 54), (row3 17 28 55), (row3 17 28 56), (row3 17 28 57), (row3 17 28 58), (row3 17 28 59), (row3 17 28 60), (row3 17 28 61), (row3 17 28 62), (row3 17 28 63)]

def b093_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_07_rows b093_07_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_07_rows b093_07_labels]
    decide +kernel

def b093_08_rows : List Row := [(row3 17 29 30), (row3 17 29 31), (row3 17 29 32), (row3 17 29 33), (row3 17 29 34), (row3 17 29 35), (row3 17 29 36), (row3 17 29 37), (row3 17 29 38), (row3 17 29 39), (row3 17 29 40), (row3 17 29 41), (row3 17 29 42), (row3 17 29 43), (row3 17 29 44), (row3 17 29 45)]

def b093_08_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_08_rows b093_08_labels 382000638273349126500000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_08_rows b093_08_labels]
    decide +kernel

def b093_09_rows : List Row := [(row3 17 29 46), (row3 17 29 47), (row3 17 29 48), (row3 17 29 49), (row3 17 29 50), (row3 17 29 51), (row3 17 29 52), (row3 17 29 53), (row3 17 29 54), (row3 17 29 55), (row3 17 29 56), (row3 17 29 57), (row3 17 29 58), (row3 17 29 59), (row3 17 29 60), (row3 17 29 61)]

def b093_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_09_rows b093_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_09_rows b093_09_labels]
    decide +kernel

def b093_10_rows : List Row := [(row3 17 29 62), (row3 17 29 63), (row3 17 30 31), (row3 17 30 32), (row3 17 30 33), (row3 17 30 34), (row3 17 30 35), (row3 17 30 36), (row3 17 30 37), (row3 17 30 38), (row3 17 30 39), (row3 17 30 40), (row3 17 30 41), (row3 17 30 42), (row3 17 30 43), (row3 17 30 44)]

def b093_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 286 286 462), (row3 248 248 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_10_rows b093_10_labels 99273593739162817328278500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_10_rows b093_10_labels]
    decide +kernel

def b093_11_rows : List Row := [(row3 17 30 45), (row3 17 30 46), (row3 17 30 47), (row3 17 30 48), (row3 17 30 49), (row3 17 30 50), (row3 17 30 51), (row3 17 30 52), (row3 17 30 53), (row3 17 30 54), (row3 17 30 55), (row3 17 30 56), (row3 17 30 57), (row3 17 30 58), (row3 17 30 59), (row3 17 30 60)]

def b093_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_11_rows b093_11_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_11_rows b093_11_labels]
    decide +kernel

def b093_12_rows : List Row := [(row3 17 30 61), (row3 17 30 62), (row3 17 30 63), (row3 17 31 32), (row3 17 31 33), (row3 17 31 34), (row3 17 31 35), (row3 17 31 36), (row3 17 31 37), (row3 17 31 38), (row3 17 31 39), (row3 17 31 40), (row3 17 31 41), (row3 17 31 42), (row3 17 31 43), (row3 17 31 44)]

def b093_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 220 222 221), (row3 292 289 292), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 287 462 287), (row3 252 462 252), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462)]

theorem b093_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_12_rows b093_12_labels 119549634120203028015994200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_12_rows b093_12_labels]
    decide +kernel

def b093_13_rows : List Row := [(row3 17 31 45), (row3 17 31 46), (row3 17 31 47), (row3 17 31 48), (row3 17 31 49), (row3 17 31 50), (row3 17 31 51), (row3 17 31 52), (row3 17 31 53), (row3 17 31 54), (row3 17 31 55), (row3 17 31 56), (row3 17 31 57), (row3 17 31 58), (row3 17 31 59), (row3 17 31 60)]

def b093_13_labels : List Row := [(row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 235 462 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 286 462 286), (row3 226 234 226), (row3 251 462 251), (row3 462 462 462), (row3 462 462 462)]

theorem b093_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_13_rows b093_13_labels 102346806032522864892967500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_13_rows b093_13_labels]
    decide +kernel

def b093_14_rows : List Row := [(row3 17 31 61), (row3 17 31 62), (row3 17 31 63), (row3 17 32 33), (row3 17 32 34), (row3 17 32 35), (row3 17 32 36), (row3 17 32 37), (row3 17 32 38), (row3 17 32 39), (row3 17 32 40), (row3 17 32 41), (row3 17 32 42), (row3 17 32 43), (row3 17 32 44), (row3 17 32 45)]

def b093_14_labels : List Row := [(row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 299 289 299), (row3 223 224 223), (row3 249 462 249), (row3 462 462 462), (row3 242 462 242), (row3 237 462 237), (row3 272 462 272), (row3 169 10 217), (row3 227 231 229), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_14_rows b093_14_labels 1176276058109026954232745450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_14_rows b093_14_labels]
    decide +kernel

def b093_15_rows : List Row := [(row3 17 32 46), (row3 17 32 47), (row3 17 32 48), (row3 17 32 49), (row3 17 32 50), (row3 17 32 51), (row3 17 32 52), (row3 17 32 53), (row3 17 32 54), (row3 17 32 55), (row3 17 32 56), (row3 17 32 57), (row3 17 32 58), (row3 17 32 59), (row3 17 32 60), (row3 17 32 61)]

def b093_15_labels : List Row := [(row3 244 462 244), (row3 235 462 235), (row3 235 462 235), (row3 251 462 251), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 217 10 169), (row3 229 231 227), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b093_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b093_15_rows b093_15_labels 900752365250428925754648750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b093_15_rows b093_15_labels]
    decide +kernel

theorem checked093 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_093 QuarticIntegerComputationalData.ids64_093 20136435914869082682599787390 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b093_00_rows ++ b093_01_rows) ++ (b093_02_rows ++ b093_03_rows)) ++ ((b093_04_rows ++ b093_05_rows) ++ (b093_06_rows ++ b093_07_rows))) ++ (((b093_08_rows ++ b093_09_rows) ++ (b093_10_rows ++ b093_11_rows)) ++ ((b093_12_rows ++ b093_13_rows) ++ (b093_14_rows ++ b093_15_rows))))
    ((((b093_00_labels ++ b093_01_labels) ++ (b093_02_labels ++ b093_03_labels)) ++ ((b093_04_labels ++ b093_05_labels) ++ (b093_06_labels ++ b093_07_labels))) ++ (((b093_08_labels ++ b093_09_labels) ++ (b093_10_labels ++ b093_11_labels)) ++ ((b093_12_labels ++ b093_13_labels) ++ (b093_14_labels ++ b093_15_labels)))) 20136435914869082682599787390
  exact ((((b093_00_checked.append (c := 17588277847399501042744026810) b093_01_checked (by decide +kernel)).append (c := 17733587064205845569495309490) (b093_02_checked.append (c := 145309216806344526751282680) b093_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17737839354871651126694007990) ((b093_04_checked.append (c := 3906925322077162260562500) b093_05_checked (by decide +kernel)).append (c := 4252290665805557198698500) (b093_06_checked.append (c := 345365343728394938136000) b093_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 20136435914869082682599787390) (((b093_08_checked.append (c := 382000638273349126500000) b093_09_checked (by decide +kernel)).append (c := 99671696485249783009423500) (b093_10_checked.append (c := 99289695846976433882923500) b093_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2398596559997431555905779400) ((b093_12_checked.append (c := 221896440152725892908961700) b093_13_checked (by decide +kernel)).append (c := 2298924863512181772896355900) (b093_14_checked.append (c := 2077028423359455879987394200) b093_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b094_00_rows : List Row := [(row3 17 32 62), (row3 17 32 63), (row3 17 33 34), (row3 17 33 35), (row3 17 33 36), (row3 17 33 37), (row3 17 33 38), (row3 17 33 39), (row3 17 33 40), (row3 17 33 41), (row3 17 33 42), (row3 17 33 43), (row3 17 33 44), (row3 17 33 45), (row3 17 33 46), (row3 17 33 47)]

def b094_00_labels : List Row := [(row3 244 462 244), (row3 235 462 235), (row3 291 291 289), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 233 462 233), (row3 277 277 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_00_rows b094_00_labels 267298886726687769675440100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_00_rows b094_00_labels]
    decide +kernel

def b094_01_rows : List Row := [(row3 17 33 48), (row3 17 33 49), (row3 17 33 50), (row3 17 33 51), (row3 17 33 52), (row3 17 33 53), (row3 17 33 54), (row3 17 33 55), (row3 17 33 56), (row3 17 33 57), (row3 17 33 58), (row3 17 33 59), (row3 17 33 60), (row3 17 33 61), (row3 17 33 62), (row3 17 33 63)]

def b094_01_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 276 276 275), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_01_rows b094_01_labels 44873465333325784904755200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_01_rows b094_01_labels]
    decide +kernel

def b094_02_rows : List Row := [(row3 17 34 35), (row3 17 34 36), (row3 17 34 37), (row3 17 34 38), (row3 17 34 39), (row3 17 34 40), (row3 17 34 41), (row3 17 34 42), (row3 17 34 43), (row3 17 34 44), (row3 17 34 45), (row3 17 34 46), (row3 17 34 47), (row3 17 34 48), (row3 17 34 49), (row3 17 34 50)]

def b094_02_labels : List Row := [(row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 247 462 247), (row3 231 231 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462)]

theorem b094_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_02_rows b094_02_labels 3934572160710204243855000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_02_rows b094_02_labels]
    decide +kernel

def b094_03_rows : List Row := [(row3 17 34 51), (row3 17 34 52), (row3 17 34 53), (row3 17 34 54), (row3 17 34 55), (row3 17 34 56), (row3 17 34 57), (row3 17 34 58), (row3 17 34 59), (row3 17 34 60), (row3 17 34 61), (row3 17 34 62), (row3 17 34 63), (row3 17 35 36), (row3 17 35 37), (row3 17 35 38)]

def b094_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 231 231), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_03_rows b094_03_labels 2541400694204920190055000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_03_rows b094_03_labels]
    decide +kernel

def b094_04_rows : List Row := [(row3 17 35 39), (row3 17 35 40), (row3 17 35 41), (row3 17 35 42), (row3 17 35 43), (row3 17 35 44), (row3 17 35 45), (row3 17 35 46), (row3 17 35 47), (row3 17 35 48), (row3 17 35 49), (row3 17 35 50), (row3 17 35 51), (row3 17 35 52), (row3 17 35 53), (row3 17 35 54)]

def b094_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_04_rows b094_04_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_04_rows b094_04_labels]
    decide +kernel

def b094_05_rows : List Row := [(row3 17 35 55), (row3 17 35 56), (row3 17 35 57), (row3 17 35 58), (row3 17 35 59), (row3 17 35 60), (row3 17 35 61), (row3 17 35 62), (row3 17 35 63), (row3 17 36 37), (row3 17 36 38), (row3 17 36 39), (row3 17 36 40), (row3 17 36 41), (row3 17 36 42), (row3 17 36 43)]

def b094_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_05_rows b094_05_labels 24153161720424831967500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_05_rows b094_05_labels]
    decide +kernel

def b094_06_rows : List Row := [(row3 17 36 44), (row3 17 36 45), (row3 17 36 46), (row3 17 36 47), (row3 17 36 48), (row3 17 36 49), (row3 17 36 50), (row3 17 36 51), (row3 17 36 52), (row3 17 36 53), (row3 17 36 54), (row3 17 36 55), (row3 17 36 56), (row3 17 36 57), (row3 17 36 58), (row3 17 36 59)]

def b094_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_06_rows b094_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_06_rows b094_06_labels]
    decide +kernel

def b094_07_rows : List Row := [(row3 17 36 60), (row3 17 36 61), (row3 17 36 62), (row3 17 36 63), (row3 17 37 38), (row3 17 37 39), (row3 17 37 40), (row3 17 37 41), (row3 17 37 42), (row3 17 37 43), (row3 17 37 44), (row3 17 37 45), (row3 17 37 46), (row3 17 37 47), (row3 17 37 48), (row3 17 37 49)]

def b094_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_07_rows b094_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_07_rows b094_07_labels]
    decide +kernel

def b094_08_rows : List Row := [(row3 17 37 50), (row3 17 37 51), (row3 17 37 52), (row3 17 37 53), (row3 17 37 54), (row3 17 37 55), (row3 17 37 56), (row3 17 37 57), (row3 17 37 58), (row3 17 37 59), (row3 17 37 60), (row3 17 37 61), (row3 17 37 62), (row3 17 37 63), (row3 17 38 39), (row3 17 38 40)]

def b094_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b094_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_08_rows b094_08_labels 10173141782965611225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_08_rows b094_08_labels]
    decide +kernel

def b094_09_rows : List Row := [(row3 17 38 41), (row3 17 38 42), (row3 17 38 43), (row3 17 38 44), (row3 17 38 45), (row3 17 38 46), (row3 17 38 47), (row3 17 38 48), (row3 17 38 49), (row3 17 38 50), (row3 17 38 51), (row3 17 38 52), (row3 17 38 53), (row3 17 38 54), (row3 17 38 55), (row3 17 38 56)]

def b094_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_09_rows b094_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_09_rows b094_09_labels]
    decide +kernel

def b094_10_rows : List Row := [(row3 17 38 57), (row3 17 38 58), (row3 17 38 59), (row3 17 38 60), (row3 17 38 61), (row3 17 38 62), (row3 17 38 63), (row3 17 39 40), (row3 17 39 41), (row3 17 39 42), (row3 17 39 43), (row3 17 39 44), (row3 17 39 45), (row3 17 39 46), (row3 17 39 47), (row3 17 39 48)]

def b094_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_10_rows b094_10_labels 426461894939994422422500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_10_rows b094_10_labels]
    decide +kernel

def b094_11_rows : List Row := [(row3 17 39 49), (row3 17 39 50), (row3 17 39 51), (row3 17 39 52), (row3 17 39 53), (row3 17 39 54), (row3 17 39 55), (row3 17 39 56), (row3 17 39 57), (row3 17 39 58), (row3 17 39 59), (row3 17 39 60), (row3 17 39 61), (row3 17 39 62), (row3 17 39 63), (row3 17 40 41)]

def b094_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 204 259 8)]

theorem b094_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_11_rows b094_11_labels 272922406367469064094430000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_11_rows b094_11_labels]
    decide +kernel

def b094_12_rows : List Row := [(row3 17 40 42), (row3 17 40 43), (row3 17 40 44), (row3 17 40 45), (row3 17 40 46), (row3 17 40 47), (row3 17 40 48), (row3 17 40 49), (row3 17 40 50), (row3 17 40 51), (row3 17 40 52), (row3 17 40 53), (row3 17 40 54), (row3 17 40 55), (row3 17 40 56), (row3 17 40 57)]

def b094_12_labels : List Row := [(row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 264 264 462), (row3 277 277 265), (row3 227 231 229), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 231 231 234), (row3 325 87 371), (row3 297 297 295)]

theorem b094_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_12_rows b094_12_labels 9821747590770289084725459600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_12_rows b094_12_labels]
    decide +kernel

def b094_13_rows : List Row := [(row3 17 40 58), (row3 17 40 59), (row3 17 40 60), (row3 17 40 61), (row3 17 40 62), (row3 17 40 63), (row3 17 41 42), (row3 17 41 43), (row3 17 41 44), (row3 17 41 45), (row3 17 41 46), (row3 17 41 47), (row3 17 41 48), (row3 17 41 49), (row3 17 41 50), (row3 17 41 51)]

def b094_13_labels : List Row := [(row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 280 280 278), (row3 264 462 264), (row3 238 462 238), (row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 238 462 238), (row3 233 462 233), (row3 169 10 217), (row3 236 462 236), (row3 243 462 243)]

theorem b094_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_13_rows b094_13_labels 943060589536284617979883350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_13_rows b094_13_labels]
    decide +kernel

def b094_14_rows : List Row := [(row3 17 41 52), (row3 17 41 53), (row3 17 41 54), (row3 17 41 55), (row3 17 41 56), (row3 17 41 57), (row3 17 41 58), (row3 17 41 59), (row3 17 41 60), (row3 17 41 61), (row3 17 41 62), (row3 17 41 63), (row3 17 42 43), (row3 17 42 44), (row3 17 42 45), (row3 17 42 46)]

def b094_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 213 11 116), (row3 195 188 194), (row3 252 462 252), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_14_rows b094_14_labels 2133429311299888306935109170 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_14_rows b094_14_labels]
    decide +kernel

def b094_15_rows : List Row := [(row3 17 42 47), (row3 17 42 48), (row3 17 42 49), (row3 17 42 50), (row3 17 42 51), (row3 17 42 52), (row3 17 42 53), (row3 17 42 54), (row3 17 42 55), (row3 17 42 56), (row3 17 42 57), (row3 17 42 58), (row3 17 42 59), (row3 17 42 60), (row3 17 42 61), (row3 17 42 62)]

def b094_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 280 280 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b094_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b094_15_rows b094_15_labels 11501084711589745513404600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b094_15_rows b094_15_labels]
    decide +kernel

theorem checked094 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_094 QuarticIntegerComputationalData.ids64_094 13501795528653350297156069520 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b094_00_rows ++ b094_01_rows) ++ (b094_02_rows ++ b094_03_rows)) ++ ((b094_04_rows ++ b094_05_rows) ++ (b094_06_rows ++ b094_07_rows))) ++ (((b094_08_rows ++ b094_09_rows) ++ (b094_10_rows ++ b094_11_rows)) ++ ((b094_12_rows ++ b094_13_rows) ++ (b094_14_rows ++ b094_15_rows))))
    ((((b094_00_labels ++ b094_01_labels) ++ (b094_02_labels ++ b094_03_labels)) ++ ((b094_04_labels ++ b094_05_labels) ++ (b094_06_labels ++ b094_07_labels))) ++ (((b094_08_labels ++ b094_09_labels) ++ (b094_10_labels ++ b094_11_labels)) ++ ((b094_12_labels ++ b094_13_labels) ++ (b094_14_labels ++ b094_15_labels)))) 13501795528653350297156069520
  exact ((((b094_00_checked.append (c := 312172352060013554580195300) b094_01_checked (by decide +kernel)).append (c := 318648324914928679014105300) (b094_02_checked.append (c := 6475972854915124433910000) b094_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 318697910931106517874135300) ((b094_04_checked.append (c := 49586016177838860030000) b094_05_checked (by decide +kernel)).append (c := 49586016177838860030000) (b094_06_checked.append (c := 0) b094_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 13501795528653350297156069520) (((b094_08_checked.append (c := 10173141782965611225000) b094_09_checked (by decide +kernel)).append (c := 273359041404192024128077500) (b094_10_checked.append (c := 273348868262409058516852500) b094_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 13183097617722243779281934220) ((b094_12_checked.append (c := 10764808180306573702705342950) b094_13_checked (by decide +kernel)).append (c := 12909738576318051755153856720) (b094_14_checked.append (c := 2144930396011478052448513770) b094_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b095_00_rows : List Row := [(row3 17 42 63), (row3 17 43 44), (row3 17 43 45), (row3 17 43 46), (row3 17 43 47), (row3 17 43 48), (row3 17 43 49), (row3 17 43 50), (row3 17 43 51), (row3 17 43 52), (row3 17 43 53), (row3 17 43 54), (row3 17 43 55), (row3 17 43 56), (row3 17 43 57), (row3 17 43 58)]

def b095_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 246 462 246)]

theorem b095_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_00_rows b095_00_labels 449979767374484965774500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_00_rows b095_00_labels]
    decide +kernel

def b095_01_rows : List Row := [(row3 17 43 59), (row3 17 43 60), (row3 17 43 61), (row3 17 43 62), (row3 17 43 63), (row3 17 44 45), (row3 17 44 46), (row3 17 44 47), (row3 17 44 48), (row3 17 44 49), (row3 17 44 50), (row3 17 44 51), (row3 17 44 52), (row3 17 44 53), (row3 17 44 54), (row3 17 44 55)]

def b095_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_01_rows b095_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_01_rows b095_01_labels]
    decide +kernel

def b095_02_rows : List Row := [(row3 17 44 56), (row3 17 44 57), (row3 17 44 58), (row3 17 44 59), (row3 17 44 60), (row3 17 44 61), (row3 17 44 62), (row3 17 44 63), (row3 17 45 46), (row3 17 45 47), (row3 17 45 48), (row3 17 45 49), (row3 17 45 50), (row3 17 45 51), (row3 17 45 52), (row3 17 45 53)]

def b095_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_02_rows b095_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_02_rows b095_02_labels]
    decide +kernel

def b095_03_rows : List Row := [(row3 17 45 54), (row3 17 45 55), (row3 17 45 56), (row3 17 45 57), (row3 17 45 58), (row3 17 45 59), (row3 17 45 60), (row3 17 45 61), (row3 17 45 62), (row3 17 45 63), (row3 17 46 47), (row3 17 46 48), (row3 17 46 49), (row3 17 46 50), (row3 17 46 51), (row3 17 46 52)]

def b095_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_03_rows b095_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_03_rows b095_03_labels]
    decide +kernel

def b095_04_rows : List Row := [(row3 17 46 53), (row3 17 46 54), (row3 17 46 55), (row3 17 46 56), (row3 17 46 57), (row3 17 46 58), (row3 17 46 59), (row3 17 46 60), (row3 17 46 61), (row3 17 46 62), (row3 17 46 63), (row3 17 47 48), (row3 17 47 49), (row3 17 47 50), (row3 17 47 51), (row3 17 47 52)]

def b095_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_04_rows b095_04_labels 785228920557954097738500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_04_rows b095_04_labels]
    decide +kernel

def b095_05_rows : List Row := [(row3 17 47 53), (row3 17 47 54), (row3 17 47 55), (row3 17 47 56), (row3 17 47 57), (row3 17 47 58), (row3 17 47 59), (row3 17 47 60), (row3 17 47 61), (row3 17 47 62), (row3 17 47 63), (row3 17 48 49), (row3 17 48 50), (row3 17 48 51), (row3 17 48 52), (row3 17 48 53)]

def b095_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 212 11 115), (row3 232 235 228), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 299 289 299), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_05_rows b095_05_labels 1899157313481350434161736950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_05_rows b095_05_labels]
    decide +kernel

def b095_06_rows : List Row := [(row3 17 48 54), (row3 17 48 55), (row3 17 48 56), (row3 17 48 57), (row3 17 48 58), (row3 17 48 59), (row3 17 48 60), (row3 17 48 61), (row3 17 48 62), (row3 17 48 63), (row3 17 49 50), (row3 17 49 51), (row3 17 49 52), (row3 17 49 53), (row3 17 49 54), (row3 17 49 55)]

def b095_06_labels : List Row := [(row3 234 234 462), (row3 291 289 291), (row3 95 435 41), (row3 125 126 128), (row3 292 289 292), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 291 289 291), (row3 137 149 146), (row3 272 272 462), (row3 237 237 462), (row3 242 242 462), (row3 462 462 462), (row3 249 249 462), (row3 223 223 224)]

theorem b095_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_06_rows b095_06_labels 354616112205967701823896121050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_06_rows b095_06_labels]
    decide +kernel

def b095_07_rows : List Row := [(row3 17 49 56), (row3 17 49 57), (row3 17 49 58), (row3 17 49 59), (row3 17 49 60), (row3 17 49 61), (row3 17 49 62), (row3 17 49 63), (row3 17 50 51), (row3 17 50 52), (row3 17 50 53), (row3 17 50 54), (row3 17 50 55), (row3 17 50 56), (row3 17 50 57), (row3 17 50 58)]

def b095_07_labels : List Row := [(row3 156 82 399), (row3 353 375 366), (row3 220 222 221), (row3 248 248 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224), (row3 311 311 306), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 214 11 117), (row3 175 161 175), (row3 287 462 287)]

theorem b095_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_07_rows b095_07_labels 38834757945602176726760243160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_07_rows b095_07_labels]
    decide +kernel

def b095_08_rows : List Row := [(row3 17 50 59), (row3 17 50 60), (row3 17 50 61), (row3 17 50 62), (row3 17 50 63), (row3 17 51 52), (row3 17 51 53), (row3 17 51 54), (row3 17 51 55), (row3 17 51 56), (row3 17 51 57), (row3 17 51 58), (row3 17 51 59), (row3 17 51 60), (row3 17 51 61), (row3 17 51 62)]

def b095_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 279 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_08_rows b095_08_labels 12969586842569232678368100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_08_rows b095_08_labels]
    decide +kernel

def b095_09_rows : List Row := [(row3 17 51 63), (row3 17 52 53), (row3 17 52 54), (row3 17 52 55), (row3 17 52 56), (row3 17 52 57), (row3 17 52 58), (row3 17 52 59), (row3 17 52 60), (row3 17 52 61), (row3 17 52 62), (row3 17 52 63), (row3 17 53 54), (row3 17 53 55), (row3 17 53 56), (row3 17 53 57)]

def b095_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_09_rows b095_09_labels 299986511582989977183000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_09_rows b095_09_labels]
    decide +kernel

def b095_10_rows : List Row := [(row3 17 53 58), (row3 17 53 59), (row3 17 53 60), (row3 17 53 61), (row3 17 53 62), (row3 17 53 63), (row3 17 54 55), (row3 17 54 56), (row3 17 54 57), (row3 17 54 58), (row3 17 54 59), (row3 17 54 60), (row3 17 54 61), (row3 17 54 62), (row3 17 54 63), (row3 17 55 56)]

def b095_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 214 11 117), (row3 228 236 225), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 157 83 399)]

theorem b095_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_10_rows b095_10_labels 21908237336146484503472801250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_10_rows b095_10_labels]
    decide +kernel

def b095_11_rows : List Row := [(row3 17 55 57), (row3 17 55 58), (row3 17 55 59), (row3 17 55 60), (row3 17 55 61), (row3 17 55 62), (row3 17 55 63), (row3 17 56 57), (row3 17 56 58), (row3 17 56 59), (row3 17 56 60), (row3 17 56 61), (row3 17 56 62), (row3 17 56 63), (row3 17 57 58), (row3 17 57 59)]

def b095_11_labels : List Row := [(row3 320 320 319), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224), (row3 309 309 306), (row3 74 44 439), (row3 121 369 85), (row3 254 171 10), (row3 462 462 462), (row3 254 171 10), (row3 122 369 86), (row3 383 43 436), (row3 354 366 376), (row3 197 196 190)]

theorem b095_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_11_rows b095_11_labels 935693716931872821336959079630 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_11_rows b095_11_labels]
    decide +kernel

def b095_12_rows : List Row := [(row3 17 57 60), (row3 17 57 61), (row3 17 57 62), (row3 17 57 63), (row3 17 58 59), (row3 17 58 60), (row3 17 58 61), (row3 17 58 62), (row3 17 58 63), (row3 17 59 60), (row3 17 59 61), (row3 17 59 62), (row3 17 59 63), (row3 17 60 61), (row3 17 60 62), (row3 17 60 63)]

def b095_12_labels : List Row := [(row3 262 261 262), (row3 232 230 238), (row3 317 308 317), (row3 109 111 110), (row3 286 286 462), (row3 235 235 462), (row3 247 247 462), (row3 224 224 224), (row3 310 310 306), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_12_rows b095_12_labels 1120111995245182003203804240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_12_rows b095_12_labels]
    decide +kernel

def b095_13_rows : List Row := [(row3 17 61 62), (row3 17 61 63), (row3 17 62 63), (row3 18 19 20), (row3 18 19 21), (row3 18 19 22), (row3 18 19 23), (row3 18 19 24), (row3 18 19 25), (row3 18 19 26), (row3 18 19 27), (row3 18 19 28), (row3 18 19 29), (row3 18 19 30), (row3 18 19 31), (row3 18 19 32)]

def b095_13_labels : List Row := [(row3 246 462 246), (row3 232 462 232), (row3 309 309 306), (row3 462 180 180), (row3 462 269 269), (row3 462 462 462), (row3 462 270 270), (row3 462 294 294), (row3 232 138 139), (row3 462 377 377), (row3 462 139 139), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_13_rows b095_13_labels 24087809399239553487518377800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_13_rows b095_13_labels]
    decide +kernel

def b095_14_rows : List Row := [(row3 18 19 33), (row3 18 19 34), (row3 18 19 35), (row3 18 19 36), (row3 18 19 37), (row3 18 19 38), (row3 18 19 39), (row3 18 19 40), (row3 18 19 41), (row3 18 19 42), (row3 18 19 43), (row3 18 19 44), (row3 18 19 45), (row3 18 19 46), (row3 18 19 47), (row3 18 19 48)]

def b095_14_labels : List Row := [(row3 462 293 293), (row3 462 180 180), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b095_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_14_rows b095_14_labels 731547242593323290349673500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_14_rows b095_14_labels]
    decide +kernel

def b095_15_rows : List Row := [(row3 18 19 49), (row3 18 19 50), (row3 18 19 51), (row3 18 19 52), (row3 18 19 53), (row3 18 19 54), (row3 18 19 55), (row3 18 19 56), (row3 18 19 57), (row3 18 19 58), (row3 18 19 59), (row3 18 19 60), (row3 18 19 61), (row3 18 19 62), (row3 18 19 63), (row3 18 20 21)]

def b095_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 271 271), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237)]

theorem b095_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b095_15_rows b095_15_labels 49981786106113127455285500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b095_15_rows b095_15_labels]
    decide +kernel

theorem checked095 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_095 QuarticIntegerComputationalData.ids64_095 1378955936938296791395496187180 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b095_00_rows ++ b095_01_rows) ++ (b095_02_rows ++ b095_03_rows)) ++ ((b095_04_rows ++ b095_05_rows) ++ (b095_06_rows ++ b095_07_rows))) ++ (((b095_08_rows ++ b095_09_rows) ++ (b095_10_rows ++ b095_11_rows)) ++ ((b095_12_rows ++ b095_13_rows) ++ (b095_14_rows ++ b095_15_rows))))
    ((((b095_00_labels ++ b095_01_labels) ++ (b095_02_labels ++ b095_03_labels)) ++ ((b095_04_labels ++ b095_05_labels) ++ (b095_06_labels ++ b095_07_labels))) ++ (((b095_08_labels ++ b095_09_labels) ++ (b095_10_labels ++ b095_11_labels)) ++ ((b095_12_labels ++ b095_13_labels) ++ (b095_14_labels ++ b095_15_labels)))) 1378955936938296791395496187180
  exact ((((b095_00_checked.append (c := 449979767374484965774500) b095_01_checked (by decide +kernel)).append (c := 449979767374484965774500) (b095_02_checked.append (c := 0) b095_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 395351262673739161423881614160) ((b095_04_checked.append (c := 1899942542401908388259475450) b095_05_checked (by decide +kernel)).append (c := 395350812693971786938915839660) (b095_06_checked.append (c := 393450870151569878550656364210) b095_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1378955936938296791395496187180) (((b095_08_checked.append (c := 13269573354152222655551100) b095_09_checked (by decide +kernel)).append (c := 957615223841373458063087431980) (b095_10_checked.append (c := 957601954268019305840431880880) b095_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 983604674264557629971614573020) ((b095_12_checked.append (c := 25207921394484735490722182040) b095_13_checked (by decide +kernel)).append (c := 25989450423184171908527141040) (b095_14_checked.append (c := 781529028699436417804959000) b095_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b096_00_rows : List Row := [(row3 18 20 22), (row3 18 20 23), (row3 18 20 24), (row3 18 20 25), (row3 18 20 26), (row3 18 20 27), (row3 18 20 28), (row3 18 20 29), (row3 18 20 30), (row3 18 20 31), (row3 18 20 32), (row3 18 20 33), (row3 18 20 34), (row3 18 20 35), (row3 18 20 36), (row3 18 20 37)]

def b096_00_labels : List Row := [(row3 462 462 462), (row3 237 235 235), (row3 462 234 234), (row3 462 278 278), (row3 462 180 180), (row3 462 278 278), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 265 265), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462)]

theorem b096_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_00_rows b096_00_labels 548664034725538316497760400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_00_rows b096_00_labels]
    decide +kernel

def b096_01_rows : List Row := [(row3 18 20 38), (row3 18 20 39), (row3 18 20 40), (row3 18 20 41), (row3 18 20 42), (row3 18 20 43), (row3 18 20 44), (row3 18 20 45), (row3 18 20 46), (row3 18 20 47), (row3 18 20 48), (row3 18 20 49), (row3 18 20 50), (row3 18 20 51), (row3 18 20 52), (row3 18 20 53)]

def b096_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_01_rows b096_01_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_01_rows b096_01_labels]
    decide +kernel

def b096_02_rows : List Row := [(row3 18 20 54), (row3 18 20 55), (row3 18 20 56), (row3 18 20 57), (row3 18 20 58), (row3 18 20 59), (row3 18 20 60), (row3 18 20 61), (row3 18 20 62), (row3 18 20 63), (row3 18 21 22), (row3 18 21 23), (row3 18 21 24), (row3 18 21 25), (row3 18 21 26), (row3 18 21 27)]

def b096_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 267 267), (row3 462 245 245), (row3 462 235 235), (row3 462 269 269), (row3 462 235 235)]

theorem b096_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_02_rows b096_02_labels 33951138317612366419305900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_02_rows b096_02_labels]
    decide +kernel

def b096_03_rows : List Row := [(row3 18 21 28), (row3 18 21 29), (row3 18 21 30), (row3 18 21 31), (row3 18 21 32), (row3 18 21 33), (row3 18 21 34), (row3 18 21 35), (row3 18 21 36), (row3 18 21 37), (row3 18 21 38), (row3 18 21 39), (row3 18 21 40), (row3 18 21 41), (row3 18 21 42), (row3 18 21 43)]

def b096_03_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462)]

theorem b096_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_03_rows b096_03_labels 173055706975043264493000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_03_rows b096_03_labels]
    decide +kernel

def b096_04_rows : List Row := [(row3 18 21 44), (row3 18 21 45), (row3 18 21 46), (row3 18 21 47), (row3 18 21 48), (row3 18 21 49), (row3 18 21 50), (row3 18 21 51), (row3 18 21 52), (row3 18 21 53), (row3 18 21 54), (row3 18 21 55), (row3 18 21 56), (row3 18 21 57), (row3 18 21 58), (row3 18 21 59)]

def b096_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462)]

theorem b096_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_04_rows b096_04_labels 4248890416128681112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_04_rows b096_04_labels]
    decide +kernel

def b096_05_rows : List Row := [(row3 18 21 60), (row3 18 21 61), (row3 18 21 62), (row3 18 21 63), (row3 18 22 23), (row3 18 22 24), (row3 18 22 25), (row3 18 22 26), (row3 18 22 27), (row3 18 22 28), (row3 18 22 29), (row3 18 22 30), (row3 18 22 31), (row3 18 22 32), (row3 18 22 33), (row3 18 22 34)]

def b096_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 154 154), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_05_rows b096_05_labels 797360801728997606481450000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_05_rows b096_05_labels]
    decide +kernel

def b096_06_rows : List Row := [(row3 18 22 35), (row3 18 22 36), (row3 18 22 37), (row3 18 22 38), (row3 18 22 39), (row3 18 22 40), (row3 18 22 41), (row3 18 22 42), (row3 18 22 43), (row3 18 22 44), (row3 18 22 45), (row3 18 22 46), (row3 18 22 47), (row3 18 22 48), (row3 18 22 49), (row3 18 22 50)]

def b096_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_06_rows b096_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_06_rows b096_06_labels]
    decide +kernel

def b096_07_rows : List Row := [(row3 18 22 51), (row3 18 22 52), (row3 18 22 53), (row3 18 22 54), (row3 18 22 55), (row3 18 22 56), (row3 18 22 57), (row3 18 22 58), (row3 18 22 59), (row3 18 22 60), (row3 18 22 61), (row3 18 22 62), (row3 18 22 63), (row3 18 23 24), (row3 18 23 25), (row3 18 23 26)]

def b096_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 295 298 298), (row3 226 224 229), (row3 462 271 271)]

theorem b096_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_07_rows b096_07_labels 73709079344502936684527700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_07_rows b096_07_labels]
    decide +kernel

def b096_08_rows : List Row := [(row3 18 23 27), (row3 18 23 28), (row3 18 23 29), (row3 18 23 30), (row3 18 23 31), (row3 18 23 32), (row3 18 23 33), (row3 18 23 34), (row3 18 23 35), (row3 18 23 36), (row3 18 23 37), (row3 18 23 38), (row3 18 23 39), (row3 18 23 40), (row3 18 23 41), (row3 18 23 42)]

def b096_08_labels : List Row := [(row3 462 235 235), (row3 462 245 245), (row3 234 234 234), (row3 278 279 279), (row3 180 154 154), (row3 234 234 234), (row3 462 246 246), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 244 244), (row3 234 234 234), (row3 265 266 266), (row3 462 245 245), (row3 462 462 462), (row3 462 242 242)]

theorem b096_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_08_rows b096_08_labels 811647345842321718192691500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_08_rows b096_08_labels]
    decide +kernel

def b096_09_rows : List Row := [(row3 18 23 43), (row3 18 23 44), (row3 18 23 45), (row3 18 23 46), (row3 18 23 47), (row3 18 23 48), (row3 18 23 49), (row3 18 23 50), (row3 18 23 51), (row3 18 23 52), (row3 18 23 53), (row3 18 23 54), (row3 18 23 55), (row3 18 23 56), (row3 18 23 57), (row3 18 23 58)]

def b096_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 234 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 249 249), (row3 462 294 294), (row3 462 228 228), (row3 462 249 249)]

theorem b096_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_09_rows b096_09_labels 110849086140985029197790000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_09_rows b096_09_labels]
    decide +kernel

def b096_10_rows : List Row := [(row3 18 23 59), (row3 18 23 60), (row3 18 23 61), (row3 18 23 62), (row3 18 23 63), (row3 18 24 25), (row3 18 24 26), (row3 18 24 27), (row3 18 24 28), (row3 18 24 29), (row3 18 24 30), (row3 18 24 31), (row3 18 24 32), (row3 18 24 33), (row3 18 24 34), (row3 18 24 35)]

def b096_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 250 250), (row3 237 226 226), (row3 356 158 89), (row3 265 302 302), (row3 237 226 226), (row3 462 249 249), (row3 237 237 237), (row3 265 266 266), (row3 180 154 154), (row3 180 154 154), (row3 278 283 283), (row3 234 228 228), (row3 462 250 250)]

theorem b096_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_10_rows b096_10_labels 8175084080711102081251016400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_10_rows b096_10_labels]
    decide +kernel

def b096_11_rows : List Row := [(row3 18 24 36), (row3 18 24 37), (row3 18 24 38), (row3 18 24 39), (row3 18 24 40), (row3 18 24 41), (row3 18 24 42), (row3 18 24 43), (row3 18 24 44), (row3 18 24 45), (row3 18 24 46), (row3 18 24 47), (row3 18 24 48), (row3 18 24 49), (row3 18 24 50), (row3 18 24 51)]

def b096_11_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 278 279 279), (row3 265 267 267), (row3 234 234 234), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 234 234 234), (row3 237 235 235), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462)]

theorem b096_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_11_rows b096_11_labels 14385654730324474650166500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_11_rows b096_11_labels]
    decide +kernel

def b096_12_rows : List Row := [(row3 18 24 52), (row3 18 24 53), (row3 18 24 54), (row3 18 24 55), (row3 18 24 56), (row3 18 24 57), (row3 18 24 58), (row3 18 24 59), (row3 18 24 60), (row3 18 24 61), (row3 18 24 62), (row3 18 24 63), (row3 18 25 26), (row3 18 25 27), (row3 18 25 28), (row3 18 25 29)]

def b096_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 462 270 270), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 235 235), (row3 163 139 124), (row3 273 295 304), (row3 236 228 225), (row3 462 462 462)]

theorem b096_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_12_rows b096_12_labels 2693328016767074570868480000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_12_rows b096_12_labels]
    decide +kernel

def b096_13_rows : List Row := [(row3 18 25 30), (row3 18 25 31), (row3 18 25 32), (row3 18 25 33), (row3 18 25 34), (row3 18 25 35), (row3 18 25 36), (row3 18 25 37), (row3 18 25 38), (row3 18 25 39), (row3 18 25 40), (row3 18 25 41), (row3 18 25 42), (row3 18 25 43), (row3 18 25 44), (row3 18 25 45)]

def b096_13_labels : List Row := [(row3 236 462 236), (row3 273 462 273), (row3 288 462 288), (row3 163 228 160), (row3 288 278 300), (row3 232 228 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 232 462 232), (row3 273 462 273), (row3 232 235 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_13_rows b096_13_labels 791897512548379171833964800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_13_rows b096_13_labels]
    decide +kernel

def b096_14_rows : List Row := [(row3 18 25 46), (row3 18 25 47), (row3 18 25 48), (row3 18 25 49), (row3 18 25 50), (row3 18 25 51), (row3 18 25 52), (row3 18 25 53), (row3 18 25 54), (row3 18 25 55), (row3 18 25 56), (row3 18 25 57), (row3 18 25 58), (row3 18 25 59), (row3 18 25 60), (row3 18 25 61)]

def b096_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_14_rows b096_14_labels 1002572601206450985900000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_14_rows b096_14_labels]
    decide +kernel

def b096_15_rows : List Row := [(row3 18 25 62), (row3 18 25 63), (row3 18 26 27), (row3 18 26 28), (row3 18 26 29), (row3 18 26 30), (row3 18 26 31), (row3 18 26 32), (row3 18 26 33), (row3 18 26 34), (row3 18 26 35), (row3 18 26 36), (row3 18 26 37), (row3 18 26 38), (row3 18 26 39), (row3 18 26 40)]

def b096_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 139 139), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 462 180 180), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b096_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b096_15_rows b096_15_labels 2602990561928409184277272500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b096_15_rows b096_15_labels]
    decide +kernel

theorem checked096 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_096 QuarticIntegerComputationalData.ids64_096 16655169784678294388369569200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b096_00_rows ++ b096_01_rows) ++ (b096_02_rows ++ b096_03_rows)) ++ ((b096_04_rows ++ b096_05_rows) ++ (b096_06_rows ++ b096_07_rows))) ++ (((b096_08_rows ++ b096_09_rows) ++ (b096_10_rows ++ b096_11_rows)) ++ ((b096_12_rows ++ b096_13_rows) ++ (b096_14_rows ++ b096_15_rows))))
    ((((b096_00_labels ++ b096_01_labels) ++ (b096_02_labels ++ b096_03_labels)) ++ ((b096_04_labels ++ b096_05_labels) ++ (b096_06_labels ++ b096_07_labels))) ++ (((b096_08_labels ++ b096_09_labels) ++ (b096_10_labels ++ b096_11_labels)) ++ ((b096_12_labels ++ b096_13_labels) ++ (b096_14_labels ++ b096_15_labels)))) 16655169784678294388369569200
  exact ((((b096_00_checked.append (c := 548786629419987625581398400) b096_01_checked (by decide +kernel)).append (c := 582910823444575035265197300) (b096_02_checked.append (c := 34124194024587409683798900) b096_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1453984953408491707112287500) ((b096_04_checked.append (c := 797365050619413735162562500) b096_05_checked (by decide +kernel)).append (c := 871074129963916671847090200) (b096_06_checked.append (c := 73709079344502936684527700) b096_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 16655169784678294388369569200) (((b096_08_checked.append (c := 922496431983306747390481500) b096_09_checked (by decide +kernel)).append (c := 9111966167424733303291664400) (b096_10_checked.append (c := 8189469735441426555901182900) b096_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 15201184831269802681257281700) ((b096_12_checked.append (c := 3485225529315453742702444800) b096_13_checked (by decide +kernel)).append (c := 6089218663845069377965617300) (b096_14_checked.append (c := 2603993134529615635263172500) b096_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
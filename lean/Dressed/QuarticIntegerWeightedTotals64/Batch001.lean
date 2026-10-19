import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch000
import Dressed.QuarticIntegerComputationalData64.Batch001


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b009_00_rows : List Row := [(row3 2 10 25), (row3 2 10 26), (row3 2 10 27), (row3 2 10 28), (row3 2 10 29), (row3 2 10 30), (row3 2 10 31), (row3 2 10 32), (row3 2 10 33), (row3 2 10 34), (row3 2 10 35), (row3 2 10 36), (row3 2 10 37), (row3 2 10 38), (row3 2 10 39), (row3 2 10 40)]

def b009_00_labels : List Row := [(row3 121 85 369), (row3 385 426 77), (row3 122 86 369), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 237 237 462), (row3 462 284 284), (row3 168 94 333), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266)]

theorem b009_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_00_rows b009_00_labels 87581872533775695167874109320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_00_rows b009_00_labels]
    decide +kernel

def b009_01_rows : List Row := [(row3 2 10 41), (row3 2 10 42), (row3 2 10 43), (row3 2 10 44), (row3 2 10 45), (row3 2 10 46), (row3 2 10 47), (row3 2 10 48), (row3 2 10 49), (row3 2 10 50), (row3 2 10 51), (row3 2 10 52), (row3 2 10 53), (row3 2 10 54), (row3 2 10 55), (row3 2 10 56)]

def b009_01_labels : List Row := [(row3 191 235 193), (row3 339 342 328), (row3 193 462 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 140 178 140), (row3 388 392 362), (row3 68 69 76), (row3 387 390 360), (row3 180 462 180), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 409 414 394)]

theorem b009_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_01_rows b009_01_labels 2100212658951416614237759140630 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_01_rows b009_01_labels]
    decide +kernel

def b009_02_rows : List Row := [(row3 2 10 57), (row3 2 10 58), (row3 2 10 59), (row3 2 10 60), (row3 2 10 61), (row3 2 10 62), (row3 2 10 63), (row3 2 11 12), (row3 2 11 13), (row3 2 11 14), (row3 2 11 15), (row3 2 11 16), (row3 2 11 17), (row3 2 11 18), (row3 2 11 19), (row3 2 11 20)]

def b009_02_labels : List Row := [(row3 48 50 61), (row3 455 447 447), (row3 49 52 62), (row3 387 391 361), (row3 191 235 193), (row3 289 291 291), (row3 133 137 132), (row3 127 137 126), (row3 288 462 288), (row3 233 462 233), (row3 288 462 288), (row3 288 462 288), (row3 142 136 141), (row3 351 348 350), (row3 127 137 126), (row3 300 462 300)]

theorem b009_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_02_rows b009_02_labels 9124364158736379650030343191070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_02_rows b009_02_labels]
    decide +kernel

def b009_03_rows : List Row := [(row3 2 11 21), (row3 2 11 22), (row3 2 11 23), (row3 2 11 24), (row3 2 11 25), (row3 2 11 26), (row3 2 11 27), (row3 2 11 28), (row3 2 11 29), (row3 2 11 30), (row3 2 11 31), (row3 2 11 32), (row3 2 11 33), (row3 2 11 34), (row3 2 11 35), (row3 2 11 36)]

def b009_03_labels : List Row := [(row3 232 462 232), (row3 462 462 462), (row3 235 462 235), (row3 238 462 238), (row3 273 462 273), (row3 197 190 196), (row3 288 462 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 236 462 236), (row3 462 462 462)]

theorem b009_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_03_rows b009_03_labels 129338196673876658094695040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_03_rows b009_03_labels]
    decide +kernel

def b009_04_rows : List Row := [(row3 2 11 37), (row3 2 11 38), (row3 2 11 39), (row3 2 11 40), (row3 2 11 41), (row3 2 11 42), (row3 2 11 43), (row3 2 11 44), (row3 2 11 45), (row3 2 11 46), (row3 2 11 47), (row3 2 11 48), (row3 2 11 49), (row3 2 11 50), (row3 2 11 51), (row3 2 11 52)]

def b009_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 273 462 273), (row3 199 190 198), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 147 137 144), (row3 345 345 347), (row3 148 137 145), (row3 278 462 278)]

theorem b009_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_04_rows b009_04_labels 2320075618542518337494491680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_04_rows b009_04_labels]
    decide +kernel

def b009_05_rows : List Row := [(row3 2 11 53), (row3 2 11 54), (row3 2 11 55), (row3 2 11 56), (row3 2 11 57), (row3 2 11 58), (row3 2 11 59), (row3 2 11 60), (row3 2 11 61), (row3 2 11 62), (row3 2 11 63), (row3 2 12 13), (row3 2 12 14), (row3 2 12 15), (row3 2 12 16), (row3 2 12 17)]

def b009_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 133 137 132), (row3 378 381 382), (row3 49 62 52), (row3 379 380 380), (row3 146 137 143), (row3 273 462 273), (row3 235 462 235), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 233 462 233), (row3 234 462 234), (row3 289 292 292)]

theorem b009_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_05_rows b009_05_labels 241709949983575600583227455240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_05_rows b009_05_labels]
    decide +kernel

def b009_06_rows : List Row := [(row3 2 12 18), (row3 2 12 19), (row3 2 12 20), (row3 2 12 21), (row3 2 12 22), (row3 2 12 23), (row3 2 12 24), (row3 2 12 25), (row3 2 12 26), (row3 2 12 27), (row3 2 12 28), (row3 2 12 29), (row3 2 12 30), (row3 2 12 31), (row3 2 12 32), (row3 2 12 33)]

def b009_06_labels : List Row := [(row3 182 182 178), (row3 289 291 291), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b009_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_06_rows b009_06_labels 188456774502646995878110320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_06_rows b009_06_labels]
    decide +kernel

def b009_07_rows : List Row := [(row3 2 12 34), (row3 2 12 35), (row3 2 12 36), (row3 2 12 37), (row3 2 12 38), (row3 2 12 39), (row3 2 12 40), (row3 2 12 41), (row3 2 12 42), (row3 2 12 43), (row3 2 12 44), (row3 2 12 45), (row3 2 12 46), (row3 2 12 47), (row3 2 12 48), (row3 2 12 49)]

def b009_07_labels : List Row := [(row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291)]

theorem b009_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_07_rows b009_07_labels 16320403907127014839617600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_07_rows b009_07_labels]
    decide +kernel

def b009_08_rows : List Row := [(row3 2 12 50), (row3 2 12 51), (row3 2 12 52), (row3 2 12 53), (row3 2 12 54), (row3 2 12 55), (row3 2 12 56), (row3 2 12 57), (row3 2 12 58), (row3 2 12 59), (row3 2 12 60), (row3 2 12 61), (row3 2 12 62), (row3 2 12 63), (row3 2 13 14), (row3 2 13 15)]

def b009_08_labels : List Row := [(row3 184 184 178), (row3 289 291 291), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291), (row3 149 146 137), (row3 387 361 391), (row3 146 143 137), (row3 289 291 291), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 235 462 235), (row3 288 462 288)]

theorem b009_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_08_rows b009_08_labels 15542521412950824933329241210 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_08_rows b009_08_labels]
    decide +kernel

def b009_09_rows : List Row := [(row3 2 13 16), (row3 2 13 17), (row3 2 13 18), (row3 2 13 19), (row3 2 13 20), (row3 2 13 21), (row3 2 13 22), (row3 2 13 23), (row3 2 13 24), (row3 2 13 25), (row3 2 13 26), (row3 2 13 27), (row3 2 13 28), (row3 2 13 29), (row3 2 13 30), (row3 2 13 31)]

def b009_09_labels : List Row := [(row3 261 462 261), (row3 232 235 235), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 238 462 238), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b009_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_09_rows b009_09_labels 5716952494344518619830400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_09_rows b009_09_labels]
    decide +kernel

def b009_10_rows : List Row := [(row3 2 13 32), (row3 2 13 33), (row3 2 13 34), (row3 2 13 35), (row3 2 13 36), (row3 2 13 37), (row3 2 13 38), (row3 2 13 39), (row3 2 13 40), (row3 2 13 41), (row3 2 13 42), (row3 2 13 43), (row3 2 13 44), (row3 2 13 45), (row3 2 13 46), (row3 2 13 47)]

def b009_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b009_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_10_rows b009_10_labels 163459592599078778184000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_10_rows b009_10_labels]
    decide +kernel

def b009_11_rows : List Row := [(row3 2 13 48), (row3 2 13 49), (row3 2 13 50), (row3 2 13 51), (row3 2 13 52), (row3 2 13 53), (row3 2 13 54), (row3 2 13 55), (row3 2 13 56), (row3 2 13 57), (row3 2 13 58), (row3 2 13 59), (row3 2 13 60), (row3 2 13 61), (row3 2 13 62), (row3 2 13 63)]

def b009_11_labels : List Row := [(row3 261 462 261), (row3 232 235 235), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 191 235 193), (row3 288 273 273), (row3 191 193 235), (row3 273 273 462), (row3 235 235 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273)]

theorem b009_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_11_rows b009_11_labels 731138605060231924967779200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_11_rows b009_11_labels]
    decide +kernel

def b009_12_rows : List Row := [(row3 2 14 15), (row3 2 14 16), (row3 2 14 17), (row3 2 14 18), (row3 2 14 19), (row3 2 14 20), (row3 2 14 21), (row3 2 14 22), (row3 2 14 23), (row3 2 14 24), (row3 2 14 25), (row3 2 14 26), (row3 2 14 27), (row3 2 14 28), (row3 2 14 29), (row3 2 14 30)]

def b009_12_labels : List Row := [(row3 127 137 126), (row3 182 178 182), (row3 289 292 292), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b009_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_12_rows b009_12_labels 8922482214662549683128666600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_12_rows b009_12_labels]
    decide +kernel

def b009_13_rows : List Row := [(row3 2 14 31), (row3 2 14 32), (row3 2 14 33), (row3 2 14 34), (row3 2 14 35), (row3 2 14 36), (row3 2 14 37), (row3 2 14 38), (row3 2 14 39), (row3 2 14 40), (row3 2 14 41), (row3 2 14 42), (row3 2 14 43), (row3 2 14 44), (row3 2 14 45), (row3 2 14 46)]

def b009_13_labels : List Row := [(row3 235 235 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b009_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_13_rows b009_13_labels 3998302287344943729458400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_13_rows b009_13_labels]
    decide +kernel

def b009_14_rows : List Row := [(row3 2 14 47), (row3 2 14 48), (row3 2 14 49), (row3 2 14 50), (row3 2 14 51), (row3 2 14 52), (row3 2 14 53), (row3 2 14 54), (row3 2 14 55), (row3 2 14 56), (row3 2 14 57), (row3 2 14 58), (row3 2 14 59), (row3 2 14 60), (row3 2 14 61), (row3 2 14 62)]

def b009_14_labels : List Row := [(row3 235 235 462), (row3 184 178 184), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 387 391 361), (row3 149 137 146), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291)]

theorem b009_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_14_rows b009_14_labels 15240303326339715606874960410 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_14_rows b009_14_labels]
    decide +kernel

def b009_15_rows : List Row := [(row3 2 14 63), (row3 2 15 16), (row3 2 15 17), (row3 2 15 18), (row3 2 15 19), (row3 2 15 20), (row3 2 15 21), (row3 2 15 22), (row3 2 15 23), (row3 2 15 24), (row3 2 15 25), (row3 2 15 26), (row3 2 15 27), (row3 2 15 28), (row3 2 15 29), (row3 2 15 30)]

def b009_15_labels : List Row := [(row3 146 137 143), (row3 351 350 348), (row3 142 141 136), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 232 232 462), (row3 300 300 462), (row3 127 126 137), (row3 197 196 190), (row3 273 273 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462)]

theorem b009_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b009_15_rows b009_15_labels 14502136008712356530953494480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b009_15_rows b009_15_labels]
    decide +kernel

theorem checked009 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_009 QuarticIntegerComputationalData.ids64_009 11611471291480873696245892425600 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b009_00_rows ++ b009_01_rows) ++ (b009_02_rows ++ b009_03_rows)) ++ ((b009_04_rows ++ b009_05_rows) ++ (b009_06_rows ++ b009_07_rows))) ++ (((b009_08_rows ++ b009_09_rows) ++ (b009_10_rows ++ b009_11_rows)) ++ ((b009_12_rows ++ b009_13_rows) ++ (b009_14_rows ++ b009_15_rows))))
    ((((b009_00_labels ++ b009_01_labels) ++ (b009_02_labels ++ b009_03_labels)) ++ ((b009_04_labels ++ b009_05_labels) ++ (b009_06_labels ++ b009_07_labels))) ++ (((b009_08_labels ++ b009_09_labels) ++ (b009_10_labels ++ b009_11_labels)) ++ ((b009_12_labels ++ b009_13_labels) ++ (b009_14_labels ++ b009_15_labels)))) 11611471291480873696245892425600
  exact ((((b009_00_checked.append (c := 2187794531485192309405633249950) b009_01_checked (by decide +kernel)).append (c := 11312288028418245836094071136060) (b009_02_checked.append (c := 9124493496933053526688437886110) b009_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 11556522831198773729025510810900) ((b009_04_checked.append (c := 244030025602118118920721946920) b009_05_checked (by decide +kernel)).append (c := 244234802780527892931439674840) (b009_06_checked.append (c := 204777178409774010717727920) b009_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11611471291480873696245892425600) (((b009_08_checked.append (c := 15548238365445169451949071610) b009_09_checked (by decide +kernel)).append (c := 16279540430098000455695034810) (b009_10_checked.append (c := 731302064652831003745963200) b009_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 54948460282099967220381614700) ((b009_12_checked.append (c := 8926480516949894626858125000) b009_13_checked (by decide +kernel)).append (c := 38668919852001966764686579890) (b009_14_checked.append (c := 29742439335052072137828454890) b009_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b010_00_rows : List Row := [(row3 2 15 31), (row3 2 15 32), (row3 2 15 33), (row3 2 15 34), (row3 2 15 35), (row3 2 15 36), (row3 2 15 37), (row3 2 15 38), (row3 2 15 39), (row3 2 15 40), (row3 2 15 41), (row3 2 15 42), (row3 2 15 43), (row3 2 15 44), (row3 2 15 45), (row3 2 15 46)]

def b010_00_labels : List Row := [(row3 288 288 462), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 199 198 190), (row3 273 273 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b010_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_00_rows b010_00_labels 108877703206096286134555680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_00_rows b010_00_labels]
    decide +kernel

def b010_01_rows : List Row := [(row3 2 15 47), (row3 2 15 48), (row3 2 15 49), (row3 2 15 50), (row3 2 15 51), (row3 2 15 52), (row3 2 15 53), (row3 2 15 54), (row3 2 15 55), (row3 2 15 56), (row3 2 15 57), (row3 2 15 58), (row3 2 15 59), (row3 2 15 60), (row3 2 15 61), (row3 2 15 62)]

def b010_01_labels : List Row := [(row3 273 273 462), (row3 345 347 345), (row3 147 144 137), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 278 278 462), (row3 148 145 137), (row3 49 52 62), (row3 378 382 381), (row3 133 132 137), (row3 288 288 462), (row3 235 235 462), (row3 273 273 462), (row3 146 143 137)]

theorem b010_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_01_rows b010_01_labels 236755375950753675890704658160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_01_rows b010_01_labels]
    decide +kernel

def b010_02_rows : List Row := [(row3 2 15 63), (row3 2 16 17), (row3 2 16 18), (row3 2 16 19), (row3 2 16 20), (row3 2 16 21), (row3 2 16 22), (row3 2 16 23), (row3 2 16 24), (row3 2 16 25), (row3 2 16 26), (row3 2 16 27), (row3 2 16 28), (row3 2 16 29), (row3 2 16 30), (row3 2 16 31)]

def b010_02_labels : List Row := [(row3 379 380 380), (row3 367 108 84), (row3 295 295 462), (row3 232 232 462), (row3 462 462 462), (row3 237 237 462), (row3 278 278 462), (row3 140 140 178), (row3 164 164 206), (row3 288 288 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 288 288 462)]

theorem b010_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_02_rows b010_02_labels 58547763103507945755557970960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_02_rows b010_02_labels]
    decide +kernel

def b010_03_rows : List Row := [(row3 2 16 32), (row3 2 16 33), (row3 2 16 34), (row3 2 16 35), (row3 2 16 36), (row3 2 16 37), (row3 2 16 38), (row3 2 16 39), (row3 2 16 40), (row3 2 16 41), (row3 2 16 42), (row3 2 16 43), (row3 2 16 44), (row3 2 16 45), (row3 2 16 46), (row3 2 16 47)]

def b010_03_labels : List Row := [(row3 273 273 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 209 209 206), (row3 261 261 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 261 462)]

theorem b010_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_03_rows b010_03_labels 47703733890498965214215280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_03_rows b010_03_labels]
    decide +kernel

def b010_04_rows : List Row := [(row3 2 16 48), (row3 2 16 49), (row3 2 16 50), (row3 2 16 51), (row3 2 16 52), (row3 2 16 53), (row3 2 16 54), (row3 2 16 55), (row3 2 16 56), (row3 2 16 57), (row3 2 16 58), (row3 2 16 59), (row3 2 16 60), (row3 2 16 61), (row3 2 16 62), (row3 2 16 63)]

def b010_04_labels : List Row := [(row3 327 327 327), (row3 182 182 178), (row3 278 278 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 265 265 462), (row3 184 184 178), (row3 68 69 76), (row3 348 351 350), (row3 140 140 178), (row3 288 288 462), (row3 234 234 462), (row3 261 261 462), (row3 184 184 178), (row3 345 345 347)]

theorem b010_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_04_rows b010_04_labels 105743623408209252320118873120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_04_rows b010_04_labels]
    decide +kernel

def b010_05_rows : List Row := [(row3 2 17 18), (row3 2 17 19), (row3 2 17 20), (row3 2 17 21), (row3 2 17 22), (row3 2 17 23), (row3 2 17 24), (row3 2 17 25), (row3 2 17 26), (row3 2 17 27), (row3 2 17 28), (row3 2 17 29), (row3 2 17 30), (row3 2 17 31), (row3 2 17 32), (row3 2 17 33)]

def b010_05_labels : List Row := [(row3 367 108 84), (row3 306 313 313), (row3 228 234 228), (row3 462 244 244), (row3 228 228 234), (row3 306 313 313), (row3 315 318 318), (row3 130 104 104), (row3 315 318 318), (row3 222 224 222), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 222 222 224), (row3 223 223 224), (row3 289 291 291)]

theorem b010_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_05_rows b010_05_labels 54265478829121627570250719020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_05_rows b010_05_labels]
    decide +kernel

def b010_06_rows : List Row := [(row3 2 17 34), (row3 2 17 35), (row3 2 17 36), (row3 2 17 37), (row3 2 17 38), (row3 2 17 39), (row3 2 17 40), (row3 2 17 41), (row3 2 17 42), (row3 2 17 43), (row3 2 17 44), (row3 2 17 45), (row3 2 17 46), (row3 2 17 47), (row3 2 17 48), (row3 2 17 49)]

def b010_06_labels : List Row := [(row3 223 224 223), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 265 268 268), (row3 226 229 229), (row3 265 268 268), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 182 178 182), (row3 306 314 314)]

theorem b010_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_06_rows b010_06_labels 147688939797159950579129760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_06_rows b010_06_labels]
    decide +kernel

def b010_07_rows : List Row := [(row3 2 17 50), (row3 2 17 51), (row3 2 17 52), (row3 2 17 53), (row3 2 17 54), (row3 2 17 55), (row3 2 17 56), (row3 2 17 57), (row3 2 17 58), (row3 2 17 59), (row3 2 17 60), (row3 2 17 61), (row3 2 17 62), (row3 2 17 63), (row3 2 18 19), (row3 2 18 20)]

def b010_07_labels : List Row := [(row3 182 182 178), (row3 289 291 291), (row3 234 462 234), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 388 392 362), (row3 107 106 106), (row3 388 362 392), (row3 147 144 137), (row3 289 291 291), (row3 232 235 235), (row3 289 291 291), (row3 147 137 144), (row3 140 178 140), (row3 278 462 278)]

theorem b010_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_07_rows b010_07_labels 53731248457010353038652971420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_07_rows b010_07_labels]
    decide +kernel

def b010_08_rows : List Row := [(row3 2 18 21), (row3 2 18 22), (row3 2 18 23), (row3 2 18 24), (row3 2 18 25), (row3 2 18 26), (row3 2 18 27), (row3 2 18 28), (row3 2 18 29), (row3 2 18 30), (row3 2 18 31), (row3 2 18 32), (row3 2 18 33), (row3 2 18 34), (row3 2 18 35), (row3 2 18 36)]

def b010_08_labels : List Row := [(row3 237 462 237), (row3 462 462 462), (row3 232 462 232), (row3 232 462 232), (row3 288 462 288), (row3 164 206 164), (row3 288 462 288), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 273 462 273), (row3 234 462 234), (row3 462 462 462)]

theorem b010_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_08_rows b010_08_labels 3351278918006154066849684480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_08_rows b010_08_labels]
    decide +kernel

def b010_09_rows : List Row := [(row3 2 18 37), (row3 2 18 38), (row3 2 18 39), (row3 2 18 40), (row3 2 18 41), (row3 2 18 42), (row3 2 18 43), (row3 2 18 44), (row3 2 18 45), (row3 2 18 46), (row3 2 18 47), (row3 2 18 48), (row3 2 18 49), (row3 2 18 50), (row3 2 18 51), (row3 2 18 52)]

def b010_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 261 462 261), (row3 209 206 209), (row3 261 462 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 182 178 182), (row3 327 327 327), (row3 184 178 184), (row3 265 462 265)]

theorem b010_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_09_rows b010_09_labels 899144443506039769422291600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_09_rows b010_09_labels]
    decide +kernel

def b010_10_rows : List Row := [(row3 2 18 53), (row3 2 18 54), (row3 2 18 55), (row3 2 18 56), (row3 2 18 57), (row3 2 18 58), (row3 2 18 59), (row3 2 18 60), (row3 2 18 61), (row3 2 18 62), (row3 2 18 63), (row3 2 19 20), (row3 2 19 21), (row3 2 19 22), (row3 2 19 23), (row3 2 19 24)]

def b010_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 140 178 140), (row3 348 350 351), (row3 68 76 69), (row3 345 347 345), (row3 184 178 184), (row3 261 462 261), (row3 234 462 234), (row3 288 462 288), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b010_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_10_rows b010_10_labels 104899526191742013863915947920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_10_rows b010_10_labels]
    decide +kernel

def b010_11_rows : List Row := [(row3 2 19 25), (row3 2 19 26), (row3 2 19 27), (row3 2 19 28), (row3 2 19 29), (row3 2 19 30), (row3 2 19 31), (row3 2 19 32), (row3 2 19 33), (row3 2 19 34), (row3 2 19 35), (row3 2 19 36), (row3 2 19 37), (row3 2 19 38), (row3 2 19 39), (row3 2 19 40)]

def b010_11_labels : List Row := [(row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b010_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_11_rows b010_11_labels 32250760181739016703421120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_11_rows b010_11_labels]
    decide +kernel

def b010_12_rows : List Row := [(row3 2 19 41), (row3 2 19 42), (row3 2 19 43), (row3 2 19 44), (row3 2 19 45), (row3 2 19 46), (row3 2 19 47), (row3 2 19 48), (row3 2 19 49), (row3 2 19 50), (row3 2 19 51), (row3 2 19 52), (row3 2 19 53), (row3 2 19 54), (row3 2 19 55), (row3 2 19 56)]

def b010_12_labels : List Row := [(row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 184 184 178), (row3 289 291 291), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291)]

theorem b010_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_12_rows b010_12_labels 284465986084048033323803520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_12_rows b010_12_labels]
    decide +kernel

def b010_13_rows : List Row := [(row3 2 19 57), (row3 2 19 58), (row3 2 19 59), (row3 2 19 60), (row3 2 19 61), (row3 2 19 62), (row3 2 19 63), (row3 2 20 21), (row3 2 20 22), (row3 2 20 23), (row3 2 20 24), (row3 2 20 25), (row3 2 20 26), (row3 2 20 27), (row3 2 20 28), (row3 2 20 29)]

def b010_13_labels : List Row := [(row3 149 146 137), (row3 387 360 390), (row3 148 145 137), (row3 289 291 291), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b010_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_13_rows b010_13_labels 15148222662021577516738447830 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_13_rows b010_13_labels]
    decide +kernel

def b010_14_rows : List Row := [(row3 2 20 30), (row3 2 20 31), (row3 2 20 32), (row3 2 20 33), (row3 2 20 34), (row3 2 20 35), (row3 2 20 36), (row3 2 20 37), (row3 2 20 38), (row3 2 20 39), (row3 2 20 40), (row3 2 20 41), (row3 2 20 42), (row3 2 20 43), (row3 2 20 44), (row3 2 20 45)]

def b010_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b010_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_14_rows b010_14_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_14_rows b010_14_labels]
    decide +kernel

def b010_15_rows : List Row := [(row3 2 20 46), (row3 2 20 47), (row3 2 20 48), (row3 2 20 49), (row3 2 20 50), (row3 2 20 51), (row3 2 20 52), (row3 2 20 53), (row3 2 20 54), (row3 2 20 55), (row3 2 20 56), (row3 2 20 57), (row3 2 20 58), (row3 2 20 59), (row3 2 20 60), (row3 2 20 61)]

def b010_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 265 265 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 278 278 462), (row3 180 180 462), (row3 278 278 462), (row3 234 234 462), (row3 462 462 462)]

theorem b010_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b010_15_rows b010_15_labels 548234026560712639400450400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b010_15_rows b010_15_labels]
    decide +kernel

theorem checked010 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_010 QuarticIntegerComputationalData.ids64_010 634511005708293343992650778270 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b010_00_rows ++ b010_01_rows) ++ (b010_02_rows ++ b010_03_rows)) ++ ((b010_04_rows ++ b010_05_rows) ++ (b010_06_rows ++ b010_07_rows))) ++ (((b010_08_rows ++ b010_09_rows) ++ (b010_10_rows ++ b010_11_rows)) ++ ((b010_12_rows ++ b010_13_rows) ++ (b010_14_rows ++ b010_15_rows))))
    ((((b010_00_labels ++ b010_01_labels) ++ (b010_02_labels ++ b010_03_labels)) ++ ((b010_04_labels ++ b010_05_labels) ++ (b010_06_labels ++ b010_07_labels))) ++ (((b010_08_labels ++ b010_09_labels) ++ (b010_10_labels ++ b010_11_labels)) ++ ((b010_12_labels ++ b010_13_labels) ++ (b010_14_labels ++ b010_15_labels)))) 634511005708293343992650778270
  exact ((((b010_00_checked.append (c := 236864253653959772176839213840) b010_01_checked (by decide +kernel)).append (c := 295459720491358216897611400080) (b010_02_checked.append (c := 58595466837398444720772186240) b010_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 509347760125496609777213093400) ((b010_04_checked.append (c := 160009102237330879890369592140) b010_05_checked (by decide +kernel)).append (c := 213888039634138392879601693320) (b010_06_checked.append (c := 53878937396807512989232101180) b010_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 634511005708293343992650778270) (((b010_08_checked.append (c := 4250423361512193836271976080) b010_09_checked (by decide +kernel)).append (c := 109182200313435946716891345120) (b010_10_checked.append (c := 104931776951923752880619369040) b010_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 125163245582796734215437684870) ((b010_12_checked.append (c := 15432688648105625550062251350) b010_13_checked (by decide +kernel)).append (c := 15981045269360787498546339750) (b010_14_checked.append (c := 548356621255161948484088400) b010_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b011_00_rows : List Row := [(row3 2 20 62), (row3 2 20 63), (row3 2 21 22), (row3 2 21 23), (row3 2 21 24), (row3 2 21 25), (row3 2 21 26), (row3 2 21 27), (row3 2 21 28), (row3 2 21 29), (row3 2 21 30), (row3 2 21 31), (row3 2 21 32), (row3 2 21 33), (row3 2 21 34), (row3 2 21 35)]

def b011_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_00_rows b011_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_00_rows b011_00_labels]
    decide +kernel

def b011_01_rows : List Row := [(row3 2 21 36), (row3 2 21 37), (row3 2 21 38), (row3 2 21 39), (row3 2 21 40), (row3 2 21 41), (row3 2 21 42), (row3 2 21 43), (row3 2 21 44), (row3 2 21 45), (row3 2 21 46), (row3 2 21 47), (row3 2 21 48), (row3 2 21 49), (row3 2 21 50), (row3 2 21 51)]

def b011_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_01_rows b011_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_01_rows b011_01_labels]
    decide +kernel

def b011_02_rows : List Row := [(row3 2 21 52), (row3 2 21 53), (row3 2 21 54), (row3 2 21 55), (row3 2 21 56), (row3 2 21 57), (row3 2 21 58), (row3 2 21 59), (row3 2 21 60), (row3 2 21 61), (row3 2 21 62), (row3 2 21 63), (row3 2 22 23), (row3 2 22 24), (row3 2 22 25), (row3 2 22 26)]

def b011_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b011_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_02_rows b011_02_labels 20783407424127807275208000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_02_rows b011_02_labels]
    decide +kernel

def b011_03_rows : List Row := [(row3 2 22 27), (row3 2 22 28), (row3 2 22 29), (row3 2 22 30), (row3 2 22 31), (row3 2 22 32), (row3 2 22 33), (row3 2 22 34), (row3 2 22 35), (row3 2 22 36), (row3 2 22 37), (row3 2 22 38), (row3 2 22 39), (row3 2 22 40), (row3 2 22 41), (row3 2 22 42)]

def b011_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b011_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_03_rows b011_03_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_03_rows b011_03_labels]
    decide +kernel

def b011_04_rows : List Row := [(row3 2 22 43), (row3 2 22 44), (row3 2 22 45), (row3 2 22 46), (row3 2 22 47), (row3 2 22 48), (row3 2 22 49), (row3 2 22 50), (row3 2 22 51), (row3 2 22 52), (row3 2 22 53), (row3 2 22 54), (row3 2 22 55), (row3 2 22 56), (row3 2 22 57), (row3 2 22 58)]

def b011_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 462 265), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 180 462 180), (row3 278 462 278), (row3 234 462 234)]

theorem b011_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_04_rows b011_04_labels 539038252460374385415102000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_04_rows b011_04_labels]
    decide +kernel

def b011_05_rows : List Row := [(row3 2 22 59), (row3 2 22 60), (row3 2 22 61), (row3 2 22 62), (row3 2 22 63), (row3 2 23 24), (row3 2 23 25), (row3 2 23 26), (row3 2 23 27), (row3 2 23 28), (row3 2 23 29), (row3 2 23 30), (row3 2 23 31), (row3 2 23 32), (row3 2 23 33), (row3 2 23 34)]

def b011_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_05_rows b011_05_labels 41446534282077270688769520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_05_rows b011_05_labels]
    decide +kernel

def b011_06_rows : List Row := [(row3 2 23 35), (row3 2 23 36), (row3 2 23 37), (row3 2 23 38), (row3 2 23 39), (row3 2 23 40), (row3 2 23 41), (row3 2 23 42), (row3 2 23 43), (row3 2 23 44), (row3 2 23 45), (row3 2 23 46), (row3 2 23 47), (row3 2 23 48), (row3 2 23 49), (row3 2 23 50)]

def b011_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 184 178 184), (row3 289 291 291), (row3 234 234 462)]

theorem b011_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_06_rows b011_06_labels 101108601258179496579591120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_06_rows b011_06_labels]
    decide +kernel

def b011_07_rows : List Row := [(row3 2 23 51), (row3 2 23 52), (row3 2 23 53), (row3 2 23 54), (row3 2 23 55), (row3 2 23 56), (row3 2 23 57), (row3 2 23 58), (row3 2 23 59), (row3 2 23 60), (row3 2 23 61), (row3 2 23 62), (row3 2 23 63), (row3 2 24 25), (row3 2 24 26), (row3 2 24 27)]

def b011_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 387 390 360), (row3 149 137 146), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 148 137 145), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_07_rows b011_07_labels 15335969827000227804698134230 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_07_rows b011_07_labels]
    decide +kernel

def b011_08_rows : List Row := [(row3 2 24 28), (row3 2 24 29), (row3 2 24 30), (row3 2 24 31), (row3 2 24 32), (row3 2 24 33), (row3 2 24 34), (row3 2 24 35), (row3 2 24 36), (row3 2 24 37), (row3 2 24 38), (row3 2 24 39), (row3 2 24 40), (row3 2 24 41), (row3 2 24 42), (row3 2 24 43)]

def b011_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_08_rows b011_08_labels 10443788674277492624545920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_08_rows b011_08_labels]
    decide +kernel

def b011_09_rows : List Row := [(row3 2 24 44), (row3 2 24 45), (row3 2 24 46), (row3 2 24 47), (row3 2 24 48), (row3 2 24 49), (row3 2 24 50), (row3 2 24 51), (row3 2 24 52), (row3 2 24 53), (row3 2 24 54), (row3 2 24 55), (row3 2 24 56), (row3 2 24 57), (row3 2 24 58), (row3 2 24 59)]

def b011_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 209 206 209), (row3 265 268 268), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 265 266 266), (row3 339 342 328), (row3 199 190 198), (row3 265 266 266), (row3 238 238 462)]

theorem b011_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_09_rows b011_09_labels 4983277691524144889588243430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_09_rows b011_09_labels]
    decide +kernel

def b011_10_rows : List Row := [(row3 2 24 60), (row3 2 24 61), (row3 2 24 62), (row3 2 24 63), (row3 2 25 26), (row3 2 25 27), (row3 2 25 28), (row3 2 25 29), (row3 2 25 30), (row3 2 25 31), (row3 2 25 32), (row3 2 25 33), (row3 2 25 34), (row3 2 25 35), (row3 2 25 36), (row3 2 25 37)]

def b011_10_labels : List Row := [(row3 462 462 462), (row3 238 238 462), (row3 265 266 266), (row3 199 190 198), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_10_rows b011_10_labels 80740770682880322468209520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_10_rows b011_10_labels]
    decide +kernel

def b011_11_rows : List Row := [(row3 2 25 38), (row3 2 25 39), (row3 2 25 40), (row3 2 25 41), (row3 2 25 42), (row3 2 25 43), (row3 2 25 44), (row3 2 25 45), (row3 2 25 46), (row3 2 25 47), (row3 2 25 48), (row3 2 25 49), (row3 2 25 50), (row3 2 25 51), (row3 2 25 52), (row3 2 25 53)]

def b011_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 226 229 229), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_11_rows b011_11_labels 6024351667584936303878400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_11_rows b011_11_labels]
    decide +kernel

def b011_12_rows : List Row := [(row3 2 25 54), (row3 2 25 55), (row3 2 25 56), (row3 2 25 57), (row3 2 25 58), (row3 2 25 59), (row3 2 25 60), (row3 2 25 61), (row3 2 25 62), (row3 2 25 63), (row3 2 26 27), (row3 2 26 28), (row3 2 26 29), (row3 2 26 30), (row3 2 26 31), (row3 2 26 32)]

def b011_12_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 191 235 193), (row3 288 288 288), (row3 191 193 235), (row3 273 273 462), (row3 235 235 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_12_rows b011_12_labels 738630663129602698703875200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_12_rows b011_12_labels]
    decide +kernel

def b011_13_rows : List Row := [(row3 2 26 33), (row3 2 26 34), (row3 2 26 35), (row3 2 26 36), (row3 2 26 37), (row3 2 26 38), (row3 2 26 39), (row3 2 26 40), (row3 2 26 41), (row3 2 26 42), (row3 2 26 43), (row3 2 26 44), (row3 2 26 45), (row3 2 26 46), (row3 2 26 47), (row3 2 26 48)]

def b011_13_labels : List Row := [(row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 255 256 256), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237)]

theorem b011_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_13_rows b011_13_labels 6202430176703316001831920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_13_rows b011_13_labels]
    decide +kernel

def b011_14_rows : List Row := [(row3 2 26 49), (row3 2 26 50), (row3 2 26 51), (row3 2 26 52), (row3 2 26 53), (row3 2 26 54), (row3 2 26 55), (row3 2 26 56), (row3 2 26 57), (row3 2 26 58), (row3 2 26 59), (row3 2 26 60), (row3 2 26 61), (row3 2 26 62), (row3 2 26 63), (row3 2 27 28)]

def b011_14_labels : List Row := [(row3 265 268 268), (row3 209 209 206), (row3 265 266 266), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 199 198 190), (row3 339 328 342), (row3 199 198 190), (row3 265 266 266), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462)]

theorem b011_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_14_rows b011_14_labels 5059115143775675963755558950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_14_rows b011_14_labels]
    decide +kernel

def b011_15_rows : List Row := [(row3 2 27 29), (row3 2 27 30), (row3 2 27 31), (row3 2 27 32), (row3 2 27 33), (row3 2 27 34), (row3 2 27 35), (row3 2 27 36), (row3 2 27 37), (row3 2 27 38), (row3 2 27 39), (row3 2 27 40), (row3 2 27 41), (row3 2 27 42), (row3 2 27 43), (row3 2 27 44)]

def b011_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462)]

theorem b011_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b011_15_rows b011_15_labels 121705541119974164220000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b011_15_rows b011_15_labels]
    decide +kernel

theorem checked011 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_011 QuarticIntegerComputationalData.ids64_011 26923025762291425667350806210 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b011_00_rows ++ b011_01_rows) ++ (b011_02_rows ++ b011_03_rows)) ++ ((b011_04_rows ++ b011_05_rows) ++ (b011_06_rows ++ b011_07_rows))) ++ (((b011_08_rows ++ b011_09_rows) ++ (b011_10_rows ++ b011_11_rows)) ++ ((b011_12_rows ++ b011_13_rows) ++ (b011_14_rows ++ b011_15_rows))))
    ((((b011_00_labels ++ b011_01_labels) ++ (b011_02_labels ++ b011_03_labels)) ++ ((b011_04_labels ++ b011_05_labels) ++ (b011_06_labels ++ b011_07_labels))) ++ (((b011_08_labels ++ b011_09_labels) ++ (b011_10_labels ++ b011_11_labels)) ++ ((b011_12_labels ++ b011_13_labels) ++ (b011_14_labels ++ b011_15_labels)))) 26923025762291425667350806210
  exact ((((b011_00_checked.append (c := 0) b011_01_checked (by decide +kernel)).append (c := 20906002118577116358846000) (b011_02_checked.append (c := 20906002118577116358846000) b011_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 16038469217119436073740442870) ((b011_04_checked.append (c := 580484786742451656103871520) b011_05_checked (by decide +kernel)).append (c := 16017563215000858957381596870) (b011_06_checked.append (c := 15437078428258407301277725350) b011_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 26923025762291425667350806210) (((b011_08_checked.append (c := 4993721480198422382212789350) b011_09_checked (by decide +kernel)).append (c := 5080486602548887640984877270) (b011_10_checked.append (c := 86765122350465258772087920) b011_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 10884556545171989593610363340) ((b011_12_checked.append (c := 744833093306306014705707120) b011_13_checked (by decide +kernel)).append (c := 5804069942623101952625486070) (b011_14_checked.append (c := 5059236849316795937919778950) b011_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b012_00_rows : List Row := [(row3 2 27 45), (row3 2 27 46), (row3 2 27 47), (row3 2 27 48), (row3 2 27 49), (row3 2 27 50), (row3 2 27 51), (row3 2 27 52), (row3 2 27 53), (row3 2 27 54), (row3 2 27 55), (row3 2 27 56), (row3 2 27 57), (row3 2 27 58), (row3 2 27 59), (row3 2 27 60)]

def b012_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 273 273 462), (row3 193 193 462), (row3 273 273 462), (row3 235 235 462)]

theorem b012_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_00_rows b012_00_labels 365489351040475092933633600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_00_rows b012_00_labels]
    decide +kernel

def b012_01_rows : List Row := [(row3 2 27 61), (row3 2 27 62), (row3 2 27 63), (row3 2 28 29), (row3 2 28 30), (row3 2 28 31), (row3 2 28 32), (row3 2 28 33), (row3 2 28 34), (row3 2 28 35), (row3 2 28 36), (row3 2 28 37), (row3 2 28 38), (row3 2 28 39), (row3 2 28 40), (row3 2 28 41)]

def b012_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_01_rows b012_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_01_rows b012_01_labels]
    decide +kernel

def b012_02_rows : List Row := [(row3 2 28 42), (row3 2 28 43), (row3 2 28 44), (row3 2 28 45), (row3 2 28 46), (row3 2 28 47), (row3 2 28 48), (row3 2 28 49), (row3 2 28 50), (row3 2 28 51), (row3 2 28 52), (row3 2 28 53), (row3 2 28 54), (row3 2 28 55), (row3 2 28 56), (row3 2 28 57)]

def b012_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_02_rows b012_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_02_rows b012_02_labels]
    decide +kernel

def b012_03_rows : List Row := [(row3 2 28 58), (row3 2 28 59), (row3 2 28 60), (row3 2 28 61), (row3 2 28 62), (row3 2 28 63), (row3 2 29 30), (row3 2 29 31), (row3 2 29 32), (row3 2 29 33), (row3 2 29 34), (row3 2 29 35), (row3 2 29 36), (row3 2 29 37), (row3 2 29 38), (row3 2 29 39)]

def b012_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_03_rows b012_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_03_rows b012_03_labels]
    decide +kernel

def b012_04_rows : List Row := [(row3 2 29 40), (row3 2 29 41), (row3 2 29 42), (row3 2 29 43), (row3 2 29 44), (row3 2 29 45), (row3 2 29 46), (row3 2 29 47), (row3 2 29 48), (row3 2 29 49), (row3 2 29 50), (row3 2 29 51), (row3 2 29 52), (row3 2 29 53), (row3 2 29 54), (row3 2 29 55)]

def b012_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_04_rows b012_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_04_rows b012_04_labels]
    decide +kernel

def b012_05_rows : List Row := [(row3 2 29 56), (row3 2 29 57), (row3 2 29 58), (row3 2 29 59), (row3 2 29 60), (row3 2 29 61), (row3 2 29 62), (row3 2 29 63), (row3 2 30 31), (row3 2 30 32), (row3 2 30 33), (row3 2 30 34), (row3 2 30 35), (row3 2 30 36), (row3 2 30 37), (row3 2 30 38)]

def b012_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_05_rows b012_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_05_rows b012_05_labels]
    decide +kernel

def b012_06_rows : List Row := [(row3 2 30 39), (row3 2 30 40), (row3 2 30 41), (row3 2 30 42), (row3 2 30 43), (row3 2 30 44), (row3 2 30 45), (row3 2 30 46), (row3 2 30 47), (row3 2 30 48), (row3 2 30 49), (row3 2 30 50), (row3 2 30 51), (row3 2 30 52), (row3 2 30 53), (row3 2 30 54)]

def b012_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_06_rows b012_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_06_rows b012_06_labels]
    decide +kernel

def b012_07_rows : List Row := [(row3 2 30 55), (row3 2 30 56), (row3 2 30 57), (row3 2 30 58), (row3 2 30 59), (row3 2 30 60), (row3 2 30 61), (row3 2 30 62), (row3 2 30 63), (row3 2 31 32), (row3 2 31 33), (row3 2 31 34), (row3 2 31 35), (row3 2 31 36), (row3 2 31 37), (row3 2 31 38)]

def b012_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_07_rows b012_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_07_rows b012_07_labels]
    decide +kernel

def b012_08_rows : List Row := [(row3 2 31 39), (row3 2 31 40), (row3 2 31 41), (row3 2 31 42), (row3 2 31 43), (row3 2 31 44), (row3 2 31 45), (row3 2 31 46), (row3 2 31 47), (row3 2 31 48), (row3 2 31 49), (row3 2 31 50), (row3 2 31 51), (row3 2 31 52), (row3 2 31 53), (row3 2 31 54)]

def b012_08_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_08_rows b012_08_labels 2516451353719344958543200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_08_rows b012_08_labels]
    decide +kernel

def b012_09_rows : List Row := [(row3 2 31 55), (row3 2 31 56), (row3 2 31 57), (row3 2 31 58), (row3 2 31 59), (row3 2 31 60), (row3 2 31 61), (row3 2 31 62), (row3 2 31 63), (row3 2 32 33), (row3 2 32 34), (row3 2 32 35), (row3 2 32 36), (row3 2 32 37), (row3 2 32 38), (row3 2 32 39)]

def b012_09_labels : List Row := [(row3 235 462 235), (row3 193 462 193), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_09_rows b012_09_labels 363094605227875722139310400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_09_rows b012_09_labels]
    decide +kernel

def b012_10_rows : List Row := [(row3 2 32 40), (row3 2 32 41), (row3 2 32 42), (row3 2 32 43), (row3 2 32 44), (row3 2 32 45), (row3 2 32 46), (row3 2 32 47), (row3 2 32 48), (row3 2 32 49), (row3 2 32 50), (row3 2 32 51), (row3 2 32 52), (row3 2 32 53), (row3 2 32 54), (row3 2 32 55)]

def b012_10_labels : List Row := [(row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 223 224 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237)]

theorem b012_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_10_rows b012_10_labels 16834355646024146995280880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_10_rows b012_10_labels]
    decide +kernel

def b012_11_rows : List Row := [(row3 2 32 56), (row3 2 32 57), (row3 2 32 58), (row3 2 32 59), (row3 2 32 60), (row3 2 32 61), (row3 2 32 62), (row3 2 32 63), (row3 2 33 34), (row3 2 33 35), (row3 2 33 36), (row3 2 33 37), (row3 2 33 38), (row3 2 33 39), (row3 2 33 40), (row3 2 33 41)]

def b012_11_labels : List Row := [(row3 168 94 333), (row3 261 288 290), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 261 462 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_11_rows b012_11_labels 3244887822336623358217272000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_11_rows b012_11_labels]
    decide +kernel

def b012_12_rows : List Row := [(row3 2 33 42), (row3 2 33 43), (row3 2 33 44), (row3 2 33 45), (row3 2 33 46), (row3 2 33 47), (row3 2 33 48), (row3 2 33 49), (row3 2 33 50), (row3 2 33 51), (row3 2 33 52), (row3 2 33 53), (row3 2 33 54), (row3 2 33 55), (row3 2 33 56), (row3 2 33 57)]

def b012_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 161 176 176)]

theorem b012_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_12_rows b012_12_labels 324746967813662106837313560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_12_rows b012_12_labels]
    decide +kernel

def b012_13_rows : List Row := [(row3 2 33 58), (row3 2 33 59), (row3 2 33 60), (row3 2 33 61), (row3 2 33 62), (row3 2 33 63), (row3 2 34 35), (row3 2 34 36), (row3 2 34 37), (row3 2 34 38), (row3 2 34 39), (row3 2 34 40), (row3 2 34 41), (row3 2 34 42), (row3 2 34 43), (row3 2 34 44)]

def b012_13_labels : List Row := [(row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_13_rows b012_13_labels 63189231567211197286047000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_13_rows b012_13_labels]
    decide +kernel

def b012_14_rows : List Row := [(row3 2 34 45), (row3 2 34 46), (row3 2 34 47), (row3 2 34 48), (row3 2 34 49), (row3 2 34 50), (row3 2 34 51), (row3 2 34 52), (row3 2 34 53), (row3 2 34 54), (row3 2 34 55), (row3 2 34 56), (row3 2 34 57), (row3 2 34 58), (row3 2 34 59), (row3 2 34 60)]

def b012_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 223 224), (row3 273 273 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 261 290 288), (row3 168 333 94), (row3 261 261 462), (row3 237 237 462)]

theorem b012_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_14_rows b012_14_labels 3259436008750416648981650880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_14_rows b012_14_labels]
    decide +kernel

def b012_15_rows : List Row := [(row3 2 34 61), (row3 2 34 62), (row3 2 34 63), (row3 2 35 36), (row3 2 35 37), (row3 2 35 38), (row3 2 35 39), (row3 2 35 40), (row3 2 35 41), (row3 2 35 42), (row3 2 35 43), (row3 2 35 44), (row3 2 35 45), (row3 2 35 46), (row3 2 35 47), (row3 2 35 48)]

def b012_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b012_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b012_15_rows b012_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b012_15_rows b012_15_labels]
    decide +kernel

theorem checked012 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_012 QuarticIntegerComputationalData.ids64_012 7640194793736007618349051520 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b012_00_rows ++ b012_01_rows) ++ (b012_02_rows ++ b012_03_rows)) ++ ((b012_04_rows ++ b012_05_rows) ++ (b012_06_rows ++ b012_07_rows))) ++ (((b012_08_rows ++ b012_09_rows) ++ (b012_10_rows ++ b012_11_rows)) ++ ((b012_12_rows ++ b012_13_rows) ++ (b012_14_rows ++ b012_15_rows))))
    ((((b012_00_labels ++ b012_01_labels) ++ (b012_02_labels ++ b012_03_labels)) ++ ((b012_04_labels ++ b012_05_labels) ++ (b012_06_labels ++ b012_07_labels))) ++ (((b012_08_labels ++ b012_09_labels) ++ (b012_10_labels ++ b012_11_labels)) ++ ((b012_12_labels ++ b012_13_labels) ++ (b012_14_labels ++ b012_15_labels)))) 7640194793736007618349051520
  exact ((((b012_00_checked.append (c := 365489351040475092933633600) b012_01_checked (by decide +kernel)).append (c := 365489351040475092933633600) (b012_02_checked.append (c := 0) b012_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 365489351040475092933633600) ((b012_04_checked.append (c := 0) b012_05_checked (by decide +kernel)).append (c := 0) (b012_06_checked.append (c := 0) b012_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7640194793736007618349051520) (((b012_08_checked.append (c := 365611056581595067097853600) b012_09_checked (by decide +kernel)).append (c := 3627333234564242572310406480) (b012_10_checked.append (c := 3261722177982647505212552880) b012_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 7274705442695532525415417920) ((b012_12_checked.append (c := 387936199380873304123360560) b012_13_checked (by decide +kernel)).append (c := 3647372208131289953105011440) (b012_14_checked.append (c := 3259436008750416648981650880) b012_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b013_00_rows : List Row := [(row3 2 35 49), (row3 2 35 50), (row3 2 35 51), (row3 2 35 52), (row3 2 35 53), (row3 2 35 54), (row3 2 35 55), (row3 2 35 56), (row3 2 35 57), (row3 2 35 58), (row3 2 35 59), (row3 2 35 60), (row3 2 35 61), (row3 2 35 62), (row3 2 35 63), (row3 2 36 37)]

def b013_00_labels : List Row := [(row3 462 248 248), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_00_rows b013_00_labels 62082383370327939168985500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_00_rows b013_00_labels]
    decide +kernel

def b013_01_rows : List Row := [(row3 2 36 38), (row3 2 36 39), (row3 2 36 40), (row3 2 36 41), (row3 2 36 42), (row3 2 36 43), (row3 2 36 44), (row3 2 36 45), (row3 2 36 46), (row3 2 36 47), (row3 2 36 48), (row3 2 36 49), (row3 2 36 50), (row3 2 36 51), (row3 2 36 52), (row3 2 36 53)]

def b013_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_01_rows b013_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_01_rows b013_01_labels]
    decide +kernel

def b013_02_rows : List Row := [(row3 2 36 54), (row3 2 36 55), (row3 2 36 56), (row3 2 36 57), (row3 2 36 58), (row3 2 36 59), (row3 2 36 60), (row3 2 36 61), (row3 2 36 62), (row3 2 36 63), (row3 2 37 38), (row3 2 37 39), (row3 2 37 40), (row3 2 37 41), (row3 2 37 42), (row3 2 37 43)]

def b013_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_02_rows b013_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_02_rows b013_02_labels]
    decide +kernel

def b013_03_rows : List Row := [(row3 2 37 44), (row3 2 37 45), (row3 2 37 46), (row3 2 37 47), (row3 2 37 48), (row3 2 37 49), (row3 2 37 50), (row3 2 37 51), (row3 2 37 52), (row3 2 37 53), (row3 2 37 54), (row3 2 37 55), (row3 2 37 56), (row3 2 37 57), (row3 2 37 58), (row3 2 37 59)]

def b013_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_03_rows b013_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_03_rows b013_03_labels]
    decide +kernel

def b013_04_rows : List Row := [(row3 2 37 60), (row3 2 37 61), (row3 2 37 62), (row3 2 37 63), (row3 2 38 39), (row3 2 38 40), (row3 2 38 41), (row3 2 38 42), (row3 2 38 43), (row3 2 38 44), (row3 2 38 45), (row3 2 38 46), (row3 2 38 47), (row3 2 38 48), (row3 2 38 49), (row3 2 38 50)]

def b013_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_04_rows b013_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_04_rows b013_04_labels]
    decide +kernel

def b013_05_rows : List Row := [(row3 2 38 51), (row3 2 38 52), (row3 2 38 53), (row3 2 38 54), (row3 2 38 55), (row3 2 38 56), (row3 2 38 57), (row3 2 38 58), (row3 2 38 59), (row3 2 38 60), (row3 2 38 61), (row3 2 38 62), (row3 2 38 63), (row3 2 39 40), (row3 2 39 41), (row3 2 39 42)]

def b013_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_05_rows b013_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_05_rows b013_05_labels]
    decide +kernel

def b013_06_rows : List Row := [(row3 2 39 43), (row3 2 39 44), (row3 2 39 45), (row3 2 39 46), (row3 2 39 47), (row3 2 39 48), (row3 2 39 49), (row3 2 39 50), (row3 2 39 51), (row3 2 39 52), (row3 2 39 53), (row3 2 39 54), (row3 2 39 55), (row3 2 39 56), (row3 2 39 57), (row3 2 39 58)]

def b013_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462)]

theorem b013_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_06_rows b013_06_labels 61708800319122667786321500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_06_rows b013_06_labels]
    decide +kernel

def b013_07_rows : List Row := [(row3 2 39 59), (row3 2 39 60), (row3 2 39 61), (row3 2 39 62), (row3 2 39 63), (row3 2 40 41), (row3 2 40 42), (row3 2 40 43), (row3 2 40 44), (row3 2 40 45), (row3 2 40 46), (row3 2 40 47), (row3 2 40 48), (row3 2 40 49), (row3 2 40 50), (row3 2 40 51)]

def b013_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 164 206 164), (row3 315 318 318), (row3 232 232 462), (row3 462 462 462)]

theorem b013_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_07_rows b013_07_labels 3396130402047914687671584000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_07_rows b013_07_labels]
    decide +kernel

def b013_08_rows : List Row := [(row3 2 40 52), (row3 2 40 53), (row3 2 40 54), (row3 2 40 55), (row3 2 40 56), (row3 2 40 57), (row3 2 40 58), (row3 2 40 59), (row3 2 40 60), (row3 2 40 61), (row3 2 40 62), (row3 2 40 63), (row3 2 41 42), (row3 2 41 43), (row3 2 41 44), (row3 2 41 45)]

def b013_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 265 266 266), (row3 385 426 77), (row3 109 110 111), (row3 265 302 302), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 265 266 266), (row3 197 190 196), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_08_rows b013_08_labels 65514508667945645939505097560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_08_rows b013_08_labels]
    decide +kernel

def b013_09_rows : List Row := [(row3 2 41 46), (row3 2 41 47), (row3 2 41 48), (row3 2 41 49), (row3 2 41 50), (row3 2 41 51), (row3 2 41 52), (row3 2 41 53), (row3 2 41 54), (row3 2 41 55), (row3 2 41 56), (row3 2 41 57), (row3 2 41 58), (row3 2 41 59), (row3 2 41 60), (row3 2 41 61)]

def b013_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 130 104 104), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 121 85 369), (row3 379 380 380), (row3 121 369 85), (row3 273 273 462), (row3 235 235 462), (row3 462 462 462)]

theorem b013_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_09_rows b013_09_labels 38035749566581585517874710880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_09_rows b013_09_labels]
    decide +kernel

def b013_10_rows : List Row := [(row3 2 41 62), (row3 2 41 63), (row3 2 42 43), (row3 2 42 44), (row3 2 42 45), (row3 2 42 46), (row3 2 42 47), (row3 2 42 48), (row3 2 42 49), (row3 2 42 50), (row3 2 42 51), (row3 2 42 52), (row3 2 42 53), (row3 2 42 54), (row3 2 42 55), (row3 2 42 56)]

def b013_10_labels : List Row := [(row3 235 462 235), (row3 273 462 273), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 315 318 318), (row3 164 164 206), (row3 265 266 266), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 302 302)]

theorem b013_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_10_rows b013_10_labels 3568976101013125928860792620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_10_rows b013_10_labels]
    decide +kernel

def b013_11_rows : List Row := [(row3 2 42 57), (row3 2 42 58), (row3 2 42 59), (row3 2 42 60), (row3 2 42 61), (row3 2 42 62), (row3 2 42 63), (row3 2 43 44), (row3 2 43 45), (row3 2 43 46), (row3 2 43 47), (row3 2 43 48), (row3 2 43 49), (row3 2 43 50), (row3 2 43 51), (row3 2 43 52)]

def b013_11_labels : List Row := [(row3 109 111 110), (row3 385 77 426), (row3 197 196 190), (row3 265 266 266), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 222 222 224), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462)]

theorem b013_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_11_rows b013_11_labels 65393329193881505660229283260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_11_rows b013_11_labels]
    decide +kernel

def b013_12_rows : List Row := [(row3 2 43 53), (row3 2 43 54), (row3 2 43 55), (row3 2 43 56), (row3 2 43 57), (row3 2 43 58), (row3 2 43 59), (row3 2 43 60), (row3 2 43 61), (row3 2 43 62), (row3 2 43 63), (row3 2 44 45), (row3 2 44 46), (row3 2 44 47), (row3 2 44 48), (row3 2 44 49)]

def b013_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 273 304 295), (row3 122 369 86), (row3 288 288 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246)]

theorem b013_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_12_rows b013_12_labels 9963182591418108033014789160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_12_rows b013_12_labels]
    decide +kernel

def b013_13_rows : List Row := [(row3 2 44 50), (row3 2 44 51), (row3 2 44 52), (row3 2 44 53), (row3 2 44 54), (row3 2 44 55), (row3 2 44 56), (row3 2 44 57), (row3 2 44 58), (row3 2 44 59), (row3 2 44 60), (row3 2 44 61), (row3 2 44 62), (row3 2 44 63), (row3 2 45 46), (row3 2 45 47)]

def b013_13_labels : List Row := [(row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_13_rows b013_13_labels 93382996147132054181215500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_13_rows b013_13_labels]
    decide +kernel

def b013_14_rows : List Row := [(row3 2 45 48), (row3 2 45 49), (row3 2 45 50), (row3 2 45 51), (row3 2 45 52), (row3 2 45 53), (row3 2 45 54), (row3 2 45 55), (row3 2 45 56), (row3 2 45 57), (row3 2 45 58), (row3 2 45 59), (row3 2 45 60), (row3 2 45 61), (row3 2 45 62), (row3 2 45 63)]

def b013_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_14_rows b013_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_14_rows b013_14_labels]
    decide +kernel

def b013_15_rows : List Row := [(row3 2 46 47), (row3 2 46 48), (row3 2 46 49), (row3 2 46 50), (row3 2 46 51), (row3 2 46 52), (row3 2 46 53), (row3 2 46 54), (row3 2 46 55), (row3 2 46 56), (row3 2 46 57), (row3 2 46 58), (row3 2 46 59), (row3 2 46 60), (row3 2 46 61), (row3 2 46 62)]

def b013_15_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b013_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b013_15_rows b013_15_labels 92141002329153392520166500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b013_15_rows b013_15_labels]
    decide +kernel

theorem checked013 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_013 QuarticIntegerComputationalData.ids64_013 186181191705053621820812946480 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b013_00_rows ++ b013_01_rows) ++ (b013_02_rows ++ b013_03_rows)) ++ ((b013_04_rows ++ b013_05_rows) ++ (b013_06_rows ++ b013_07_rows))) ++ (((b013_08_rows ++ b013_09_rows) ++ (b013_10_rows ++ b013_11_rows)) ++ ((b013_12_rows ++ b013_13_rows) ++ (b013_14_rows ++ b013_15_rows))))
    ((((b013_00_labels ++ b013_01_labels) ++ (b013_02_labels ++ b013_03_labels)) ++ ((b013_04_labels ++ b013_05_labels) ++ (b013_06_labels ++ b013_07_labels))) ++ (((b013_08_labels ++ b013_09_labels) ++ (b013_10_labels ++ b013_11_labels)) ++ ((b013_12_labels ++ b013_13_labels) ++ (b013_14_labels ++ b013_15_labels)))) 186181191705053621820812946480
  exact ((((b013_00_checked.append (c := 62082383370327939168985500) b013_01_checked (by decide +kernel)).append (c := 62082383370327939168985500) (b013_02_checked.append (c := 0) b013_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3519921585737365294626891000) ((b013_04_checked.append (c := 0) b013_05_checked (by decide +kernel)).append (c := 3457839202367037355457905500) (b013_06_checked.append (c := 3457839202367037355457905500) b013_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 186181191705053621820812946480) (((b013_08_checked.append (c := 103550258234527231457379808440) b013_09_checked (by decide +kernel)).append (c := 172512563529421863046469884320) (b013_10_checked.append (c := 68962305294894631589090075880) b013_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 182661270119316256526186055480) ((b013_12_checked.append (c := 10056565587565240087196004660) b013_13_checked (by decide +kernel)).append (c := 10148706589894393479716171160) (b013_14_checked.append (c := 92141002329153392520166500) b013_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b014_00_rows : List Row := [(row3 2 46 63), (row3 2 47 48), (row3 2 47 49), (row3 2 47 50), (row3 2 47 51), (row3 2 47 52), (row3 2 47 53), (row3 2 47 54), (row3 2 47 55), (row3 2 47 56), (row3 2 47 57), (row3 2 47 58), (row3 2 47 59), (row3 2 47 60), (row3 2 47 61), (row3 2 47 62)]

def b014_00_labels : List Row := [(row3 232 462 232), (row3 288 462 288), (row3 222 224 222), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 122 86 369), (row3 273 295 304), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b014_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_00_rows b014_00_labels 9992817923667869224276254720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_00_rows b014_00_labels]
    decide +kernel

def b014_01_rows : List Row := [(row3 2 47 63), (row3 2 48 49), (row3 2 48 50), (row3 2 48 51), (row3 2 48 52), (row3 2 48 53), (row3 2 48 54), (row3 2 48 55), (row3 2 48 56), (row3 2 48 57), (row3 2 48 58), (row3 2 48 59), (row3 2 48 60), (row3 2 48 61), (row3 2 48 62), (row3 2 48 63)]

def b014_01_labels : List Row := [(row3 288 462 288), (row3 367 108 84), (row3 295 295 462), (row3 232 232 462), (row3 462 462 462), (row3 237 237 462), (row3 278 278 462), (row3 140 140 178), (row3 37 28 444), (row3 406 406 405), (row3 108 367 84), (row3 288 288 462), (row3 234 234 462), (row3 261 261 462), (row3 182 182 178), (row3 351 348 350)]

theorem b014_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_01_rows b014_01_labels 4644929657156688977572439864640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_01_rows b014_01_labels]
    decide +kernel

def b014_02_rows : List Row := [(row3 2 49 50), (row3 2 49 51), (row3 2 49 52), (row3 2 49 53), (row3 2 49 54), (row3 2 49 55), (row3 2 49 56), (row3 2 49 57), (row3 2 49 58), (row3 2 49 59), (row3 2 49 60), (row3 2 49 61), (row3 2 49 62), (row3 2 49 63), (row3 2 50 51), (row3 2 50 52)]

def b014_02_labels : List Row := [(row3 367 108 84), (row3 306 313 313), (row3 228 234 228), (row3 462 244 244), (row3 228 228 234), (row3 306 313 313), (row3 411 432 60), (row3 38 33 33), (row3 411 60 432), (row3 142 141 136), (row3 289 292 292), (row3 232 235 235), (row3 289 292 292), (row3 142 136 141), (row3 140 178 140), (row3 278 462 278)]

theorem b014_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_02_rows b014_02_labels 2091195687814838877901134959460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_02_rows b014_02_labels]
    decide +kernel

def b014_03_rows : List Row := [(row3 2 50 53), (row3 2 50 54), (row3 2 50 55), (row3 2 50 56), (row3 2 50 57), (row3 2 50 58), (row3 2 50 59), (row3 2 50 60), (row3 2 50 61), (row3 2 50 62), (row3 2 50 63), (row3 2 51 52), (row3 2 51 53), (row3 2 51 54), (row3 2 51 55), (row3 2 51 56)]

def b014_03_labels : List Row := [(row3 237 462 237), (row3 462 462 462), (row3 232 462 232), (row3 108 84 367), (row3 406 405 406), (row3 37 444 28), (row3 351 350 348), (row3 182 178 182), (row3 261 462 261), (row3 234 462 234), (row3 288 462 288), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 305 305)]

theorem b014_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_03_rows b014_03_labels 4597154256051524077001741351160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_03_rows b014_03_labels]
    decide +kernel

def b014_04_rows : List Row := [(row3 2 51 57), (row3 2 51 58), (row3 2 51 59), (row3 2 51 60), (row3 2 51 61), (row3 2 51 62), (row3 2 51 63), (row3 2 52 53), (row3 2 52 54), (row3 2 52 55), (row3 2 52 56), (row3 2 52 57), (row3 2 52 58), (row3 2 52 59), (row3 2 52 60), (row3 2 52 61)]

def b014_04_labels : List Row := [(row3 98 101 99), (row3 410 59 431), (row3 127 126 137), (row3 289 291 291), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 278 300 288), (row3 114 368 86), (row3 300 300 462), (row3 234 234 462), (row3 462 462 462)]

theorem b014_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_04_rows b014_04_labels 170176807457149957581896524620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_04_rows b014_04_labels]
    decide +kernel

def b014_05_rows : List Row := [(row3 2 52 62), (row3 2 52 63), (row3 2 53 54), (row3 2 53 55), (row3 2 53 56), (row3 2 53 57), (row3 2 53 58), (row3 2 53 59), (row3 2 53 60), (row3 2 53 61), (row3 2 53 62), (row3 2 53 63), (row3 2 54 55), (row3 2 54 56), (row3 2 54 57), (row3 2 54 58)]

def b014_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 462 462), (row3 462 284 284), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 234 462 234), (row3 114 86 368), (row3 278 288 300), (row3 234 462 234)]

theorem b014_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_05_rows b014_05_labels 10004824232181965878252038000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_05_rows b014_05_labels]
    decide +kernel

def b014_06_rows : List Row := [(row3 2 54 59), (row3 2 54 60), (row3 2 54 61), (row3 2 54 62), (row3 2 54 63), (row3 2 55 56), (row3 2 55 57), (row3 2 55 58), (row3 2 55 59), (row3 2 55 60), (row3 2 55 61), (row3 2 55 62), (row3 2 55 63), (row3 2 56 57), (row3 2 56 58), (row3 2 56 59)]

def b014_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 300 462 300), (row3 410 431 59), (row3 98 99 101), (row3 289 305 305), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 127 137 126), (row3 451 442 24), (row3 419 63 433), (row3 123 331 92)]

theorem b014_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_06_rows b014_06_labels 35932134811188618437387754342780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_06_rows b014_06_labels]
    decide +kernel

def b014_07_rows : List Row := [(row3 2 56 60), (row3 2 56 61), (row3 2 56 62), (row3 2 56 63), (row3 2 57 58), (row3 2 57 59), (row3 2 57 60), (row3 2 57 61), (row3 2 57 62), (row3 2 57 63), (row3 2 58 59), (row3 2 58 60), (row3 2 58 61), (row3 2 58 62), (row3 2 58 63), (row3 2 59 60)]

def b014_07_labels : List Row := [(row3 289 299 299), (row3 155 332 93), (row3 401 78 427), (row3 34 443 27), (row3 451 442 24), (row3 402 404 403), (row3 126 125 128), (row3 288 288 288), (row3 126 128 125), (row3 402 403 404), (row3 34 27 443), (row3 401 427 78), (row3 155 93 332), (row3 289 299 299), (row3 123 92 331), (row3 127 137 126)]

theorem b014_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_07_rows b014_07_labels 37819958425428502033127695530000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_07_rows b014_07_labels]
    decide +kernel

def b014_08_rows : List Row := [(row3 2 59 61), (row3 2 59 62), (row3 2 59 63), (row3 2 60 61), (row3 2 60 62), (row3 2 60 63), (row3 2 61 62), (row3 2 61 63), (row3 2 62 63), (row3 3 4 5), (row3 3 4 6), (row3 3 4 7), (row3 3 4 8), (row3 3 4 9), (row3 3 4 10), (row3 3 4 11)]

def b014_08_labels : List Row := [(row3 288 462 288), (row3 233 462 233), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 233 462 233), (row3 235 462 235), (row3 288 462 288), (row3 127 137 126), (row3 70 434 70), (row3 205 96 335), (row3 219 9 185), (row3 269 462 269), (row3 153 151 179), (row3 375 366 353), (row3 55 64 66)]

theorem b014_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_08_rows b014_08_labels 571081968203261367991227658110 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_08_rows b014_08_labels]
    decide +kernel

def b014_09_rows : List Row := [(row3 3 4 12), (row3 3 4 13), (row3 3 4 14), (row3 3 4 15), (row3 3 4 16), (row3 3 4 17), (row3 3 4 18), (row3 3 4 19), (row3 3 4 20), (row3 3 4 21), (row3 3 4 22), (row3 3 4 23), (row3 3 4 24), (row3 3 4 25), (row3 3 4 26), (row3 3 4 27)]

def b014_09_labels : List Row := [(row3 341 429 71), (row3 187 90 357), (row3 217 10 169), (row3 238 462 238), (row3 239 462 239), (row3 270 462 270), (row3 154 154 180), (row3 342 339 328), (row3 168 94 333), (row3 218 10 170), (row3 462 462 462), (row3 242 462 242), (row3 240 462 240), (row3 462 462 462), (row3 263 462 263), (row3 201 201 208)]

theorem b014_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_09_rows b014_09_labels 126318333792082408717707669150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_09_rows b014_09_labels]
    decide +kernel

def b014_10_rows : List Row := [(row3 3 4 28), (row3 3 4 29), (row3 3 4 30), (row3 3 4 31), (row3 3 4 32), (row3 3 4 33), (row3 3 4 34), (row3 3 4 35), (row3 3 4 36), (row3 3 4 37), (row3 3 4 38), (row3 3 4 39), (row3 3 4 40), (row3 3 4 41), (row3 3 4 42), (row3 3 4 43)]

def b014_10_labels : List Row := [(row3 254 8 203), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 257 462 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 462 462 462), (row3 263 462 263), (row3 201 201 208)]

theorem b014_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_10_rows b014_10_labels 463771611686668379741902500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_10_rows b014_10_labels]
    decide +kernel

def b014_11_rows : List Row := [(row3 3 4 44), (row3 3 4 45), (row3 3 4 46), (row3 3 4 47), (row3 3 4 48), (row3 3 4 49), (row3 3 4 50), (row3 3 4 51), (row3 3 4 52), (row3 3 4 53), (row3 3 4 54), (row3 3 4 55), (row3 3 4 56), (row3 3 4 57), (row3 3 4 58), (row3 3 4 59)]

def b014_11_labels : List Row := [(row3 254 8 203), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 270 462 270), (row3 154 154 180), (row3 342 339 328), (row3 168 94 333), (row3 218 10 170), (row3 462 462 462), (row3 242 462 242), (row3 269 462 269), (row3 153 151 179), (row3 375 366 353), (row3 55 64 66)]

theorem b014_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_11_rows b014_11_labels 294764404949766666068446240050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_11_rows b014_11_labels]
    decide +kernel

def b014_12_rows : List Row := [(row3 3 4 60), (row3 3 4 61), (row3 3 4 62), (row3 3 4 63), (row3 3 5 6), (row3 3 5 7), (row3 3 5 8), (row3 3 5 9), (row3 3 5 10), (row3 3 5 11), (row3 3 5 12), (row3 3 5 13), (row3 3 5 14), (row3 3 5 15), (row3 3 5 16), (row3 3 5 17)]

def b014_12_labels : List Row := [(row3 341 429 71), (row3 187 90 357), (row3 217 10 169), (row3 238 462 238), (row3 75 425 326), (row3 205 96 335), (row3 200 200 207), (row3 276 276 275), (row3 188 194 195), (row3 344 329 340), (row3 165 165 176), (row3 329 344 340), (row3 194 188 195), (row3 276 276 275), (row3 256 256 255), (row3 235 237 235)]

theorem b014_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_12_rows b014_12_labels 216369161186160043326510227250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_12_rows b014_12_labels]
    decide +kernel

def b014_13_rows : List Row := [(row3 3 5 18), (row3 3 5 19), (row3 3 5 20), (row3 3 5 21), (row3 3 5 22), (row3 3 5 23), (row3 3 5 24), (row3 3 5 25), (row3 3 5 26), (row3 3 5 27), (row3 3 5 28), (row3 3 5 29), (row3 3 5 30), (row3 3 5 31), (row3 3 5 32), (row3 3 5 33)]

def b014_13_labels : List Row := [(row3 267 267 265), (row3 206 209 209), (row3 281 281 278), (row3 209 206 209), (row3 267 267 265), (row3 237 235 235), (row3 239 239 239), (row3 241 241 462), (row3 238 462 238), (row3 256 256 255), (row3 238 238 236), (row3 256 256 255), (row3 462 238 238), (row3 241 241 462), (row3 240 240 462), (row3 462 462 462)]

theorem b014_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_13_rows b014_13_labels 77185015844063486810567700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_13_rows b014_13_labels]
    decide +kernel

def b014_14_rows : List Row := [(row3 3 5 34), (row3 3 5 35), (row3 3 5 36), (row3 3 5 37), (row3 3 5 38), (row3 3 5 39), (row3 3 5 40), (row3 3 5 41), (row3 3 5 42), (row3 3 5 43), (row3 3 5 44), (row3 3 5 45), (row3 3 5 46), (row3 3 5 47), (row3 3 5 48), (row3 3 5 49)]

def b014_14_labels : List Row := [(row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 239 239 239), (row3 241 241 462), (row3 238 462 238), (row3 256 256 255), (row3 238 238 236), (row3 256 256 255), (row3 462 238 238), (row3 241 241 462), (row3 256 256 255), (row3 235 237 235)]

theorem b014_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_14_rows b014_14_labels 6480458550521122358237520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_14_rows b014_14_labels]
    decide +kernel

def b014_15_rows : List Row := [(row3 3 5 50), (row3 3 5 51), (row3 3 5 52), (row3 3 5 53), (row3 3 5 54), (row3 3 5 55), (row3 3 5 56), (row3 3 5 57), (row3 3 5 58), (row3 3 5 59), (row3 3 5 60), (row3 3 5 61), (row3 3 5 62), (row3 3 5 63), (row3 3 6 7), (row3 3 6 8)]

def b014_15_labels : List Row := [(row3 267 267 265), (row3 206 209 209), (row3 281 281 278), (row3 209 206 209), (row3 267 267 265), (row3 237 235 235), (row3 200 200 207), (row3 276 276 275), (row3 188 194 195), (row3 344 329 340), (row3 165 165 176), (row3 329 344 340), (row3 194 188 195), (row3 276 276 275), (row3 70 434 70), (row3 344 340 329)]

theorem b014_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b014_15_rows b014_15_labels 255870130878667302853936565730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b014_15_rows b014_15_labels]
    decide +kernel

theorem checked014 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_014 QuarticIntegerComputationalData.ids64_014 86740498723349191237621929933390 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b014_00_rows ++ b014_01_rows) ++ (b014_02_rows ++ b014_03_rows)) ++ ((b014_04_rows ++ b014_05_rows) ++ (b014_06_rows ++ b014_07_rows))) ++ (((b014_08_rows ++ b014_09_rows) ++ (b014_10_rows ++ b014_11_rows)) ++ ((b014_12_rows ++ b014_13_rows) ++ (b014_14_rows ++ b014_15_rows))))
    ((((b014_00_labels ++ b014_01_labels) ++ (b014_02_labels ++ b014_03_labels)) ++ ((b014_04_labels ++ b014_05_labels) ++ (b014_06_labels ++ b014_07_labels))) ++ (((b014_08_labels ++ b014_09_labels) ++ (b014_10_labels ++ b014_11_labels)) ++ ((b014_12_labels ++ b014_13_labels) ++ (b014_14_labels ++ b014_15_labels)))) 86740498723349191237621929933390
  exact ((((b014_00_checked.append (c := 4654922475080356846796716119360) b014_01_checked (by decide +kernel)).append (c := 11343272418946719801699592429980) (b014_02_checked.append (c := 6688349943866362954902876310620) b014_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 85275547287253172195675190865380) ((b014_04_checked.append (c := 180181631689331923460148562620) b014_05_checked (by decide +kernel)).append (c := 73932274868306452393975598435400) (b014_06_checked.append (c := 73752093236617120470515449872780) b014_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 86740498723349191237621929933390) (((b014_08_checked.append (c := 697400301995343776708935327260) b014_09_checked (by decide +kernel)).append (c := 992628478556797111157123469810) (b014_10_checked.append (c := 295228176561453334448188142550) b014_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1464951436096019041946739068010) ((b014_12_checked.append (c := 216446346202004106813320794950) b014_13_checked (by decide +kernel)).append (c := 472322957539221930789615598200) (b014_14_checked.append (c := 255876611337217823976294803250) b014_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b015_00_rows : List Row := [(row3 3 6 9), (row3 3 6 10), (row3 3 6 11), (row3 3 6 12), (row3 3 6 13), (row3 3 6 14), (row3 3 6 15), (row3 3 6 16), (row3 3 6 17), (row3 3 6 18), (row3 3 6 19), (row3 3 6 20), (row3 3 6 21), (row3 3 6 22), (row3 3 6 23), (row3 3 6 24)]

def b015_00_labels : List Row := [(row3 188 195 194), (row3 276 275 276), (row3 200 207 200), (row3 276 275 276), (row3 194 195 188), (row3 329 340 344), (row3 165 176 165), (row3 206 209 209), (row3 267 265 267), (row3 235 235 237), (row3 256 255 256), (row3 237 235 235), (row3 267 265 267), (row3 209 209 206), (row3 281 278 281), (row3 256 255 256)]

theorem b015_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_00_rows b015_00_labels 7639253568928102325432219250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_00_rows b015_00_labels]
    decide +kernel

def b015_01_rows : List Row := [(row3 3 6 25), (row3 3 6 26), (row3 3 6 27), (row3 3 6 28), (row3 3 6 29), (row3 3 6 30), (row3 3 6 31), (row3 3 6 32), (row3 3 6 33), (row3 3 6 34), (row3 3 6 35), (row3 3 6 36), (row3 3 6 37), (row3 3 6 38), (row3 3 6 39), (row3 3 6 40)]

def b015_01_labels : List Row := [(row3 238 238 462), (row3 241 462 241), (row3 239 239 239), (row3 241 462 241), (row3 462 238 238), (row3 256 255 256), (row3 238 236 238), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 256 255 256)]

theorem b015_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_01_rows b015_01_labels 2588687633096754814955100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_01_rows b015_01_labels]
    decide +kernel

def b015_02_rows : List Row := [(row3 3 6 41), (row3 3 6 42), (row3 3 6 43), (row3 3 6 44), (row3 3 6 45), (row3 3 6 46), (row3 3 6 47), (row3 3 6 48), (row3 3 6 49), (row3 3 6 50), (row3 3 6 51), (row3 3 6 52), (row3 3 6 53), (row3 3 6 54), (row3 3 6 55), (row3 3 6 56)]

def b015_02_labels : List Row := [(row3 238 238 462), (row3 241 462 241), (row3 239 239 239), (row3 241 462 241), (row3 462 238 238), (row3 256 255 256), (row3 238 236 238), (row3 206 209 209), (row3 267 265 267), (row3 235 235 237), (row3 256 255 256), (row3 237 235 235), (row3 267 265 267), (row3 209 209 206), (row3 281 278 281), (row3 344 340 329)]

theorem b015_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_02_rows b015_02_labels 5896604889898101182515360770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_02_rows b015_02_labels]
    decide +kernel

def b015_03_rows : List Row := [(row3 3 6 57), (row3 3 6 58), (row3 3 6 59), (row3 3 6 60), (row3 3 6 61), (row3 3 6 62), (row3 3 6 63), (row3 3 7 8), (row3 3 7 9), (row3 3 7 10), (row3 3 7 11), (row3 3 7 12), (row3 3 7 13), (row3 3 7 14), (row3 3 7 15), (row3 3 7 16)]

def b015_03_labels : List Row := [(row3 188 195 194), (row3 276 275 276), (row3 200 207 200), (row3 276 275 276), (row3 194 195 188), (row3 329 340 344), (row3 165 176 165), (row3 55 66 64), (row3 375 353 366), (row3 153 179 151), (row3 269 269 462), (row3 238 238 462), (row3 217 169 10), (row3 187 357 90), (row3 341 71 429), (row3 342 328 339)]

theorem b015_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_03_rows b015_03_labels 414198026038632843811059424080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_03_rows b015_03_labels]
    decide +kernel

def b015_04_rows : List Row := [(row3 3 7 17), (row3 3 7 18), (row3 3 7 19), (row3 3 7 20), (row3 3 7 21), (row3 3 7 22), (row3 3 7 23), (row3 3 7 24), (row3 3 7 25), (row3 3 7 26), (row3 3 7 27), (row3 3 7 28), (row3 3 7 29), (row3 3 7 30), (row3 3 7 31), (row3 3 7 32)]

def b015_04_labels : List Row := [(row3 154 180 154), (row3 270 270 462), (row3 239 239 462), (row3 242 242 462), (row3 462 462 462), (row3 218 170 10), (row3 168 333 94), (row3 201 208 201), (row3 263 263 462), (row3 462 462 462), (row3 240 240 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 203 8), (row3 257 257 462)]

theorem b015_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_04_rows b015_04_labels 5067830528218609511331981750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_04_rows b015_04_labels]
    decide +kernel

def b015_05_rows : List Row := [(row3 3 7 33), (row3 3 7 34), (row3 3 7 35), (row3 3 7 36), (row3 3 7 37), (row3 3 7 38), (row3 3 7 39), (row3 3 7 40), (row3 3 7 41), (row3 3 7 42), (row3 3 7 43), (row3 3 7 44), (row3 3 7 45), (row3 3 7 46), (row3 3 7 47), (row3 3 7 48)]

def b015_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 201 208 201), (row3 263 263 462), (row3 462 462 462), (row3 240 240 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 203 8), (row3 342 328 339)]

theorem b015_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_05_rows b015_05_labels 5236225981969333769137652550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_05_rows b015_05_labels]
    decide +kernel

def b015_06_rows : List Row := [(row3 3 7 49), (row3 3 7 50), (row3 3 7 51), (row3 3 7 52), (row3 3 7 53), (row3 3 7 54), (row3 3 7 55), (row3 3 7 56), (row3 3 7 57), (row3 3 7 58), (row3 3 7 59), (row3 3 7 60), (row3 3 7 61), (row3 3 7 62), (row3 3 7 63), (row3 3 8 9)]

def b015_06_labels : List Row := [(row3 154 180 154), (row3 270 270 462), (row3 239 239 462), (row3 242 242 462), (row3 462 462 462), (row3 218 170 10), (row3 168 333 94), (row3 55 66 64), (row3 375 353 366), (row3 153 179 151), (row3 269 269 462), (row3 238 238 462), (row3 217 169 10), (row3 187 357 90), (row3 341 71 429), (row3 44 74 439)]

theorem b015_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_06_rows b015_06_labels 931539903463799824414590377250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_06_rows b015_06_labels]
    decide +kernel

def b015_07_rows : List Row := [(row3 3 8 10), (row3 3 8 11), (row3 3 8 12), (row3 3 8 13), (row3 3 8 14), (row3 3 8 15), (row3 3 8 16), (row3 3 8 17), (row3 3 8 18), (row3 3 8 19), (row3 3 8 20), (row3 3 8 21), (row3 3 8 22), (row3 3 8 23), (row3 3 8 24), (row3 3 8 25)]

def b015_07_labels : List Row := [(row3 123 331 92), (row3 269 186 9), (row3 236 236 462), (row3 259 204 8), (row3 155 332 93), (row3 359 73 429), (row3 336 72 428), (row3 158 356 89), (row3 260 173 10), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 258 172 10), (row3 159 356 91), (row3 202 334 97), (row3 254 171 10)]

theorem b015_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_07_rows b015_07_labels 279593874103862109878938556400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_07_rows b015_07_labels]
    decide +kernel

def b015_08_rows : List Row := [(row3 3 8 26), (row3 3 8 27), (row3 3 8 28), (row3 3 8 29), (row3 3 8 30), (row3 3 8 31), (row3 3 8 32), (row3 3 8 33), (row3 3 8 34), (row3 3 8 35), (row3 3 8 36), (row3 3 8 37), (row3 3 8 38), (row3 3 8 39), (row3 3 8 40), (row3 3 8 41)]

def b015_08_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 171 10), (row3 254 203 8), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 201 208 201), (row3 263 263 462)]

theorem b015_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_08_rows b015_08_labels 971383421196097984911840000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_08_rows b015_08_labels]
    decide +kernel

def b015_09_rows : List Row := [(row3 3 8 42), (row3 3 8 43), (row3 3 8 44), (row3 3 8 45), (row3 3 8 46), (row3 3 8 47), (row3 3 8 48), (row3 3 8 49), (row3 3 8 50), (row3 3 8 51), (row3 3 8 52), (row3 3 8 53), (row3 3 8 54), (row3 3 8 55), (row3 3 8 56), (row3 3 8 57)]

def b015_09_labels : List Row := [(row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 343 330 338), (row3 154 180 154), (row3 271 271 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 269 269 462), (row3 154 180 154), (row3 54 65 65), (row3 376 354 366)]

theorem b015_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_09_rows b015_09_labels 274975351807482735311302618800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_09_rows b015_09_labels]
    decide +kernel

def b015_10_rows : List Row := [(row3 3 8 58), (row3 3 8 59), (row3 3 8 60), (row3 3 8 61), (row3 3 8 62), (row3 3 8 63), (row3 3 9 10), (row3 3 9 11), (row3 3 9 12), (row3 3 9 13), (row3 3 9 14), (row3 3 9 15), (row3 3 9 16), (row3 3 9 17), (row3 3 9 18), (row3 3 9 19)]

def b015_10_labels : List Row := [(row3 152 177 150), (row3 274 274 462), (row3 236 236 462), (row3 264 264 462), (row3 154 180 154), (row3 373 352 365), (row3 40 413 438), (row3 123 331 92), (row3 296 295 296), (row3 231 227 229), (row3 297 295 297), (row3 126 128 125), (row3 110 111 109), (row3 395 407 415), (row3 120 120 112), (row3 318 315 318)]

theorem b015_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_10_rows b015_10_labels 468928110153536902984111014180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_10_rows b015_10_labels]
    decide +kernel

def b015_11_rows : List Row := [(row3 3 9 20), (row3 3 9 21), (row3 3 9 22), (row3 3 9 23), (row3 3 9 24), (row3 3 9 25), (row3 3 9 26), (row3 3 9 27), (row3 3 9 28), (row3 3 9 29), (row3 3 9 30), (row3 3 9 31), (row3 3 9 32), (row3 3 9 33), (row3 3 9 34), (row3 3 9 35)]

def b015_11_labels : List Row := [(row3 234 226 226), (row3 244 462 244), (row3 235 228 232), (row3 320 319 320), (row3 317 308 317), (row3 148 145 137), (row3 310 306 310), (row3 237 226 226), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 236 225 228), (row3 238 230 232), (row3 279 278 279), (row3 462 232 232), (row3 242 462 242)]

theorem b015_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_11_rows b015_11_labels 370891791925244019191323920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_11_rows b015_11_labels]
    decide +kernel

def b015_12_rows : List Row := [(row3 3 9 36), (row3 3 9 37), (row3 3 9 38), (row3 3 9 39), (row3 3 9 40), (row3 3 9 41), (row3 3 9 42), (row3 3 9 43), (row3 3 9 44), (row3 3 9 45), (row3 3 9 46), (row3 3 9 47), (row3 3 9 48), (row3 3 9 49), (row3 3 9 50), (row3 3 9 51)]

def b015_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 262 261 262), (row3 236 233 235), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 190 196 197), (row3 298 295 298), (row3 229 224 226), (row3 266 265 266)]

theorem b015_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_12_rows b015_12_labels 137101123232206626076815000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_12_rows b015_12_labels]
    decide +kernel

def b015_13_rows : List Row := [(row3 3 9 52), (row3 3 9 53), (row3 3 9 54), (row3 3 9 55), (row3 3 9 56), (row3 3 9 57), (row3 3 9 58), (row3 3 9 59), (row3 3 9 60), (row3 3 9 61), (row3 3 9 62), (row3 3 9 63), (row3 3 10 11), (row3 3 10 12), (row3 3 10 13), (row3 3 10 14)]

def b015_13_labels : List Row := [(row3 234 234 234), (row3 244 462 244), (row3 235 235 462), (row3 279 278 279), (row3 376 366 354), (row3 107 106 106), (row3 324 323 324), (row3 152 177 150), (row3 279 278 279), (row3 231 231 234), (row3 280 278 280), (row3 161 175 175), (row3 44 74 439), (row3 126 125 128), (row3 297 297 295), (row3 231 229 227)]

theorem b015_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_13_rows b015_13_labels 551235972422122772388020463390 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_13_rows b015_13_labels]
    decide +kernel

def b015_14_rows : List Row := [(row3 3 10 15), (row3 3 10 16), (row3 3 10 17), (row3 3 10 18), (row3 3 10 19), (row3 3 10 20), (row3 3 10 21), (row3 3 10 22), (row3 3 10 23), (row3 3 10 24), (row3 3 10 25), (row3 3 10 26), (row3 3 10 27), (row3 3 10 28), (row3 3 10 29), (row3 3 10 30)]

def b015_14_labels : List Row := [(row3 296 296 295), (row3 318 318 315), (row3 120 112 120), (row3 395 415 407), (row3 110 109 111), (row3 320 320 319), (row3 235 232 228), (row3 244 244 462), (row3 234 226 226), (row3 237 226 226), (row3 310 310 306), (row3 148 137 145), (row3 317 317 308), (row3 236 228 225), (row3 462 462 462), (row3 462 462 462)]

theorem b015_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_14_rows b015_14_labels 39586236076245812160019346130 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_14_rows b015_14_labels]
    decide +kernel

def b015_15_rows : List Row := [(row3 3 10 31), (row3 3 10 32), (row3 3 10 33), (row3 3 10 34), (row3 3 10 35), (row3 3 10 36), (row3 3 10 37), (row3 3 10 38), (row3 3 10 39), (row3 3 10 40), (row3 3 10 41), (row3 3 10 42), (row3 3 10 43), (row3 3 10 44), (row3 3 10 45), (row3 3 10 46)]

def b015_15_labels : List Row := [(row3 243 243 462), (row3 242 242 462), (row3 462 232 232), (row3 279 279 278), (row3 238 232 230), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 243 243 462), (row3 236 235 233), (row3 262 262 261), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462)]

theorem b015_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b015_15_rows b015_15_labels 16099423084333757988423300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b015_15_rows b015_15_labels]
    decide +kernel

theorem checked015 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_015 QuarticIntegerComputationalData.ids64_015 2985395453481768126879442371870 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b015_00_rows ++ b015_01_rows) ++ (b015_02_rows ++ b015_03_rows)) ++ ((b015_04_rows ++ b015_05_rows) ++ (b015_06_rows ++ b015_07_rows))) ++ (((b015_08_rows ++ b015_09_rows) ++ (b015_10_rows ++ b015_11_rows)) ++ ((b015_12_rows ++ b015_13_rows) ++ (b015_14_rows ++ b015_15_rows))))
    ((((b015_00_labels ++ b015_01_labels) ++ (b015_02_labels ++ b015_03_labels)) ++ ((b015_04_labels ++ b015_05_labels) ++ (b015_06_labels ++ b015_07_labels))) ++ (((b015_08_labels ++ b015_09_labels) ++ (b015_10_labels ++ b015_11_labels)) ++ ((b015_12_labels ++ b015_13_labels) ++ (b015_14_labels ++ b015_15_labels)))) 2985395453481768126879442371870
  exact ((((b015_00_checked.append (c := 7641842256561199080247174350) b015_01_checked (by decide +kernel)).append (c := 427736473185092144073821959200) (b015_02_checked.append (c := 420094630928530944993574784850) b015_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1649174307262942021647820527150) ((b015_04_checked.append (c := 10304056510187943280469634300) b015_05_checked (by decide +kernel)).append (c := 1221437834077849877573998567950) (b015_06_checked.append (c := 1211133777567661934293528933650) b015_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2985395453481768126879442371870) (((b015_08_checked.append (c := 275946735228678833296214458800) b015_09_checked (by decide +kernel)).append (c := 745245737174140980299516796900) (b015_10_checked.append (c := 469299001945462147003302338100) b015_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1336221146218826105231621844720) ((b015_12_checked.append (c := 551373073545354979014097278390) b015_13_checked (by decide +kernel)).append (c := 590975409044685124932105047820) (b015_14_checked.append (c := 39602335499330145918007769430) b015_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b016_00_rows : List Row := [(row3 3 10 47), (row3 3 10 48), (row3 3 10 49), (row3 3 10 50), (row3 3 10 51), (row3 3 10 52), (row3 3 10 53), (row3 3 10 54), (row3 3 10 55), (row3 3 10 56), (row3 3 10 57), (row3 3 10 58), (row3 3 10 59), (row3 3 10 60), (row3 3 10 61), (row3 3 10 62)]

def b016_00_labels : List Row := [(row3 243 243 462), (row3 266 266 265), (row3 229 226 224), (row3 298 298 295), (row3 190 197 196), (row3 279 279 278), (row3 235 462 235), (row3 244 244 462), (row3 234 234 234), (row3 152 150 177), (row3 324 324 323), (row3 107 106 106), (row3 376 354 366), (row3 161 175 175), (row3 280 280 278), (row3 231 234 231)]

theorem b016_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_00_rows b016_00_labels 25479816582651805491139148070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_00_rows b016_00_labels]
    decide +kernel

def b016_01_rows : List Row := [(row3 3 10 63), (row3 3 11 12), (row3 3 11 13), (row3 3 11 14), (row3 3 11 15), (row3 3 11 16), (row3 3 11 17), (row3 3 11 18), (row3 3 11 19), (row3 3 11 20), (row3 3 11 21), (row3 3 11 22), (row3 3 11 23), (row3 3 11 24), (row3 3 11 25), (row3 3 11 26)]

def b016_01_labels : List Row := [(row3 279 279 278), (row3 359 429 73), (row3 155 93 332), (row3 259 8 204), (row3 236 462 236), (row3 238 462 238), (row3 260 10 173), (row3 158 89 356), (row3 336 428 72), (row3 159 91 356), (row3 258 10 172), (row3 462 462 462), (row3 243 462 243), (row3 241 462 241), (row3 462 462 462), (row3 254 10 171)]

theorem b016_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_01_rows b016_01_labels 228912718061184684414550802880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_01_rows b016_01_labels]
    decide +kernel

def b016_02_rows : List Row := [(row3 3 11 27), (row3 3 11 28), (row3 3 11 29), (row3 3 11 30), (row3 3 11 31), (row3 3 11 32), (row3 3 11 33), (row3 3 11 34), (row3 3 11 35), (row3 3 11 36), (row3 3 11 37), (row3 3 11 38), (row3 3 11 39), (row3 3 11 40), (row3 3 11 41), (row3 3 11 42)]

def b016_02_labels : List Row := [(row3 202 97 334), (row3 254 10 171), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 254 8 203), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 263 462 263)]

theorem b016_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_02_rows b016_02_labels 3768272765636709280463376000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_02_rows b016_02_labels]
    decide +kernel

def b016_03_rows : List Row := [(row3 3 11 43), (row3 3 11 44), (row3 3 11 45), (row3 3 11 46), (row3 3 11 47), (row3 3 11 48), (row3 3 11 49), (row3 3 11 50), (row3 3 11 51), (row3 3 11 52), (row3 3 11 53), (row3 3 11 54), (row3 3 11 55), (row3 3 11 56), (row3 3 11 57), (row3 3 11 58)]

def b016_03_labels : List Row := [(row3 201 201 208), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 271 462 271), (row3 154 154 180), (row3 343 338 330), (row3 154 154 180), (row3 269 462 269), (row3 462 462 462), (row3 243 462 243), (row3 274 462 274), (row3 152 150 177), (row3 376 366 354)]

theorem b016_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_03_rows b016_03_labels 32997430518652159008305731800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_03_rows b016_03_labels]
    decide +kernel

def b016_04_rows : List Row := [(row3 3 11 59), (row3 3 11 60), (row3 3 11 61), (row3 3 11 62), (row3 3 11 63), (row3 3 12 13), (row3 3 12 14), (row3 3 12 15), (row3 3 12 16), (row3 3 12 17), (row3 3 12 18), (row3 3 12 19), (row3 3 12 20), (row3 3 12 21), (row3 3 12 22), (row3 3 12 23)]

def b016_04_labels : List Row := [(row3 54 65 65), (row3 373 365 352), (row3 154 154 180), (row3 264 462 264), (row3 236 462 236), (row3 301 301 278), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 283 283 278), (row3 190 199 198), (row3 279 279 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b016_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_04_rows b016_04_labels 263328395140380478259706839430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_04_rows b016_04_labels]
    decide +kernel

def b016_05_rows : List Row := [(row3 3 12 24), (row3 3 12 25), (row3 3 12 26), (row3 3 12 27), (row3 3 12 28), (row3 3 12 29), (row3 3 12 30), (row3 3 12 31), (row3 3 12 32), (row3 3 12 33), (row3 3 12 34), (row3 3 12 35), (row3 3 12 36), (row3 3 12 37), (row3 3 12 38), (row3 3 12 39)]

def b016_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 262 262 261), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b016_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_05_rows b016_05_labels 4041461358967705192549200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_05_rows b016_05_labels]
    decide +kernel

def b016_06_rows : List Row := [(row3 3 12 40), (row3 3 12 41), (row3 3 12 42), (row3 3 12 43), (row3 3 12 44), (row3 3 12 45), (row3 3 12 46), (row3 3 12 47), (row3 3 12 48), (row3 3 12 49), (row3 3 12 50), (row3 3 12 51), (row3 3 12 52), (row3 3 12 53), (row3 3 12 54), (row3 3 12 55)]

def b016_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 262 262 261), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 279 279 278), (row3 190 199 198), (row3 279 279 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b016_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_06_rows b016_06_labels 96694680293360250504629520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_06_rows b016_06_labels]
    decide +kernel

def b016_07_rows : List Row := [(row3 3 12 56), (row3 3 12 57), (row3 3 12 58), (row3 3 12 59), (row3 3 12 60), (row3 3 12 61), (row3 3 12 62), (row3 3 12 63), (row3 3 13 14), (row3 3 13 15), (row3 3 13 16), (row3 3 13 17), (row3 3 13 18), (row3 3 13 19), (row3 3 13 20), (row3 3 13 21)]

def b016_07_labels : List Row := [(row3 236 462 236), (row3 279 279 278), (row3 161 175 175), (row3 373 352 365), (row3 161 176 176), (row3 282 282 278), (row3 236 462 236), (row3 462 462 462), (row3 116 11 213), (row3 233 462 233), (row3 238 462 238), (row3 245 462 245), (row3 234 234 234), (row3 268 265 268), (row3 226 234 226), (row3 285 462 285)]

theorem b016_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_07_rows b016_07_labels 13018808169463803757235828220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_07_rows b016_07_labels]
    decide +kernel

def b016_08_rows : List Row := [(row3 3 13 22), (row3 3 13 23), (row3 3 13 24), (row3 3 13 25), (row3 3 13 26), (row3 3 13 27), (row3 3 13 28), (row3 3 13 29), (row3 3 13 30), (row3 3 13 31), (row3 3 13 32), (row3 3 13 33), (row3 3 13 34), (row3 3 13 35), (row3 3 13 36), (row3 3 13 37)]

def b016_08_labels : List Row := [(row3 232 462 232), (row3 247 462 247), (row3 241 462 241), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 247 462 247), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 243 462 243)]

theorem b016_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_08_rows b016_08_labels 1487618722847373073372500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_08_rows b016_08_labels]
    decide +kernel

def b016_09_rows : List Row := [(row3 3 13 38), (row3 3 13 39), (row3 3 13 40), (row3 3 13 41), (row3 3 13 42), (row3 3 13 43), (row3 3 13 44), (row3 3 13 45), (row3 3 13 46), (row3 3 13 47), (row3 3 13 48), (row3 3 13 49), (row3 3 13 50), (row3 3 13 51), (row3 3 13 52), (row3 3 13 53)]

def b016_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 245 462 245), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234), (row3 245 462 245)]

theorem b016_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_09_rows b016_09_labels 4155491215879120622954400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_09_rows b016_09_labels]
    decide +kernel

def b016_10_rows : List Row := [(row3 3 13 54), (row3 3 13 55), (row3 3 13 56), (row3 3 13 57), (row3 3 13 58), (row3 3 13 59), (row3 3 13 60), (row3 3 13 61), (row3 3 13 62), (row3 3 13 63), (row3 3 14 15), (row3 3 14 16), (row3 3 14 17), (row3 3 14 18), (row3 3 14 19), (row3 3 14 20)]

def b016_10_labels : List Row := [(row3 462 462 462), (row3 243 462 243), (row3 264 462 264), (row3 231 234 231), (row3 280 278 280), (row3 154 180 154), (row3 282 278 282), (row3 226 229 229), (row3 252 462 252), (row3 236 462 236), (row3 301 301 278), (row3 268 268 265), (row3 234 234 234), (row3 245 245 462), (row3 238 238 462), (row3 247 247 462)]

theorem b016_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_10_rows b016_10_labels 1021935223996307592331220700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_10_rows b016_10_labels]
    decide +kernel

def b016_11_rows : List Row := [(row3 3 14 21), (row3 3 14 22), (row3 3 14 23), (row3 3 14 24), (row3 3 14 25), (row3 3 14 26), (row3 3 14 27), (row3 3 14 28), (row3 3 14 29), (row3 3 14 30), (row3 3 14 31), (row3 3 14 32), (row3 3 14 33), (row3 3 14 34), (row3 3 14 35), (row3 3 14 36)]

def b016_11_labels : List Row := [(row3 232 232 462), (row3 285 285 462), (row3 226 226 234), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 247 247 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b016_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_11_rows b016_11_labels 76042493094365383342776000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_11_rows b016_11_labels]
    decide +kernel

def b016_12_rows : List Row := [(row3 3 14 37), (row3 3 14 38), (row3 3 14 39), (row3 3 14 40), (row3 3 14 41), (row3 3 14 42), (row3 3 14 43), (row3 3 14 44), (row3 3 14 45), (row3 3 14 46), (row3 3 14 47), (row3 3 14 48), (row3 3 14 49), (row3 3 14 50), (row3 3 14 51), (row3 3 14 52)]

def b016_12_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 237 237 237), (row3 243 243 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 245 245 462), (row3 238 238 462), (row3 243 243 462)]

theorem b016_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_12_rows b016_12_labels 3828877792195317513891900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_12_rows b016_12_labels]
    decide +kernel

def b016_13_rows : List Row := [(row3 3 14 53), (row3 3 14 54), (row3 3 14 55), (row3 3 14 56), (row3 3 14 57), (row3 3 14 58), (row3 3 14 59), (row3 3 14 60), (row3 3 14 61), (row3 3 14 62), (row3 3 14 63), (row3 3 15 16), (row3 3 15 17), (row3 3 15 18), (row3 3 15 19), (row3 3 15 20)]

def b016_13_labels : List Row := [(row3 462 462 462), (row3 245 245 462), (row3 234 234 234), (row3 154 154 180), (row3 280 280 278), (row3 231 231 234), (row3 264 264 462), (row3 236 236 462), (row3 252 252 462), (row3 226 229 229), (row3 282 282 278), (row3 190 198 199), (row3 283 278 283), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462)]

theorem b016_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_13_rows b016_13_labels 985873333124838342799587480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_13_rows b016_13_labels]
    decide +kernel

def b016_14_rows : List Row := [(row3 3 15 21), (row3 3 15 22), (row3 3 15 23), (row3 3 15 24), (row3 3 15 25), (row3 3 15 26), (row3 3 15 27), (row3 3 15 28), (row3 3 15 29), (row3 3 15 30), (row3 3 15 31), (row3 3 15 32), (row3 3 15 33), (row3 3 15 34), (row3 3 15 35), (row3 3 15 36)]

def b016_14_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 279 278 279), (row3 262 261 262), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b016_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_14_rows b016_14_labels 93303735039928076476684800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_14_rows b016_14_labels]
    decide +kernel

def b016_15_rows : List Row := [(row3 3 15 37), (row3 3 15 38), (row3 3 15 39), (row3 3 15 40), (row3 3 15 41), (row3 3 15 42), (row3 3 15 43), (row3 3 15 44), (row3 3 15 45), (row3 3 15 46), (row3 3 15 47), (row3 3 15 48), (row3 3 15 49), (row3 3 15 50), (row3 3 15 51), (row3 3 15 52)]

def b016_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 262 261 262), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 190 198 199), (row3 279 278 279), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462)]

theorem b016_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b016_15_rows b016_15_labels 86550363274698244398349920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b016_15_rows b016_15_labels]
    decide +kernel

theorem checked016 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_016 QuarticIntegerComputationalData.ids64_016 569879354515883027617657742820 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b016_00_rows ++ b016_01_rows) ++ (b016_02_rows ++ b016_03_rows)) ++ ((b016_04_rows ++ b016_05_rows) ++ (b016_06_rows ++ b016_07_rows))) ++ (((b016_08_rows ++ b016_09_rows) ++ (b016_10_rows ++ b016_11_rows)) ++ ((b016_12_rows ++ b016_13_rows) ++ (b016_14_rows ++ b016_15_rows))))
    ((((b016_00_labels ++ b016_01_labels) ++ (b016_02_labels ++ b016_03_labels)) ++ ((b016_04_labels ++ b016_05_labels) ++ (b016_06_labels ++ b016_07_labels))) ++ (((b016_08_labels ++ b016_09_labels) ++ (b016_10_labels ++ b016_11_labels)) ++ ((b016_12_labels ++ b016_13_labels) ++ (b016_14_labels ++ b016_15_labels)))) 569879354515883027617657742820
  exact ((((b016_00_checked.append (c := 254392534643836489905689950950) b016_01_checked (by decide +kernel)).append (c := 291158237928125358194459058750) (b016_02_checked.append (c := 36765703284288868288769107800) b016_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 567606177379621968167098905120) ((b016_04_checked.append (c := 263332436601739445964899388630) b016_05_checked (by decide +kernel)).append (c := 276447939451496609972639846370) (b016_06_checked.append (c := 13115502849757164007740457740) b016_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 569879354515883027617657742820) (((b016_08_checked.append (c := 5643109938726493696326900) b016_09_checked (by decide +kernel)).append (c := 1103620827029399469370323600) (b016_10_checked.append (c := 1097977717090672975673996700) b016_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2273177136261059450558837700) ((b016_12_checked.append (c := 989702210917033660313479380) b016_13_checked (by decide +kernel)).append (c := 1169556309231659981188514100) (b016_14_checked.append (c := 179854098314626320875034720) b016_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
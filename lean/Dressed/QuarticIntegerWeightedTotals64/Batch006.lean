import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch005
import Dressed.QuarticIntegerComputationalData64.Batch006


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b049_00_rows : List Row := [(row3 8 20 35), (row3 8 20 36), (row3 8 20 37), (row3 8 20 38), (row3 8 20 39), (row3 8 20 40), (row3 8 20 41), (row3 8 20 42), (row3 8 20 43), (row3 8 20 44), (row3 8 20 45), (row3 8 20 46), (row3 8 20 47), (row3 8 20 48), (row3 8 20 49), (row3 8 20 50)]

def b049_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b049_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_00_rows b049_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_00_rows b049_00_labels]
    decide +kernel

def b049_01_rows : List Row := [(row3 8 20 51), (row3 8 20 52), (row3 8 20 53), (row3 8 20 54), (row3 8 20 55), (row3 8 20 56), (row3 8 20 57), (row3 8 20 58), (row3 8 20 59), (row3 8 20 60), (row3 8 20 61), (row3 8 20 62), (row3 8 20 63), (row3 8 21 22), (row3 8 21 23), (row3 8 21 24)]

def b049_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 307 307 462), (row3 127 126 137), (row3 193 192 238)]

theorem b049_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_01_rows b049_01_labels 20050718773248408895664126580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_01_rows b049_01_labels]
    decide +kernel

def b049_02_rows : List Row := [(row3 8 21 25), (row3 8 21 26), (row3 8 21 27), (row3 8 21 28), (row3 8 21 29), (row3 8 21 30), (row3 8 21 31), (row3 8 21 32), (row3 8 21 33), (row3 8 21 34), (row3 8 21 35), (row3 8 21 36), (row3 8 21 37), (row3 8 21 38), (row3 8 21 39), (row3 8 21 40)]

def b049_02_labels : List Row := [(row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 286 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b049_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_02_rows b049_02_labels 178122113627555485236300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_02_rows b049_02_labels]
    decide +kernel

def b049_03_rows : List Row := [(row3 8 21 41), (row3 8 21 42), (row3 8 21 43), (row3 8 21 44), (row3 8 21 45), (row3 8 21 46), (row3 8 21 47), (row3 8 21 48), (row3 8 21 49), (row3 8 21 50), (row3 8 21 51), (row3 8 21 52), (row3 8 21 53), (row3 8 21 54), (row3 8 21 55), (row3 8 21 56)]

def b049_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462)]

theorem b049_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_03_rows b049_03_labels 526157920619652690971079000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_03_rows b049_03_labels]
    decide +kernel

def b049_04_rows : List Row := [(row3 8 21 57), (row3 8 21 58), (row3 8 21 59), (row3 8 21 60), (row3 8 21 61), (row3 8 21 62), (row3 8 21 63), (row3 8 22 23), (row3 8 22 24), (row3 8 22 25), (row3 8 22 26), (row3 8 22 27), (row3 8 22 28), (row3 8 22 29), (row3 8 22 30), (row3 8 22 31)]

def b049_04_labels : List Row := [(row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 418 422 424), (row3 363 386 393), (row3 131 105 105), (row3 293 462 293), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 316 462 316), (row3 129 103 102)]

theorem b049_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_04_rows b049_04_labels 4086275255599144251897286260750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_04_rows b049_04_labels]
    decide +kernel

def b049_05_rows : List Row := [(row3 8 22 32), (row3 8 22 33), (row3 8 22 34), (row3 8 22 35), (row3 8 22 36), (row3 8 22 37), (row3 8 22 38), (row3 8 22 39), (row3 8 22 40), (row3 8 22 41), (row3 8 22 42), (row3 8 22 43), (row3 8 22 44), (row3 8 22 45), (row3 8 22 46), (row3 8 22 47)]

def b049_05_labels : List Row := [(row3 180 154 154), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 462 234), (row3 287 462 287), (row3 170 10 218), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462)]

theorem b049_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_05_rows b049_05_labels 1512832013366221882586234250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_05_rows b049_05_labels]
    decide +kernel

def b049_06_rows : List Row := [(row3 8 22 48), (row3 8 22 49), (row3 8 22 50), (row3 8 22 51), (row3 8 22 52), (row3 8 22 53), (row3 8 22 54), (row3 8 22 55), (row3 8 22 56), (row3 8 22 57), (row3 8 22 58), (row3 8 22 59), (row3 8 22 60), (row3 8 22 61), (row3 8 22 62), (row3 8 22 63)]

def b049_06_labels : List Row := [(row3 370 88 211), (row3 117 11 214), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 42 435 181), (row3 398 83 135), (row3 118 11 215), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 119 11 216), (row3 398 81 134)]

theorem b049_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_06_rows b049_06_labels 401108183073298585387390707450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_06_rows b049_06_labels]
    decide +kernel

def b049_07_rows : List Row := [(row3 8 23 24), (row3 8 23 25), (row3 8 23 26), (row3 8 23 27), (row3 8 23 28), (row3 8 23 29), (row3 8 23 30), (row3 8 23 31), (row3 8 23 32), (row3 8 23 33), (row3 8 23 34), (row3 8 23 35), (row3 8 23 36), (row3 8 23 37), (row3 8 23 38), (row3 8 23 39)]

def b049_07_labels : List Row := [(row3 57 53 51), (row3 396 416 408), (row3 139 232 138), (row3 462 462 462), (row3 462 232 232), (row3 309 309 306), (row3 100 113 100), (row3 417 423 422), (row3 353 375 366), (row3 163 228 160), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 309 309 306), (row3 127 137 126)]

theorem b049_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_07_rows b049_07_labels 5509793849467965898743878782620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_07_rows b049_07_labels]
    decide +kernel

def b049_08_rows : List Row := [(row3 8 23 40), (row3 8 23 41), (row3 8 23 42), (row3 8 23 43), (row3 8 23 44), (row3 8 23 45), (row3 8 23 46), (row3 8 23 47), (row3 8 23 48), (row3 8 23 49), (row3 8 23 50), (row3 8 23 51), (row3 8 23 52), (row3 8 23 53), (row3 8 23 54), (row3 8 23 55)]

def b049_08_labels : List Row := [(row3 357 90 187), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 301 301 278), (row3 58 430 372), (row3 399 83 157), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 399 82 156)]

theorem b049_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_08_rows b049_08_labels 185950852803894471537236596020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_08_rows b049_08_labels]
    decide +kernel

def b049_09_rows : List Row := [(row3 8 23 56), (row3 8 23 57), (row3 8 23 58), (row3 8 23 59), (row3 8 23 60), (row3 8 23 61), (row3 8 23 62), (row3 8 23 63), (row3 8 24 25), (row3 8 24 26), (row3 8 24 27), (row3 8 24 28), (row3 8 24 29), (row3 8 24 30), (row3 8 24 31), (row3 8 24 32)]

def b049_09_labels : List Row := [(row3 453 26 47), (row3 39 437 412), (row3 398 83 135), (row3 284 284 462), (row3 462 462 462), (row3 284 284 462), (row3 398 81 134), (row3 40 438 413), (row3 384 400 397), (row3 164 206 164), (row3 256 256 255), (row3 462 239 239), (row3 256 256 255), (row3 164 206 164), (row3 384 400 397), (row3 355 374 364)]

theorem b049_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_09_rows b049_09_labels 16599834091323521425538968690260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_09_rows b049_09_labels]
    decide +kernel

def b049_10_rows : List Row := [(row3 8 24 33), (row3 8 24 34), (row3 8 24 35), (row3 8 24 36), (row3 8 24 37), (row3 8 24 38), (row3 8 24 39), (row3 8 24 40), (row3 8 24 41), (row3 8 24 42), (row3 8 24 43), (row3 8 24 44), (row3 8 24 45), (row3 8 24 46), (row3 8 24 47), (row3 8 24 48)]

def b049_10_labels : List Row := [(row3 166 190 167), (row3 266 266 265), (row3 462 238 238), (row3 462 462 462), (row3 462 238 238), (row3 266 266 265), (row3 166 190 167), (row3 335 96 205), (row3 277 277 265), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 277 277 265), (row3 75 425 326)]

theorem b049_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_10_rows b049_10_labels 98713002827415092188286440500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_10_rows b049_10_labels]
    decide +kernel

def b049_11_rows : List Row := [(row3 8 24 49), (row3 8 24 50), (row3 8 24 51), (row3 8 24 52), (row3 8 24 53), (row3 8 24 54), (row3 8 24 55), (row3 8 24 56), (row3 8 24 57), (row3 8 24 58), (row3 8 24 59), (row3 8 24 60), (row3 8 24 61), (row3 8 24 62), (row3 8 24 63), (row3 8 25 26)]

def b049_11_labels : List Row := [(row3 371 87 325), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 371 87 325), (row3 446 30 80), (row3 58 430 372), (row3 370 88 211), (row3 263 263 462), (row3 462 462 462), (row3 263 263 462), (row3 370 88 211), (row3 58 430 372), (row3 307 462 307)]

theorem b049_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_11_rows b049_11_labels 4094419455189972412376905727940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_11_rows b049_11_labels]
    decide +kernel

def b049_12_rows : List Row := [(row3 8 25 27), (row3 8 25 28), (row3 8 25 29), (row3 8 25 30), (row3 8 25 31), (row3 8 25 32), (row3 8 25 33), (row3 8 25 34), (row3 8 25 35), (row3 8 25 36), (row3 8 25 37), (row3 8 25 38), (row3 8 25 39), (row3 8 25 40), (row3 8 25 41), (row3 8 25 42)]

def b049_12_labels : List Row := [(row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 294 462 294), (row3 130 104 104), (row3 179 153 151), (row3 303 462 303), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 169 10 217), (row3 235 462 235), (row3 246 462 246)]

theorem b049_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_12_rows b049_12_labels 27491597897068827672466433250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_12_rows b049_12_labels]
    decide +kernel

def b049_13_rows : List Row := [(row3 8 25 43), (row3 8 25 44), (row3 8 25 45), (row3 8 25 46), (row3 8 25 47), (row3 8 25 48), (row3 8 25 49), (row3 8 25 50), (row3 8 25 51), (row3 8 25 52), (row3 8 25 53), (row3 8 25 54), (row3 8 25 55), (row3 8 25 56), (row3 8 25 57), (row3 8 25 58)]

def b049_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 371 87 325), (row3 116 11 213), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 115 11 212), (row3 41 435 95), (row3 399 82 156), (row3 117 11 214)]

theorem b049_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_13_rows b049_13_labels 388502488095404785090570786200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_13_rows b049_13_labels]
    decide +kernel

def b049_14_rows : List Row := [(row3 8 25 59), (row3 8 25 60), (row3 8 25 61), (row3 8 25 62), (row3 8 25 63), (row3 8 26 27), (row3 8 26 28), (row3 8 26 29), (row3 8 26 30), (row3 8 26 31), (row3 8 26 32), (row3 8 26 33), (row3 8 26 34), (row3 8 26 35), (row3 8 26 36), (row3 8 26 37)]

def b049_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 399 83 157), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 294 294 462), (row3 270 270 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b049_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_14_rows b049_14_labels 22059184149208771807942001250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_14_rows b049_14_labels]
    decide +kernel

def b049_15_rows : List Row := [(row3 8 26 38), (row3 8 26 39), (row3 8 26 40), (row3 8 26 41), (row3 8 26 42), (row3 8 26 43), (row3 8 26 44), (row3 8 26 45), (row3 8 26 46), (row3 8 26 47), (row3 8 26 48), (row3 8 26 49), (row3 8 26 50), (row3 8 26 51), (row3 8 26 52), (row3 8 26 53)]

def b049_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b049_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b049_15_rows b049_15_labels 30282188517912052206022500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b049_15_rows b049_15_labels]
    decide +kernel

theorem checked049 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_049 QuarticIntegerComputationalData.ids64_049 31436446073436274273247596188570 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b049_00_rows ++ b049_01_rows) ++ (b049_02_rows ++ b049_03_rows)) ++ ((b049_04_rows ++ b049_05_rows) ++ (b049_06_rows ++ b049_07_rows))) ++ (((b049_08_rows ++ b049_09_rows) ++ (b049_10_rows ++ b049_11_rows)) ++ ((b049_12_rows ++ b049_13_rows) ++ (b049_14_rows ++ b049_15_rows))))
    ((((b049_00_labels ++ b049_01_labels) ++ (b049_02_labels ++ b049_03_labels)) ++ ((b049_04_labels ++ b049_05_labels) ++ (b049_06_labels ++ b049_07_labels))) ++ (((b049_08_labels ++ b049_09_labels) ++ (b049_10_labels ++ b049_11_labels)) ++ ((b049_12_labels ++ b049_13_labels) ++ (b049_14_labels ++ b049_15_labels)))) 31436446073436274273247596188570
  exact ((((b049_00_checked.append (c := 20050718773248408895664126580) b049_01_checked (by decide +kernel)).append (c := 20754998807495617071871505580) (b049_02_checked.append (c := 704280034247208176207379000) b049_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 10019445118961270574983013490650) ((b049_04_checked.append (c := 4087788087612510473779872495000) b049_05_checked (by decide +kernel)).append (c := 9998690120153774957911141985070) (b049_06_checked.append (c := 5910902032541264484131269490070) b049_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 31436446073436274273247596188570) (((b049_08_checked.append (c := 16785784944127415897076205286280) b049_09_checked (by decide +kernel)).append (c := 20978917402144803401641397454720) (b049_10_checked.append (c := 4193132458017387504565192168440) b049_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 21417000954475003698264582697920) ((b049_12_checked.append (c := 415994085992473612763037219450) b049_13_checked (by decide +kernel)).append (c := 438083552330200296623185243200) (b049_14_checked.append (c := 22089466337726683860148023750) b049_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b050_00_rows : List Row := [(row3 8 26 54), (row3 8 26 55), (row3 8 26 56), (row3 8 26 57), (row3 8 26 58), (row3 8 26 59), (row3 8 26 60), (row3 8 26 61), (row3 8 26 62), (row3 8 26 63), (row3 8 27 28), (row3 8 27 29), (row3 8 27 30), (row3 8 27 31), (row3 8 27 32), (row3 8 27 33)]

def b050_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 180 180 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_00_rows b050_00_labels 945931314185876589119091000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_00_rows b050_00_labels]
    decide +kernel

def b050_01_rows : List Row := [(row3 8 27 34), (row3 8 27 35), (row3 8 27 36), (row3 8 27 37), (row3 8 27 38), (row3 8 27 39), (row3 8 27 40), (row3 8 27 41), (row3 8 27 42), (row3 8 27 43), (row3 8 27 44), (row3 8 27 45), (row3 8 27 46), (row3 8 27 47), (row3 8 27 48), (row3 8 27 49)]

def b050_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_01_rows b050_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_01_rows b050_01_labels]
    decide +kernel

def b050_02_rows : List Row := [(row3 8 27 50), (row3 8 27 51), (row3 8 27 52), (row3 8 27 53), (row3 8 27 54), (row3 8 27 55), (row3 8 27 56), (row3 8 27 57), (row3 8 27 58), (row3 8 27 59), (row3 8 27 60), (row3 8 27 61), (row3 8 27 62), (row3 8 27 63), (row3 8 28 29), (row3 8 28 30)]

def b050_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_02_rows b050_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_02_rows b050_02_labels]
    decide +kernel

def b050_03_rows : List Row := [(row3 8 28 31), (row3 8 28 32), (row3 8 28 33), (row3 8 28 34), (row3 8 28 35), (row3 8 28 36), (row3 8 28 37), (row3 8 28 38), (row3 8 28 39), (row3 8 28 40), (row3 8 28 41), (row3 8 28 42), (row3 8 28 43), (row3 8 28 44), (row3 8 28 45), (row3 8 28 46)]

def b050_03_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_03_rows b050_03_labels 214654640140428770925000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_03_rows b050_03_labels]
    decide +kernel

def b050_04_rows : List Row := [(row3 8 28 47), (row3 8 28 48), (row3 8 28 49), (row3 8 28 50), (row3 8 28 51), (row3 8 28 52), (row3 8 28 53), (row3 8 28 54), (row3 8 28 55), (row3 8 28 56), (row3 8 28 57), (row3 8 28 58), (row3 8 28 59), (row3 8 28 60), (row3 8 28 61), (row3 8 28 62)]

def b050_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_04_rows b050_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_04_rows b050_04_labels]
    decide +kernel

def b050_05_rows : List Row := [(row3 8 28 63), (row3 8 29 30), (row3 8 29 31), (row3 8 29 32), (row3 8 29 33), (row3 8 29 34), (row3 8 29 35), (row3 8 29 36), (row3 8 29 37), (row3 8 29 38), (row3 8 29 39), (row3 8 29 40), (row3 8 29 41), (row3 8 29 42), (row3 8 29 43), (row3 8 29 44)]

def b050_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_05_rows b050_05_labels 13733899408298564019252000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_05_rows b050_05_labels]
    decide +kernel

def b050_06_rows : List Row := [(row3 8 29 45), (row3 8 29 46), (row3 8 29 47), (row3 8 29 48), (row3 8 29 49), (row3 8 29 50), (row3 8 29 51), (row3 8 29 52), (row3 8 29 53), (row3 8 29 54), (row3 8 29 55), (row3 8 29 56), (row3 8 29 57), (row3 8 29 58), (row3 8 29 59), (row3 8 29 60)]

def b050_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_06_rows b050_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_06_rows b050_06_labels]
    decide +kernel

def b050_07_rows : List Row := [(row3 8 29 61), (row3 8 29 62), (row3 8 29 63), (row3 8 30 31), (row3 8 30 32), (row3 8 30 33), (row3 8 30 34), (row3 8 30 35), (row3 8 30 36), (row3 8 30 37), (row3 8 30 38), (row3 8 30 39), (row3 8 30 40), (row3 8 30 41), (row3 8 30 42), (row3 8 30 43)]

def b050_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 307 307 462), (row3 270 270 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_07_rows b050_07_labels 11030594412383764203312337500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_07_rows b050_07_labels]
    decide +kernel

def b050_08_rows : List Row := [(row3 8 30 44), (row3 8 30 45), (row3 8 30 46), (row3 8 30 47), (row3 8 30 48), (row3 8 30 49), (row3 8 30 50), (row3 8 30 51), (row3 8 30 52), (row3 8 30 53), (row3 8 30 54), (row3 8 30 55), (row3 8 30 56), (row3 8 30 57), (row3 8 30 58), (row3 8 30 59)]

def b050_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 180 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_08_rows b050_08_labels 882725191816633838890866000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_08_rows b050_08_labels]
    decide +kernel

def b050_09_rows : List Row := [(row3 8 30 60), (row3 8 30 61), (row3 8 30 62), (row3 8 30 63), (row3 8 31 32), (row3 8 31 33), (row3 8 31 34), (row3 8 31 35), (row3 8 31 36), (row3 8 31 37), (row3 8 31 38), (row3 8 31 39), (row3 8 31 40), (row3 8 31 41), (row3 8 31 42), (row3 8 31 43)]

def b050_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 179 153 151), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 303 462 303), (row3 169 10 217), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_09_rows b050_09_labels 16472556610864689134237864250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_09_rows b050_09_labels]
    decide +kernel

def b050_10_rows : List Row := [(row3 8 31 44), (row3 8 31 45), (row3 8 31 46), (row3 8 31 47), (row3 8 31 48), (row3 8 31 49), (row3 8 31 50), (row3 8 31 51), (row3 8 31 52), (row3 8 31 53), (row3 8 31 54), (row3 8 31 55), (row3 8 31 56), (row3 8 31 57), (row3 8 31 58), (row3 8 31 59)]

def b050_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 371 87 325), (row3 115 11 212), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 116 11 213), (row3 41 435 95), (row3 399 83 157), (row3 117 11 214), (row3 462 462 462)]

theorem b050_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_10_rows b050_10_labels 388515053979245307004945213200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_10_rows b050_10_labels]
    decide +kernel

def b050_11_rows : List Row := [(row3 8 31 60), (row3 8 31 61), (row3 8 31 62), (row3 8 31 63), (row3 8 32 33), (row3 8 32 34), (row3 8 32 35), (row3 8 32 36), (row3 8 32 37), (row3 8 32 38), (row3 8 32 39), (row3 8 32 40), (row3 8 32 41), (row3 8 32 42), (row3 8 32 43), (row3 8 32 44)]

def b050_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 399 82 156), (row3 269 462 269), (row3 239 462 239), (row3 240 462 240), (row3 462 462 462), (row3 240 462 240), (row3 239 462 239), (row3 269 462 269), (row3 185 9 219), (row3 238 462 238), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462)]

theorem b050_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_11_rows b050_11_labels 52649994622448502870506430750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_11_rows b050_11_labels]
    decide +kernel

def b050_12_rows : List Row := [(row3 8 32 45), (row3 8 32 46), (row3 8 32 47), (row3 8 32 48), (row3 8 32 49), (row3 8 32 50), (row3 8 32 51), (row3 8 32 52), (row3 8 32 53), (row3 8 32 54), (row3 8 32 55), (row3 8 32 56), (row3 8 32 57), (row3 8 32 58), (row3 8 32 59), (row3 8 32 60)]

def b050_12_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 238 462 238), (row3 335 96 205), (row3 169 10 217), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 169 10 217), (row3 70 434 70), (row3 357 90 187), (row3 170 10 218), (row3 462 462 462), (row3 462 462 462)]

theorem b050_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_12_rows b050_12_labels 259546278794999572972690727970 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_12_rows b050_12_labels]
    decide +kernel

def b050_13_rows : List Row := [(row3 8 32 61), (row3 8 32 62), (row3 8 32 63), (row3 8 33 34), (row3 8 33 35), (row3 8 33 36), (row3 8 33 37), (row3 8 33 38), (row3 8 33 39), (row3 8 33 40), (row3 8 33 41), (row3 8 33 42), (row3 8 33 43), (row3 8 33 44), (row3 8 33 45), (row3 8 33 46)]

def b050_13_labels : List Row := [(row3 462 462 462), (row3 170 10 218), (row3 357 90 187), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_13_rows b050_13_labels 7089855376081162750445409750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_13_rows b050_13_labels]
    decide +kernel

def b050_14_rows : List Row := [(row3 8 33 47), (row3 8 33 48), (row3 8 33 49), (row3 8 33 50), (row3 8 33 51), (row3 8 33 52), (row3 8 33 53), (row3 8 33 54), (row3 8 33 55), (row3 8 33 56), (row3 8 33 57), (row3 8 33 58), (row3 8 33 59), (row3 8 33 60), (row3 8 33 61), (row3 8 33 62)]

def b050_14_labels : List Row := [(row3 462 462 462), (row3 277 277 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 163 193), (row3 301 301 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b050_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_14_rows b050_14_labels 1279811055788984807092680000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_14_rows b050_14_labels]
    decide +kernel

def b050_15_rows : List Row := [(row3 8 33 63), (row3 8 34 35), (row3 8 34 36), (row3 8 34 37), (row3 8 34 38), (row3 8 34 39), (row3 8 34 40), (row3 8 34 41), (row3 8 34 42), (row3 8 34 43), (row3 8 34 44), (row3 8 34 45), (row3 8 34 46), (row3 8 34 47), (row3 8 34 48), (row3 8 34 49)]

def b050_15_labels : List Row := [(row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 246 462 246)]

theorem b050_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b050_15_rows b050_15_labels 64177243888706404069000500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b050_15_rows b050_15_labels]
    decide +kernel

theorem checked050 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_050 QuarticIntegerComputationalData.ids64_050 738490927155751639568099797920 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b050_00_rows ++ b050_01_rows) ++ (b050_02_rows ++ b050_03_rows)) ++ ((b050_04_rows ++ b050_05_rows) ++ (b050_06_rows ++ b050_07_rows))) ++ (((b050_08_rows ++ b050_09_rows) ++ (b050_10_rows ++ b050_11_rows)) ++ ((b050_12_rows ++ b050_13_rows) ++ (b050_14_rows ++ b050_15_rows))))
    ((((b050_00_labels ++ b050_01_labels) ++ (b050_02_labels ++ b050_03_labels)) ++ ((b050_04_labels ++ b050_05_labels) ++ (b050_06_labels ++ b050_07_labels))) ++ (((b050_08_labels ++ b050_09_labels) ++ (b050_10_labels ++ b050_11_labels)) ++ ((b050_12_labels ++ b050_13_labels) ++ (b050_14_labels ++ b050_15_labels)))) 738490927155751639568099797920
  exact ((((b050_00_checked.append (c := 945931314185876589119091000) b050_01_checked (by decide +kernel)).append (c := 946145968826017017890016000) (b050_02_checked.append (c := 214654640140428770925000) b050_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 11990474280618079785221605500) ((b050_04_checked.append (c := 13733899408298564019252000) b050_05_checked (by decide +kernel)).append (c := 11044328311792062767331589500) (b050_06_checked.append (c := 11030594412383764203312337500) b050_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 738490927155751639568099797920) (((b050_08_checked.append (c := 17355281802681322973128730250) b050_09_checked (by decide +kernel)).append (c := 458520330404375132848580374200) (b050_10_checked.append (c := 441165048601693809875451643950) b050_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 726500452875133559782878192420) ((b050_12_checked.append (c := 266636134171080735723136137720) b050_13_checked (by decide +kernel)).append (c := 267980122470758426934297818220) (b050_14_checked.append (c := 1343988299677691211161680500) b050_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b051_00_rows : List Row := [(row3 8 34 50), (row3 8 34 51), (row3 8 34 52), (row3 8 34 53), (row3 8 34 54), (row3 8 34 55), (row3 8 34 56), (row3 8 34 57), (row3 8 34 58), (row3 8 34 59), (row3 8 34 60), (row3 8 34 61), (row3 8 34 62), (row3 8 34 63), (row3 8 35 36), (row3 8 35 37)]

def b051_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_00_rows b051_00_labels 3974736731292688009171500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_00_rows b051_00_labels]
    decide +kernel

def b051_01_rows : List Row := [(row3 8 35 38), (row3 8 35 39), (row3 8 35 40), (row3 8 35 41), (row3 8 35 42), (row3 8 35 43), (row3 8 35 44), (row3 8 35 45), (row3 8 35 46), (row3 8 35 47), (row3 8 35 48), (row3 8 35 49), (row3 8 35 50), (row3 8 35 51), (row3 8 35 52), (row3 8 35 53)]

def b051_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_01_rows b051_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_01_rows b051_01_labels]
    decide +kernel

def b051_02_rows : List Row := [(row3 8 35 54), (row3 8 35 55), (row3 8 35 56), (row3 8 35 57), (row3 8 35 58), (row3 8 35 59), (row3 8 35 60), (row3 8 35 61), (row3 8 35 62), (row3 8 35 63), (row3 8 36 37), (row3 8 36 38), (row3 8 36 39), (row3 8 36 40), (row3 8 36 41), (row3 8 36 42)]

def b051_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_02_rows b051_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_02_rows b051_02_labels]
    decide +kernel

def b051_03_rows : List Row := [(row3 8 36 43), (row3 8 36 44), (row3 8 36 45), (row3 8 36 46), (row3 8 36 47), (row3 8 36 48), (row3 8 36 49), (row3 8 36 50), (row3 8 36 51), (row3 8 36 52), (row3 8 36 53), (row3 8 36 54), (row3 8 36 55), (row3 8 36 56), (row3 8 36 57), (row3 8 36 58)]

def b051_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_03_rows b051_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_03_rows b051_03_labels]
    decide +kernel

def b051_04_rows : List Row := [(row3 8 36 59), (row3 8 36 60), (row3 8 36 61), (row3 8 36 62), (row3 8 36 63), (row3 8 37 38), (row3 8 37 39), (row3 8 37 40), (row3 8 37 41), (row3 8 37 42), (row3 8 37 43), (row3 8 37 44), (row3 8 37 45), (row3 8 37 46), (row3 8 37 47), (row3 8 37 48)]

def b051_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_04_rows b051_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_04_rows b051_04_labels]
    decide +kernel

def b051_05_rows : List Row := [(row3 8 37 49), (row3 8 37 50), (row3 8 37 51), (row3 8 37 52), (row3 8 37 53), (row3 8 37 54), (row3 8 37 55), (row3 8 37 56), (row3 8 37 57), (row3 8 37 58), (row3 8 37 59), (row3 8 37 60), (row3 8 37 61), (row3 8 37 62), (row3 8 37 63), (row3 8 38 39)]

def b051_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_05_rows b051_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_05_rows b051_05_labels]
    decide +kernel

def b051_06_rows : List Row := [(row3 8 38 40), (row3 8 38 41), (row3 8 38 42), (row3 8 38 43), (row3 8 38 44), (row3 8 38 45), (row3 8 38 46), (row3 8 38 47), (row3 8 38 48), (row3 8 38 49), (row3 8 38 50), (row3 8 38 51), (row3 8 38 52), (row3 8 38 53), (row3 8 38 54), (row3 8 38 55)]

def b051_06_labels : List Row := [(row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246)]

theorem b051_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_06_rows b051_06_labels 1851703297269869112835500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_06_rows b051_06_labels]
    decide +kernel

def b051_07_rows : List Row := [(row3 8 38 56), (row3 8 38 57), (row3 8 38 58), (row3 8 38 59), (row3 8 38 60), (row3 8 38 61), (row3 8 38 62), (row3 8 38 63), (row3 8 39 40), (row3 8 39 41), (row3 8 39 42), (row3 8 39 43), (row3 8 39 44), (row3 8 39 45), (row3 8 39 46), (row3 8 39 47)]

def b051_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 232 232), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_07_rows b051_07_labels 12136640268036705517759500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_07_rows b051_07_labels]
    decide +kernel

def b051_08_rows : List Row := [(row3 8 39 48), (row3 8 39 49), (row3 8 39 50), (row3 8 39 51), (row3 8 39 52), (row3 8 39 53), (row3 8 39 54), (row3 8 39 55), (row3 8 39 56), (row3 8 39 57), (row3 8 39 58), (row3 8 39 59), (row3 8 39 60), (row3 8 39 61), (row3 8 39 62), (row3 8 39 63)]

def b051_08_labels : List Row := [(row3 277 277 265), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 193 163 193), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 301 301 278)]

theorem b051_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_08_rows b051_08_labels 1342136596380421342048845000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_08_rows b051_08_labels]
    decide +kernel

def b051_09_rows : List Row := [(row3 8 40 41), (row3 8 40 42), (row3 8 40 43), (row3 8 40 44), (row3 8 40 45), (row3 8 40 46), (row3 8 40 47), (row3 8 40 48), (row3 8 40 49), (row3 8 40 50), (row3 8 40 51), (row3 8 40 52), (row3 8 40 53), (row3 8 40 54), (row3 8 40 55), (row3 8 40 56)]

def b051_09_labels : List Row := [(row3 269 269 462), (row3 239 239 462), (row3 240 240 462), (row3 462 462 462), (row3 240 240 462), (row3 239 239 462), (row3 269 269 462), (row3 355 374 364), (row3 179 153 151), (row3 270 270 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 270 270 462), (row3 179 153 151), (row3 80 30 446)]

theorem b051_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_09_rows b051_09_labels 4465885673937162684233907077700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_09_rows b051_09_labels]
    decide +kernel

def b051_10_rows : List Row := [(row3 8 40 57), (row3 8 40 58), (row3 8 40 59), (row3 8 40 60), (row3 8 40 61), (row3 8 40 62), (row3 8 40 63), (row3 8 41 42), (row3 8 41 43), (row3 8 41 44), (row3 8 41 45), (row3 8 41 46), (row3 8 41 47), (row3 8 41 48), (row3 8 41 49), (row3 8 41 50)]

def b051_10_labels : List Row := [(row3 353 375 366), (row3 180 154 154), (row3 263 263 462), (row3 462 462 462), (row3 263 263 462), (row3 180 154 154), (row3 353 375 366), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 166 190 167), (row3 303 462 303), (row3 462 462 462)]

theorem b051_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_10_rows b051_10_labels 49556902881859030608639174900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_10_rows b051_10_labels]
    decide +kernel

def b051_11_rows : List Row := [(row3 8 41 51), (row3 8 41 52), (row3 8 41 53), (row3 8 41 54), (row3 8 41 55), (row3 8 41 56), (row3 8 41 57), (row3 8 41 58), (row3 8 41 59), (row3 8 41 60), (row3 8 41 61), (row3 8 41 62), (row3 8 41 63), (row3 8 42 43), (row3 8 42 44), (row3 8 42 45)]

def b051_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 95 435 41), (row3 127 137 126), (row3 287 462 287), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 163 228 160), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_11_rows b051_11_labels 362933928235342411797440722530 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_11_rows b051_11_labels]
    decide +kernel

def b051_12_rows : List Row := [(row3 8 42 46), (row3 8 42 47), (row3 8 42 48), (row3 8 42 49), (row3 8 42 50), (row3 8 42 51), (row3 8 42 52), (row3 8 42 53), (row3 8 42 54), (row3 8 42 55), (row3 8 42 56), (row3 8 42 57), (row3 8 42 58), (row3 8 42 59), (row3 8 42 60), (row3 8 42 61)]

def b051_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 266 266 265), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 180 180), (row3 309 309 306), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_12_rows b051_12_labels 1238902257926344867165537200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_12_rows b051_12_labels]
    decide +kernel

def b051_13_rows : List Row := [(row3 8 42 62), (row3 8 42 63), (row3 8 43 44), (row3 8 43 45), (row3 8 43 46), (row3 8 43 47), (row3 8 43 48), (row3 8 43 49), (row3 8 43 50), (row3 8 43 51), (row3 8 43 52), (row3 8 43 53), (row3 8 43 54), (row3 8 43 55), (row3 8 43 56), (row3 8 43 57)]

def b051_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228)]

theorem b051_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_13_rows b051_13_labels 6907911636058179450183000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_13_rows b051_13_labels]
    decide +kernel

def b051_14_rows : List Row := [(row3 8 43 58), (row3 8 43 59), (row3 8 43 60), (row3 8 43 61), (row3 8 43 62), (row3 8 43 63), (row3 8 44 45), (row3 8 44 46), (row3 8 44 47), (row3 8 44 48), (row3 8 44 49), (row3 8 44 50), (row3 8 44 51), (row3 8 44 52), (row3 8 44 53), (row3 8 44 54)]

def b051_14_labels : List Row := [(row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_14_rows b051_14_labels 1309335396475262222362500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_14_rows b051_14_labels]
    decide +kernel

def b051_15_rows : List Row := [(row3 8 44 55), (row3 8 44 56), (row3 8 44 57), (row3 8 44 58), (row3 8 44 59), (row3 8 44 60), (row3 8 44 61), (row3 8 44 62), (row3 8 44 63), (row3 8 45 46), (row3 8 45 47), (row3 8 45 48), (row3 8 45 49), (row3 8 45 50), (row3 8 45 51), (row3 8 45 52)]

def b051_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b051_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b051_15_rows b051_15_labels 555889215118270689432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b051_15_rows b051_15_labels]
    decide +kernel

theorem checked051 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_051 QuarticIntegerComputationalData.ids64_051 4880984280125215143824203101330 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b051_00_rows ++ b051_01_rows) ++ (b051_02_rows ++ b051_03_rows)) ++ ((b051_04_rows ++ b051_05_rows) ++ (b051_06_rows ++ b051_07_rows))) ++ (((b051_08_rows ++ b051_09_rows) ++ (b051_10_rows ++ b051_11_rows)) ++ ((b051_12_rows ++ b051_13_rows) ++ (b051_14_rows ++ b051_15_rows))))
    ((((b051_00_labels ++ b051_01_labels) ++ (b051_02_labels ++ b051_03_labels)) ++ ((b051_04_labels ++ b051_05_labels) ++ (b051_06_labels ++ b051_07_labels))) ++ (((b051_08_labels ++ b051_09_labels) ++ (b051_10_labels ++ b051_11_labels)) ++ ((b051_12_labels ++ b051_13_labels) ++ (b051_14_labels ++ b051_15_labels)))) 4880984280125215143824203101330
  exact ((((b051_00_checked.append (c := 3974736731292688009171500) b051_01_checked (by decide +kernel)).append (c := 3974736731292688009171500) (b051_02_checked.append (c := 0) b051_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17963080296599262639766500) ((b051_04_checked.append (c := 0) b051_05_checked (by decide +kernel)).append (c := 13988343565306574630595000) (b051_06_checked.append (c := 13988343565306574630595000) b051_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4880984280125215143824203101330) (((b051_08_checked.append (c := 4467227810533543105575955922700) b051_09_checked (by decide +kernel)).append (c := 4879718641650744547982035820130) (b051_10_checked.append (c := 412490831117201442406079897430) b051_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4880966317044918544561563334830) ((b051_12_checked.append (c := 1245810169562403046615720200) b051_13_checked (by decide +kernel)).append (c := 1247675394173996579527514700) (b051_14_checked.append (c := 1865224611593532911794500) b051_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b052_00_rows : List Row := [(row3 8 45 53), (row3 8 45 54), (row3 8 45 55), (row3 8 45 56), (row3 8 45 57), (row3 8 45 58), (row3 8 45 59), (row3 8 45 60), (row3 8 45 61), (row3 8 45 62), (row3 8 45 63), (row3 8 46 47), (row3 8 46 48), (row3 8 46 49), (row3 8 46 50), (row3 8 46 51)]

def b052_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 228 228), (row3 462 462 462), (row3 266 266 265), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b052_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_00_rows b052_00_labels 65040659106850875639357900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_00_rows b052_00_labels]
    decide +kernel

def b052_01_rows : List Row := [(row3 8 46 52), (row3 8 46 53), (row3 8 46 54), (row3 8 46 55), (row3 8 46 56), (row3 8 46 57), (row3 8 46 58), (row3 8 46 59), (row3 8 46 60), (row3 8 46 61), (row3 8 46 62), (row3 8 46 63), (row3 8 47 48), (row3 8 47 49), (row3 8 47 50), (row3 8 47 51)]

def b052_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 462 180 180), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 309 309 306), (row3 166 190 167), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462)]

theorem b052_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_01_rows b052_01_labels 7317390670038363357922543200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_01_rows b052_01_labels]
    decide +kernel

def b052_02_rows : List Row := [(row3 8 47 52), (row3 8 47 53), (row3 8 47 54), (row3 8 47 55), (row3 8 47 56), (row3 8 47 57), (row3 8 47 58), (row3 8 47 59), (row3 8 47 60), (row3 8 47 61), (row3 8 47 62), (row3 8 47 63), (row3 8 48 49), (row3 8 48 50), (row3 8 48 51), (row3 8 48 52)]

def b052_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 303 462 303), (row3 95 435 41), (row3 163 228 160), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 287 462 287), (row3 127 137 126), (row3 384 397 400), (row3 164 164 206), (row3 256 255 256), (row3 462 239 239)]

theorem b052_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_02_rows b052_02_labels 1723246101617280392739974423190 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_02_rows b052_02_labels]
    decide +kernel

def b052_03_rows : List Row := [(row3 8 48 53), (row3 8 48 54), (row3 8 48 55), (row3 8 48 56), (row3 8 48 57), (row3 8 48 58), (row3 8 48 59), (row3 8 48 60), (row3 8 48 61), (row3 8 48 62), (row3 8 48 63), (row3 8 49 50), (row3 8 49 51), (row3 8 49 52), (row3 8 49 53), (row3 8 49 54)]

def b052_03_labels : List Row := [(row3 256 255 256), (row3 164 164 206), (row3 384 397 400), (row3 441 459 21), (row3 57 53 51), (row3 363 386 393), (row3 193 192 238), (row3 462 462 462), (row3 193 192 238), (row3 363 386 393), (row3 57 53 51), (row3 307 307 462), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 294 294 462)]

theorem b052_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_03_rows b052_03_labels 871336195950183442579811260160820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_03_rows b052_03_labels]
    decide +kernel

def b052_04_rows : List Row := [(row3 8 49 55), (row3 8 49 56), (row3 8 49 57), (row3 8 49 58), (row3 8 49 59), (row3 8 49 60), (row3 8 49 61), (row3 8 49 62), (row3 8 49 63), (row3 8 50 51), (row3 8 50 52), (row3 8 50 53), (row3 8 50 54), (row3 8 50 55), (row3 8 50 56), (row3 8 50 57)]

def b052_04_labels : List Row := [(row3 130 104 104), (row3 47 26 453), (row3 417 423 422), (row3 129 103 102), (row3 286 286 462), (row3 462 462 462), (row3 284 284 462), (row3 131 105 105), (row3 396 416 408), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 294 462 294), (row3 181 435 42), (row3 100 113 100)]

theorem b052_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_04_rows b052_04_labels 16929041379008516140041793038240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_04_rows b052_04_labels]
    decide +kernel

def b052_05_rows : List Row := [(row3 8 50 58), (row3 8 50 59), (row3 8 50 60), (row3 8 50 61), (row3 8 50 62), (row3 8 50 63), (row3 8 51 52), (row3 8 51 53), (row3 8 51 54), (row3 8 51 55), (row3 8 51 56), (row3 8 51 57), (row3 8 51 58), (row3 8 51 59), (row3 8 51 60), (row3 8 51 61)]

def b052_05_labels : List Row := [(row3 316 462 316), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 139 232 138), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 193 193), (row3 309 309 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b052_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_05_rows b052_05_labels 15293820079324370977961217300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_05_rows b052_05_labels]
    decide +kernel

def b052_06_rows : List Row := [(row3 8 51 62), (row3 8 51 63), (row3 8 52 53), (row3 8 52 54), (row3 8 52 55), (row3 8 52 56), (row3 8 52 57), (row3 8 52 58), (row3 8 52 59), (row3 8 52 60), (row3 8 52 61), (row3 8 52 62), (row3 8 52 63), (row3 8 53 54), (row3 8 53 55), (row3 8 53 56)]

def b052_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 232 232), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 232 232), (row3 462 462 462), (row3 235 462 235), (row3 462 193 193)]

theorem b052_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_06_rows b052_06_labels 529842529324598263107534000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_06_rows b052_06_labels]
    decide +kernel

def b052_07_rows : List Row := [(row3 8 53 57), (row3 8 53 58), (row3 8 53 59), (row3 8 53 60), (row3 8 53 61), (row3 8 53 62), (row3 8 53 63), (row3 8 54 55), (row3 8 54 56), (row3 8 54 57), (row3 8 54 58), (row3 8 54 59), (row3 8 54 60), (row3 8 54 61), (row3 8 54 62), (row3 8 54 63)]

def b052_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 309 309 306), (row3 307 462 307), (row3 181 435 42), (row3 139 232 138), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 316 462 316), (row3 100 113 100)]

theorem b052_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_07_rows b052_07_labels 398229244370842248936440758890 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_07_rows b052_07_labels]
    decide +kernel

def b052_08_rows : List Row := [(row3 8 55 56), (row3 8 55 57), (row3 8 55 58), (row3 8 55 59), (row3 8 55 60), (row3 8 55 61), (row3 8 55 62), (row3 8 55 63), (row3 8 56 57), (row3 8 56 58), (row3 8 56 59), (row3 8 56 60), (row3 8 56 61), (row3 8 56 62), (row3 8 56 63), (row3 8 57 58)]

def b052_08_labels : List Row := [(row3 47 26 453), (row3 396 416 408), (row3 131 105 105), (row3 284 284 462), (row3 462 462 462), (row3 286 286 462), (row3 129 103 102), (row3 417 423 422), (row3 450 22 460), (row3 37 444 28), (row3 336 72 428), (row3 462 208 208), (row3 336 72 428), (row3 37 444 28), (row3 450 22 460), (row3 418 422 424)]

theorem b052_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_08_rows b052_08_labels 1968464444021044327589394960474030 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_08_rows b052_08_labels]
    decide +kernel

def b052_09_rows : List Row := [(row3 8 57 59), (row3 8 57 60), (row3 8 57 61), (row3 8 57 62), (row3 8 57 63), (row3 8 58 59), (row3 8 58 60), (row3 8 58 61), (row3 8 58 62), (row3 8 58 63), (row3 8 59 60), (row3 8 59 61), (row3 8 59 62), (row3 8 59 63), (row3 8 60 61), (row3 8 60 62)]

def b052_09_labels : List Row := [(row3 127 126 137), (row3 279 278 279), (row3 163 162 235), (row3 395 407 415), (row3 38 33 33), (row3 307 307 462), (row3 234 234 462), (row3 285 285 462), (row3 131 105 105), (row3 395 415 407), (row3 462 462 462), (row3 462 462 462), (row3 285 462 285), (row3 163 235 162), (row3 462 462 462), (row3 234 462 234)]

theorem b052_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_09_rows b052_09_labels 1701820894838258550759589130760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_09_rows b052_09_labels]
    decide +kernel

def b052_10_rows : List Row := [(row3 8 60 63), (row3 8 61 62), (row3 8 61 63), (row3 8 62 63), (row3 9 10 11), (row3 9 10 12), (row3 9 10 13), (row3 9 10 14), (row3 9 10 15), (row3 9 10 16), (row3 9 10 17), (row3 9 10 18), (row3 9 10 19), (row3 9 10 20), (row3 9 10 21), (row3 9 10 22)]

def b052_10_labels : List Row := [(row3 279 279 278), (row3 307 462 307), (row3 127 137 126), (row3 418 424 422), (row3 47 26 453), (row3 372 430 58), (row3 187 90 357), (row3 366 375 353), (row3 51 53 57), (row3 33 33 38), (row3 458 456 456), (row3 32 25 452), (row3 412 437 39), (row3 157 83 399), (row3 462 284 284), (row3 160 228 163)]

theorem b052_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_10_rows b052_10_labels 52279183303784979721993190764230 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_10_rows b052_10_labels]
    decide +kernel

def b052_11_rows : List Row := [(row3 9 10 23), (row3 9 10 24), (row3 9 10 25), (row3 9 10 26), (row3 9 10 27), (row3 9 10 28), (row3 9 10 29), (row3 9 10 30), (row3 9 10 31), (row3 9 10 32), (row3 9 10 33), (row3 9 10 34), (row3 9 10 35), (row3 9 10 36), (row3 9 10 37), (row3 9 10 38)]

def b052_11_labels : List Row := [(row3 408 416 396), (row3 407 415 395), (row3 52 49 62), (row3 410 431 59), (row3 135 83 398), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 138 232 139), (row3 162 235 163), (row3 365 373 352), (row3 159 91 356), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b052_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_11_rows b052_11_labels 481366779660935307292298818350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_11_rows b052_11_labels]
    decide +kernel

def b052_12_rows : List Row := [(row3 9 10 39), (row3 9 10 40), (row3 9 10 41), (row3 9 10 42), (row3 9 10 43), (row3 9 10 44), (row3 9 10 45), (row3 9 10 46), (row3 9 10 47), (row3 9 10 48), (row3 9 10 49), (row3 9 10 50), (row3 9 10 51), (row3 9 10 52), (row3 9 10 53), (row3 9 10 54)]

def b052_12_labels : List Row := [(row3 462 462 462), (row3 278 279 279), (row3 189 232 193), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 126 137 127), (row3 366 376 354), (row3 158 89 356), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462)]

theorem b052_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_12_rows b052_12_labels 32290617508227891769097642430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_12_rows b052_12_labels]
    decide +kernel

def b052_13_rows : List Row := [(row3 9 10 55), (row3 9 10 56), (row3 9 10 57), (row3 9 10 58), (row3 9 10 59), (row3 9 10 60), (row3 9 10 61), (row3 9 10 62), (row3 9 10 63), (row3 9 11 12), (row3 9 11 13), (row3 9 11 14), (row3 9 11 15), (row3 9 11 16), (row3 9 11 17), (row3 9 11 18)]

def b052_13_labels : List Row := [(row3 306 309 309), (row3 422 424 418), (row3 50 48 61), (row3 411 432 60), (row3 134 81 398), (row3 462 293 293), (row3 232 232 462), (row3 306 309 309), (row3 100 113 100), (row3 166 190 167), (row3 273 462 273), (row3 194 188 195), (row3 350 346 349), (row3 380 380 379), (row3 52 62 49), (row3 382 381 378)]

theorem b052_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_13_rows b052_13_labels 5889875593335738811694165527020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_13_rows b052_13_labels]
    decide +kernel

def b052_14_rows : List Row := [(row3 9 11 19), (row3 9 11 20), (row3 9 11 21), (row3 9 11 22), (row3 9 11 23), (row3 9 11 24), (row3 9 11 25), (row3 9 11 26), (row3 9 11 27), (row3 9 11 28), (row3 9 11 29), (row3 9 11 30), (row3 9 11 31), (row3 9 11 32), (row3 9 11 33), (row3 9 11 34)]

def b052_14_labels : List Row := [(row3 132 137 133), (row3 288 462 288), (row3 235 462 235), (row3 273 462 273), (row3 143 137 146), (row3 145 137 148), (row3 347 345 345), (row3 144 137 147), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 273 462 273), (row3 198 190 199), (row3 273 462 273)]

theorem b052_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_14_rows b052_14_labels 15253838411582099037540504960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_14_rows b052_14_labels]
    decide +kernel

def b052_15_rows : List Row := [(row3 9 11 35), (row3 9 11 36), (row3 9 11 37), (row3 9 11 38), (row3 9 11 39), (row3 9 11 40), (row3 9 11 41), (row3 9 11 42), (row3 9 11 43), (row3 9 11 44), (row3 9 11 45), (row3 9 11 46), (row3 9 11 47), (row3 9 11 48), (row3 9 11 49), (row3 9 11 50)]

def b052_15_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 261 462 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 196 190 197), (row3 273 462 273)]

theorem b052_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b052_15_rows b052_15_labels 126041965129541610598811040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b052_15_rows b052_15_labels]
    decide +kernel

theorem checked052 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_052 QuarticIntegerComputationalData.ids64_052 2919274279859667055058555540706360 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b052_00_rows ++ b052_01_rows) ++ (b052_02_rows ++ b052_03_rows)) ++ ((b052_04_rows ++ b052_05_rows) ++ (b052_06_rows ++ b052_07_rows))) ++ (((b052_08_rows ++ b052_09_rows) ++ (b052_10_rows ++ b052_11_rows)) ++ ((b052_12_rows ++ b052_13_rows) ++ (b052_14_rows ++ b052_15_rows))))
    ((((b052_00_labels ++ b052_01_labels) ++ (b052_02_labels ++ b052_03_labels)) ++ ((b052_04_labels ++ b052_05_labels) ++ (b052_06_labels ++ b052_07_labels))) ++ (((b052_08_labels ++ b052_09_labels) ++ (b052_10_labels ++ b052_11_labels)) ++ ((b052_12_labels ++ b052_13_labels) ++ (b052_14_labels ++ b052_15_labels)))) 2919274279859667055058555540706360
  exact ((((b052_00_checked.append (c := 7382431329145214233561901100) b052_01_checked (by decide +kernel)).append (c := 873066824483129868186784796485110) (b052_02_checked.append (c := 873059442051800722972551234584010) b052_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 890409918769117875545004099033540) ((b052_04_checked.append (c := 16944335199087840511019754255540) b052_05_checked (by decide +kernel)).append (c := 17343094285988007358219302548430) (b052_06_checked.append (c := 398759086900166847199548292890) b052_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2919274279859667055058555540706360) (((b052_08_checked.append (c := 1970166264915882586140154549604790) b052_09_checked (by decide +kernel)).append (c := 2022926814999328501169440039187370) (b052_10_checked.append (c := 52760550083445915029285489582580) b052_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2028864361090549179513551441672820) ((b052_12_checked.append (c := 5922166210843966703463263169450) b052_13_checked (by decide +kernel)).append (c := 5937546091220678344111402485450) (b052_14_checked.append (c := 15379880376711640648139316000) b052_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b053_00_rows : List Row := [(row3 9 11 51), (row3 9 11 52), (row3 9 11 53), (row3 9 11 54), (row3 9 11 55), (row3 9 11 56), (row3 9 11 57), (row3 9 11 58), (row3 9 11 59), (row3 9 11 60), (row3 9 11 61), (row3 9 11 62), (row3 9 11 63), (row3 9 12 13), (row3 9 12 14), (row3 9 12 15)]

def b053_00_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 126 137 127), (row3 350 348 351), (row3 141 136 142), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 232 462 232), (row3 300 462 300), (row3 238 462 238), (row3 275 276 276), (row3 165 176 165)]

theorem b053_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_00_rows b053_00_labels 14430161291902283153912898000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_00_rows b053_00_labels]
    decide +kernel

def b053_01_rows : List Row := [(row3 9 12 16), (row3 9 12 17), (row3 9 12 18), (row3 9 12 19), (row3 9 12 20), (row3 9 12 21), (row3 9 12 22), (row3 9 12 23), (row3 9 12 24), (row3 9 12 25), (row3 9 12 26), (row3 9 12 27), (row3 9 12 28), (row3 9 12 29), (row3 9 12 30), (row3 9 12 31)]

def b053_01_labels : List Row := [(row3 176 176 161), (row3 365 352 373), (row3 175 175 161), (row3 278 279 279), (row3 236 462 236), (row3 462 462 462), (row3 236 462 236), (row3 278 282 282), (row3 278 279 279), (row3 198 199 190), (row3 278 279 279), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b053_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_01_rows b053_01_labels 11000003816351057008034407890 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_01_rows b053_01_labels]
    decide +kernel

def b053_02_rows : List Row := [(row3 9 12 32), (row3 9 12 33), (row3 9 12 34), (row3 9 12 35), (row3 9 12 36), (row3 9 12 37), (row3 9 12 38), (row3 9 12 39), (row3 9 12 40), (row3 9 12 41), (row3 9 12 42), (row3 9 12 43), (row3 9 12 44), (row3 9 12 45), (row3 9 12 46), (row3 9 12 47)]

def b053_02_labels : List Row := [(row3 236 462 236), (row3 261 262 262), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_02_rows b053_02_labels 3691450176326031038725200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_02_rows b053_02_labels]
    decide +kernel

def b053_03_rows : List Row := [(row3 9 12 48), (row3 9 12 49), (row3 9 12 50), (row3 9 12 51), (row3 9 12 52), (row3 9 12 53), (row3 9 12 54), (row3 9 12 55), (row3 9 12 56), (row3 9 12 57), (row3 9 12 58), (row3 9 12 59), (row3 9 12 60), (row3 9 12 61), (row3 9 12 62), (row3 9 12 63)]

def b053_03_labels : List Row := [(row3 236 462 236), (row3 261 262 262), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 279 279), (row3 198 199 190), (row3 278 283 283), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b053_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_03_rows b053_03_labels 224627500915791723222254580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_03_rows b053_03_labels]
    decide +kernel

def b053_04_rows : List Row := [(row3 9 13 14), (row3 9 13 15), (row3 9 13 16), (row3 9 13 17), (row3 9 13 18), (row3 9 13 19), (row3 9 13 20), (row3 9 13 21), (row3 9 13 22), (row3 9 13 23), (row3 9 13 24), (row3 9 13 25), (row3 9 13 26), (row3 9 13 27), (row3 9 13 28), (row3 9 13 29)]

def b053_04_labels : List Row := [(row3 179 153 151), (row3 349 346 350), (row3 288 288 288), (row3 189 193 232), (row3 273 273 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 220 222 221), (row3 233 235 236), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_04_rows b053_04_labels 11863423833332085443351255040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_04_rows b053_04_labels]
    decide +kernel

def b053_05_rows : List Row := [(row3 9 13 30), (row3 9 13 31), (row3 9 13 32), (row3 9 13 33), (row3 9 13 34), (row3 9 13 35), (row3 9 13 36), (row3 9 13 37), (row3 9 13 38), (row3 9 13 39), (row3 9 13 40), (row3 9 13 41), (row3 9 13 42), (row3 9 13 43), (row3 9 13 44), (row3 9 13 45)]

def b053_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_05_rows b053_05_labels 387015114171401891532000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_05_rows b053_05_labels]
    decide +kernel

def b053_06_rows : List Row := [(row3 9 13 46), (row3 9 13 47), (row3 9 13 48), (row3 9 13 49), (row3 9 13 50), (row3 9 13 51), (row3 9 13 52), (row3 9 13 53), (row3 9 13 54), (row3 9 13 55), (row3 9 13 56), (row3 9 13 57), (row3 9 13 58), (row3 9 13 59), (row3 9 13 60), (row3 9 13 61)]

def b053_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 230 238 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 162 235 163), (row3 290 261 288), (row3 228 235 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_06_rows b053_06_labels 757857142072329819165676800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_06_rows b053_06_labels]
    decide +kernel

def b053_07_rows : List Row := [(row3 9 13 62), (row3 9 13 63), (row3 9 14 15), (row3 9 14 16), (row3 9 14 17), (row3 9 14 18), (row3 9 14 19), (row3 9 14 20), (row3 9 14 21), (row3 9 14 22), (row3 9 14 23), (row3 9 14 24), (row3 9 14 25), (row3 9 14 26), (row3 9 14 27), (row3 9 14 28)]

def b053_07_labels : List Row := [(row3 232 462 232), (row3 288 462 288), (row3 57 53 51), (row3 106 106 107), (row3 366 354 376), (row3 175 175 161), (row3 278 280 280), (row3 231 234 231), (row3 278 279 279), (row3 177 150 152), (row3 323 324 324), (row3 295 298 298), (row3 196 197 190), (row3 278 279 279), (row3 235 462 235), (row3 462 244 244)]

theorem b053_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_07_rows b053_07_labels 1407783304940169528514530471630 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_07_rows b053_07_labels]
    decide +kernel

def b053_08_rows : List Row := [(row3 9 14 29), (row3 9 14 30), (row3 9 14 31), (row3 9 14 32), (row3 9 14 33), (row3 9 14 34), (row3 9 14 35), (row3 9 14 36), (row3 9 14 37), (row3 9 14 38), (row3 9 14 39), (row3 9 14 40), (row3 9 14 41), (row3 9 14 42), (row3 9 14 43), (row3 9 14 44)]

def b053_08_labels : List Row := [(row3 234 234 234), (row3 265 266 266), (row3 224 226 229), (row3 233 235 236), (row3 261 262 262), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 243 243), (row3 278 279 279), (row3 230 232 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_08_rows b053_08_labels 37500447490200637050655920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_08_rows b053_08_labels]
    decide +kernel

def b053_09_rows : List Row := [(row3 9 14 45), (row3 9 14 46), (row3 9 14 47), (row3 9 14 48), (row3 9 14 49), (row3 9 14 50), (row3 9 14 51), (row3 9 14 52), (row3 9 14 53), (row3 9 14 54), (row3 9 14 55), (row3 9 14 56), (row3 9 14 57), (row3 9 14 58), (row3 9 14 59), (row3 9 14 60)]

def b053_09_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 232 232 462), (row3 145 137 148), (row3 308 317 317), (row3 225 228 236), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 226 226 237), (row3 306 310 310), (row3 407 415 395), (row3 111 109 110), (row3 319 320 320), (row3 228 232 235), (row3 462 244 244)]

theorem b053_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_09_rows b053_09_labels 38538413069180951407841700510 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_09_rows b053_09_labels]
    decide +kernel

def b053_10_rows : List Row := [(row3 9 14 61), (row3 9 14 62), (row3 9 14 63), (row3 9 15 16), (row3 9 15 17), (row3 9 15 18), (row3 9 15 19), (row3 9 15 20), (row3 9 15 21), (row3 9 15 22), (row3 9 15 23), (row3 9 15 24), (row3 9 15 25), (row3 9 15 26), (row3 9 15 27), (row3 9 15 28)]

def b053_10_labels : List Row := [(row3 226 226 234), (row3 315 318 318), (row3 120 112 120), (row3 421 421 420), (row3 50 61 48), (row3 381 382 378), (row3 146 137 149), (row3 273 273 288), (row3 137 146 149), (row3 382 381 378), (row3 61 50 48), (row3 106 106 107), (row3 350 351 348), (row3 146 137 149), (row3 278 462 278), (row3 462 462 462)]

theorem b053_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_10_rows b053_10_labels 2869758033241727426828132265120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_10_rows b053_10_labels]
    decide +kernel

def b053_11_rows : List Row := [(row3 9 15 29), (row3 9 15 30), (row3 9 15 31), (row3 9 15 32), (row3 9 15 33), (row3 9 15 34), (row3 9 15 35), (row3 9 15 36), (row3 9 15 37), (row3 9 15 38), (row3 9 15 39), (row3 9 15 40), (row3 9 15 41), (row3 9 15 42), (row3 9 15 43), (row3 9 15 44)]

def b053_11_labels : List Row := [(row3 462 278 278), (row3 137 146 149), (row3 351 350 348), (row3 288 288 288), (row3 198 190 199), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 273 273), (row3 190 198 199), (row3 176 176 161), (row3 290 288 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_11_rows b053_11_labels 5889389070380051484165960000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_11_rows b053_11_labels]
    decide +kernel

def b053_12_rows : List Row := [(row3 9 15 45), (row3 9 15 46), (row3 9 15 47), (row3 9 15 48), (row3 9 15 49), (row3 9 15 50), (row3 9 15 51), (row3 9 15 52), (row3 9 15 53), (row3 9 15 54), (row3 9 15 55), (row3 9 15 56), (row3 9 15 57), (row3 9 15 58), (row3 9 15 59), (row3 9 15 60)]

def b053_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 288 290 261), (row3 380 380 379), (row3 111 110 109), (row3 304 295 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 295 304 273), (row3 110 111 109), (row3 33 33 38), (row3 405 406 406), (row3 101 99 98), (row3 300 288 278), (row3 462 462 462)]

theorem b053_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_12_rows b053_12_labels 1654325348542261107284423892960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_12_rows b053_12_labels]
    decide +kernel

def b053_13_rows : List Row := [(row3 9 15 61), (row3 9 15 62), (row3 9 15 63), (row3 9 16 17), (row3 9 16 18), (row3 9 16 19), (row3 9 16 20), (row3 9 16 21), (row3 9 16 22), (row3 9 16 23), (row3 9 16 24), (row3 9 16 25), (row3 9 16 26), (row3 9 16 27), (row3 9 16 28), (row3 9 16 29)]

def b053_13_labels : List Row := [(row3 288 300 278), (row3 99 101 98), (row3 406 405 406), (row3 442 451 24), (row3 406 406 405), (row3 110 109 111), (row3 288 261 290), (row3 190 199 198), (row3 351 348 350), (row3 61 48 50), (row3 57 53 51), (row3 404 402 403), (row3 99 98 101), (row3 295 273 304), (row3 462 462 462), (row3 462 273 273)]

theorem b053_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_13_rows b053_13_labels 30555769126365194646960876067200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_13_rows b053_13_labels]
    decide +kernel

def b053_14_rows : List Row := [(row3 9 16 30), (row3 9 16 31), (row3 9 16 32), (row3 9 16 33), (row3 9 16 34), (row3 9 16 35), (row3 9 16 36), (row3 9 16 37), (row3 9 16 38), (row3 9 16 39), (row3 9 16 40), (row3 9 16 41), (row3 9 16 42), (row3 9 16 43), (row3 9 16 44), (row3 9 16 45)]

def b053_14_labels : List Row := [(row3 137 149 146), (row3 382 378 381), (row3 349 346 350), (row3 125 126 128), (row3 288 278 300), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 278 278), (row3 137 149 146), (row3 165 176 165), (row3 288 288 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b053_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_14_rows b053_14_labels 22358401623587458014239828160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_14_rows b053_14_labels]
    decide +kernel

def b053_15_rows : List Row := [(row3 9 16 46), (row3 9 16 47), (row3 9 16 48), (row3 9 16 49), (row3 9 16 50), (row3 9 16 51), (row3 9 16 52), (row3 9 16 53), (row3 9 16 54), (row3 9 16 55), (row3 9 16 56), (row3 9 16 57), (row3 9 16 58), (row3 9 16 59), (row3 9 16 60), (row3 9 16 61)]

def b053_15_labels : List Row := [(row3 462 462 462), (row3 273 288 273), (row3 350 346 349), (row3 128 126 125), (row3 300 278 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 278 462), (row3 146 149 137), (row3 51 53 57), (row3 403 402 404), (row3 101 98 99), (row3 304 273 295), (row3 462 462 462), (row3 273 273 462)]

theorem b053_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b053_15_rows b053_15_labels 1427127934232017324308028496400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b053_15_rows b053_15_labels]
    decide +kernel

theorem checked053 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_053 QuarticIntegerComputationalData.ids64_053 38019867603581872740019906087410 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b053_00_rows ++ b053_01_rows) ++ (b053_02_rows ++ b053_03_rows)) ++ ((b053_04_rows ++ b053_05_rows) ++ (b053_06_rows ++ b053_07_rows))) ++ (((b053_08_rows ++ b053_09_rows) ++ (b053_10_rows ++ b053_11_rows)) ++ ((b053_12_rows ++ b053_13_rows) ++ (b053_14_rows ++ b053_15_rows))))
    ((((b053_00_labels ++ b053_01_labels) ++ (b053_02_labels ++ b053_03_labels)) ++ ((b053_04_labels ++ b053_05_labels) ++ (b053_06_labels ++ b053_07_labels))) ++ (((b053_08_labels ++ b053_09_labels) ++ (b053_10_labels ++ b053_11_labels)) ++ ((b053_12_labels ++ b053_13_labels) ++ (b053_14_labels ++ b053_15_labels)))) 38019867603581872740019906087410
  exact ((((b053_00_checked.append (c := 25430165108253340161947305890) b053_01_checked (by decide +kernel)).append (c := 25658484059345457916208285670) (b053_02_checked.append (c := 228318951092117754260979780) b053_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1446063456990033573095147221140) ((b053_04_checked.append (c := 11863810848446256845242787040) b053_05_checked (by decide +kernel)).append (c := 1420404972930688115178938935470) (b053_06_checked.append (c := 1408541162082241858333696148430) b053_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 38019867603581872740019906087410) (((b053_08_checked.append (c := 38575913516671152044892356430) b053_09_checked (by decide +kernel)).append (c := 2914223335828778630357190581550) (b053_10_checked.append (c := 2875647422312107478312298225120) b053_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 36573804146591839166924758866270) ((b053_12_checked.append (c := 32210094474907455754245299960160) b053_13_checked (by decide +kernel)).append (c := 33659580810763060536567568284720) (b053_14_checked.append (c := 1449486335855604782322268324560) b053_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b054_00_rows : List Row := [(row3 9 16 62), (row3 9 16 63), (row3 9 17 18), (row3 9 17 19), (row3 9 17 20), (row3 9 17 21), (row3 9 17 22), (row3 9 17 23), (row3 9 17 24), (row3 9 17 25), (row3 9 17 26), (row3 9 17 27), (row3 9 17 28), (row3 9 17 29), (row3 9 17 30), (row3 9 17 31)]

def b054_00_labels : List Row := [(row3 146 149 137), (row3 381 378 382), (row3 32 25 452), (row3 410 431 59), (row3 159 91 356), (row3 462 269 269), (row3 158 89 356), (row3 411 432 60), (row3 413 438 40), (row3 47 26 453), (row3 412 437 39), (row3 135 83 398), (row3 462 284 284), (row3 462 462 462), (row3 462 284 284), (row3 134 81 398)]

theorem b054_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_00_rows b054_00_labels 27397314647039428782700705207380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_00_rows b054_00_labels]
    decide +kernel

def b054_01_rows : List Row := [(row3 9 17 32), (row3 9 17 33), (row3 9 17 34), (row3 9 17 35), (row3 9 17 36), (row3 9 17 37), (row3 9 17 38), (row3 9 17 39), (row3 9 17 40), (row3 9 17 41), (row3 9 17 42), (row3 9 17 43), (row3 9 17 44), (row3 9 17 45), (row3 9 17 46), (row3 9 17 47)]

def b054_01_labels : List Row := [(row3 156 82 399), (row3 372 430 58), (row3 157 83 399), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 278 301 301), (row3 187 90 357), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462)]

theorem b054_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_01_rows b054_01_labels 185950852803894471537236596020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_01_rows b054_01_labels]
    decide +kernel

def b054_02_rows : List Row := [(row3 9 17 48), (row3 9 17 49), (row3 9 17 50), (row3 9 17 51), (row3 9 17 52), (row3 9 17 53), (row3 9 17 54), (row3 9 17 55), (row3 9 17 56), (row3 9 17 57), (row3 9 17 58), (row3 9 17 59), (row3 9 17 60), (row3 9 17 61), (row3 9 17 62), (row3 9 17 63)]

def b054_02_labels : List Row := [(row3 126 137 127), (row3 366 375 353), (row3 160 228 163), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 306 309 309), (row3 422 423 417), (row3 51 53 57), (row3 408 416 396), (row3 138 232 139), (row3 462 462 462), (row3 232 232 462), (row3 306 309 309), (row3 100 113 100)]

theorem b054_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_02_rows b054_02_labels 5509793849467965898743878782620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_02_rows b054_02_labels]
    decide +kernel

def b054_03_rows : List Row := [(row3 9 18 19), (row3 9 18 20), (row3 9 18 21), (row3 9 18 22), (row3 9 18 23), (row3 9 18 24), (row3 9 18 25), (row3 9 18 26), (row3 9 18 27), (row3 9 18 28), (row3 9 18 29), (row3 9 18 30), (row3 9 18 31), (row3 9 18 32), (row3 9 18 33), (row3 9 18 34)]

def b054_03_labels : List Row := [(row3 100 113 100), (row3 300 462 300), (row3 235 462 235), (row3 288 462 288), (row3 120 112 120), (row3 120 112 120), (row3 382 378 381), (row3 100 113 100), (row3 319 462 319), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 295 462 295), (row3 288 462 288), (row3 175 161 175), (row3 300 462 300)]

theorem b054_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_03_rows b054_03_labels 73805957168259624914349959040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_03_rows b054_03_labels]
    decide +kernel

def b054_04_rows : List Row := [(row3 9 18 35), (row3 9 18 36), (row3 9 18 37), (row3 9 18 38), (row3 9 18 39), (row3 9 18 40), (row3 9 18 41), (row3 9 18 42), (row3 9 18 43), (row3 9 18 44), (row3 9 18 45), (row3 9 18 46), (row3 9 18 47), (row3 9 18 48), (row3 9 18 49), (row3 9 18 50)]

def b054_04_labels : List Row := [(row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 300 462 300), (row3 175 161 175), (row3 288 462 288)]

theorem b054_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_04_rows b054_04_labels 341266342286094831963090720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_04_rows b054_04_labels]
    decide +kernel

def b054_05_rows : List Row := [(row3 9 18 51), (row3 9 18 52), (row3 9 18 53), (row3 9 18 54), (row3 9 18 55), (row3 9 18 56), (row3 9 18 57), (row3 9 18 58), (row3 9 18 59), (row3 9 18 60), (row3 9 18 61), (row3 9 18 62), (row3 9 18 63), (row3 9 19 20), (row3 9 19 21), (row3 9 19 22)]

def b054_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 100 113 100), (row3 381 378 382), (row3 120 112 120), (row3 295 462 295), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 319 462 319), (row3 232 462 232), (row3 462 462 462), (row3 232 462 232)]

theorem b054_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_05_rows b054_05_labels 44644061868410307549858746400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_05_rows b054_05_labels]
    decide +kernel

def b054_06_rows : List Row := [(row3 9 19 23), (row3 9 19 24), (row3 9 19 25), (row3 9 19 26), (row3 9 19 27), (row3 9 19 28), (row3 9 19 29), (row3 9 19 30), (row3 9 19 31), (row3 9 19 32), (row3 9 19 33), (row3 9 19 34), (row3 9 19 35), (row3 9 19 36), (row3 9 19 37), (row3 9 19 38)]

def b054_06_labels : List Row := [(row3 306 311 311), (row3 306 310 310), (row3 144 147 137), (row3 306 309 309), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 232 462 232), (row3 278 279 279), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b054_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_06_rows b054_06_labels 648607866595300836597351060 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_06_rows b054_06_labels]
    decide +kernel

def b054_07_rows : List Row := [(row3 9 19 39), (row3 9 19 40), (row3 9 19 41), (row3 9 19 42), (row3 9 19 43), (row3 9 19 44), (row3 9 19 45), (row3 9 19 46), (row3 9 19 47), (row3 9 19 48), (row3 9 19 49), (row3 9 19 50), (row3 9 19 51), (row3 9 19 52), (row3 9 19 53), (row3 9 19 54)]

def b054_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 278 279 279), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b054_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_07_rows b054_07_labels 12974390868591459057999600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_07_rows b054_07_labels]
    decide +kernel

def b054_08_rows : List Row := [(row3 9 19 55), (row3 9 19 56), (row3 9 19 57), (row3 9 19 58), (row3 9 19 59), (row3 9 19 60), (row3 9 19 61), (row3 9 19 62), (row3 9 19 63), (row3 9 20 21), (row3 9 20 22), (row3 9 20 23), (row3 9 20 24), (row3 9 20 25), (row3 9 20 26), (row3 9 20 27)]

def b054_08_labels : List Row := [(row3 462 462 462), (row3 306 309 309), (row3 146 149 137), (row3 306 312 312), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 226 226 234), (row3 232 232 462), (row3 273 273 462), (row3 232 232 462), (row3 462 462 462)]

theorem b054_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_08_rows b054_08_labels 820143436445931781651201560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_08_rows b054_08_labels]
    decide +kernel

def b054_09_rows : List Row := [(row3 9 20 28), (row3 9 20 29), (row3 9 20 30), (row3 9 20 31), (row3 9 20 32), (row3 9 20 33), (row3 9 20 34), (row3 9 20 35), (row3 9 20 36), (row3 9 20 37), (row3 9 20 38), (row3 9 20 39), (row3 9 20 40), (row3 9 20 41), (row3 9 20 42), (row3 9 20 43)]

def b054_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b054_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_09_rows b054_09_labels 258010076114267927688000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_09_rows b054_09_labels]
    decide +kernel

def b054_10_rows : List Row := [(row3 9 20 44), (row3 9 20 45), (row3 9 20 46), (row3 9 20 47), (row3 9 20 48), (row3 9 20 49), (row3 9 20 50), (row3 9 20 51), (row3 9 20 52), (row3 9 20 53), (row3 9 20 54), (row3 9 20 55), (row3 9 20 56), (row3 9 20 57), (row3 9 20 58), (row3 9 20 59)]

def b054_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 273 273 462), (row3 232 232 462), (row3 462 462 462)]

theorem b054_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_10_rows b054_10_labels 12169246176507690557884800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_10_rows b054_10_labels]
    decide +kernel

def b054_11_rows : List Row := [(row3 9 20 60), (row3 9 20 61), (row3 9 20 62), (row3 9 20 63), (row3 9 21 22), (row3 9 21 23), (row3 9 21 24), (row3 9 21 25), (row3 9 21 26), (row3 9 21 27), (row3 9 21 28), (row3 9 21 29), (row3 9 21 30), (row3 9 21 31), (row3 9 21 32), (row3 9 21 33)]

def b054_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b054_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_11_rows b054_11_labels 54426079666796290222878360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_11_rows b054_11_labels]
    decide +kernel

def b054_12_rows : List Row := [(row3 9 21 34), (row3 9 21 35), (row3 9 21 36), (row3 9 21 37), (row3 9 21 38), (row3 9 21 39), (row3 9 21 40), (row3 9 21 41), (row3 9 21 42), (row3 9 21 43), (row3 9 21 44), (row3 9 21 45), (row3 9 21 46), (row3 9 21 47), (row3 9 21 48), (row3 9 21 49)]

def b054_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b054_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_12_rows b054_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_12_rows b054_12_labels]
    decide +kernel

def b054_13_rows : List Row := [(row3 9 21 50), (row3 9 21 51), (row3 9 21 52), (row3 9 21 53), (row3 9 21 54), (row3 9 21 55), (row3 9 21 56), (row3 9 21 57), (row3 9 21 58), (row3 9 21 59), (row3 9 21 60), (row3 9 21 61), (row3 9 21 62), (row3 9 21 63), (row3 9 22 23), (row3 9 22 24)]

def b054_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 129 103 102), (row3 224 226 229)]

theorem b054_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_13_rows b054_13_labels 19613942118905767224115752000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_13_rows b054_13_labels]
    decide +kernel

def b054_14_rows : List Row := [(row3 9 22 25), (row3 9 22 26), (row3 9 22 27), (row3 9 22 28), (row3 9 22 29), (row3 9 22 30), (row3 9 22 31), (row3 9 22 32), (row3 9 22 33), (row3 9 22 34), (row3 9 22 35), (row3 9 22 36), (row3 9 22 37), (row3 9 22 38), (row3 9 22 39), (row3 9 22 40)]

def b054_14_labels : List Row := [(row3 273 273 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b054_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_14_rows b054_14_labels 7281290366715016617285600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_14_rows b054_14_labels]
    decide +kernel

def b054_15_rows : List Row := [(row3 9 22 41), (row3 9 22 42), (row3 9 22 43), (row3 9 22 44), (row3 9 22 45), (row3 9 22 46), (row3 9 22 47), (row3 9 22 48), (row3 9 22 49), (row3 9 22 50), (row3 9 22 51), (row3 9 22 52), (row3 9 22 53), (row3 9 22 54), (row3 9 22 55), (row3 9 22 56)]

def b054_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 225 236 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 138 232 139)]

theorem b054_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b054_15_rows b054_15_labels 1105694881601429922480770400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b054_15_rows b054_15_labels]
    decide +kernel

theorem checked054 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_054 QuarticIntegerComputationalData.ids64_054 33234126132010948334767221193560 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b054_00_rows ++ b054_01_rows) ++ (b054_02_rows ++ b054_03_rows)) ++ ((b054_04_rows ++ b054_05_rows) ++ (b054_06_rows ++ b054_07_rows))) ++ (((b054_08_rows ++ b054_09_rows) ++ (b054_10_rows ++ b054_11_rows)) ++ ((b054_12_rows ++ b054_13_rows) ++ (b054_14_rows ++ b054_15_rows))))
    ((((b054_00_labels ++ b054_01_labels) ++ (b054_02_labels ++ b054_03_labels)) ++ ((b054_04_labels ++ b054_05_labels) ++ (b054_06_labels ++ b054_07_labels))) ++ (((b054_08_labels ++ b054_09_labels) ++ (b054_10_labels ++ b054_11_labels)) ++ ((b054_12_labels ++ b054_13_labels) ++ (b054_14_labels ++ b054_15_labels)))) 33234126132010948334767221193560
  exact ((((b054_00_checked.append (c := 27583265499843323254237941803400) b054_01_checked (by decide +kernel)).append (c := 33166865306479548777896170545060) (b054_02_checked.append (c := 5583599806636225523658228741660) b054_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 33212512216947709072573647732840) ((b054_04_checked.append (c := 44985328210696402381821837120) b054_05_checked (by decide +kernel)).append (c := 45646910468160294677477187780) (b054_06_checked.append (c := 661582257463892295655350660) b054_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 33234126132010948334767221193560) (((b054_08_checked.append (c := 820401446522046049578889560) b054_09_checked (by decide +kernel)).append (c := 886996772365350030359652720) (b054_10_checked.append (c := 66595325843303980780763160) b054_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 21613915063239262193573460720) ((b054_12_checked.append (c := 19613942118905767224115752000) b054_13_checked (by decide +kernel)).append (c := 20726918290873912163213808000) (b054_14_checked.append (c := 1112976171968144939098056000) b054_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b055_00_rows : List Row := [(row3 9 22 57), (row3 9 22 58), (row3 9 22 59), (row3 9 22 60), (row3 9 22 61), (row3 9 22 62), (row3 9 22 63), (row3 9 23 24), (row3 9 23 25), (row3 9 23 26), (row3 9 23 27), (row3 9 23 28), (row3 9 23 29), (row3 9 23 30), (row3 9 23 31), (row3 9 23 32)]

def b055_00_labels : List Row := [(row3 304 273 295), (row3 223 232 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 295 462 295), (row3 323 324 324), (row3 141 142 136), (row3 306 312 312), (row3 228 462 228), (row3 462 246 246), (row3 224 224 224), (row3 306 309 309), (row3 129 103 102), (row3 220 222 221)]

theorem b055_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_00_rows b055_00_labels 20775185044581960244753339680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_00_rows b055_00_labels]
    decide +kernel

def b055_01_rows : List Row := [(row3 9 23 33), (row3 9 23 34), (row3 9 23 35), (row3 9 23 36), (row3 9 23 37), (row3 9 23 38), (row3 9 23 39), (row3 9 23 40), (row3 9 23 41), (row3 9 23 42), (row3 9 23 43), (row3 9 23 44), (row3 9 23 45), (row3 9 23 46), (row3 9 23 47), (row3 9 23 48)]

def b055_01_labels : List Row := [(row3 278 283 283), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 224 224 224), (row3 289 291 291), (row3 278 282 282), (row3 228 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 226 226 234), (row3 143 137 146)]

theorem b055_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_01_rows b055_01_labels 357374234623148793849047400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_01_rows b055_01_labels]
    decide +kernel

def b055_02_rows : List Row := [(row3 9 23 49), (row3 9 23 50), (row3 9 23 51), (row3 9 23 52), (row3 9 23 53), (row3 9 23 54), (row3 9 23 55), (row3 9 23 56), (row3 9 23 57), (row3 9 23 58), (row3 9 23 59), (row3 9 23 60), (row3 9 23 61), (row3 9 23 62), (row3 9 23 63), (row3 9 24 25)]

def b055_02_labels : List Row := [(row3 319 320 320), (row3 223 228 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 306 311 311), (row3 408 416 396), (row3 101 98 99), (row3 321 322 322), (row3 223 232 228), (row3 462 462 462), (row3 232 232 462), (row3 306 312 312), (row3 120 112 120), (row3 331 123 92)]

theorem b055_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_02_rows b055_02_labels 74757561984340866412141464090 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_02_rows b055_02_labels]
    decide +kernel

def b055_03_rows : List Row := [(row3 9 24 26), (row3 9 24 27), (row3 9 24 28), (row3 9 24 29), (row3 9 24 30), (row3 9 24 31), (row3 9 24 32), (row3 9 24 33), (row3 9 24 34), (row3 9 24 35), (row3 9 24 36), (row3 9 24 37), (row3 9 24 38), (row3 9 24 39), (row3 9 24 40), (row3 9 24 41)]

def b055_03_labels : List Row := [(row3 315 318 318), (row3 226 237 226), (row3 462 242 242), (row3 237 237 237), (row3 265 266 266), (row3 177 152 150), (row3 179 153 151), (row3 295 296 296), (row3 226 234 226), (row3 462 243 243), (row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 278 279 279), (row3 275 276 276), (row3 227 231 229)]

theorem b055_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_03_rows b055_03_labels 13498952374673023548323241300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_03_rows b055_03_labels]
    decide +kernel

def b055_04_rows : List Row := [(row3 9 24 42), (row3 9 24 43), (row3 9 24 44), (row3 9 24 45), (row3 9 24 46), (row3 9 24 47), (row3 9 24 48), (row3 9 24 49), (row3 9 24 50), (row3 9 24 51), (row3 9 24 52), (row3 9 24 53), (row3 9 24 54), (row3 9 24 55), (row3 9 24 56), (row3 9 24 57)]

def b055_04_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 231 231 234), (row3 194 188 195), (row3 295 297 297), (row3 228 235 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 278 280 280), (row3 366 375 353), (row3 128 126 125)]

theorem b055_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_04_rows b055_04_labels 17409396188193998489859623610 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_04_rows b055_04_labels]
    decide +kernel

def b055_05_rows : List Row := [(row3 9 24 58), (row3 9 24 59), (row3 9 24 60), (row3 9 24 61), (row3 9 24 62), (row3 9 24 63), (row3 9 25 26), (row3 9 25 27), (row3 9 25 28), (row3 9 25 29), (row3 9 25 30), (row3 9 25 31), (row3 9 25 32), (row3 9 25 33), (row3 9 25 34), (row3 9 25 35)]

def b055_05_labels : List Row := [(row3 319 320 320), (row3 225 236 228), (row3 462 462 462), (row3 236 236 462), (row3 278 279 279), (row3 175 161 175), (row3 132 137 133), (row3 288 462 288), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 288 462 288), (row3 288 462 288), (row3 166 190 167), (row3 288 462 288), (row3 235 462 235)]

theorem b055_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_05_rows b055_05_labels 19131702481425778836831215280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_05_rows b055_05_labels]
    decide +kernel

def b055_06_rows : List Row := [(row3 9 25 36), (row3 9 25 37), (row3 9 25 38), (row3 9 25 39), (row3 9 25 40), (row3 9 25 41), (row3 9 25 42), (row3 9 25 43), (row3 9 25 44), (row3 9 25 45), (row3 9 25 46), (row3 9 25 47), (row3 9 25 48), (row3 9 25 49), (row3 9 25 50), (row3 9 25 51)]

def b055_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 233 462 233), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 194 188 195), (row3 273 462 273), (row3 462 462 462)]

theorem b055_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_06_rows b055_06_labels 154935424706978324241761040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_06_rows b055_06_labels]
    decide +kernel

def b055_07_rows : List Row := [(row3 9 25 52), (row3 9 25 53), (row3 9 25 54), (row3 9 25 55), (row3 9 25 56), (row3 9 25 57), (row3 9 25 58), (row3 9 25 59), (row3 9 25 60), (row3 9 25 61), (row3 9 25 62), (row3 9 25 63), (row3 9 26 27), (row3 9 26 28), (row3 9 26 29), (row3 9 26 30)]

def b055_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 126 137 127), (row3 350 346 349), (row3 143 137 146), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 300 462 300), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_07_rows b055_07_labels 14061908376546699520649034720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_07_rows b055_07_labels]
    decide +kernel

def b055_08_rows : List Row := [(row3 9 26 31), (row3 9 26 32), (row3 9 26 33), (row3 9 26 34), (row3 9 26 35), (row3 9 26 36), (row3 9 26 37), (row3 9 26 38), (row3 9 26 39), (row3 9 26 40), (row3 9 26 41), (row3 9 26 42), (row3 9 26 43), (row3 9 26 44), (row3 9 26 45), (row3 9 26 46)]

def b055_08_labels : List Row := [(row3 228 462 228), (row3 232 462 232), (row3 278 279 279), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_08_rows b055_08_labels 114331845982568808047996880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_08_rows b055_08_labels]
    decide +kernel

def b055_09_rows : List Row := [(row3 9 26 47), (row3 9 26 48), (row3 9 26 49), (row3 9 26 50), (row3 9 26 51), (row3 9 26 52), (row3 9 26 53), (row3 9 26 54), (row3 9 26 55), (row3 9 26 56), (row3 9 26 57), (row3 9 26 58), (row3 9 26 59), (row3 9 26 60), (row3 9 26 61), (row3 9 26 62)]

def b055_09_labels : List Row := [(row3 462 462 462), (row3 232 462 232), (row3 278 280 280), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 306 309 309), (row3 146 149 137), (row3 306 311 311), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_09_rows b055_09_labels 820169165976659143081113060 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_09_rows b055_09_labels]
    decide +kernel

def b055_10_rows : List Row := [(row3 9 26 63), (row3 9 27 28), (row3 9 27 29), (row3 9 27 30), (row3 9 27 31), (row3 9 27 32), (row3 9 27 33), (row3 9 27 34), (row3 9 27 35), (row3 9 27 36), (row3 9 27 37), (row3 9 27 38), (row3 9 27 39), (row3 9 27 40), (row3 9 27 41), (row3 9 27 42)]

def b055_10_labels : List Row := [(row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_10_rows b055_10_labels 3231802572162044760936000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_10_rows b055_10_labels]
    decide +kernel

def b055_11_rows : List Row := [(row3 9 27 43), (row3 9 27 44), (row3 9 27 45), (row3 9 27 46), (row3 9 27 47), (row3 9 27 48), (row3 9 27 49), (row3 9 27 50), (row3 9 27 51), (row3 9 27 52), (row3 9 27 53), (row3 9 27 54), (row3 9 27 55), (row3 9 27 56), (row3 9 27 57), (row3 9 27 58)]

def b055_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 278 278 462), (row3 228 228 462)]

theorem b055_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_11_rows b055_11_labels 18253869264761535836827200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_11_rows b055_11_labels]
    decide +kernel

def b055_12_rows : List Row := [(row3 9 27 59), (row3 9 27 60), (row3 9 27 61), (row3 9 27 62), (row3 9 27 63), (row3 9 28 29), (row3 9 28 30), (row3 9 28 31), (row3 9 28 32), (row3 9 28 33), (row3 9 28 34), (row3 9 28 35), (row3 9 28 36), (row3 9 28 37), (row3 9 28 38), (row3 9 28 39)]

def b055_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_12_rows b055_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_12_rows b055_12_labels]
    decide +kernel

def b055_13_rows : List Row := [(row3 9 28 40), (row3 9 28 41), (row3 9 28 42), (row3 9 28 43), (row3 9 28 44), (row3 9 28 45), (row3 9 28 46), (row3 9 28 47), (row3 9 28 48), (row3 9 28 49), (row3 9 28 50), (row3 9 28 51), (row3 9 28 52), (row3 9 28 53), (row3 9 28 54), (row3 9 28 55)]

def b055_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_13_rows b055_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_13_rows b055_13_labels]
    decide +kernel

def b055_14_rows : List Row := [(row3 9 28 56), (row3 9 28 57), (row3 9 28 58), (row3 9 28 59), (row3 9 28 60), (row3 9 28 61), (row3 9 28 62), (row3 9 28 63), (row3 9 29 30), (row3 9 29 31), (row3 9 29 32), (row3 9 29 33), (row3 9 29 34), (row3 9 29 35), (row3 9 29 36), (row3 9 29 37)]

def b055_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_14_rows b055_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_14_rows b055_14_labels]
    decide +kernel

def b055_15_rows : List Row := [(row3 9 29 38), (row3 9 29 39), (row3 9 29 40), (row3 9 29 41), (row3 9 29 42), (row3 9 29 43), (row3 9 29 44), (row3 9 29 45), (row3 9 29 46), (row3 9 29 47), (row3 9 29 48), (row3 9 29 49), (row3 9 29 50), (row3 9 29 51), (row3 9 29 52), (row3 9 29 53)]

def b055_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b055_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b055_15_rows b055_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b055_15_rows b055_15_labels]
    decide +kernel

theorem checked055 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_055 QuarticIntegerComputationalData.ids64_055 161103002792888605702375600260 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b055_00_rows ++ b055_01_rows) ++ (b055_02_rows ++ b055_03_rows)) ++ ((b055_04_rows ++ b055_05_rows) ++ (b055_06_rows ++ b055_07_rows))) ++ (((b055_08_rows ++ b055_09_rows) ++ (b055_10_rows ++ b055_11_rows)) ++ ((b055_12_rows ++ b055_13_rows) ++ (b055_14_rows ++ b055_15_rows))))
    ((((b055_00_labels ++ b055_01_labels) ++ (b055_02_labels ++ b055_03_labels)) ++ ((b055_04_labels ++ b055_05_labels) ++ (b055_06_labels ++ b055_07_labels))) ++ (((b055_08_labels ++ b055_09_labels) ++ (b055_10_labels ++ b055_11_labels)) ++ ((b055_12_labels ++ b055_13_labels) ++ (b055_14_labels ++ b055_15_labels)))) 161103002792888605702375600260
  exact ((((b055_00_checked.append (c := 21132559279205109038602387080) b055_01_checked (by decide +kernel)).append (c := 109389073638218998999067092470) (b055_02_checked.append (c := 88256514359013889960464705390) b055_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 160147016109092454170648727120) ((b055_04_checked.append (c := 36541098669619777326690838890) b055_05_checked (by decide +kernel)).append (c := 50757942470873455171581634650) (b055_06_checked.append (c := 14216843801253677844890795760) b055_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 161103002792888605702375600260) (((b055_08_checked.append (c := 934501011959227951129109940) b055_09_checked (by decide +kernel)).append (c := 955986683796151531726873140) (b055_10_checked.append (c := 21485671836923580597763200) b055_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 955986683796151531726873140) ((b055_12_checked.append (c := 0) b055_13_checked (by decide +kernel)).append (c := 0) (b055_14_checked.append (c := 0) b055_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b056_00_rows : List Row := [(row3 9 29 54), (row3 9 29 55), (row3 9 29 56), (row3 9 29 57), (row3 9 29 58), (row3 9 29 59), (row3 9 29 60), (row3 9 29 61), (row3 9 29 62), (row3 9 29 63), (row3 9 30 31), (row3 9 30 32), (row3 9 30 33), (row3 9 30 34), (row3 9 30 35), (row3 9 30 36)]

def b056_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_00_rows b056_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_00_rows b056_00_labels]
    decide +kernel

def b056_01_rows : List Row := [(row3 9 30 37), (row3 9 30 38), (row3 9 30 39), (row3 9 30 40), (row3 9 30 41), (row3 9 30 42), (row3 9 30 43), (row3 9 30 44), (row3 9 30 45), (row3 9 30 46), (row3 9 30 47), (row3 9 30 48), (row3 9 30 49), (row3 9 30 50), (row3 9 30 51), (row3 9 30 52)]

def b056_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_01_rows b056_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_01_rows b056_01_labels]
    decide +kernel

def b056_02_rows : List Row := [(row3 9 30 53), (row3 9 30 54), (row3 9 30 55), (row3 9 30 56), (row3 9 30 57), (row3 9 30 58), (row3 9 30 59), (row3 9 30 60), (row3 9 30 61), (row3 9 30 62), (row3 9 30 63), (row3 9 31 32), (row3 9 31 33), (row3 9 31 34), (row3 9 31 35), (row3 9 31 36)]

def b056_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_02_rows b056_02_labels 601543560723870591540000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_02_rows b056_02_labels]
    decide +kernel

def b056_03_rows : List Row := [(row3 9 31 37), (row3 9 31 38), (row3 9 31 39), (row3 9 31 40), (row3 9 31 41), (row3 9 31 42), (row3 9 31 43), (row3 9 31 44), (row3 9 31 45), (row3 9 31 46), (row3 9 31 47), (row3 9 31 48), (row3 9 31 49), (row3 9 31 50), (row3 9 31 51), (row3 9 31 52)]

def b056_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 228 235 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_03_rows b056_03_labels 7445414349725112376257600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_03_rows b056_03_labels]
    decide +kernel

def b056_04_rows : List Row := [(row3 9 31 53), (row3 9 31 54), (row3 9 31 55), (row3 9 31 56), (row3 9 31 57), (row3 9 31 58), (row3 9 31 59), (row3 9 31 60), (row3 9 31 61), (row3 9 31 62), (row3 9 31 63), (row3 9 32 33), (row3 9 32 34), (row3 9 32 35), (row3 9 32 36), (row3 9 32 37)]

def b056_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 160 228 163), (row3 300 278 288), (row3 223 228 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_04_rows b056_04_labels 795090457318250717194233600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_04_rows b056_04_labels]
    decide +kernel

def b056_05_rows : List Row := [(row3 9 32 38), (row3 9 32 39), (row3 9 32 40), (row3 9 32 41), (row3 9 32 42), (row3 9 32 43), (row3 9 32 44), (row3 9 32 45), (row3 9 32 46), (row3 9 32 47), (row3 9 32 48), (row3 9 32 49), (row3 9 32 50), (row3 9 32 51), (row3 9 32 52), (row3 9 32 53)]

def b056_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 227 231 229), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_05_rows b056_05_labels 29688690339444181904631360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_05_rows b056_05_labels]
    decide +kernel

def b056_06_rows : List Row := [(row3 9 32 54), (row3 9 32 55), (row3 9 32 56), (row3 9 32 57), (row3 9 32 58), (row3 9 32 59), (row3 9 32 60), (row3 9 32 61), (row3 9 32 62), (row3 9 32 63), (row3 9 33 34), (row3 9 33 35), (row3 9 33 36), (row3 9 33 37), (row3 9 33 38), (row3 9 33 39)]

def b056_06_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 187 90 357), (row3 288 288 288), (row3 228 232 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_06_rows b056_06_labels 6596032349227809840856750800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_06_rows b056_06_labels]
    decide +kernel

def b056_07_rows : List Row := [(row3 9 33 40), (row3 9 33 41), (row3 9 33 42), (row3 9 33 43), (row3 9 33 44), (row3 9 33 45), (row3 9 33 46), (row3 9 33 47), (row3 9 33 48), (row3 9 33 49), (row3 9 33 50), (row3 9 33 51), (row3 9 33 52), (row3 9 33 53), (row3 9 33 54), (row3 9 33 55)]

def b056_07_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 233 462 233), (row3 275 276 276), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_07_rows b056_07_labels 39993575327277132059911200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_07_rows b056_07_labels]
    decide +kernel

def b056_08_rows : List Row := [(row3 9 33 56), (row3 9 33 57), (row3 9 33 58), (row3 9 33 59), (row3 9 33 60), (row3 9 33 61), (row3 9 33 62), (row3 9 33 63), (row3 9 34 35), (row3 9 34 36), (row3 9 34 37), (row3 9 34 38), (row3 9 34 39), (row3 9 34 40), (row3 9 34 41), (row3 9 34 42)]

def b056_08_labels : List Row := [(row3 278 301 301), (row3 165 176 165), (row3 278 282 282), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_08_rows b056_08_labels 435181036718548003273885440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_08_rows b056_08_labels]
    decide +kernel

def b056_09_rows : List Row := [(row3 9 34 43), (row3 9 34 44), (row3 9 34 45), (row3 9 34 46), (row3 9 34 47), (row3 9 34 48), (row3 9 34 49), (row3 9 34 50), (row3 9 34 51), (row3 9 34 52), (row3 9 34 53), (row3 9 34 54), (row3 9 34 55), (row3 9 34 56), (row3 9 34 57), (row3 9 34 58)]

def b056_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 231 231 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 273 288 273), (row3 226 226 234)]

theorem b056_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_09_rows b056_09_labels 22057648295060652391857600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_09_rows b056_09_labels]
    decide +kernel

def b056_10_rows : List Row := [(row3 9 34 59), (row3 9 34 60), (row3 9 34 61), (row3 9 34 62), (row3 9 34 63), (row3 9 35 36), (row3 9 35 37), (row3 9 35 38), (row3 9 35 39), (row3 9 35 40), (row3 9 35 41), (row3 9 35 42), (row3 9 35 43), (row3 9 35 44), (row3 9 35 45), (row3 9 35 46)]

def b056_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_10_rows b056_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_10_rows b056_10_labels]
    decide +kernel

def b056_11_rows : List Row := [(row3 9 35 47), (row3 9 35 48), (row3 9 35 49), (row3 9 35 50), (row3 9 35 51), (row3 9 35 52), (row3 9 35 53), (row3 9 35 54), (row3 9 35 55), (row3 9 35 56), (row3 9 35 57), (row3 9 35 58), (row3 9 35 59), (row3 9 35 60), (row3 9 35 61), (row3 9 35 62)]

def b056_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_11_rows b056_11_labels 75474487824386394802500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_11_rows b056_11_labels]
    decide +kernel

def b056_12_rows : List Row := [(row3 9 35 63), (row3 9 36 37), (row3 9 36 38), (row3 9 36 39), (row3 9 36 40), (row3 9 36 41), (row3 9 36 42), (row3 9 36 43), (row3 9 36 44), (row3 9 36 45), (row3 9 36 46), (row3 9 36 47), (row3 9 36 48), (row3 9 36 49), (row3 9 36 50), (row3 9 36 51)]

def b056_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_12_rows b056_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_12_rows b056_12_labels]
    decide +kernel

def b056_13_rows : List Row := [(row3 9 36 52), (row3 9 36 53), (row3 9 36 54), (row3 9 36 55), (row3 9 36 56), (row3 9 36 57), (row3 9 36 58), (row3 9 36 59), (row3 9 36 60), (row3 9 36 61), (row3 9 36 62), (row3 9 36 63), (row3 9 37 38), (row3 9 37 39), (row3 9 37 40), (row3 9 37 41)]

def b056_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_13_rows b056_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_13_rows b056_13_labels]
    decide +kernel

def b056_14_rows : List Row := [(row3 9 37 42), (row3 9 37 43), (row3 9 37 44), (row3 9 37 45), (row3 9 37 46), (row3 9 37 47), (row3 9 37 48), (row3 9 37 49), (row3 9 37 50), (row3 9 37 51), (row3 9 37 52), (row3 9 37 53), (row3 9 37 54), (row3 9 37 55), (row3 9 37 56), (row3 9 37 57)]

def b056_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_14_rows b056_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_14_rows b056_14_labels]
    decide +kernel

def b056_15_rows : List Row := [(row3 9 37 58), (row3 9 37 59), (row3 9 37 60), (row3 9 37 61), (row3 9 37 62), (row3 9 37 63), (row3 9 38 39), (row3 9 38 40), (row3 9 38 41), (row3 9 38 42), (row3 9 38 43), (row3 9 38 44), (row3 9 38 45), (row3 9 38 46), (row3 9 38 47), (row3 9 38 48)]

def b056_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b056_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b056_15_rows b056_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b056_15_rows b056_15_labels]
    decide +kernel

theorem checked056 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_056 QuarticIntegerComputationalData.ids64_056 7926166189624663897043870100 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b056_00_rows ++ b056_01_rows) ++ (b056_02_rows ++ b056_03_rows)) ++ ((b056_04_rows ++ b056_05_rows) ++ (b056_06_rows ++ b056_07_rows))) ++ (((b056_08_rows ++ b056_09_rows) ++ (b056_10_rows ++ b056_11_rows)) ++ ((b056_12_rows ++ b056_13_rows) ++ (b056_14_rows ++ b056_15_rows))))
    ((((b056_00_labels ++ b056_01_labels) ++ (b056_02_labels ++ b056_03_labels)) ++ ((b056_04_labels ++ b056_05_labels) ++ (b056_06_labels ++ b056_07_labels))) ++ (((b056_08_labels ++ b056_09_labels) ++ (b056_10_labels ++ b056_11_labels)) ++ ((b056_12_labels ++ b056_13_labels) ++ (b056_14_labels ++ b056_15_labels)))) 7926166189624663897043870100
  exact ((((b056_00_checked.append (c := 0) b056_01_checked (by decide +kernel)).append (c := 8046957910448982967797600) (b056_02_checked.append (c := 8046957910448982967797600) b056_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 7468852030123230854983324560) ((b056_04_checked.append (c := 824779147657694899098864960) b056_05_checked (by decide +kernel)).append (c := 7460805072212781872015526960) (b056_06_checked.append (c := 6636025924555086972916662000) b056_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7926166189624663897043870100) (((b056_08_checked.append (c := 457238685013608655665743040) b056_09_checked (by decide +kernel)).append (c := 457314159501433042060545540) (b056_10_checked.append (c := 75474487824386394802500) b056_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 457314159501433042060545540) ((b056_12_checked.append (c := 0) b056_13_checked (by decide +kernel)).append (c := 0) (b056_14_checked.append (c := 0) b056_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
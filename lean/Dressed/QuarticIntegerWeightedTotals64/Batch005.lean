import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch004
import Dressed.QuarticIntegerComputationalData64.Batch005


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b041_00_rows : List Row := [(row3 7 8 54), (row3 7 8 55), (row3 7 8 56), (row3 7 8 57), (row3 7 8 58), (row3 7 8 59), (row3 7 8 60), (row3 7 8 61), (row3 7 8 62), (row3 7 8 63), (row3 7 9 10), (row3 7 9 11), (row3 7 9 12), (row3 7 9 13), (row3 7 9 14), (row3 7 9 15)]

def b041_00_labels : List Row := [(row3 45 389 436), (row3 443 34 27), (row3 18 19 19), (row3 456 456 458), (row3 36 35 31), (row3 358 358 462), (row3 163 462 163), (row3 43 383 436), (row3 452 32 25), (row3 23 457 461), (row3 417 422 423), (row3 127 126 137), (row3 301 278 301), (row3 399 156 82), (row3 40 413 438), (row3 451 442 24)]

theorem b041_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_00_rows b041_00_labels 2277370528191647587270046737352160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_00_rows b041_00_labels]
    decide +kernel

def b041_01_rows : List Row := [(row3 7 9 16), (row3 7 9 17), (row3 7 9 18), (row3 7 9 19), (row3 7 9 20), (row3 7 9 21), (row3 7 9 22), (row3 7 9 23), (row3 7 9 24), (row3 7 9 25), (row3 7 9 26), (row3 7 9 27), (row3 7 9 28), (row3 7 9 29), (row3 7 9 30), (row3 7 9 31)]

def b041_01_labels : List Row := [(row3 61 50 48), (row3 418 422 424), (row3 100 100 113), (row3 309 306 309), (row3 462 232 232), (row3 293 462 293), (row3 398 134 81), (row3 60 411 432), (row3 354 366 376), (row3 127 126 137), (row3 309 306 309), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 356 158 89)]

theorem b041_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_01_rows b041_01_labels 5681862983116799857345232764470 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_01_rows b041_01_labels]
    decide +kernel

def b041_02_rows : List Row := [(row3 7 9 32), (row3 7 9 33), (row3 7 9 34), (row3 7 9 35), (row3 7 9 36), (row3 7 9 37), (row3 7 9 38), (row3 7 9 39), (row3 7 9 40), (row3 7 9 41), (row3 7 9 42), (row3 7 9 43), (row3 7 9 44), (row3 7 9 45), (row3 7 9 46), (row3 7 9 47)]

def b041_02_labels : List Row := [(row3 193 189 232), (row3 279 278 279), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 352 365 373), (row3 163 162 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 356 159 91)]

theorem b041_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_02_rows b041_02_labels 18031017778764466462345784550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_02_rows b041_02_labels]
    decide +kernel

def b041_03_rows : List Row := [(row3 7 9 48), (row3 7 9 49), (row3 7 9 50), (row3 7 9 51), (row3 7 9 52), (row3 7 9 53), (row3 7 9 54), (row3 7 9 55), (row3 7 9 56), (row3 7 9 57), (row3 7 9 58), (row3 7 9 59), (row3 7 9 60), (row3 7 9 61), (row3 7 9 62), (row3 7 9 63)]

def b041_03_labels : List Row := [(row3 62 52 49), (row3 395 407 415), (row3 139 138 232), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 398 135 83), (row3 59 410 431), (row3 456 458 456), (row3 38 33 33), (row3 396 408 416), (row3 163 160 228), (row3 284 462 284), (row3 399 157 83), (row3 39 412 437), (row3 452 32 25)]

theorem b041_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_03_rows b041_03_labels 34700899696972054730256450896580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_03_rows b041_03_labels]
    decide +kernel

def b041_04_rows : List Row := [(row3 7 10 11), (row3 7 10 12), (row3 7 10 13), (row3 7 10 14), (row3 7 10 15), (row3 7 10 16), (row3 7 10 17), (row3 7 10 18), (row3 7 10 19), (row3 7 10 20), (row3 7 10 21), (row3 7 10 22), (row3 7 10 23), (row3 7 10 24), (row3 7 10 25), (row3 7 10 26)]

def b041_04_labels : List Row := [(row3 303 303 462), (row3 235 235 462), (row3 116 213 11), (row3 399 156 82), (row3 44 74 439), (row3 362 392 388), (row3 129 103 102), (row3 307 307 462), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 117 214 11), (row3 369 121 85), (row3 180 154 154), (row3 286 286 462), (row3 235 235 462)]

theorem b041_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_04_rows b041_04_labels 622487193095142015851151851250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_04_rows b041_04_labels]
    decide +kernel

def b041_05_rows : List Row := [(row3 7 10 27), (row3 7 10 28), (row3 7 10 29), (row3 7 10 30), (row3 7 10 31), (row3 7 10 32), (row3 7 10 33), (row3 7 10 34), (row3 7 10 35), (row3 7 10 36), (row3 7 10 37), (row3 7 10 38), (row3 7 10 39), (row3 7 10 40), (row3 7 10 41), (row3 7 10 42)]

def b041_05_labels : List Row := [(row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 254 10), (row3 269 269 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 154 154), (row3 284 284 462), (row3 462 462 462)]

theorem b041_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_05_rows b041_05_labels 1404778032043106682101175000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_05_rows b041_05_labels]
    decide +kernel

def b041_06_rows : List Row := [(row3 7 10 43), (row3 7 10 44), (row3 7 10 45), (row3 7 10 46), (row3 7 10 47), (row3 7 10 48), (row3 7 10 49), (row3 7 10 50), (row3 7 10 51), (row3 7 10 52), (row3 7 10 53), (row3 7 10 54), (row3 7 10 55), (row3 7 10 56), (row3 7 10 57), (row3 7 10 58)]

def b041_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 254 10), (row3 360 390 387), (row3 131 105 105), (row3 294 294 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 214 11), (row3 369 122 86), (row3 36 31 35), (row3 396 416 408), (row3 130 104 104)]

theorem b041_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_06_rows b041_06_labels 887258236173166670751579424050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_06_rows b041_06_labels]
    decide +kernel

def b041_07_rows : List Row := [(row3 7 10 59), (row3 7 10 60), (row3 7 10 61), (row3 7 10 62), (row3 7 10 63), (row3 7 11 12), (row3 7 11 13), (row3 7 11 14), (row3 7 11 15), (row3 7 11 16), (row3 7 11 17), (row3 7 11 18), (row3 7 11 19), (row3 7 11 20), (row3 7 11 21), (row3 7 11 22)]

def b041_07_labels : List Row := [(row3 286 286 462), (row3 462 462 462), (row3 115 212 11), (row3 399 157 83), (row3 43 383 436), (row3 462 462 462), (row3 235 235 462), (row3 301 278 301), (row3 163 193 139), (row3 193 235 191), (row3 287 462 287), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_07_rows b041_07_labels 396901059468449129577321190650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_07_rows b041_07_labels]
    decide +kernel

def b041_08_rows : List Row := [(row3 7 11 23), (row3 7 11 24), (row3 7 11 25), (row3 7 11 26), (row3 7 11 27), (row3 7 11 28), (row3 7 11 29), (row3 7 11 30), (row3 7 11 31), (row3 7 11 32), (row3 7 11 33), (row3 7 11 34), (row3 7 11 35), (row3 7 11 36), (row3 7 11 37), (row3 7 11 38)]

def b041_08_labels : List Row := [(row3 284 462 284), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_08_rows b041_08_labels 80617028594769644558820000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_08_rows b041_08_labels]
    decide +kernel

def b041_09_rows : List Row := [(row3 7 11 39), (row3 7 11 40), (row3 7 11 41), (row3 7 11 42), (row3 7 11 43), (row3 7 11 44), (row3 7 11 45), (row3 7 11 46), (row3 7 11 47), (row3 7 11 48), (row3 7 11 49), (row3 7 11 50), (row3 7 11 51), (row3 7 11 52), (row3 7 11 53), (row3 7 11 54)]

def b041_09_labels : List Row := [(row3 462 462 462), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_09_rows b041_09_labels 426795099393901852511304000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_09_rows b041_09_labels]
    decide +kernel

def b041_10_rows : List Row := [(row3 7 11 55), (row3 7 11 56), (row3 7 11 57), (row3 7 11 58), (row3 7 11 59), (row3 7 11 60), (row3 7 11 61), (row3 7 11 62), (row3 7 11 63), (row3 7 12 13), (row3 7 12 14), (row3 7 12 15), (row3 7 12 16), (row3 7 12 17), (row3 7 12 18), (row3 7 12 19)]

def b041_10_labels : List Row := [(row3 284 462 284), (row3 358 462 358), (row3 163 228 160), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 163 462 163), (row3 303 303 462), (row3 127 126 137), (row3 359 73 429), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_10_rows b041_10_labels 142478660557282428787339896180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_10_rows b041_10_labels]
    decide +kernel

def b041_11_rows : List Row := [(row3 7 12 20), (row3 7 12 21), (row3 7 12 22), (row3 7 12 23), (row3 7 12 24), (row3 7 12 25), (row3 7 12 26), (row3 7 12 27), (row3 7 12 28), (row3 7 12 29), (row3 7 12 30), (row3 7 12 31), (row3 7 12 32), (row3 7 12 33), (row3 7 12 34), (row3 7 12 35)]

def b041_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 287 287 462), (row3 193 191 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_11_rows b041_11_labels 468363075397046399378602500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_11_rows b041_11_labels]
    decide +kernel

def b041_12_rows : List Row := [(row3 7 12 36), (row3 7 12 37), (row3 7 12 38), (row3 7 12 39), (row3 7 12 40), (row3 7 12 41), (row3 7 12 42), (row3 7 12 43), (row3 7 12 44), (row3 7 12 45), (row3 7 12 46), (row3 7 12 47), (row3 7 12 48), (row3 7 12 49), (row3 7 12 50), (row3 7 12 51)]

def b041_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b041_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_12_rows b041_12_labels 80617028594769644558820000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_12_rows b041_12_labels]
    decide +kernel

def b041_13_rows : List Row := [(row3 7 12 52), (row3 7 12 53), (row3 7 12 54), (row3 7 12 55), (row3 7 12 56), (row3 7 12 57), (row3 7 12 58), (row3 7 12 59), (row3 7 12 60), (row3 7 12 61), (row3 7 12 62), (row3 7 12 63), (row3 7 13 14), (row3 7 13 15), (row3 7 13 16), (row3 7 13 17)]

def b041_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 193 193 462), (row3 163 163 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 286 462), (row3 163 160 228), (row3 358 358 462), (row3 417 422 423), (row3 34 443 27), (row3 369 85 121), (row3 117 11 214)]

theorem b041_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_13_rows b041_13_labels 8987388744057328752840133535850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_13_rows b041_13_labels]
    decide +kernel

def b041_14_rows : List Row := [(row3 7 13 18), (row3 7 13 19), (row3 7 13 20), (row3 7 13 21), (row3 7 13 22), (row3 7 13 23), (row3 7 13 24), (row3 7 13 25), (row3 7 13 26), (row3 7 13 27), (row3 7 13 28), (row3 7 13 29), (row3 7 13 30), (row3 7 13 31), (row3 7 13 32), (row3 7 13 33)]

def b041_14_labels : List Row := [(row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 307 462 307), (row3 129 102 103), (row3 362 388 392), (row3 171 10 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 286 462 286), (row3 180 154 154), (row3 462 462 462), (row3 462 462 462)]

theorem b041_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_14_rows b041_14_labels 55287156222217204955226154350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_14_rows b041_14_labels]
    decide +kernel

def b041_15_rows : List Row := [(row3 7 13 34), (row3 7 13 35), (row3 7 13 36), (row3 7 13 37), (row3 7 13 38), (row3 7 13 39), (row3 7 13 40), (row3 7 13 41), (row3 7 13 42), (row3 7 13 43), (row3 7 13 44), (row3 7 13 45), (row3 7 13 46), (row3 7 13 47), (row3 7 13 48), (row3 7 13 49)]

def b041_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 269 462 269), (row3 171 10 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 180 154 154), (row3 369 86 122), (row3 117 11 214)]

theorem b041_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b041_15_rows b041_15_labels 12948593539416450363581973750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b041_15_rows b041_15_labels]
    decide +kernel

theorem checked041 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_041 QuarticIntegerComputationalData.ids64_041 2328878532702892232571460209545340 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b041_00_rows ++ b041_01_rows) ++ (b041_02_rows ++ b041_03_rows)) ++ ((b041_04_rows ++ b041_05_rows) ++ (b041_06_rows ++ b041_07_rows))) ++ (((b041_08_rows ++ b041_09_rows) ++ (b041_10_rows ++ b041_11_rows)) ++ ((b041_12_rows ++ b041_13_rows) ++ (b041_14_rows ++ b041_15_rows))))
    ((((b041_00_labels ++ b041_01_labels) ++ (b041_02_labels ++ b041_03_labels)) ++ ((b041_04_labels ++ b041_05_labels) ++ (b041_06_labels ++ b041_07_labels))) ++ (((b041_08_labels ++ b041_09_labels) ++ (b041_10_labels ++ b041_11_labels)) ++ ((b041_12_labels ++ b041_13_labels) ++ (b041_14_labels ++ b041_15_labels)))) 2328878532702892232571460209545340
  exact ((((b041_00_checked.append (c := 2283052391174764387127391970116630) b041_01_checked (by decide +kernel)).append (c := 2317771321889515206324110766797760) (b041_02_checked.append (c := 34718930714750819196718796681130) b041_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2319679373156284007246972920438710) ((b041_04_checked.append (c := 623891971127185122533253026250) b041_05_checked (by decide +kernel)).append (c := 1908051266768800922862153640950) (b041_06_checked.append (c := 1284159295641615800328900614700) b041_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2328878532702892232571460209545340) (((b041_08_checked.append (c := 507412127988671497070124000) b041_09_checked (by decide +kernel)).append (c := 143454435760668146683788622680) (b041_10_checked.append (c := 142947023632679475186718498680) b041_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 9199159546608225324487289106630) ((b041_12_checked.append (c := 8987469361085923522484692355850) b041_13_checked (by decide +kernel)).append (c := 9055705110847557177803500483950) (b041_14_checked.append (c := 68235749761633655318808128100) b041_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b042_00_rows : List Row := [(row3 7 13 50), (row3 7 13 51), (row3 7 13 52), (row3 7 13 53), (row3 7 13 54), (row3 7 13 55), (row3 7 13 56), (row3 7 13 57), (row3 7 13 58), (row3 7 13 59), (row3 7 13 60), (row3 7 13 61), (row3 7 13 62), (row3 7 13 63), (row3 7 14 15), (row3 7 14 16)]

def b042_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 294 462 294), (row3 131 105 105), (row3 360 387 390), (row3 43 436 383), (row3 399 83 157), (row3 115 11 212), (row3 462 462 462), (row3 286 462 286), (row3 130 104 104), (row3 396 408 416), (row3 36 35 31), (row3 457 23 461), (row3 60 432 411)]

theorem b042_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_00_rows b042_00_labels 1073566384345278354922715859225390 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_00_rows b042_00_labels]
    decide +kernel

def b042_01_rows : List Row := [(row3 7 14 17), (row3 7 14 18), (row3 7 14 19), (row3 7 14 20), (row3 7 14 21), (row3 7 14 22), (row3 7 14 23), (row3 7 14 24), (row3 7 14 25), (row3 7 14 26), (row3 7 14 27), (row3 7 14 28), (row3 7 14 29), (row3 7 14 30), (row3 7 14 31), (row3 7 14 32)]

def b042_01_labels : List Row := [(row3 398 81 134), (row3 293 293 462), (row3 462 232 232), (row3 309 309 306), (row3 100 113 100), (row3 418 424 422), (row3 61 48 50), (row3 356 89 158), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 309 309 306), (row3 127 137 126), (row3 354 376 366), (row3 269 269 462)]

theorem b042_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_01_rows b042_01_labels 5462491831284720309489215776110 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_01_rows b042_01_labels]
    decide +kernel

def b042_02_rows : List Row := [(row3 7 14 33), (row3 7 14 34), (row3 7 14 35), (row3 7 14 36), (row3 7 14 37), (row3 7 14 38), (row3 7 14 39), (row3 7 14 40), (row3 7 14 41), (row3 7 14 42), (row3 7 14 43), (row3 7 14 44), (row3 7 14 45), (row3 7 14 46), (row3 7 14 47), (row3 7 14 48)]

def b042_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 279 279 278), (row3 193 232 189), (row3 356 91 159), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 235 162), (row3 352 373 365), (row3 59 431 410)]

theorem b042_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_02_rows b042_02_labels 168051778683837972219799132350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_02_rows b042_02_labels]
    decide +kernel

def b042_03_rows : List Row := [(row3 7 14 49), (row3 7 14 50), (row3 7 14 51), (row3 7 14 52), (row3 7 14 53), (row3 7 14 54), (row3 7 14 55), (row3 7 14 56), (row3 7 14 57), (row3 7 14 58), (row3 7 14 59), (row3 7 14 60), (row3 7 14 61), (row3 7 14 62), (row3 7 14 63), (row3 7 15 16)]

def b042_03_labels : List Row := [(row3 398 83 135), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 139 232 138), (row3 395 415 407), (row3 62 49 52), (row3 452 25 32), (row3 39 437 412), (row3 399 83 157), (row3 284 284 462), (row3 163 228 160), (row3 396 416 408), (row3 38 33 33), (row3 456 456 458), (row3 442 24 451)]

theorem b042_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_03_rows b042_03_labels 62242864186835781466404426350760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_03_rows b042_03_labels]
    decide +kernel

def b042_04_rows : List Row := [(row3 7 15 17), (row3 7 15 18), (row3 7 15 19), (row3 7 15 20), (row3 7 15 21), (row3 7 15 22), (row3 7 15 23), (row3 7 15 24), (row3 7 15 25), (row3 7 15 26), (row3 7 15 27), (row3 7 15 28), (row3 7 15 29), (row3 7 15 30), (row3 7 15 31), (row3 7 15 32)]

def b042_04_labels : List Row := [(row3 46 440 46), (row3 139 124 163), (row3 462 462 462), (row3 462 163 163), (row3 389 436 45), (row3 32 25 452), (row3 450 460 22), (row3 74 439 44), (row3 163 124 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 139 139), (row3 383 436 43), (row3 56 29 445), (row3 193 139 163)]

theorem b042_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_04_rows b042_04_labels 989481843532535616935975986009440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_04_rows b042_04_labels]
    decide +kernel

def b042_05_rows : List Row := [(row3 7 15 33), (row3 7 15 34), (row3 7 15 35), (row3 7 15 36), (row3 7 15 37), (row3 7 15 38), (row3 7 15 39), (row3 7 15 40), (row3 7 15 41), (row3 7 15 42), (row3 7 15 43), (row3 7 15 44), (row3 7 15 45), (row3 7 15 46), (row3 7 15 47), (row3 7 15 48)]

def b042_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 341 429 71), (row3 73 429 359), (row3 163 163 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 358 462 358), (row3 64 55 66), (row3 443 27 34)]

theorem b042_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_05_rows b042_05_labels 5431733672858710671773432643600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_05_rows b042_05_labels]
    decide +kernel

def b042_06_rows : List Row := [(row3 7 15 49), (row3 7 15 50), (row3 7 15 51), (row3 7 15 52), (row3 7 15 53), (row3 7 15 54), (row3 7 15 55), (row3 7 15 56), (row3 7 15 57), (row3 7 15 58), (row3 7 15 59), (row3 7 15 60), (row3 7 15 61), (row3 7 15 62), (row3 7 15 63), (row3 7 16 17)]

def b042_06_labels : List Row := [(row3 45 436 389), (row3 139 139 462), (row3 462 462 462), (row3 462 462 462), (row3 377 462 377), (row3 35 31 36), (row3 448 454 449), (row3 23 461 457), (row3 452 25 32), (row3 43 436 383), (row3 163 163 462), (row3 358 462 358), (row3 36 31 35), (row3 456 458 456), (row3 18 19 19), (row3 394 409 414)]

theorem b042_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_06_rows b042_06_labels 2250403764713866584957887067811920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_06_rows b042_06_labels]
    decide +kernel

def b042_07_rows : List Row := [(row3 7 16 18), (row3 7 16 19), (row3 7 16 20), (row3 7 16 21), (row3 7 16 22), (row3 7 16 23), (row3 7 16 24), (row3 7 16 25), (row3 7 16 26), (row3 7 16 27), (row3 7 16 28), (row3 7 16 29), (row3 7 16 30), (row3 7 16 31), (row3 7 16 32), (row3 7 16 33)]

def b042_07_labels : List Row := [(row3 140 140 178), (row3 266 265 266), (row3 462 237 237), (row3 302 265 302), (row3 367 108 84), (row3 63 419 433), (row3 384 397 400), (row3 132 133 137), (row3 291 289 291), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 305 289 305), (row3 331 123 92), (row3 174 174 178), (row3 291 289 291)]

theorem b042_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_07_rows b042_07_labels 9492805781106101876339547936480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_07_rows b042_07_labels]
    decide +kernel

def b042_08_rows : List Row := [(row3 7 16 34), (row3 7 16 35), (row3 7 16 36), (row3 7 16 37), (row3 7 16 38), (row3 7 16 39), (row3 7 16 40), (row3 7 16 41), (row3 7 16 42), (row3 7 16 43), (row3 7 16 44), (row3 7 16 45), (row3 7 16 46), (row3 7 16 47), (row3 7 16 48), (row3 7 16 49)]

def b042_08_labels : List Row := [(row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 299 289 299), (row3 329 340 344), (row3 193 191 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 332 155 93), (row3 79 67 67), (row3 361 387 391)]

theorem b042_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_08_rows b042_08_labels 118653775937897019822512020800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_08_rows b042_08_labels]
    decide +kernel

def b042_09_rows : List Row := [(row3 7 16 50), (row3 7 16 51), (row3 7 16 52), (row3 7 16 53), (row3 7 16 54), (row3 7 16 55), (row3 7 16 56), (row3 7 16 57), (row3 7 16 58), (row3 7 16 59), (row3 7 16 60), (row3 7 16 61), (row3 7 16 62), (row3 7 16 63), (row3 7 17 18), (row3 7 17 19)]

def b042_09_labels : List Row := [(row3 180 180 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 368 114 86), (row3 78 401 427), (row3 448 454 449), (row3 62 49 52), (row3 360 387 390), (row3 193 193 462), (row3 284 462 284), (row3 369 122 86), (row3 59 410 431), (row3 443 34 27), (row3 316 316 462), (row3 234 234 462)]

theorem b042_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_09_rows b042_09_labels 12732924600801589319009126176290 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_09_rows b042_09_labels]
    decide +kernel

def b042_10_rows : List Row := [(row3 7 17 20), (row3 7 17 21), (row3 7 17 22), (row3 7 17 23), (row3 7 17 24), (row3 7 17 25), (row3 7 17 26), (row3 7 17 27), (row3 7 17 28), (row3 7 17 29), (row3 7 17 30), (row3 7 17 31), (row3 7 17 32), (row3 7 17 33), (row3 7 17 34), (row3 7 17 35)]

def b042_10_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 119 216 11), (row3 367 108 84), (row3 177 150 152), (row3 307 307 462), (row3 228 228 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 173 260 10), (row3 272 272 462), (row3 234 234 462), (row3 248 248 462), (row3 462 462 462)]

theorem b042_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_10_rows b042_10_labels 63369356803305623624190149190 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_10_rows b042_10_labels]
    decide +kernel

def b042_11_rows : List Row := [(row3 7 17 36), (row3 7 17 37), (row3 7 17 38), (row3 7 17 39), (row3 7 17 40), (row3 7 17 41), (row3 7 17 42), (row3 7 17 43), (row3 7 17 44), (row3 7 17 45), (row3 7 17 46), (row3 7 17 47), (row3 7 17 48), (row3 7 17 49), (row3 7 17 50), (row3 7 17 51)]

def b042_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 154 154), (row3 285 285 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 172 258 10), (row3 361 391 387), (row3 131 105 105), (row3 293 293 462), (row3 462 462 462)]

theorem b042_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_11_rows b042_11_labels 18384102910846044122996730150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_11_rows b042_11_labels]
    decide +kernel

def b042_12_rows : List Row := [(row3 7 17 52), (row3 7 17 53), (row3 7 17 54), (row3 7 17 55), (row3 7 17 56), (row3 7 17 57), (row3 7 17 58), (row3 7 17 59), (row3 7 17 60), (row3 7 17 61), (row3 7 17 62), (row3 7 17 63), (row3 7 18 19), (row3 7 18 20), (row3 7 18 21), (row3 7 18 22)]

def b042_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 118 215 11), (row3 368 114 86), (row3 35 31 36), (row3 395 415 407), (row3 131 105 105), (row3 284 284 462), (row3 462 462 462), (row3 117 214 11), (row3 398 135 83), (row3 45 389 436), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b042_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_12_rows b042_12_labels 1244691076286031796753108976250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_12_rows b042_12_labels]
    decide +kernel

def b042_13_rows : List Row := [(row3 7 18 23), (row3 7 18 24), (row3 7 18 25), (row3 7 18 26), (row3 7 18 27), (row3 7 18 28), (row3 7 18 29), (row3 7 18 30), (row3 7 18 31), (row3 7 18 32), (row3 7 18 33), (row3 7 18 34), (row3 7 18 35), (row3 7 18 36), (row3 7 18 37), (row3 7 18 38)]

def b042_13_labels : List Row := [(row3 302 265 302), (row3 271 462 271), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b042_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_13_rows b042_13_labels 202722614314531821665627400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_13_rows b042_13_labels]
    decide +kernel

def b042_14_rows : List Row := [(row3 7 18 39), (row3 7 18 40), (row3 7 18 41), (row3 7 18 42), (row3 7 18 43), (row3 7 18 44), (row3 7 18 45), (row3 7 18 46), (row3 7 18 47), (row3 7 18 48), (row3 7 18 49), (row3 7 18 50), (row3 7 18 51), (row3 7 18 52), (row3 7 18 53), (row3 7 18 54)]

def b042_14_labels : List Row := [(row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 462 180), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b042_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_14_rows b042_14_labels 640192649090852778766956000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_14_rows b042_14_labels]
    decide +kernel

def b042_15_rows : List Row := [(row3 7 18 55), (row3 7 18 56), (row3 7 18 57), (row3 7 18 58), (row3 7 18 59), (row3 7 18 60), (row3 7 18 61), (row3 7 18 62), (row3 7 18 63), (row3 7 19 20), (row3 7 19 21), (row3 7 19 22), (row3 7 19 23), (row3 7 19 24), (row3 7 19 25), (row3 7 19 26)]

def b042_15_labels : List Row := [(row3 293 462 293), (row3 377 462 377), (row3 139 232 138), (row3 294 462 294), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 139 462 139), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b042_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b042_15_rows b042_15_labels 22986972628269911856687217500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b042_15_rows b042_15_labels]
    decide +kernel

theorem checked042 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_042 QuarticIntegerComputationalData.ids64_042 4410451792643081054212594388739630 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b042_00_rows ++ b042_01_rows) ++ (b042_02_rows ++ b042_03_rows)) ++ ((b042_04_rows ++ b042_05_rows) ++ (b042_06_rows ++ b042_07_rows))) ++ (((b042_08_rows ++ b042_09_rows) ++ (b042_10_rows ++ b042_11_rows)) ++ ((b042_12_rows ++ b042_13_rows) ++ (b042_14_rows ++ b042_15_rows))))
    ((((b042_00_labels ++ b042_01_labels) ++ (b042_02_labels ++ b042_03_labels)) ++ ((b042_04_labels ++ b042_05_labels) ++ (b042_06_labels ++ b042_07_labels))) ++ (((b042_08_labels ++ b042_09_labels) ++ (b042_10_labels ++ b042_11_labels)) ++ ((b042_12_labels ++ b042_13_labels) ++ (b042_14_labels ++ b042_15_labels)))) 4410451792643081054212594388739630
  exact ((((b042_00_checked.append (c := 1079028876176563075232205075001500) b042_01_checked (by decide +kernel)).append (c := 1141439792142082694670829300484610) (b042_02_checked.append (c := 62410915965519619438624225483110) b042_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4396249939842449709112805334886050) ((b042_04_checked.append (c := 994913577205394327607749418653040) b042_05_checked (by decide +kernel)).append (c := 3254810147700367014441976034401440) (b042_06_checked.append (c := 2259896570494972686834226615748400) b042_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4410451792643081054212594388739630) (((b042_08_checked.append (c := 12851578376739486338831638197090) b042_09_checked (by decide +kernel)).append (c := 12933331836453638006578825076430) (b042_10_checked.append (c := 81753459714151667747186879340) b042_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 14201852800631345099789053853580) ((b042_12_checked.append (c := 1244893798900346328574774603650) b042_13_checked (by decide +kernel)).append (c := 1268520964177707093210228777150) (b042_14_checked.append (c := 23627165277360764635454173500) b042_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b043_00_rows : List Row := [(row3 7 19 27), (row3 7 19 28), (row3 7 19 29), (row3 7 19 30), (row3 7 19 31), (row3 7 19 32), (row3 7 19 33), (row3 7 19 34), (row3 7 19 35), (row3 7 19 36), (row3 7 19 37), (row3 7 19 38), (row3 7 19 39), (row3 7 19 40), (row3 7 19 41), (row3 7 19 42)]

def b043_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_00_rows b043_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_00_rows b043_00_labels]
    decide +kernel

def b043_01_rows : List Row := [(row3 7 19 43), (row3 7 19 44), (row3 7 19 45), (row3 7 19 46), (row3 7 19 47), (row3 7 19 48), (row3 7 19 49), (row3 7 19 50), (row3 7 19 51), (row3 7 19 52), (row3 7 19 53), (row3 7 19 54), (row3 7 19 55), (row3 7 19 56), (row3 7 19 57), (row3 7 19 58)]

def b043_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_01_rows b043_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_01_rows b043_01_labels]
    decide +kernel

def b043_02_rows : List Row := [(row3 7 19 59), (row3 7 19 60), (row3 7 19 61), (row3 7 19 62), (row3 7 19 63), (row3 7 20 21), (row3 7 20 22), (row3 7 20 23), (row3 7 20 24), (row3 7 20 25), (row3 7 20 26), (row3 7 20 27), (row3 7 20 28), (row3 7 20 29), (row3 7 20 30), (row3 7 20 31)]

def b043_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 266 265 266), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_02_rows b043_02_labels 63533873167872911719250400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_02_rows b043_02_labels]
    decide +kernel

def b043_03_rows : List Row := [(row3 7 20 32), (row3 7 20 33), (row3 7 20 34), (row3 7 20 35), (row3 7 20 36), (row3 7 20 37), (row3 7 20 38), (row3 7 20 39), (row3 7 20 40), (row3 7 20 41), (row3 7 20 42), (row3 7 20 43), (row3 7 20 44), (row3 7 20 45), (row3 7 20 46), (row3 7 20 47)]

def b043_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_03_rows b043_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_03_rows b043_03_labels]
    decide +kernel

def b043_04_rows : List Row := [(row3 7 20 48), (row3 7 20 49), (row3 7 20 50), (row3 7 20 51), (row3 7 20 52), (row3 7 20 53), (row3 7 20 54), (row3 7 20 55), (row3 7 20 56), (row3 7 20 57), (row3 7 20 58), (row3 7 20 59), (row3 7 20 60), (row3 7 20 61), (row3 7 20 62), (row3 7 20 63)]

def b043_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_04_rows b043_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_04_rows b043_04_labels]
    decide +kernel

def b043_05_rows : List Row := [(row3 7 21 22), (row3 7 21 23), (row3 7 21 24), (row3 7 21 25), (row3 7 21 26), (row3 7 21 27), (row3 7 21 28), (row3 7 21 29), (row3 7 21 30), (row3 7 21 31), (row3 7 21 32), (row3 7 21 33), (row3 7 21 34), (row3 7 21 35), (row3 7 21 36), (row3 7 21 37)]

def b043_05_labels : List Row := [(row3 316 316 462), (row3 140 140 178), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 271 271 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_05_rows b043_05_labels 18336300502841716294073304180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_05_rows b043_05_labels]
    decide +kernel

def b043_06_rows : List Row := [(row3 7 21 38), (row3 7 21 39), (row3 7 21 40), (row3 7 21 41), (row3 7 21 42), (row3 7 21 43), (row3 7 21 44), (row3 7 21 45), (row3 7 21 46), (row3 7 21 47), (row3 7 21 48), (row3 7 21 49), (row3 7 21 50), (row3 7 21 51), (row3 7 21 52), (row3 7 21 53)]

def b043_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_06_rows b043_06_labels 120925542892154466838230000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_06_rows b043_06_labels]
    decide +kernel

def b043_07_rows : List Row := [(row3 7 21 54), (row3 7 21 55), (row3 7 21 56), (row3 7 21 57), (row3 7 21 58), (row3 7 21 59), (row3 7 21 60), (row3 7 21 61), (row3 7 21 62), (row3 7 21 63), (row3 7 22 23), (row3 7 22 24), (row3 7 22 25), (row3 7 22 26), (row3 7 22 27), (row3 7 22 28)]

def b043_07_labels : List Row := [(row3 293 293 462), (row3 180 180 462), (row3 139 139 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 294 294 462), (row3 139 138 232), (row3 377 377 462), (row3 394 409 414), (row3 173 10 260), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248)]

theorem b043_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_07_rows b043_07_labels 1982506030047514239007519167300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_07_rows b043_07_labels]
    decide +kernel

def b043_08_rows : List Row := [(row3 7 22 29), (row3 7 22 30), (row3 7 22 31), (row3 7 22 32), (row3 7 22 33), (row3 7 22 34), (row3 7 22 35), (row3 7 22 36), (row3 7 22 37), (row3 7 22 38), (row3 7 22 39), (row3 7 22 40), (row3 7 22 41), (row3 7 22 42), (row3 7 22 43), (row3 7 22 44)]

def b043_08_labels : List Row := [(row3 228 462 228), (row3 307 462 307), (row3 177 152 150), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 462 234), (row3 272 462 272), (row3 172 10 258), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_08_rows b043_08_labels 18220669739441732881946929500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_08_rows b043_08_labels]
    decide +kernel

def b043_09_rows : List Row := [(row3 7 22 45), (row3 7 22 46), (row3 7 22 47), (row3 7 22 48), (row3 7 22 49), (row3 7 22 50), (row3 7 22 51), (row3 7 22 52), (row3 7 22 53), (row3 7 22 54), (row3 7 22 55), (row3 7 22 56), (row3 7 22 57), (row3 7 22 58), (row3 7 22 59), (row3 7 22 60)]

def b043_09_labels : List Row := [(row3 462 462 462), (row3 285 462 285), (row3 180 154 154), (row3 368 86 114), (row3 118 11 215), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 131 105 105), (row3 361 387 391), (row3 45 436 389), (row3 398 83 135), (row3 117 11 214), (row3 462 462 462), (row3 284 462 284)]

theorem b043_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_09_rows b043_09_labels 424904466618740863915871332950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_09_rows b043_09_labels]
    decide +kernel

def b043_10_rows : List Row := [(row3 7 22 61), (row3 7 22 62), (row3 7 22 63), (row3 7 23 24), (row3 7 23 25), (row3 7 23 26), (row3 7 23 27), (row3 7 23 28), (row3 7 23 29), (row3 7 23 30), (row3 7 23 31), (row3 7 23 32), (row3 7 23 33), (row3 7 23 34), (row3 7 23 35), (row3 7 23 36)]

def b043_10_labels : List Row := [(row3 131 105 105), (row3 395 407 415), (row3 35 36 31), (row3 331 92 123), (row3 305 305 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 291 289), (row3 132 137 133), (row3 384 400 397), (row3 299 299 289), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_10_rows b043_10_labels 2222442247223639770378147194750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_10_rows b043_10_labels]
    decide +kernel

def b043_11_rows : List Row := [(row3 7 23 37), (row3 7 23 38), (row3 7 23 39), (row3 7 23 40), (row3 7 23 41), (row3 7 23 42), (row3 7 23 43), (row3 7 23 44), (row3 7 23 45), (row3 7 23 46), (row3 7 23 47), (row3 7 23 48), (row3 7 23 49), (row3 7 23 50), (row3 7 23 51), (row3 7 23 52)]

def b043_11_labels : List Row := [(row3 462 234 234), (row3 291 291 289), (row3 174 178 174), (row3 332 93 155), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 235 191), (row3 329 344 340), (row3 78 427 401), (row3 368 86 114), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_11_rows b043_11_labels 91975841555239556243564327370 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_11_rows b043_11_labels]
    decide +kernel

def b043_12_rows : List Row := [(row3 7 23 53), (row3 7 23 54), (row3 7 23 55), (row3 7 23 56), (row3 7 23 57), (row3 7 23 58), (row3 7 23 59), (row3 7 23 60), (row3 7 23 61), (row3 7 23 62), (row3 7 23 63), (row3 7 24 25), (row3 7 24 26), (row3 7 24 27), (row3 7 24 28), (row3 7 24 29)]

def b043_12_labels : List Row := [(row3 180 462 180), (row3 361 391 387), (row3 79 67 67), (row3 443 27 34), (row3 59 431 410), (row3 369 86 122), (row3 284 284 462), (row3 193 462 193), (row3 360 390 387), (row3 62 52 49), (row3 448 449 454), (row3 274 274 462), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462)]

theorem b043_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_12_rows b043_12_labels 12752836631414975367677653023900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_12_rows b043_12_labels]
    decide +kernel

def b043_13_rows : List Row := [(row3 7 24 30), (row3 7 24 31), (row3 7 24 32), (row3 7 24 33), (row3 7 24 34), (row3 7 24 35), (row3 7 24 36), (row3 7 24 37), (row3 7 24 38), (row3 7 24 39), (row3 7 24 40), (row3 7 24 41), (row3 7 24 42), (row3 7 24 43), (row3 7 24 44), (row3 7 24 45)]

def b043_13_labels : List Row := [(row3 238 238 462), (row3 186 269 9), (row3 269 269 462), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 207 200 200), (row3 264 264 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_13_rows b043_13_labels 28000495934990080000446775500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_13_rows b043_13_labels]
    decide +kernel

def b043_14_rows : List Row := [(row3 7 24 46), (row3 7 24 47), (row3 7 24 48), (row3 7 24 49), (row3 7 24 50), (row3 7 24 51), (row3 7 24 52), (row3 7 24 53), (row3 7 24 54), (row3 7 24 55), (row3 7 24 56), (row3 7 24 57), (row3 7 24 58), (row3 7 24 59), (row3 7 24 60), (row3 7 24 61)]

def b043_14_labels : List Row := [(row3 462 462 462), (row3 204 259 8), (row3 329 344 340), (row3 180 154 154), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 172 258 10), (row3 332 155 93), (row3 64 55 66), (row3 352 373 365), (row3 180 154 154), (row3 263 263 462), (row3 462 462 462), (row3 171 254 10)]

theorem b043_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_14_rows b043_14_labels 282169858062597297980912403900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_14_rows b043_14_labels]
    decide +kernel

def b043_15_rows : List Row := [(row3 7 24 62), (row3 7 24 63), (row3 7 25 26), (row3 7 25 27), (row3 7 25 28), (row3 7 25 29), (row3 7 25 30), (row3 7 25 31), (row3 7 25 32), (row3 7 25 33), (row3 7 25 34), (row3 7 25 35), (row3 7 25 36), (row3 7 25 37), (row3 7 25 38), (row3 7 25 39)]

def b043_15_labels : List Row := [(row3 356 159 91), (row3 73 359 429), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b043_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b043_15_rows b043_15_labels 115965110764340880541120232100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b043_15_rows b043_15_labels]
    decide +kernel

theorem checked043 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_043 QuarticIntegerComputationalData.ids64_043 17937542111280381532299812171850 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b043_00_rows ++ b043_01_rows) ++ (b043_02_rows ++ b043_03_rows)) ++ ((b043_04_rows ++ b043_05_rows) ++ (b043_06_rows ++ b043_07_rows))) ++ (((b043_08_rows ++ b043_09_rows) ++ (b043_10_rows ++ b043_11_rows)) ++ ((b043_12_rows ++ b043_13_rows) ++ (b043_14_rows ++ b043_15_rows))))
    ((((b043_00_labels ++ b043_01_labels) ++ (b043_02_labels ++ b043_03_labels)) ++ ((b043_04_labels ++ b043_05_labels) ++ (b043_06_labels ++ b043_07_labels))) ++ (((b043_08_labels ++ b043_09_labels) ++ (b043_10_labels ++ b043_11_labels)) ++ ((b043_12_labels ++ b043_13_labels) ++ (b043_14_labels ++ b043_15_labels)))) 17937542111280381532299812171850
  exact ((((b043_00_checked.append (c := 0) b043_01_checked (by decide +kernel)).append (c := 63533873167872911719250400) (b043_02_checked.append (c := 63533873167872911719250400) b043_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2001026789966415982680149951880) ((b043_04_checked.append (c := 18336300502841716294073304180) b043_05_checked (by decide +kernel)).append (c := 2000963256093248109768430701480) (b043_06_checked.append (c := 1982626955590406393474357397300) b043_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 17937542111280381532299812171850) (((b043_08_checked.append (c := 443125136358182596797818262450) b043_09_checked (by decide +kernel)).append (c := 2757543225137061923419529784570) (b043_10_checked.append (c := 2314418088778879326621711522120) b043_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 15936515321313965549619662219970) ((b043_12_checked.append (c := 12780837127349965447678099799400) b043_13_checked (by decide +kernel)).append (c := 13178972096176903626200132435400) (b043_14_checked.append (c := 398134968826938178522032636000) b043_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b044_00_rows : List Row := [(row3 7 25 40), (row3 7 25 41), (row3 7 25 42), (row3 7 25 43), (row3 7 25 44), (row3 7 25 45), (row3 7 25 46), (row3 7 25 47), (row3 7 25 48), (row3 7 25 49), (row3 7 25 50), (row3 7 25 51), (row3 7 25 52), (row3 7 25 53), (row3 7 25 54), (row3 7 25 55)]

def b044_00_labels : List Row := [(row3 264 462 264), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 235 191), (row3 285 462 285), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284)]

theorem b044_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_00_rows b044_00_labels 515710713067513015914397500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_00_rows b044_00_labels]
    decide +kernel

def b044_01_rows : List Row := [(row3 7 25 56), (row3 7 25 57), (row3 7 25 58), (row3 7 25 59), (row3 7 25 60), (row3 7 25 61), (row3 7 25 62), (row3 7 25 63), (row3 7 26 27), (row3 7 26 28), (row3 7 26 29), (row3 7 26 30), (row3 7 26 31), (row3 7 26 32), (row3 7 26 33), (row3 7 26 34)]

def b044_01_labels : List Row := [(row3 358 462 358), (row3 163 235 162), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 163 462 163), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_01_rows b044_01_labels 15249430475993740988029224000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_01_rows b044_01_labels]
    decide +kernel

def b044_02_rows : List Row := [(row3 7 26 35), (row3 7 26 36), (row3 7 26 37), (row3 7 26 38), (row3 7 26 39), (row3 7 26 40), (row3 7 26 41), (row3 7 26 42), (row3 7 26 43), (row3 7 26 44), (row3 7 26 45), (row3 7 26 46), (row3 7 26 47), (row3 7 26 48), (row3 7 26 49), (row3 7 26 50)]

def b044_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_02_rows b044_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_02_rows b044_02_labels]
    decide +kernel

def b044_03_rows : List Row := [(row3 7 26 51), (row3 7 26 52), (row3 7 26 53), (row3 7 26 54), (row3 7 26 55), (row3 7 26 56), (row3 7 26 57), (row3 7 26 58), (row3 7 26 59), (row3 7 26 60), (row3 7 26 61), (row3 7 26 62), (row3 7 26 63), (row3 7 27 28), (row3 7 27 29), (row3 7 27 30)]

def b044_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_03_rows b044_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_03_rows b044_03_labels]
    decide +kernel

def b044_04_rows : List Row := [(row3 7 27 31), (row3 7 27 32), (row3 7 27 33), (row3 7 27 34), (row3 7 27 35), (row3 7 27 36), (row3 7 27 37), (row3 7 27 38), (row3 7 27 39), (row3 7 27 40), (row3 7 27 41), (row3 7 27 42), (row3 7 27 43), (row3 7 27 44), (row3 7 27 45), (row3 7 27 46)]

def b044_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_04_rows b044_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_04_rows b044_04_labels]
    decide +kernel

def b044_05_rows : List Row := [(row3 7 27 47), (row3 7 27 48), (row3 7 27 49), (row3 7 27 50), (row3 7 27 51), (row3 7 27 52), (row3 7 27 53), (row3 7 27 54), (row3 7 27 55), (row3 7 27 56), (row3 7 27 57), (row3 7 27 58), (row3 7 27 59), (row3 7 27 60), (row3 7 27 61), (row3 7 27 62)]

def b044_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_05_rows b044_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_05_rows b044_05_labels]
    decide +kernel

def b044_06_rows : List Row := [(row3 7 27 63), (row3 7 28 29), (row3 7 28 30), (row3 7 28 31), (row3 7 28 32), (row3 7 28 33), (row3 7 28 34), (row3 7 28 35), (row3 7 28 36), (row3 7 28 37), (row3 7 28 38), (row3 7 28 39), (row3 7 28 40), (row3 7 28 41), (row3 7 28 42), (row3 7 28 43)]

def b044_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_06_rows b044_06_labels 71216546417574934875000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_06_rows b044_06_labels]
    decide +kernel

def b044_07_rows : List Row := [(row3 7 28 44), (row3 7 28 45), (row3 7 28 46), (row3 7 28 47), (row3 7 28 48), (row3 7 28 49), (row3 7 28 50), (row3 7 28 51), (row3 7 28 52), (row3 7 28 53), (row3 7 28 54), (row3 7 28 55), (row3 7 28 56), (row3 7 28 57), (row3 7 28 58), (row3 7 28 59)]

def b044_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_07_rows b044_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_07_rows b044_07_labels]
    decide +kernel

def b044_08_rows : List Row := [(row3 7 28 60), (row3 7 28 61), (row3 7 28 62), (row3 7 28 63), (row3 7 29 30), (row3 7 29 31), (row3 7 29 32), (row3 7 29 33), (row3 7 29 34), (row3 7 29 35), (row3 7 29 36), (row3 7 29 37), (row3 7 29 38), (row3 7 29 39), (row3 7 29 40), (row3 7 29 41)]

def b044_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_08_rows b044_08_labels 4572338464461712461804000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_08_rows b044_08_labels]
    decide +kernel

def b044_09_rows : List Row := [(row3 7 29 42), (row3 7 29 43), (row3 7 29 44), (row3 7 29 45), (row3 7 29 46), (row3 7 29 47), (row3 7 29 48), (row3 7 29 49), (row3 7 29 50), (row3 7 29 51), (row3 7 29 52), (row3 7 29 53), (row3 7 29 54), (row3 7 29 55), (row3 7 29 56), (row3 7 29 57)]

def b044_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_09_rows b044_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_09_rows b044_09_labels]
    decide +kernel

def b044_10_rows : List Row := [(row3 7 29 58), (row3 7 29 59), (row3 7 29 60), (row3 7 29 61), (row3 7 29 62), (row3 7 29 63), (row3 7 30 31), (row3 7 30 32), (row3 7 30 33), (row3 7 30 34), (row3 7 30 35), (row3 7 30 36), (row3 7 30 37), (row3 7 30 38), (row3 7 30 39), (row3 7 30 40)]

def b044_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 274 274 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b044_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_10_rows b044_10_labels 2928198593616723603168150000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_10_rows b044_10_labels]
    decide +kernel

def b044_11_rows : List Row := [(row3 7 30 41), (row3 7 30 42), (row3 7 30 43), (row3 7 30 44), (row3 7 30 45), (row3 7 30 46), (row3 7 30 47), (row3 7 30 48), (row3 7 30 49), (row3 7 30 50), (row3 7 30 51), (row3 7 30 52), (row3 7 30 53), (row3 7 30 54), (row3 7 30 55), (row3 7 30 56)]

def b044_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 264 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 285 285 462), (row3 193 191 235), (row3 163 163 462)]

theorem b044_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_11_rows b044_11_labels 1559513815894221071631373500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_11_rows b044_11_labels]
    decide +kernel

def b044_12_rows : List Row := [(row3 7 30 57), (row3 7 30 58), (row3 7 30 59), (row3 7 30 60), (row3 7 30 61), (row3 7 30 62), (row3 7 30 63), (row3 7 31 32), (row3 7 31 33), (row3 7 31 34), (row3 7 31 35), (row3 7 31 36), (row3 7 31 37), (row3 7 31 38), (row3 7 31 39), (row3 7 31 40)]

def b044_12_labels : List Row := [(row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 163 162 235), (row3 358 358 462), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 269 462 269), (row3 204 8 259)]

theorem b044_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_12_rows b044_12_labels 16707830886026985255438750000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_12_rows b044_12_labels]
    decide +kernel

def b044_13_rows : List Row := [(row3 7 31 41), (row3 7 31 42), (row3 7 31 43), (row3 7 31 44), (row3 7 31 45), (row3 7 31 46), (row3 7 31 47), (row3 7 31 48), (row3 7 31 49), (row3 7 31 50), (row3 7 31 51), (row3 7 31 52), (row3 7 31 53), (row3 7 31 54), (row3 7 31 55), (row3 7 31 56)]

def b044_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 462 264), (row3 207 200 200), (row3 332 93 155), (row3 172 10 258), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 180 154 154), (row3 329 340 344), (row3 73 429 359)]

theorem b044_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_13_rows b044_13_labels 121115781609094970652555125550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_13_rows b044_13_labels]
    decide +kernel

def b044_14_rows : List Row := [(row3 7 31 57), (row3 7 31 58), (row3 7 31 59), (row3 7 31 60), (row3 7 31 61), (row3 7 31 62), (row3 7 31 63), (row3 7 32 33), (row3 7 32 34), (row3 7 32 35), (row3 7 32 36), (row3 7 32 37), (row3 7 32 38), (row3 7 32 39), (row3 7 32 40), (row3 7 32 41)]

def b044_14_labels : List Row := [(row3 356 91 159), (row3 171 10 254), (row3 462 462 462), (row3 263 462 263), (row3 180 154 154), (row3 352 365 373), (row3 64 66 55), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 462 462 462)]

theorem b044_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_14_rows b044_14_labels 280192712083516786989735888450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_14_rows b044_14_labels]
    decide +kernel

def b044_15_rows : List Row := [(row3 7 32 42), (row3 7 32 43), (row3 7 32 44), (row3 7 32 45), (row3 7 32 46), (row3 7 32 47), (row3 7 32 48), (row3 7 32 49), (row3 7 32 50), (row3 7 32 51), (row3 7 32 52), (row3 7 32 53), (row3 7 32 54), (row3 7 32 55), (row3 7 32 56), (row3 7 32 57)]

def b044_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 174 178 174), (row3 272 462 272), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 299 289 299), (row3 341 429 71), (row3 193 232 189)]

theorem b044_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b044_15_rows b044_15_labels 113404366002465108122498664480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b044_15_rows b044_15_labels]
    decide +kernel

theorem checked044 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_044 QuarticIntegerComputationalData.ids64_044 551678187734686928986368252480 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b044_00_rows ++ b044_01_rows) ++ (b044_02_rows ++ b044_03_rows)) ++ ((b044_04_rows ++ b044_05_rows) ++ (b044_06_rows ++ b044_07_rows))) ++ (((b044_08_rows ++ b044_09_rows) ++ (b044_10_rows ++ b044_11_rows)) ++ ((b044_12_rows ++ b044_13_rows) ++ (b044_14_rows ++ b044_15_rows))))
    ((((b044_00_labels ++ b044_01_labels) ++ (b044_02_labels ++ b044_03_labels)) ++ ((b044_04_labels ++ b044_05_labels) ++ (b044_06_labels ++ b044_07_labels))) ++ (((b044_08_labels ++ b044_09_labels) ++ (b044_10_labels ++ b044_11_labels)) ++ ((b044_12_labels ++ b044_13_labels) ++ (b044_14_labels ++ b044_15_labels)))) 551678187734686928986368252480
  exact ((((b044_00_checked.append (c := 15765141189061254003943621500) b044_01_checked (by decide +kernel)).append (c := 15765141189061254003943621500) (b044_02_checked.append (c := 0) b044_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 15765212405607671578878496500) ((b044_04_checked.append (c := 0) b044_05_checked (by decide +kernel)).append (c := 71216546417574934875000) (b044_06_checked.append (c := 71216546417574934875000) b044_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 551678187734686928986368252480) (((b044_08_checked.append (c := 4572338464461712461804000) b044_09_checked (by decide +kernel)).append (c := 4492284747975406387261327500) (b044_10_checked.append (c := 4487712409510944674799523500) b044_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 535912975329079257407489755980) ((b044_12_checked.append (c := 137823612495121955907993875550) b044_13_checked (by decide +kernel)).append (c := 531420690581103851020228428480) (b044_14_checked.append (c := 393597078085981895112234552930) b044_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b045_00_rows : List Row := [(row3 7 32 58), (row3 7 32 59), (row3 7 32 60), (row3 7 32 61), (row3 7 32 62), (row3 7 32 63), (row3 7 33 34), (row3 7 33 35), (row3 7 33 36), (row3 7 33 37), (row3 7 33 38), (row3 7 33 39), (row3 7 33 40), (row3 7 33 41), (row3 7 33 42), (row3 7 33 43)]

def b045_00_labels : List Row := [(row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 193 163 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_00_rows b045_00_labels 1642931523648530459647785000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_00_rows b045_00_labels]
    decide +kernel

def b045_01_rows : List Row := [(row3 7 33 44), (row3 7 33 45), (row3 7 33 46), (row3 7 33 47), (row3 7 33 48), (row3 7 33 49), (row3 7 33 50), (row3 7 33 51), (row3 7 33 52), (row3 7 33 53), (row3 7 33 54), (row3 7 33 55), (row3 7 33 56), (row3 7 33 57), (row3 7 33 58), (row3 7 33 59)]

def b045_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 291 291 289), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 163 163), (row3 279 279 278), (row3 462 462 462), (row3 462 462 462)]

theorem b045_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_01_rows b045_01_labels 1328465579470823962674667800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_01_rows b045_01_labels]
    decide +kernel

def b045_02_rows : List Row := [(row3 7 33 60), (row3 7 33 61), (row3 7 33 62), (row3 7 33 63), (row3 7 34 35), (row3 7 34 36), (row3 7 34 37), (row3 7 34 38), (row3 7 34 39), (row3 7 34 40), (row3 7 34 41), (row3 7 34 42), (row3 7 34 43), (row3 7 34 44), (row3 7 34 45), (row3 7 34 46)]

def b045_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_02_rows b045_02_labels 289958420551243194225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_02_rows b045_02_labels]
    decide +kernel

def b045_03_rows : List Row := [(row3 7 34 47), (row3 7 34 48), (row3 7 34 49), (row3 7 34 50), (row3 7 34 51), (row3 7 34 52), (row3 7 34 53), (row3 7 34 54), (row3 7 34 55), (row3 7 34 56), (row3 7 34 57), (row3 7 34 58), (row3 7 34 59), (row3 7 34 60), (row3 7 34 61), (row3 7 34 62)]

def b045_03_labels : List Row := [(row3 462 462 462), (row3 462 234 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_03_rows b045_03_labels 7703572298100093899275500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_03_rows b045_03_labels]
    decide +kernel

def b045_04_rows : List Row := [(row3 7 34 63), (row3 7 35 36), (row3 7 35 37), (row3 7 35 38), (row3 7 35 39), (row3 7 35 40), (row3 7 35 41), (row3 7 35 42), (row3 7 35 43), (row3 7 35 44), (row3 7 35 45), (row3 7 35 46), (row3 7 35 47), (row3 7 35 48), (row3 7 35 49), (row3 7 35 50)]

def b045_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_04_rows b045_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_04_rows b045_04_labels]
    decide +kernel

def b045_05_rows : List Row := [(row3 7 35 51), (row3 7 35 52), (row3 7 35 53), (row3 7 35 54), (row3 7 35 55), (row3 7 35 56), (row3 7 35 57), (row3 7 35 58), (row3 7 35 59), (row3 7 35 60), (row3 7 35 61), (row3 7 35 62), (row3 7 35 63), (row3 7 36 37), (row3 7 36 38), (row3 7 36 39)]

def b045_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_05_rows b045_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_05_rows b045_05_labels]
    decide +kernel

def b045_06_rows : List Row := [(row3 7 36 40), (row3 7 36 41), (row3 7 36 42), (row3 7 36 43), (row3 7 36 44), (row3 7 36 45), (row3 7 36 46), (row3 7 36 47), (row3 7 36 48), (row3 7 36 49), (row3 7 36 50), (row3 7 36 51), (row3 7 36 52), (row3 7 36 53), (row3 7 36 54), (row3 7 36 55)]

def b045_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_06_rows b045_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_06_rows b045_06_labels]
    decide +kernel

def b045_07_rows : List Row := [(row3 7 36 56), (row3 7 36 57), (row3 7 36 58), (row3 7 36 59), (row3 7 36 60), (row3 7 36 61), (row3 7 36 62), (row3 7 36 63), (row3 7 37 38), (row3 7 37 39), (row3 7 37 40), (row3 7 37 41), (row3 7 37 42), (row3 7 37 43), (row3 7 37 44), (row3 7 37 45)]

def b045_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_07_rows b045_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_07_rows b045_07_labels]
    decide +kernel

def b045_08_rows : List Row := [(row3 7 37 46), (row3 7 37 47), (row3 7 37 48), (row3 7 37 49), (row3 7 37 50), (row3 7 37 51), (row3 7 37 52), (row3 7 37 53), (row3 7 37 54), (row3 7 37 55), (row3 7 37 56), (row3 7 37 57), (row3 7 37 58), (row3 7 37 59), (row3 7 37 60), (row3 7 37 61)]

def b045_08_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462)]

theorem b045_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_08_rows b045_08_labels 4340775947569292240716500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_08_rows b045_08_labels]
    decide +kernel

def b045_09_rows : List Row := [(row3 7 37 62), (row3 7 37 63), (row3 7 38 39), (row3 7 38 40), (row3 7 38 41), (row3 7 38 42), (row3 7 38 43), (row3 7 38 44), (row3 7 38 45), (row3 7 38 46), (row3 7 38 47), (row3 7 38 48), (row3 7 38 49), (row3 7 38 50), (row3 7 38 51), (row3 7 38 52)]

def b045_09_labels : List Row := [(row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_09_rows b045_09_labels 22793347755523681117389000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_09_rows b045_09_labels]
    decide +kernel

def b045_10_rows : List Row := [(row3 7 38 53), (row3 7 38 54), (row3 7 38 55), (row3 7 38 56), (row3 7 38 57), (row3 7 38 58), (row3 7 38 59), (row3 7 38 60), (row3 7 38 61), (row3 7 38 62), (row3 7 38 63), (row3 7 39 40), (row3 7 39 41), (row3 7 39 42), (row3 7 39 43), (row3 7 39 44)]

def b045_10_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 291 289 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279), (row3 462 163 163), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_10_rows b045_10_labels 1341972600633358396444414800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_10_rows b045_10_labels]
    decide +kernel

def b045_11_rows : List Row := [(row3 7 39 45), (row3 7 39 46), (row3 7 39 47), (row3 7 39 48), (row3 7 39 49), (row3 7 39 50), (row3 7 39 51), (row3 7 39 52), (row3 7 39 53), (row3 7 39 54), (row3 7 39 55), (row3 7 39 56), (row3 7 39 57), (row3 7 39 58), (row3 7 39 59), (row3 7 39 60)]

def b045_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 299 299 289), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 272 272 462), (row3 174 174 178), (row3 193 139 163), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_11_rows b045_11_labels 7617766764247980552199645380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_11_rows b045_11_labels]
    decide +kernel

def b045_12_rows : List Row := [(row3 7 39 61), (row3 7 39 62), (row3 7 39 63), (row3 7 40 41), (row3 7 40 42), (row3 7 40 43), (row3 7 40 44), (row3 7 40 45), (row3 7 40 46), (row3 7 40 47), (row3 7 40 48), (row3 7 40 49), (row3 7 40 50), (row3 7 40 51), (row3 7 40 52), (row3 7 40 53)]

def b045_12_labels : List Row := [(row3 269 269 462), (row3 193 189 232), (row3 341 71 429), (row3 274 274 462), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 186 269 9), (row3 384 400 397), (row3 177 152 150), (row3 271 271 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b045_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_12_rows b045_12_labels 1492025473917264952203432640800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_12_rows b045_12_labels]
    decide +kernel

def b045_13_rows : List Row := [(row3 7 40 54), (row3 7 40 55), (row3 7 40 56), (row3 7 40 57), (row3 7 40 58), (row3 7 40 59), (row3 7 40 60), (row3 7 40 61), (row3 7 40 62), (row3 7 40 63), (row3 7 41 42), (row3 7 41 43), (row3 7 41 44), (row3 7 41 45), (row3 7 41 46), (row3 7 41 47)]

def b045_13_labels : List Row := [(row3 173 260 10), (row3 331 123 92), (row3 56 29 445), (row3 354 376 366), (row3 180 154 154), (row3 263 263 462), (row3 462 462 462), (row3 171 254 10), (row3 356 158 89), (row3 74 44 439), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462)]

theorem b045_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_13_rows b045_13_labels 4730974338110697146570217607050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_13_rows b045_13_labels]
    decide +kernel

def b045_14_rows : List Row := [(row3 7 41 48), (row3 7 41 49), (row3 7 41 50), (row3 7 41 51), (row3 7 41 52), (row3 7 41 53), (row3 7 41 54), (row3 7 41 55), (row3 7 41 56), (row3 7 41 57), (row3 7 41 58), (row3 7 41 59), (row3 7 41 60), (row3 7 41 61), (row3 7 41 62), (row3 7 41 63)]

def b045_14_labels : List Row := [(row3 132 137 133), (row3 307 462 307), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 305 289 305), (row3 383 436 43), (row3 127 137 126), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 163 139 124)]

theorem b045_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_14_rows b045_14_labels 408011871020586355275277441680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_14_rows b045_14_labels]
    decide +kernel

def b045_15_rows : List Row := [(row3 7 42 43), (row3 7 42 44), (row3 7 42 45), (row3 7 42 46), (row3 7 42 47), (row3 7 42 48), (row3 7 42 49), (row3 7 42 50), (row3 7 42 51), (row3 7 42 52), (row3 7 42 53), (row3 7 42 54), (row3 7 42 55), (row3 7 42 56), (row3 7 42 57), (row3 7 42 58)]

def b045_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 291 291 289), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 139 139), (row3 309 309 306), (row3 235 462 235)]

theorem b045_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b045_15_rows b045_15_labels 2180380633572284773274859000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b045_15_rows b045_15_labels]
    decide +kernel

theorem checked045 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_045 QuarticIntegerComputationalData.ids64_045 6645158327804543176503620667510 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b045_00_rows ++ b045_01_rows) ++ (b045_02_rows ++ b045_03_rows)) ++ ((b045_04_rows ++ b045_05_rows) ++ (b045_06_rows ++ b045_07_rows))) ++ (((b045_08_rows ++ b045_09_rows) ++ (b045_10_rows ++ b045_11_rows)) ++ ((b045_12_rows ++ b045_13_rows) ++ (b045_14_rows ++ b045_15_rows))))
    ((((b045_00_labels ++ b045_01_labels) ++ (b045_02_labels ++ b045_03_labels)) ++ ((b045_04_labels ++ b045_05_labels) ++ (b045_06_labels ++ b045_07_labels))) ++ (((b045_08_labels ++ b045_09_labels) ++ (b045_10_labels ++ b045_11_labels)) ++ ((b045_12_labels ++ b045_13_labels) ++ (b045_14_labels ++ b045_15_labels)))) 6645158327804543176503620667510
  exact ((((b045_00_checked.append (c := 2971397103119354422322452800) b045_01_checked (by decide +kernel)).append (c := 2979390633838005759415953300) (b045_02_checked.append (c := 7993530718651337093500500) b045_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2979390633838005759415953300) ((b045_04_checked.append (c := 0) b045_05_checked (by decide +kernel)).append (c := 0) (b045_06_checked.append (c := 0) b045_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 6645158327804543176503620667510) (((b045_08_checked.append (c := 27134123703092973358105500) b045_09_checked (by decide +kernel)).append (c := 8986873488584431922002165680) (b045_10_checked.append (c := 8959739364881338948644060180) b045_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 6642178937170705170744204714210) ((b045_12_checked.append (c := 6222999812027962098773650247850) b045_13_checked (by decide +kernel)).append (c := 6633192063682120738822202548530) (b045_14_checked.append (c := 410192251654158640048552300680) b045_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b046_00_rows : List Row := [(row3 7 42 59), (row3 7 42 60), (row3 7 42 61), (row3 7 42 62), (row3 7 42 63), (row3 7 43 44), (row3 7 43 45), (row3 7 43 46), (row3 7 43 47), (row3 7 43 48), (row3 7 43 49), (row3 7 43 50), (row3 7 43 51), (row3 7 43 52), (row3 7 43 53), (row3 7 43 54)]

def b046_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b046_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_00_rows b046_00_labels 2993887056743500924498500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_00_rows b046_00_labels]
    decide +kernel

def b046_01_rows : List Row := [(row3 7 43 55), (row3 7 43 56), (row3 7 43 57), (row3 7 43 58), (row3 7 43 59), (row3 7 43 60), (row3 7 43 61), (row3 7 43 62), (row3 7 43 63), (row3 7 44 45), (row3 7 44 46), (row3 7 44 47), (row3 7 44 48), (row3 7 44 49), (row3 7 44 50), (row3 7 44 51)]

def b046_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b046_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_01_rows b046_01_labels 6423238967357483695626000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_01_rows b046_01_labels]
    decide +kernel

def b046_02_rows : List Row := [(row3 7 44 52), (row3 7 44 53), (row3 7 44 54), (row3 7 44 55), (row3 7 44 56), (row3 7 44 57), (row3 7 44 58), (row3 7 44 59), (row3 7 44 60), (row3 7 44 61), (row3 7 44 62), (row3 7 44 63), (row3 7 45 46), (row3 7 45 47), (row3 7 45 48), (row3 7 45 49)]

def b046_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 235 235), (row3 462 462 462)]

theorem b046_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_02_rows b046_02_labels 15602799602413360849189500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_02_rows b046_02_labels]
    decide +kernel

def b046_03_rows : List Row := [(row3 7 45 50), (row3 7 45 51), (row3 7 45 52), (row3 7 45 53), (row3 7 45 54), (row3 7 45 55), (row3 7 45 56), (row3 7 45 57), (row3 7 45 58), (row3 7 45 59), (row3 7 45 60), (row3 7 45 61), (row3 7 45 62), (row3 7 45 63), (row3 7 46 47), (row3 7 46 48)]

def b046_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 291 289 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 309 306 309), (row3 462 139 139), (row3 274 274 462), (row3 305 305 289)]

theorem b046_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_03_rows b046_03_labels 5379016912242902450457652200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_03_rows b046_03_labels]
    decide +kernel

def b046_04_rows : List Row := [(row3 7 46 49), (row3 7 46 50), (row3 7 46 51), (row3 7 46 52), (row3 7 46 53), (row3 7 46 54), (row3 7 46 55), (row3 7 46 56), (row3 7 46 57), (row3 7 46 58), (row3 7 46 59), (row3 7 46 60), (row3 7 46 61), (row3 7 46 62), (row3 7 46 63), (row3 7 47 48)]

def b046_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 307 307 462), (row3 132 133 137), (row3 163 124 139), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 286 462), (row3 127 126 137), (row3 383 43 436), (row3 331 92 123)]

theorem b046_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_04_rows b046_04_labels 430910471488283226223807439880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_04_rows b046_04_labels]
    decide +kernel

def b046_05_rows : List Row := [(row3 7 47 49), (row3 7 47 50), (row3 7 47 51), (row3 7 47 52), (row3 7 47 53), (row3 7 47 54), (row3 7 47 55), (row3 7 47 56), (row3 7 47 57), (row3 7 47 58), (row3 7 47 59), (row3 7 47 60), (row3 7 47 61), (row3 7 47 62), (row3 7 47 63), (row3 7 48 49)]

def b046_05_labels : List Row := [(row3 173 10 260), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 271 462 271), (row3 177 150 152), (row3 384 397 400), (row3 74 439 44), (row3 356 89 158), (row3 171 10 254), (row3 462 462 462), (row3 263 462 263), (row3 180 154 154), (row3 354 366 376), (row3 56 445 29), (row3 394 409 414)]

theorem b046_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_05_rows b046_05_labels 8020937373454757793282689223150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_05_rows b046_05_labels]
    decide +kernel

def b046_06_rows : List Row := [(row3 7 48 50), (row3 7 48 51), (row3 7 48 52), (row3 7 48 53), (row3 7 48 54), (row3 7 48 55), (row3 7 48 56), (row3 7 48 57), (row3 7 48 58), (row3 7 48 59), (row3 7 48 60), (row3 7 48 61), (row3 7 48 62), (row3 7 48 63), (row3 7 49 50), (row3 7 49 51)]

def b046_06_labels : List Row := [(row3 140 140 178), (row3 266 265 266), (row3 462 237 237), (row3 302 265 302), (row3 367 108 84), (row3 63 419 433), (row3 450 460 22), (row3 61 48 50), (row3 362 388 392), (row3 193 191 235), (row3 284 462 284), (row3 369 121 85), (row3 60 411 432), (row3 442 451 24), (row3 316 316 462), (row3 234 234 462)]

theorem b046_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_06_rows b046_06_labels 1006753521396069799040737427719770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_06_rows b046_06_labels]
    decide +kernel

def b046_07_rows : List Row := [(row3 7 49 52), (row3 7 49 53), (row3 7 49 54), (row3 7 49 55), (row3 7 49 56), (row3 7 49 57), (row3 7 49 58), (row3 7 49 59), (row3 7 49 60), (row3 7 49 61), (row3 7 49 62), (row3 7 49 63), (row3 7 50 51), (row3 7 50 52), (row3 7 50 53), (row3 7 50 54)]

def b046_07_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 119 216 11), (row3 367 108 84), (row3 32 25 452), (row3 418 424 422), (row3 129 102 103), (row3 287 287 462), (row3 462 462 462), (row3 117 214 11), (row3 398 134 81), (row3 46 46 440), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b046_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_07_rows b046_07_labels 18820570966865701177478159985840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_07_rows b046_07_labels]
    decide +kernel

def b046_08_rows : List Row := [(row3 7 50 55), (row3 7 50 56), (row3 7 50 57), (row3 7 50 58), (row3 7 50 59), (row3 7 50 60), (row3 7 50 61), (row3 7 50 62), (row3 7 50 63), (row3 7 51 52), (row3 7 51 53), (row3 7 51 54), (row3 7 51 55), (row3 7 51 56), (row3 7 51 57), (row3 7 51 58)]

def b046_08_labels : List Row := [(row3 302 265 302), (row3 389 436 45), (row3 100 113 100), (row3 307 462 307), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 139 163 124), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 237 237), (row3 462 163 163), (row3 309 309 306), (row3 232 462 232)]

theorem b046_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_08_rows b046_08_labels 417049316915824269630220171140 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_08_rows b046_08_labels]
    decide +kernel

def b046_09_rows : List Row := [(row3 7 51 59), (row3 7 51 60), (row3 7 51 61), (row3 7 51 62), (row3 7 51 63), (row3 7 52 53), (row3 7 52 54), (row3 7 52 55), (row3 7 52 56), (row3 7 52 57), (row3 7 52 58), (row3 7 52 59), (row3 7 52 60), (row3 7 52 61), (row3 7 52 62), (row3 7 52 63)]

def b046_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 266 265 266), (row3 462 462 462), (row3 462 232 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 309 306 309), (row3 462 163 163)]

theorem b046_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_09_rows b046_09_labels 1518355681178273072334763200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_09_rows b046_09_labels]
    decide +kernel

def b046_10_rows : List Row := [(row3 7 53 54), (row3 7 53 55), (row3 7 53 56), (row3 7 53 57), (row3 7 53 58), (row3 7 53 59), (row3 7 53 60), (row3 7 53 61), (row3 7 53 62), (row3 7 53 63), (row3 7 54 55), (row3 7 54 56), (row3 7 54 57), (row3 7 54 58), (row3 7 54 59), (row3 7 54 60)]

def b046_10_labels : List Row := [(row3 316 316 462), (row3 140 140 178), (row3 139 124 163), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 307 307 462), (row3 100 100 113), (row3 389 45 436), (row3 394 409 414), (row3 46 440 46), (row3 398 81 134), (row3 117 11 214), (row3 462 462 462), (row3 287 462 287)]

theorem b046_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_10_rows b046_10_labels 3338361759073513682664293976270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_10_rows b046_10_labels]
    decide +kernel

def b046_11_rows : List Row := [(row3 7 54 61), (row3 7 54 62), (row3 7 54 63), (row3 7 55 56), (row3 7 55 57), (row3 7 55 58), (row3 7 55 59), (row3 7 55 60), (row3 7 55 61), (row3 7 55 62), (row3 7 55 63), (row3 7 56 57), (row3 7 56 58), (row3 7 56 59), (row3 7 56 60), (row3 7 56 61)]

def b046_11_labels : List Row := [(row3 129 103 102), (row3 418 422 424), (row3 32 452 25), (row3 442 24 451), (row3 60 432 411), (row3 369 85 121), (row3 284 284 462), (row3 193 235 191), (row3 362 392 388), (row3 61 50 48), (row3 450 22 460), (row3 457 23 461), (row3 34 443 27), (row3 359 73 429), (row3 163 193 139), (row3 44 74 439)]

theorem b046_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_11_rows b046_11_labels 2094115989883252331016822260278650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_11_rows b046_11_labels]
    decide +kernel

def b046_12_rows : List Row := [(row3 7 56 62), (row3 7 56 63), (row3 7 57 58), (row3 7 57 59), (row3 7 57 60), (row3 7 57 61), (row3 7 57 62), (row3 7 57 63), (row3 7 58 59), (row3 7 58 60), (row3 7 58 61), (row3 7 58 62), (row3 7 58 63), (row3 7 59 60), (row3 7 59 61), (row3 7 59 62)]

def b046_12_labels : List Row := [(row3 451 442 24), (row3 20 20 17), (row3 417 422 423), (row3 127 126 137), (row3 301 278 301), (row3 399 156 82), (row3 40 413 438), (row3 451 442 24), (row3 303 303 462), (row3 235 235 462), (row3 116 213 11), (row3 399 156 82), (row3 44 74 439), (row3 462 462 462), (row3 235 235 462), (row3 301 278 301)]

theorem b046_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_12_rows b046_12_labels 9308696511179309912576902781844690 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_12_rows b046_12_labels]
    decide +kernel

def b046_13_rows : List Row := [(row3 7 59 63), (row3 7 60 61), (row3 7 60 62), (row3 7 60 63), (row3 7 61 62), (row3 7 61 63), (row3 7 62 63), (row3 8 9 10), (row3 8 9 11), (row3 8 9 12), (row3 8 9 13), (row3 8 9 14), (row3 8 9 15), (row3 8 9 16), (row3 8 9 17), (row3 8 9 18)]

def b046_13_labels : List Row := [(row3 163 193 139), (row3 303 303 462), (row3 127 126 137), (row3 359 73 429), (row3 417 422 423), (row3 34 443 27), (row3 457 23 461), (row3 450 460 22), (row3 56 29 445), (row3 341 429 71), (row3 64 55 66), (row3 448 454 449), (row3 18 19 19), (row3 19 19 18), (row3 457 461 23), (row3 32 25 452)]

theorem b046_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_13_rows b046_13_labels 5417000047095836547108172506946080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_13_rows b046_13_labels]
    decide +kernel

def b046_14_rows : List Row := [(row3 8 9 19), (row3 8 9 20), (row3 8 9 21), (row3 8 9 22), (row3 8 9 23), (row3 8 9 24), (row3 8 9 25), (row3 8 9 26), (row3 8 9 27), (row3 8 9 28), (row3 8 9 29), (row3 8 9 30), (row3 8 9 31), (row3 8 9 32), (row3 8 9 33), (row3 8 9 34)]

def b046_14_labels : List Row := [(row3 383 436 43), (row3 462 163 163), (row3 358 462 358), (row3 35 31 36), (row3 456 458 456), (row3 449 454 448), (row3 34 27 443), (row3 389 436 45), (row3 462 139 139), (row3 462 462 462), (row3 462 462 462), (row3 377 462 377), (row3 36 31 35), (row3 66 55 64), (row3 359 429 73), (row3 462 163 163)]

theorem b046_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_14_rows b046_14_labels 33498998513890640829008580693540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_14_rows b046_14_labels]
    decide +kernel

def b046_15_rows : List Row := [(row3 8 9 35), (row3 8 9 36), (row3 8 9 37), (row3 8 9 38), (row3 8 9 39), (row3 8 9 40), (row3 8 9 41), (row3 8 9 42), (row3 8 9 43), (row3 8 9 44), (row3 8 9 45), (row3 8 9 46), (row3 8 9 47), (row3 8 9 48), (row3 8 9 49), (row3 8 9 50)]

def b046_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 358 462 358), (row3 71 429 341), (row3 163 139 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 163 462), (row3 445 29 56), (row3 44 439 74), (row3 139 124 163)]

theorem b046_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b046_15_rows b046_15_labels 4810379905931804188005053716500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b046_15_rows b046_15_labels]
    decide +kernel

theorem checked046 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_046 QuarticIntegerComputationalData.ids64_046 17895910200254608162598796043724910 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b046_00_rows ++ b046_01_rows) ++ (b046_02_rows ++ b046_03_rows)) ++ ((b046_04_rows ++ b046_05_rows) ++ (b046_06_rows ++ b046_07_rows))) ++ (((b046_08_rows ++ b046_09_rows) ++ (b046_10_rows ++ b046_11_rows)) ++ ((b046_12_rows ++ b046_13_rows) ++ (b046_14_rows ++ b046_15_rows))))
    ((((b046_00_labels ++ b046_01_labels) ++ (b046_02_labels ++ b046_03_labels)) ++ ((b046_04_labels ++ b046_05_labels) ++ (b046_06_labels ++ b046_07_labels))) ++ (((b046_08_labels ++ b046_09_labels) ++ (b046_10_labels ++ b046_11_labels)) ++ ((b046_12_labels ++ b046_13_labels) ++ (b046_14_labels ++ b046_15_labels)))) 17895910200254608162598796043724910
  exact ((((b046_00_checked.append (c := 9417126024100984620124500) b046_01_checked (by decide +kernel)).append (c := 5404036837869416795926966200) (b046_02_checked.append (c := 5394619711845315811306841700) b046_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1034031344244716410654518011334840) ((b046_04_checked.append (c := 8451847844943041019506496663030) b046_05_checked (by decide +kernel)).append (c := 1034025940207878541237722084368640) (b046_06_checked.append (c := 1025574092362935500218215587705610) b046_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 17895910200254608162598796043724910) (((b046_08_checked.append (c := 418567672597002542702554934340) b046_09_checked (by decide +kernel)).append (c := 2097872919314922847242189109189260) (b046_10_checked.append (c := 2097454351642325844699486554254920) b046_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 16861878856009891751944278032390070) ((b046_12_checked.append (c := 14725696558275146459685075288790770) b046_13_checked (by decide +kernel)).append (c := 14764005936694968904702088923200810) (b046_14_checked.append (c := 38309378419822445017013634410040) b046_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b047_00_rows : List Row := [(row3 8 9 51), (row3 8 9 52), (row3 8 9 53), (row3 8 9 54), (row3 8 9 55), (row3 8 9 56), (row3 8 9 57), (row3 8 9 58), (row3 8 9 59), (row3 8 9 60), (row3 8 9 61), (row3 8 9 62), (row3 8 9 63), (row3 8 10 11), (row3 8 10 12), (row3 8 10 13)]

def b047_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 139 139 462), (row3 43 436 383), (row3 22 460 450), (row3 451 24 442), (row3 46 440 46), (row3 163 124 139), (row3 462 462 462), (row3 163 163 462), (row3 45 436 389), (row3 452 25 32), (row3 384 400 397), (row3 174 178 174), (row3 329 344 340)]

theorem b047_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_00_rows b047_00_labels 1013844796872625639580480093611350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_00_rows b047_00_labels]
    decide +kernel

def b047_01_rows : List Row := [(row3 8 10 14), (row3 8 10 15), (row3 8 10 16), (row3 8 10 17), (row3 8 10 18), (row3 8 10 19), (row3 8 10 20), (row3 8 10 21), (row3 8 10 22), (row3 8 10 23), (row3 8 10 24), (row3 8 10 25), (row3 8 10 26), (row3 8 10 27), (row3 8 10 28), (row3 8 10 29)]

def b047_01_labels : List Row := [(row3 79 67 67), (row3 448 449 454), (row3 447 447 455), (row3 61 50 48), (row3 394 414 409), (row3 132 137 133), (row3 291 291 289), (row3 193 235 191), (row3 361 391 387), (row3 62 52 49), (row3 76 69 68), (row3 362 392 388), (row3 140 178 140), (row3 291 291 289), (row3 462 234 234), (row3 462 462 462)]

theorem b047_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_01_rows b047_01_labels 18597556002030952886328407112360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_01_rows b047_01_labels]
    decide +kernel

def b047_02_rows : List Row := [(row3 8 10 30), (row3 8 10 31), (row3 8 10 32), (row3 8 10 33), (row3 8 10 34), (row3 8 10 35), (row3 8 10 36), (row3 8 10 37), (row3 8 10 38), (row3 8 10 39), (row3 8 10 40), (row3 8 10 41), (row3 8 10 42), (row3 8 10 43), (row3 8 10 44), (row3 8 10 45)]

def b047_02_labels : List Row := [(row3 180 462 180), (row3 360 390 387), (row3 328 342 339), (row3 193 235 191), (row3 266 266 265), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 333 94 168), (row3 284 284 462), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b047_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_02_rows b047_02_labels 23802175220496446335815335100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_02_rows b047_02_labels]
    decide +kernel

def b047_03_rows : List Row := [(row3 8 10 46), (row3 8 10 47), (row3 8 10 48), (row3 8 10 49), (row3 8 10 50), (row3 8 10 51), (row3 8 10 52), (row3 8 10 53), (row3 8 10 54), (row3 8 10 55), (row3 8 10 56), (row3 8 10 57), (row3 8 10 58), (row3 8 10 59), (row3 8 10 60), (row3 8 10 61)]

def b047_03_labels : List Row := [(row3 462 462 462), (row3 284 284 462), (row3 77 426 385), (row3 369 85 121), (row3 302 302 265), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 369 86 122), (row3 444 28 37), (row3 60 432 411), (row3 367 84 108), (row3 305 305 289), (row3 462 234 234), (row3 284 284 462)]

theorem b047_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_03_rows b047_03_labels 4855688176370070721926940868520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_03_rows b047_03_labels]
    decide +kernel

def b047_04_rows : List Row := [(row3 8 10 62), (row3 8 10 63), (row3 8 11 12), (row3 8 11 13), (row3 8 11 14), (row3 8 11 15), (row3 8 11 16), (row3 8 11 17), (row3 8 11 18), (row3 8 11 19), (row3 8 11 20), (row3 8 11 21), (row3 8 11 22), (row3 8 11 23), (row3 8 11 24), (row3 8 11 25)]

def b047_04_labels : List Row := [(row3 368 86 114), (row3 59 431 410), (row3 269 462 269), (row3 207 200 200), (row3 329 340 344), (row3 64 66 55), (row3 65 65 54), (row3 354 366 376), (row3 177 150 152), (row3 274 462 274), (row3 236 462 236), (row3 264 462 264), (row3 180 154 154), (row3 352 365 373), (row3 330 338 343), (row3 180 154 154)]

theorem b047_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_04_rows b047_04_labels 723805410476437510714980847500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_04_rows b047_04_labels]
    decide +kernel

def b047_05_rows : List Row := [(row3 8 11 26), (row3 8 11 27), (row3 8 11 28), (row3 8 11 29), (row3 8 11 30), (row3 8 11 31), (row3 8 11 32), (row3 8 11 33), (row3 8 11 34), (row3 8 11 35), (row3 8 11 36), (row3 8 11 37), (row3 8 11 38), (row3 8 11 39), (row3 8 11 40), (row3 8 11 41)]

def b047_05_labels : List Row := [(row3 271 462 271), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 269 462 269), (row3 180 154 154), (row3 208 201 201), (row3 263 462 263), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 203 8 254), (row3 462 462 462)]

theorem b047_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_05_rows b047_05_labels 1354281828302652172957006500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_05_rows b047_05_labels]
    decide +kernel

def b047_06_rows : List Row := [(row3 8 11 42), (row3 8 11 43), (row3 8 11 44), (row3 8 11 45), (row3 8 11 46), (row3 8 11 47), (row3 8 11 48), (row3 8 11 49), (row3 8 11 50), (row3 8 11 51), (row3 8 11 52), (row3 8 11 53), (row3 8 11 54), (row3 8 11 55), (row3 8 11 56), (row3 8 11 57)]

def b047_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 334 97 202), (row3 171 10 254), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 10 254), (row3 72 428 336), (row3 356 89 158)]

theorem b047_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_06_rows b047_06_labels 111669214912073103788668116900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_06_rows b047_06_labels]
    decide +kernel

def b047_07_rows : List Row := [(row3 8 11 58), (row3 8 11 59), (row3 8 11 60), (row3 8 11 61), (row3 8 11 62), (row3 8 11 63), (row3 8 12 13), (row3 8 12 14), (row3 8 12 15), (row3 8 12 16), (row3 8 12 17), (row3 8 12 18), (row3 8 12 19), (row3 8 12 20), (row3 8 12 21), (row3 8 12 22)]

def b047_07_labels : List Row := [(row3 173 10 260), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 172 10 258), (row3 356 91 159), (row3 269 269 462), (row3 174 174 178), (row3 341 71 429), (row3 337 337 462), (row3 193 189 232), (row3 272 272 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 272 272 462)]

theorem b047_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_07_rows b047_07_labels 129775046727379528392234963780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_07_rows b047_07_labels]
    decide +kernel

def b047_08_rows : List Row := [(row3 8 12 23), (row3 8 12 24), (row3 8 12 25), (row3 8 12 26), (row3 8 12 27), (row3 8 12 28), (row3 8 12 29), (row3 8 12 30), (row3 8 12 31), (row3 8 12 32), (row3 8 12 33), (row3 8 12 34), (row3 8 12 35), (row3 8 12 36), (row3 8 12 37), (row3 8 12 38)]

def b047_08_labels : List Row := [(row3 193 189 232), (row3 208 208 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 257 257 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b047_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_08_rows b047_08_labels 609848742616374086930086500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_08_rows b047_08_labels]
    decide +kernel

def b047_09_rows : List Row := [(row3 8 12 39), (row3 8 12 40), (row3 8 12 41), (row3 8 12 42), (row3 8 12 43), (row3 8 12 44), (row3 8 12 45), (row3 8 12 46), (row3 8 12 47), (row3 8 12 48), (row3 8 12 49), (row3 8 12 50), (row3 8 12 51), (row3 8 12 52), (row3 8 12 53), (row3 8 12 54)]

def b047_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 257 257 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b047_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_09_rows b047_09_labels 10094062839304017402007500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_09_rows b047_09_labels]
    decide +kernel

def b047_10_rows : List Row := [(row3 8 12 55), (row3 8 12 56), (row3 8 12 57), (row3 8 12 58), (row3 8 12 59), (row3 8 12 60), (row3 8 12 61), (row3 8 12 62), (row3 8 12 63), (row3 8 13 14), (row3 8 13 15), (row3 8 13 16), (row3 8 13 17), (row3 8 13 18), (row3 8 13 19), (row3 8 13 20)]

def b047_10_labels : List Row := [(row3 462 462 462), (row3 208 208 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 384 397 400), (row3 56 445 29), (row3 65 65 54), (row3 352 365 373), (row3 180 154 154), (row3 264 462 264), (row3 236 462 236)]

theorem b047_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_10_rows b047_10_labels 5769141677817823733494649034150 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_10_rows b047_10_labels]
    decide +kernel

def b047_11_rows : List Row := [(row3 8 13 21), (row3 8 13 22), (row3 8 13 23), (row3 8 13 24), (row3 8 13 25), (row3 8 13 26), (row3 8 13 27), (row3 8 13 28), (row3 8 13 29), (row3 8 13 30), (row3 8 13 31), (row3 8 13 32), (row3 8 13 33), (row3 8 13 34), (row3 8 13 35), (row3 8 13 36)]

def b047_11_labels : List Row := [(row3 274 462 274), (row3 177 150 152), (row3 354 366 376), (row3 330 338 343), (row3 180 154 154), (row3 269 462 269), (row3 462 462 462), (row3 243 462 243), (row3 238 462 238), (row3 271 462 271), (row3 180 154 154), (row3 208 201 201), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b047_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_11_rows b047_11_labels 32997430518652159008305731800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_11_rows b047_11_labels]
    decide +kernel

def b047_12_rows : List Row := [(row3 8 13 37), (row3 8 13 38), (row3 8 13 39), (row3 8 13 40), (row3 8 13 41), (row3 8 13 42), (row3 8 13 43), (row3 8 13 44), (row3 8 13 45), (row3 8 13 46), (row3 8 13 47), (row3 8 13 48), (row3 8 13 49), (row3 8 13 50), (row3 8 13 51), (row3 8 13 52)]

def b047_12_labels : List Row := [(row3 241 462 241), (row3 462 462 462), (row3 263 462 263), (row3 203 8 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 334 97 202), (row3 171 10 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b047_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_12_rows b047_12_labels 3768272765636709280463376000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_12_rows b047_12_labels]
    decide +kernel

def b047_13_rows : List Row := [(row3 8 13 53), (row3 8 13 54), (row3 8 13 55), (row3 8 13 56), (row3 8 13 57), (row3 8 13 58), (row3 8 13 59), (row3 8 13 60), (row3 8 13 61), (row3 8 13 62), (row3 8 13 63), (row3 8 14 15), (row3 8 14 16), (row3 8 14 17), (row3 8 14 18), (row3 8 14 19)]

def b047_13_labels : List Row := [(row3 241 462 241), (row3 462 462 462), (row3 171 10 254), (row3 72 428 336), (row3 356 91 159), (row3 172 10 258), (row3 462 462 462), (row3 243 462 243), (row3 238 462 238), (row3 173 10 260), (row3 356 89 158), (row3 450 22 460), (row3 447 447 455), (row3 62 52 49), (row3 361 391 387), (row3 193 235 191)]

theorem b047_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_13_rows b047_13_labels 977185749366988830451006250320530 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_13_rows b047_13_labels]
    decide +kernel

def b047_14_rows : List Row := [(row3 8 14 20), (row3 8 14 21), (row3 8 14 22), (row3 8 14 23), (row3 8 14 24), (row3 8 14 25), (row3 8 14 26), (row3 8 14 27), (row3 8 14 28), (row3 8 14 29), (row3 8 14 30), (row3 8 14 31), (row3 8 14 32), (row3 8 14 33), (row3 8 14 34), (row3 8 14 35)]

def b047_14_labels : List Row := [(row3 291 291 289), (row3 132 137 133), (row3 394 414 409), (row3 61 50 48), (row3 76 69 68), (row3 360 390 387), (row3 180 462 180), (row3 462 462 462), (row3 462 234 234), (row3 291 291 289), (row3 140 178 140), (row3 362 392 388), (row3 328 342 339), (row3 193 462 193), (row3 462 462 462), (row3 462 462 462)]

theorem b047_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_14_rows b047_14_labels 3467430778335173831109567837270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_14_rows b047_14_labels]
    decide +kernel

def b047_15_rows : List Row := [(row3 8 14 36), (row3 8 14 37), (row3 8 14 38), (row3 8 14 39), (row3 8 14 40), (row3 8 14 41), (row3 8 14 42), (row3 8 14 43), (row3 8 14 44), (row3 8 14 45), (row3 8 14 46), (row3 8 14 47), (row3 8 14 48), (row3 8 14 49), (row3 8 14 50), (row3 8 14 51)]

def b047_15_labels : List Row := [(row3 462 462 462), (row3 462 235 235), (row3 266 266 265), (row3 193 235 191), (row3 333 94 168), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 284 284 462), (row3 77 426 385), (row3 369 86 122), (row3 293 293 462), (row3 462 462 462)]

theorem b047_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b047_15_rows b047_15_labels 78027026713269362342277799320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b047_15_rows b047_15_labels]
    decide +kernel

theorem checked047 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_047 QuarticIntegerComputationalData.ids64_047 2024826181676136194354485944055080 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b047_00_rows ++ b047_01_rows) ++ (b047_02_rows ++ b047_03_rows)) ++ ((b047_04_rows ++ b047_05_rows) ++ (b047_06_rows ++ b047_07_rows))) ++ (((b047_08_rows ++ b047_09_rows) ++ (b047_10_rows ++ b047_11_rows)) ++ ((b047_12_rows ++ b047_13_rows) ++ (b047_14_rows ++ b047_15_rows))))
    ((((b047_00_labels ++ b047_01_labels) ++ (b047_02_labels ++ b047_03_labels)) ++ ((b047_04_labels ++ b047_05_labels) ++ (b047_06_labels ++ b047_07_labels))) ++ (((b047_08_labels ++ b047_09_labels) ++ (b047_10_labels ++ b047_11_labels)) ++ ((b047_12_labels ++ b047_13_labels) ++ (b047_14_labels ++ b047_15_labels)))) 2024826181676136194354485944055080
  exact ((((b047_00_checked.append (c := 1032442352874656592466808500723710) b047_01_checked (by decide +kernel)).append (c := 1037321843226247159635071256927330) (b047_02_checked.append (c := 4879490351590567168262756203620) b047_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1038288447180191352430140097862010) ((b047_04_checked.append (c := 725159692304740162887937854000) b047_05_checked (by decide +kernel)).append (c := 966603953944192795068840934680) (b047_06_checked.append (c := 241444261639452632180903080680) b047_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2024826181676136194354485944055080) (((b047_08_checked.append (c := 619942805455678104332094000) b047_09_checked (by decide +kernel)).append (c := 5802759051141931570607286859950) (b047_10_checked.append (c := 5802139108336475892502954765950) b047_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 986537734495944841924345846193070) ((b047_12_checked.append (c := 977189517639754467160286713696530) b047_13_checked (by decide +kernel)).append (c := 980734975444802910353738559333120) (b047_14_checked.append (c := 3545457805048443193451845636590) b047_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b048_00_rows : List Row := [(row3 8 14 52), (row3 8 14 53), (row3 8 14 54), (row3 8 14 55), (row3 8 14 56), (row3 8 14 57), (row3 8 14 58), (row3 8 14 59), (row3 8 14 60), (row3 8 14 61), (row3 8 14 62), (row3 8 14 63), (row3 8 15 16), (row3 8 15 17), (row3 8 15 18), (row3 8 15 19)]

def b048_00_labels : List Row := [(row3 462 462 462), (row3 462 235 235), (row3 302 302 265), (row3 369 85 121), (row3 444 28 37), (row3 59 431 410), (row3 368 86 114), (row3 284 284 462), (row3 462 234 234), (row3 305 305 289), (row3 367 84 108), (row3 60 432 411), (row3 19 19 18), (row3 456 458 456), (row3 35 31 36), (row3 358 462 358)]

theorem b048_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_00_rows b048_00_labels 1158638038342907299534798735728240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_00_rows b048_00_labels]
    decide +kernel

def b048_01_rows : List Row := [(row3 8 15 20), (row3 8 15 21), (row3 8 15 22), (row3 8 15 23), (row3 8 15 24), (row3 8 15 25), (row3 8 15 26), (row3 8 15 27), (row3 8 15 28), (row3 8 15 29), (row3 8 15 30), (row3 8 15 31), (row3 8 15 32), (row3 8 15 33), (row3 8 15 34), (row3 8 15 35)]

def b048_01_labels : List Row := [(row3 462 163 163), (row3 383 436 43), (row3 32 25 452), (row3 457 461 23), (row3 449 454 448), (row3 36 31 35), (row3 377 462 377), (row3 462 462 462), (row3 462 462 462), (row3 462 139 139), (row3 389 436 45), (row3 34 27 443), (row3 66 55 64), (row3 358 462 358), (row3 462 462 462), (row3 462 462 462)]

theorem b048_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_01_rows b048_01_labels 1099959683354070800567639597302680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_01_rows b048_01_labels]
    decide +kernel

def b048_02_rows : List Row := [(row3 8 15 36), (row3 8 15 37), (row3 8 15 38), (row3 8 15 39), (row3 8 15 40), (row3 8 15 41), (row3 8 15 42), (row3 8 15 43), (row3 8 15 44), (row3 8 15 45), (row3 8 15 46), (row3 8 15 47), (row3 8 15 48), (row3 8 15 49), (row3 8 15 50), (row3 8 15 51)]

def b048_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 359 429 73), (row3 71 429 341), (row3 163 163 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 139 193), (row3 445 29 56), (row3 43 436 383), (row3 139 139 462), (row3 462 462 462)]

theorem b048_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_02_rows b048_02_labels 4754181198779728890061310314500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_02_rows b048_02_labels]
    decide +kernel

def b048_03_rows : List Row := [(row3 8 15 52), (row3 8 15 53), (row3 8 15 54), (row3 8 15 55), (row3 8 15 56), (row3 8 15 57), (row3 8 15 58), (row3 8 15 59), (row3 8 15 60), (row3 8 15 61), (row3 8 15 62), (row3 8 15 63), (row3 8 16 17), (row3 8 16 18), (row3 8 16 19), (row3 8 16 20)]

def b048_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 139 124 163), (row3 44 439 74), (row3 22 460 450), (row3 452 25 32), (row3 45 436 389), (row3 163 163 462), (row3 462 462 462), (row3 163 124 139), (row3 46 440 46), (row3 451 24 442), (row3 450 460 22), (row3 37 28 444), (row3 336 428 72), (row3 462 208 208)]

theorem b048_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_03_rows b048_03_labels 1986586662240670358180650378403460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_03_rows b048_03_labels]
    decide +kernel

def b048_04_rows : List Row := [(row3 8 16 21), (row3 8 16 22), (row3 8 16 23), (row3 8 16 24), (row3 8 16 25), (row3 8 16 26), (row3 8 16 27), (row3 8 16 28), (row3 8 16 29), (row3 8 16 30), (row3 8 16 31), (row3 8 16 32), (row3 8 16 33), (row3 8 16 34), (row3 8 16 35), (row3 8 16 36)]

def b048_04_labels : List Row := [(row3 336 428 72), (row3 37 28 444), (row3 450 460 22), (row3 441 459 21), (row3 47 26 453), (row3 181 435 42), (row3 462 193 193), (row3 462 462 462), (row3 462 193 193), (row3 181 435 42), (row3 47 26 453), (row3 80 30 446), (row3 95 435 41), (row3 462 180 180), (row3 462 462 462), (row3 462 462 462)]

theorem b048_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_04_rows b048_04_labels 1870821488458151950212880773761550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_04_rows b048_04_labels]
    decide +kernel

def b048_05_rows : List Row := [(row3 8 16 37), (row3 8 16 38), (row3 8 16 39), (row3 8 16 40), (row3 8 16 41), (row3 8 16 42), (row3 8 16 43), (row3 8 16 44), (row3 8 16 45), (row3 8 16 46), (row3 8 16 47), (row3 8 16 48), (row3 8 16 49), (row3 8 16 50), (row3 8 16 51), (row3 8 16 52)]

def b048_05_labels : List Row := [(row3 462 462 462), (row3 462 180 180), (row3 95 435 41), (row3 70 434 70), (row3 193 163 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 163 193), (row3 446 30 80), (row3 41 435 95), (row3 180 180 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_05_rows b048_05_labels 4714572191186647725568426417800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_05_rows b048_05_labels]
    decide +kernel

def b048_06_rows : List Row := [(row3 8 16 53), (row3 8 16 54), (row3 8 16 55), (row3 8 16 56), (row3 8 16 57), (row3 8 16 58), (row3 8 16 59), (row3 8 16 60), (row3 8 16 61), (row3 8 16 62), (row3 8 16 63), (row3 8 17 18), (row3 8 17 19), (row3 8 17 20), (row3 8 17 21), (row3 8 17 22)]

def b048_06_labels : List Row := [(row3 462 462 462), (row3 180 180 462), (row3 41 435 95), (row3 21 459 441), (row3 453 26 47), (row3 42 435 181), (row3 193 193 462), (row3 462 462 462), (row3 193 193 462), (row3 42 435 181), (row3 453 26 47), (row3 418 424 422), (row3 127 137 126), (row3 279 279 278), (row3 163 235 162), (row3 395 415 407)]

theorem b048_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_06_rows b048_06_labels 897181300006584488877691225405440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_06_rows b048_06_labels]
    decide +kernel

def b048_07_rows : List Row := [(row3 8 17 23), (row3 8 17 24), (row3 8 17 25), (row3 8 17 26), (row3 8 17 27), (row3 8 17 28), (row3 8 17 29), (row3 8 17 30), (row3 8 17 31), (row3 8 17 32), (row3 8 17 33), (row3 8 17 34), (row3 8 17 35), (row3 8 17 36), (row3 8 17 37), (row3 8 17 38)]

def b048_07_labels : List Row := [(row3 38 33 33), (row3 57 53 51), (row3 417 423 422), (row3 100 113 100), (row3 309 309 306), (row3 462 232 232), (row3 462 462 462), (row3 139 232 138), (row3 396 416 408), (row3 353 375 366), (row3 127 137 126), (row3 309 309 306), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_07_rows b048_07_labels 7112574826494985839214448226300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_07_rows b048_07_labels]
    decide +kernel

def b048_08_rows : List Row := [(row3 8 17 39), (row3 8 17 40), (row3 8 17 41), (row3 8 17 42), (row3 8 17 43), (row3 8 17 44), (row3 8 17 45), (row3 8 17 46), (row3 8 17 47), (row3 8 17 48), (row3 8 17 49), (row3 8 17 50), (row3 8 17 51), (row3 8 17 52), (row3 8 17 53), (row3 8 17 54)]

def b048_08_labels : List Row := [(row3 163 228 160), (row3 357 90 187), (row3 301 301 278), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 58 430 372), (row3 399 82 156), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462)]

theorem b048_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_08_rows b048_08_labels 166424299901512606215799108020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_08_rows b048_08_labels]
    decide +kernel

def b048_09_rows : List Row := [(row3 8 17 55), (row3 8 17 56), (row3 8 17 57), (row3 8 17 58), (row3 8 17 59), (row3 8 17 60), (row3 8 17 61), (row3 8 17 62), (row3 8 17 63), (row3 8 18 19), (row3 8 18 20), (row3 8 18 21), (row3 8 18 22), (row3 8 18 23), (row3 8 18 24), (row3 8 18 25)]

def b048_09_labels : List Row := [(row3 399 83 157), (row3 453 26 47), (row3 40 438 413), (row3 398 81 134), (row3 284 284 462), (row3 462 462 462), (row3 284 284 462), (row3 398 83 135), (row3 39 437 412), (row3 307 462 307), (row3 234 462 234), (row3 285 462 285), (row3 131 105 105), (row3 395 407 415), (row3 363 386 393), (row3 129 103 102)]

theorem b048_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_09_rows b048_09_labels 13330732414325818468502063247840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_09_rows b048_09_labels]
    decide +kernel

def b048_10_rows : List Row := [(row3 8 18 26), (row3 8 18 27), (row3 8 18 28), (row3 8 18 29), (row3 8 18 30), (row3 8 18 31), (row3 8 18 32), (row3 8 18 33), (row3 8 18 34), (row3 8 18 35), (row3 8 18 36), (row3 8 18 37), (row3 8 18 38), (row3 8 18 39), (row3 8 18 40), (row3 8 18 41)]

def b048_10_labels : List Row := [(row3 316 462 316), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 293 462 293), (row3 131 105 105), (row3 180 154 154), (row3 287 462 287), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 170 10 218), (row3 462 462 462)]

theorem b048_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_10_rows b048_10_labels 17261679509664613547949123750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_10_rows b048_10_labels]
    decide +kernel

def b048_11_rows : List Row := [(row3 8 18 42), (row3 8 18 43), (row3 8 18 44), (row3 8 18 45), (row3 8 18 46), (row3 8 18 47), (row3 8 18 48), (row3 8 18 49), (row3 8 18 50), (row3 8 18 51), (row3 8 18 52), (row3 8 18 53), (row3 8 18 54), (row3 8 18 55), (row3 8 18 56), (row3 8 18 57)]

def b048_11_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 370 88 211), (row3 117 11 214), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 42 435 181), (row3 398 81 134)]

theorem b048_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_11_rows b048_11_labels 377410478995289802539619027450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_11_rows b048_11_labels]
    decide +kernel

def b048_12_rows : List Row := [(row3 8 18 58), (row3 8 18 59), (row3 8 18 60), (row3 8 18 61), (row3 8 18 62), (row3 8 18 63), (row3 8 19 20), (row3 8 19 21), (row3 8 19 22), (row3 8 19 23), (row3 8 19 24), (row3 8 19 25), (row3 8 19 26), (row3 8 19 27), (row3 8 19 28), (row3 8 19 29)]

def b048_12_labels : List Row := [(row3 119 11 216), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 118 11 215), (row3 398 83 135), (row3 462 462 462), (row3 462 462 462), (row3 285 285 462), (row3 163 162 235), (row3 193 192 238), (row3 286 286 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_12_rows b048_12_labels 24945713326820176443923184000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_12_rows b048_12_labels]
    decide +kernel

def b048_13_rows : List Row := [(row3 8 19 30), (row3 8 19 31), (row3 8 19 32), (row3 8 19 33), (row3 8 19 34), (row3 8 19 35), (row3 8 19 36), (row3 8 19 37), (row3 8 19 38), (row3 8 19 39), (row3 8 19 40), (row3 8 19 41), (row3 8 19 42), (row3 8 19 43), (row3 8 19 44), (row3 8 19 45)]

def b048_13_labels : List Row := [(row3 462 462 462), (row3 284 284 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_13_rows b048_13_labels 79194550338313450657800000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_13_rows b048_13_labels]
    decide +kernel

def b048_14_rows : List Row := [(row3 8 19 46), (row3 8 19 47), (row3 8 19 48), (row3 8 19 49), (row3 8 19 50), (row3 8 19 51), (row3 8 19 52), (row3 8 19 53), (row3 8 19 54), (row3 8 19 55), (row3 8 19 56), (row3 8 19 57), (row3 8 19 58), (row3 8 19 59), (row3 8 19 60), (row3 8 19 61)]

def b048_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_14_rows b048_14_labels 588483461211089225927244000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_14_rows b048_14_labels]
    decide +kernel

def b048_15_rows : List Row := [(row3 8 19 62), (row3 8 19 63), (row3 8 20 21), (row3 8 20 22), (row3 8 20 23), (row3 8 20 24), (row3 8 20 25), (row3 8 20 26), (row3 8 20 27), (row3 8 20 28), (row3 8 20 29), (row3 8 20 30), (row3 8 20 31), (row3 8 20 32), (row3 8 20 33), (row3 8 20 34)]

def b048_15_labels : List Row := [(row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 234 234 462), (row3 279 278 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b048_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b048_15_rows b048_15_labels 171454929345400340012718600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b048_15_rows b048_15_labels]
    decide +kernel

theorem checked048 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_048 QuarticIntegerComputationalData.ids64_048 7043686114337846260298770847013630 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b048_00_rows ++ b048_01_rows) ++ (b048_02_rows ++ b048_03_rows)) ++ ((b048_04_rows ++ b048_05_rows) ++ (b048_06_rows ++ b048_07_rows))) ++ (((b048_08_rows ++ b048_09_rows) ++ (b048_10_rows ++ b048_11_rows)) ++ ((b048_12_rows ++ b048_13_rows) ++ (b048_14_rows ++ b048_15_rows))))
    ((((b048_00_labels ++ b048_01_labels) ++ (b048_02_labels ++ b048_03_labels)) ++ ((b048_04_labels ++ b048_05_labels) ++ (b048_06_labels ++ b048_07_labels))) ++ (((b048_08_labels ++ b048_09_labels) ++ (b048_10_labels ++ b048_11_labels)) ++ ((b048_12_labels ++ b048_13_labels) ++ (b048_14_labels ++ b048_15_labels)))) 7043686114337846260298770847013630
  exact ((((b048_00_checked.append (c := 2258597721696978100102438333030920) b048_01_checked (by decide +kernel)).append (c := 4249938565136428187173150021748880) (b048_02_checked.append (c := 1991340843439450087070711688717960) b048_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 7029768500618846259828504895559970) ((b048_04_checked.append (c := 1875536060649338597938449200179350) b048_05_checked (by decide +kernel)).append (c := 2779829935482418072655354873811090) (b048_06_checked.append (c := 904293874833079474716905673631740) b048_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7043686114337846260298770847013630) (((b048_08_checked.append (c := 13497156714227331074717862355860) b048_09_checked (by decide +kernel)).append (c := 13891828872732285490805430507060) (b048_10_checked.append (c := 394672158504954416087568151200) b048_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 13917613719000000470265951453660) ((b048_12_checked.append (c := 25024907877158489894580984000) b048_13_checked (by decide +kernel)).append (c := 25784846267714979460520946600) (b048_14_checked.append (c := 759938390556489565939962600) b048_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
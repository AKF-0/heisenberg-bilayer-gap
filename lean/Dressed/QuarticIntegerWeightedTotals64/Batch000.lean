import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Block001
import Dressed.QuarticIntegerComputationalData64.Batch000


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b001_00_rows : List Row := [(row3 1 6 25), (row3 1 6 26), (row3 1 6 27), (row3 1 6 28), (row3 1 6 29), (row3 1 6 30), (row3 1 6 31), (row3 1 6 32), (row3 1 6 33), (row3 1 6 34), (row3 1 6 35), (row3 1 6 36), (row3 1 6 37), (row3 1 6 38), (row3 1 6 39), (row3 1 6 40)]

def b001_00_labels : List Row := [(row3 334 202 97), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 256 255 256), (row3 193 192 238), (row3 208 208 462), (row3 257 462 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 330 338 343)]

theorem b001_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_00_rows b001_00_labels 8552734446049683410408159850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_00_rows b001_00_labels]
    decide +kernel

def b001_01_rows : List Row := [(row3 1 6 41), (row3 1 6 42), (row3 1 6 43), (row3 1 6 44), (row3 1 6 45), (row3 1 6 46), (row3 1 6 47), (row3 1 6 48), (row3 1 6 49), (row3 1 6 50), (row3 1 6 51), (row3 1 6 52), (row3 1 6 53), (row3 1 6 54), (row3 1 6 55), (row3 1 6 56)]

def b001_01_labels : List Row := [(row3 334 202 97), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 256 255 256), (row3 193 192 238), (row3 76 69 68), (row3 77 385 426), (row3 370 211 88), (row3 269 462 269), (row3 462 237 237), (row3 266 265 266), (row3 164 164 206), (row3 363 386 393), (row3 449 454 448)]

theorem b001_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_01_rows b001_01_labels 7519430580926164811725787492130 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_01_rows b001_01_labels]
    decide +kernel

def b001_02_rows : List Row := [(row3 1 6 57), (row3 1 6 58), (row3 1 6 59), (row3 1 6 60), (row3 1 6 61), (row3 1 6 62), (row3 1 6 63), (row3 1 7 8), (row3 1 7 9), (row3 1 7 10), (row3 1 7 11), (row3 1 7 12), (row3 1 7 13), (row3 1 7 14), (row3 1 7 15), (row3 1 7 16)]

def b001_02_labels : List Row := [(row3 445 56 29), (row3 58 372 430), (row3 371 325 87), (row3 277 265 277), (row3 166 167 190), (row3 384 397 400), (row3 57 53 51), (row3 19 19 18), (row3 22 450 460), (row3 453 47 26), (row3 41 95 435), (row3 193 193 163), (row3 95 41 435), (row3 47 453 26), (row3 450 22 460), (row3 447 447 455)]

theorem b001_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_02_rows b001_02_labels 3113233014677993897999560659218640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_02_rows b001_02_labels]
    decide +kernel

def b001_03_rows : List Row := [(row3 1 7 17), (row3 1 7 18), (row3 1 7 19), (row3 1 7 20), (row3 1 7 21), (row3 1 7 22), (row3 1 7 23), (row3 1 7 24), (row3 1 7 25), (row3 1 7 26), (row3 1 7 27), (row3 1 7 28), (row3 1 7 29), (row3 1 7 30), (row3 1 7 31), (row3 1 7 32)]

def b001_03_labels : List Row := [(row3 444 37 28), (row3 42 181 435), (row3 180 462 180), (row3 462 462 462), (row3 462 180 180), (row3 181 42 435), (row3 37 444 28), (row3 65 65 54), (row3 72 336 428), (row3 193 462 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 193 193), (row3 336 72 428), (row3 337 337 462)]

theorem b001_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_03_rows b001_03_labels 10169489165976951672113655600600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_03_rows b001_03_labels]
    decide +kernel

def b001_04_rows : List Row := [(row3 1 7 33), (row3 1 7 34), (row3 1 7 35), (row3 1 7 36), (row3 1 7 37), (row3 1 7 38), (row3 1 7 39), (row3 1 7 40), (row3 1 7 41), (row3 1 7 42), (row3 1 7 43), (row3 1 7 44), (row3 1 7 45), (row3 1 7 46), (row3 1 7 47), (row3 1 7 48)]

def b001_04_labels : List Row := [(row3 208 462 208), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 208 208), (row3 65 65 54), (row3 72 336 428), (row3 193 462 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 193 193), (row3 336 72 428), (row3 447 447 455)]

theorem b001_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_04_rows b001_04_labels 7968578535838022066794035702540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_04_rows b001_04_labels]
    decide +kernel

def b001_05_rows : List Row := [(row3 1 7 49), (row3 1 7 50), (row3 1 7 51), (row3 1 7 52), (row3 1 7 53), (row3 1 7 54), (row3 1 7 55), (row3 1 7 56), (row3 1 7 57), (row3 1 7 58), (row3 1 7 59), (row3 1 7 60), (row3 1 7 61), (row3 1 7 62), (row3 1 7 63), (row3 1 8 9)]

def b001_05_labels : List Row := [(row3 444 37 28), (row3 42 181 435), (row3 180 462 180), (row3 462 462 462), (row3 462 180 180), (row3 181 42 435), (row3 37 444 28), (row3 19 19 18), (row3 22 450 460), (row3 453 47 26), (row3 41 95 435), (row3 193 193 163), (row3 95 41 435), (row3 47 453 26), (row3 450 22 460), (row3 20 20 17)]

theorem b001_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_05_rows b001_05_labels 12356704817049856499940201497088000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_05_rows b001_05_labels]
    decide +kernel

def b001_06_rows : List Row := [(row3 1 8 10), (row3 1 8 11), (row3 1 8 12), (row3 1 8 13), (row3 1 8 14), (row3 1 8 15), (row3 1 8 16), (row3 1 8 17), (row3 1 8 18), (row3 1 8 19), (row3 1 8 20), (row3 1 8 21), (row3 1 8 22), (row3 1 8 23), (row3 1 8 24), (row3 1 8 25)]

def b001_06_labels : List Row := [(row3 451 442 24), (row3 44 74 439), (row3 163 193 139), (row3 359 73 429), (row3 34 443 27), (row3 457 23 461), (row3 450 22 460), (row3 442 451 24), (row3 46 46 440), (row3 139 163 124), (row3 462 462 462), (row3 462 163 163), (row3 389 45 436), (row3 32 452 25), (row3 56 445 29), (row3 74 44 439)]

theorem b001_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_06_rows b001_06_labels 2122138360848205988892935052237180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_06_rows b001_06_labels]
    decide +kernel

def b001_07_rows : List Row := [(row3 1 8 26), (row3 1 8 27), (row3 1 8 28), (row3 1 8 29), (row3 1 8 30), (row3 1 8 31), (row3 1 8 32), (row3 1 8 33), (row3 1 8 34), (row3 1 8 35), (row3 1 8 36), (row3 1 8 37), (row3 1 8 38), (row3 1 8 39), (row3 1 8 40), (row3 1 8 41)]

def b001_07_labels : List Row := [(row3 163 139 124), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 139 139), (row3 383 43 436), (row3 341 71 429), (row3 193 163 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 64 66 55), (row3 73 359 429)]

theorem b001_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_07_rows b001_07_labels 858129847210564384389414850500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_07_rows b001_07_labels]
    decide +kernel

def b001_08_rows : List Row := [(row3 1 8 42), (row3 1 8 43), (row3 1 8 44), (row3 1 8 45), (row3 1 8 46), (row3 1 8 47), (row3 1 8 48), (row3 1 8 49), (row3 1 8 50), (row3 1 8 51), (row3 1 8 52), (row3 1 8 53), (row3 1 8 54), (row3 1 8 55), (row3 1 8 56), (row3 1 8 57)]

def b001_08_labels : List Row := [(row3 163 462 163), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 358 358 462), (row3 448 449 454), (row3 443 34 27), (row3 45 389 436), (row3 139 462 139), (row3 462 462 462), (row3 462 462 462), (row3 377 377 462), (row3 35 36 31), (row3 18 19 19), (row3 23 457 461)]

theorem b001_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_08_rows b001_08_labels 2219939245695854388181519279097580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_08_rows b001_08_labels]
    decide +kernel

def b001_09_rows : List Row := [(row3 1 8 58), (row3 1 8 59), (row3 1 8 60), (row3 1 8 61), (row3 1 8 62), (row3 1 8 63), (row3 1 9 10), (row3 1 9 11), (row3 1 9 12), (row3 1 9 13), (row3 1 9 14), (row3 1 9 15), (row3 1 9 16), (row3 1 9 17), (row3 1 9 18), (row3 1 9 19)]

def b001_09_labels : List Row := [(row3 452 32 25), (row3 43 383 436), (row3 163 462 163), (row3 358 358 462), (row3 36 35 31), (row3 456 456 458), (row3 457 461 23), (row3 34 27 443), (row3 359 429 73), (row3 163 139 193), (row3 44 439 74), (row3 451 24 442), (row3 442 24 451), (row3 450 460 22), (row3 32 25 452), (row3 389 436 45)]

theorem b001_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_09_rows b001_09_labels 2149985887377986661828295263948120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_09_rows b001_09_labels]
    decide +kernel

def b001_10_rows : List Row := [(row3 1 9 20), (row3 1 9 21), (row3 1 9 22), (row3 1 9 23), (row3 1 9 24), (row3 1 9 25), (row3 1 9 26), (row3 1 9 27), (row3 1 9 28), (row3 1 9 29), (row3 1 9 30), (row3 1 9 31), (row3 1 9 32), (row3 1 9 33), (row3 1 9 34), (row3 1 9 35)]

def b001_10_labels : List Row := [(row3 462 163 163), (row3 462 462 462), (row3 139 124 163), (row3 46 440 46), (row3 74 439 44), (row3 56 29 445), (row3 383 436 43), (row3 462 139 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 124 139), (row3 193 139 163), (row3 341 429 71), (row3 462 163 163), (row3 462 462 462)]

theorem b001_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_10_rows b001_10_labels 6099520331347339501347970929900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_10_rows b001_10_labels]
    decide +kernel

def b001_11_rows : List Row := [(row3 1 9 36), (row3 1 9 37), (row3 1 9 38), (row3 1 9 39), (row3 1 9 40), (row3 1 9 41), (row3 1 9 42), (row3 1 9 43), (row3 1 9 44), (row3 1 9 45), (row3 1 9 46), (row3 1 9 47), (row3 1 9 48), (row3 1 9 49), (row3 1 9 50), (row3 1 9 51)]

def b001_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 73 429 359), (row3 64 55 66), (row3 358 462 358), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 163 462), (row3 443 27 34), (row3 448 454 449), (row3 35 31 36), (row3 377 462 377)]

theorem b001_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_11_rows b001_11_labels 13461397916290830022820915345400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_11_rows b001_11_labels]
    decide +kernel

def b001_12_rows : List Row := [(row3 1 9 52), (row3 1 9 53), (row3 1 9 54), (row3 1 9 55), (row3 1 9 56), (row3 1 9 57), (row3 1 9 58), (row3 1 9 59), (row3 1 9 60), (row3 1 9 61), (row3 1 9 62), (row3 1 9 63), (row3 1 10 11), (row3 1 10 12), (row3 1 10 13), (row3 1 10 14)]

def b001_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 139 139 462), (row3 45 436 389), (row3 23 461 457), (row3 18 19 19), (row3 456 458 456), (row3 36 31 35), (row3 358 462 358), (row3 163 163 462), (row3 43 436 383), (row3 452 25 32), (row3 417 423 422), (row3 127 137 126), (row3 301 301 278), (row3 399 82 156)]

theorem b001_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_12_rows b001_12_labels 2244357370104070685210221126058100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_12_rows b001_12_labels]
    decide +kernel

def b001_13_rows : List Row := [(row3 1 10 15), (row3 1 10 16), (row3 1 10 17), (row3 1 10 18), (row3 1 10 19), (row3 1 10 20), (row3 1 10 21), (row3 1 10 22), (row3 1 10 23), (row3 1 10 24), (row3 1 10 25), (row3 1 10 26), (row3 1 10 27), (row3 1 10 28), (row3 1 10 29), (row3 1 10 30)]

def b001_13_labels : List Row := [(row3 40 438 413), (row3 60 432 411), (row3 61 48 50), (row3 418 424 422), (row3 100 113 100), (row3 309 309 306), (row3 462 232 232), (row3 293 293 462), (row3 398 81 134), (row3 356 89 158), (row3 354 376 366), (row3 127 137 126), (row3 309 309 306), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462)]

theorem b001_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_13_rows b001_13_labels 6066883245908828948180077792650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_13_rows b001_13_labels]
    decide +kernel

def b001_14_rows : List Row := [(row3 1 10 31), (row3 1 10 32), (row3 1 10 33), (row3 1 10 34), (row3 1 10 35), (row3 1 10 36), (row3 1 10 37), (row3 1 10 38), (row3 1 10 39), (row3 1 10 40), (row3 1 10 41), (row3 1 10 42), (row3 1 10 43), (row3 1 10 44), (row3 1 10 45), (row3 1 10 46)]

def b001_14_labels : List Row := [(row3 284 284 462), (row3 269 269 462), (row3 193 232 189), (row3 279 279 278), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 356 91 159), (row3 352 373 365), (row3 163 235 162), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b001_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_14_rows b001_14_labels 18031017778764466462345784550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_14_rows b001_14_labels]
    decide +kernel

def b001_15_rows : List Row := [(row3 1 10 47), (row3 1 10 48), (row3 1 10 49), (row3 1 10 50), (row3 1 10 51), (row3 1 10 52), (row3 1 10 53), (row3 1 10 54), (row3 1 10 55), (row3 1 10 56), (row3 1 10 57), (row3 1 10 58), (row3 1 10 59), (row3 1 10 60), (row3 1 10 61), (row3 1 10 62)]

def b001_15_labels : List Row := [(row3 284 284 462), (row3 59 431 410), (row3 62 49 52), (row3 395 415 407), (row3 139 232 138), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 398 83 135), (row3 452 25 32), (row3 456 456 458), (row3 38 33 33), (row3 396 416 408), (row3 163 228 160), (row3 284 284 462), (row3 399 83 157)]

theorem b001_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b001_15_rows b001_15_labels 34361747212378540274634003330720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b001_15_rows b001_15_labels]
    decide +kernel

theorem checked001 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_001 QuarticIntegerComputationalData.ids64_001 24292890456342070177884611492636460 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b001_00_rows ++ b001_01_rows) ++ (b001_02_rows ++ b001_03_rows)) ++ ((b001_04_rows ++ b001_05_rows) ++ (b001_06_rows ++ b001_07_rows))) ++ (((b001_08_rows ++ b001_09_rows) ++ (b001_10_rows ++ b001_11_rows)) ++ ((b001_12_rows ++ b001_13_rows) ++ (b001_14_rows ++ b001_15_rows))))
    ((((b001_00_labels ++ b001_01_labels) ++ (b001_02_labels ++ b001_03_labels)) ++ ((b001_04_labels ++ b001_05_labels) ++ (b001_06_labels ++ b001_07_labels))) ++ (((b001_08_labels ++ b001_09_labels) ++ (b001_10_labels ++ b001_11_labels)) ++ ((b001_12_labels ++ b001_13_labels) ++ (b001_14_labels ++ b001_15_labels)))) 24292890456342070177884611492636460
  exact ((((b001_00_checked.append (c := 7527983315372214495136195651980) b001_01_checked (by decide +kernel)).append (c := 3130930487159343064166810510471220) (b001_02_checked.append (c := 3123402503843970849671674314819240) b001_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17618600373440454139451130510349440) ((b001_04_checked.append (c := 12364673395585694522006995532790540) b001_05_checked (by decide +kernel)).append (c := 14487669886281111075284319999878220) (b001_06_checked.append (c := 2122996490695416553277324467087680) b001_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 24292890456342070177884611492636460) (((b001_08_checked.append (c := 4369925133073841050009814543045700) b001_09_checked (by decide +kernel)).append (c := 4389486051321479219533983429321000) (b001_10_checked.append (c := 19560918247638169524168886275300) b001_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 6674290082901616038433480982287020) ((b001_12_checked.append (c := 2250424253349979514158401203850750) b001_13_checked (by decide +kernel)).append (c := 2284804031580136818899497552966020) (b001_14_checked.append (c := 34379778230157304741096349115270) b001_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b002_00_rows : List Row := [(row3 1 10 63), (row3 1 11 12), (row3 1 11 13), (row3 1 11 14), (row3 1 11 15), (row3 1 11 16), (row3 1 11 17), (row3 1 11 18), (row3 1 11 19), (row3 1 11 20), (row3 1 11 21), (row3 1 11 22), (row3 1 11 23), (row3 1 11 24), (row3 1 11 25), (row3 1 11 26)]

def b002_00_labels : List Row := [(row3 39 437 412), (row3 303 462 303), (row3 235 462 235), (row3 116 11 213), (row3 399 82 156), (row3 369 85 121), (row3 362 388 392), (row3 129 102 103), (row3 307 462 307), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 117 11 214), (row3 171 10 254), (row3 180 154 154), (row3 286 462 286)]

theorem b002_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_00_rows b002_00_labels 437125941540341140343678880210 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_00_rows b002_00_labels]
    decide +kernel

def b002_01_rows : List Row := [(row3 1 11 27), (row3 1 11 28), (row3 1 11 29), (row3 1 11 30), (row3 1 11 31), (row3 1 11 32), (row3 1 11 33), (row3 1 11 34), (row3 1 11 35), (row3 1 11 36), (row3 1 11 37), (row3 1 11 38), (row3 1 11 39), (row3 1 11 40), (row3 1 11 41), (row3 1 11 42)]

def b002_01_labels : List Row := [(row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 10 254), (row3 180 154 154), (row3 284 462 284)]

theorem b002_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_01_rows b002_01_labels 1418511931451405246120427000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_01_rows b002_01_labels]
    decide +kernel

def b002_02_rows : List Row := [(row3 1 11 43), (row3 1 11 44), (row3 1 11 45), (row3 1 11 46), (row3 1 11 47), (row3 1 11 48), (row3 1 11 49), (row3 1 11 50), (row3 1 11 51), (row3 1 11 52), (row3 1 11 53), (row3 1 11 54), (row3 1 11 55), (row3 1 11 56), (row3 1 11 57), (row3 1 11 58)]

def b002_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 369 86 122), (row3 360 387 390), (row3 131 105 105), (row3 294 462 294), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 117 11 214), (row3 43 436 383), (row3 36 35 31), (row3 396 408 416)]

theorem b002_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_02_rows b002_02_labels 1248444261102729922349712116850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_02_rows b002_02_labels]
    decide +kernel

def b002_03_rows : List Row := [(row3 1 11 59), (row3 1 11 60), (row3 1 11 61), (row3 1 11 62), (row3 1 11 63), (row3 1 12 13), (row3 1 12 14), (row3 1 12 15), (row3 1 12 16), (row3 1 12 17), (row3 1 12 18), (row3 1 12 19), (row3 1 12 20), (row3 1 12 21), (row3 1 12 22), (row3 1 12 23)]

def b002_03_labels : List Row := [(row3 130 104 104), (row3 286 462 286), (row3 462 462 462), (row3 115 11 212), (row3 399 83 157), (row3 462 462 462), (row3 235 462 235), (row3 301 301 278), (row3 284 284 462), (row3 193 191 235), (row3 287 287 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_03_rows b002_03_labels 33692799762614680767213841350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_03_rows b002_03_labels]
    decide +kernel

def b002_04_rows : List Row := [(row3 1 12 24), (row3 1 12 25), (row3 1 12 26), (row3 1 12 27), (row3 1 12 28), (row3 1 12 29), (row3 1 12 30), (row3 1 12 31), (row3 1 12 32), (row3 1 12 33), (row3 1 12 34), (row3 1 12 35), (row3 1 12 36), (row3 1 12 37), (row3 1 12 38), (row3 1 12 39)]

def b002_04_labels : List Row := [(row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_04_rows b002_04_labels 19713966259789303503675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_04_rows b002_04_labels]
    decide +kernel

def b002_05_rows : List Row := [(row3 1 12 40), (row3 1 12 41), (row3 1 12 42), (row3 1 12 43), (row3 1 12 44), (row3 1 12 45), (row3 1 12 46), (row3 1 12 47), (row3 1 12 48), (row3 1 12 49), (row3 1 12 50), (row3 1 12 51), (row3 1 12 52), (row3 1 12 53), (row3 1 12 54), (row3 1 12 55)]

def b002_05_labels : List Row := [(row3 462 462 462), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 193 193 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_05_rows b002_05_labels 487698161728882193566449000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_05_rows b002_05_labels]
    decide +kernel

def b002_06_rows : List Row := [(row3 1 12 56), (row3 1 12 57), (row3 1 12 58), (row3 1 12 59), (row3 1 12 60), (row3 1 12 61), (row3 1 12 62), (row3 1 12 63), (row3 1 13 14), (row3 1 13 15), (row3 1 13 16), (row3 1 13 17), (row3 1 13 18), (row3 1 13 19), (row3 1 13 20), (row3 1 13 21)]

def b002_06_labels : List Row := [(row3 163 163 462), (row3 358 358 462), (row3 163 160 228), (row3 286 286 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 303 462 303), (row3 127 137 126), (row3 193 235 191), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_06_rows b002_06_labels 33209839522433179192006501080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_06_rows b002_06_labels]
    decide +kernel

def b002_07_rows : List Row := [(row3 1 13 22), (row3 1 13 23), (row3 1 13 24), (row3 1 13 25), (row3 1 13 26), (row3 1 13 27), (row3 1 13 28), (row3 1 13 29), (row3 1 13 30), (row3 1 13 31), (row3 1 13 32), (row3 1 13 33), (row3 1 13 34), (row3 1 13 35), (row3 1 13 36), (row3 1 13 37)]

def b002_07_labels : List Row := [(row3 462 462 462), (row3 287 462 287), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_07_rows b002_07_labels 119077974681189758822962500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_07_rows b002_07_labels]
    decide +kernel

def b002_08_rows : List Row := [(row3 1 13 38), (row3 1 13 39), (row3 1 13 40), (row3 1 13 41), (row3 1 13 42), (row3 1 13 43), (row3 1 13 44), (row3 1 13 45), (row3 1 13 46), (row3 1 13 47), (row3 1 13 48), (row3 1 13 49), (row3 1 13 50), (row3 1 13 51), (row3 1 13 52), (row3 1 13 53)]

def b002_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 263 462 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_08_rows b002_08_labels 428217577650358046412324000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_08_rows b002_08_labels]
    decide +kernel

def b002_09_rows : List Row := [(row3 1 13 54), (row3 1 13 55), (row3 1 13 56), (row3 1 13 57), (row3 1 13 58), (row3 1 13 59), (row3 1 13 60), (row3 1 13 61), (row3 1 13 62), (row3 1 13 63), (row3 1 14 15), (row3 1 14 16), (row3 1 14 17), (row3 1 14 18), (row3 1 14 19), (row3 1 14 20)]

def b002_09_labels : List Row := [(row3 462 462 462), (row3 284 462 284), (row3 358 462 358), (row3 163 462 163), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 163 228 160), (row3 417 423 422), (row3 362 392 388), (row3 369 121 85), (row3 117 214 11), (row3 462 462 462), (row3 246 246 462)]

theorem b002_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_09_rows b002_09_labels 4072634037139435357048431118800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_09_rows b002_09_labels]
    decide +kernel

def b002_10_rows : List Row := [(row3 1 14 21), (row3 1 14 22), (row3 1 14 23), (row3 1 14 24), (row3 1 14 25), (row3 1 14 26), (row3 1 14 27), (row3 1 14 28), (row3 1 14 29), (row3 1 14 30), (row3 1 14 31), (row3 1 14 32), (row3 1 14 33), (row3 1 14 34), (row3 1 14 35), (row3 1 14 36)]

def b002_10_labels : List Row := [(row3 232 232 462), (row3 307 307 462), (row3 129 103 102), (row3 180 154 154), (row3 171 254 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 286 286 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_10_rows b002_10_labels 32099212523668640052173449500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_10_rows b002_10_labels]
    decide +kernel

def b002_11_rows : List Row := [(row3 1 14 37), (row3 1 14 38), (row3 1 14 39), (row3 1 14 40), (row3 1 14 41), (row3 1 14 42), (row3 1 14 43), (row3 1 14 44), (row3 1 14 45), (row3 1 14 46), (row3 1 14 47), (row3 1 14 48), (row3 1 14 49), (row3 1 14 50), (row3 1 14 51), (row3 1 14 52)]

def b002_11_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 180 154 154), (row3 171 254 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 360 390 387), (row3 369 122 86), (row3 117 214 11), (row3 462 462 462), (row3 462 462 462)]

theorem b002_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_11_rows b002_11_labels 27393198186606328149451691400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_11_rows b002_11_labels]
    decide +kernel

def b002_12_rows : List Row := [(row3 1 14 53), (row3 1 14 54), (row3 1 14 55), (row3 1 14 56), (row3 1 14 57), (row3 1 14 58), (row3 1 14 59), (row3 1 14 60), (row3 1 14 61), (row3 1 14 62), (row3 1 14 63), (row3 1 15 16), (row3 1 15 17), (row3 1 15 18), (row3 1 15 19), (row3 1 15 20)]

def b002_12_labels : List Row := [(row3 462 462 462), (row3 294 294 462), (row3 131 105 105), (row3 36 31 35), (row3 43 383 436), (row3 399 157 83), (row3 115 212 11), (row3 462 462 462), (row3 286 286 462), (row3 130 104 104), (row3 396 416 408), (row3 61 50 48), (row3 60 411 432), (row3 398 134 81), (row3 293 462 293), (row3 462 232 232)]

theorem b002_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_12_rows b002_12_labels 2849871529326745550123392703400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_12_rows b002_12_labels]
    decide +kernel

def b002_13_rows : List Row := [(row3 1 15 21), (row3 1 15 22), (row3 1 15 23), (row3 1 15 24), (row3 1 15 25), (row3 1 15 26), (row3 1 15 27), (row3 1 15 28), (row3 1 15 29), (row3 1 15 30), (row3 1 15 31), (row3 1 15 32), (row3 1 15 33), (row3 1 15 34), (row3 1 15 35), (row3 1 15 36)]

def b002_13_labels : List Row := [(row3 309 306 309), (row3 100 100 113), (row3 418 422 424), (row3 354 366 376), (row3 356 158 89), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 309 306 309), (row3 127 126 137), (row3 193 189 232), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b002_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_13_rows b002_13_labels 4087820830968364519198651894770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_13_rows b002_13_labels]
    decide +kernel

def b002_14_rows : List Row := [(row3 1 15 37), (row3 1 15 38), (row3 1 15 39), (row3 1 15 40), (row3 1 15 41), (row3 1 15 42), (row3 1 15 43), (row3 1 15 44), (row3 1 15 45), (row3 1 15 46), (row3 1 15 47), (row3 1 15 48), (row3 1 15 49), (row3 1 15 50), (row3 1 15 51), (row3 1 15 52)]

def b002_14_labels : List Row := [(row3 462 462 462), (row3 462 232 232), (row3 279 278 279), (row3 352 365 373), (row3 356 159 91), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 162 235), (row3 62 52 49), (row3 59 410 431), (row3 398 135 83), (row3 293 462 293), (row3 462 462 462)]

theorem b002_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_14_rows b002_14_labels 393921076872363199438754033850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_14_rows b002_14_labels]
    decide +kernel

def b002_15_rows : List Row := [(row3 1 15 53), (row3 1 15 54), (row3 1 15 55), (row3 1 15 56), (row3 1 15 57), (row3 1 15 58), (row3 1 15 59), (row3 1 15 60), (row3 1 15 61), (row3 1 15 62), (row3 1 15 63), (row3 1 16 17), (row3 1 16 18), (row3 1 16 19), (row3 1 16 20), (row3 1 16 21)]

def b002_15_labels : List Row := [(row3 462 462 462), (row3 139 138 232), (row3 395 407 415), (row3 456 458 456), (row3 452 32 25), (row3 39 412 437), (row3 399 157 83), (row3 284 462 284), (row3 163 160 228), (row3 396 408 416), (row3 38 33 33), (row3 63 419 433), (row3 367 108 84), (row3 302 265 302), (row3 462 237 237), (row3 266 265 266)]

theorem b002_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b002_15_rows b002_15_labels 42424023856904422215035207235600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b002_15_rows b002_15_labels]
    decide +kernel

theorem checked002 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_002 QuarticIntegerComputationalData.ids64_002 55642709803461496356247099304310 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b002_00_rows ++ b002_01_rows) ++ (b002_02_rows ++ b002_03_rows)) ++ ((b002_04_rows ++ b002_05_rows) ++ (b002_06_rows ++ b002_07_rows))) ++ (((b002_08_rows ++ b002_09_rows) ++ (b002_10_rows ++ b002_11_rows)) ++ ((b002_12_rows ++ b002_13_rows) ++ (b002_14_rows ++ b002_15_rows))))
    ((((b002_00_labels ++ b002_01_labels) ++ (b002_02_labels ++ b002_03_labels)) ++ ((b002_04_labels ++ b002_05_labels) ++ (b002_06_labels ++ b002_07_labels))) ++ (((b002_08_labels ++ b002_09_labels) ++ (b002_10_labels ++ b002_11_labels)) ++ ((b002_12_labels ++ b002_13_labels) ++ (b002_14_labels ++ b002_15_labels)))) 55642709803461496356247099304310
  exact ((((b002_00_checked.append (c := 438544453471792545589799307210) b002_01_checked (by decide +kernel)).append (c := 1720681514337137148706725265410) (b002_02_checked.append (c := 1282137060865344603116925958200) b002_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1754517843962240189154624852990) ((b002_04_checked.append (c := 507412127988671497070124000) b002_05_checked (by decide +kernel)).append (c := 33836329625103040447899587580) (b002_06_checked.append (c := 33328917497114368950829463580) b002_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 55642709803461496356247099304310) (((b002_08_checked.append (c := 4073062254717085715094843442800) b002_09_checked (by decide +kernel)).append (c := 4132554665427360683296468583700) (b002_10_checked.append (c := 59492410710274968201625140900) b002_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 53888191959499256167092474451320) ((b002_12_checked.append (c := 6937692360295110069322044598170) b002_13_checked (by decide +kernel)).append (c := 49755637294071895483796005867620) (b002_14_checked.append (c := 42817944933776785414473961269450) b002_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b003_00_rows : List Row := [(row3 1 16 22), (row3 1 16 23), (row3 1 16 24), (row3 1 16 25), (row3 1 16 26), (row3 1 16 27), (row3 1 16 28), (row3 1 16 29), (row3 1 16 30), (row3 1 16 31), (row3 1 16 32), (row3 1 16 33), (row3 1 16 34), (row3 1 16 35), (row3 1 16 36), (row3 1 16 37)]

def b003_00_labels : List Row := [(row3 140 140 178), (row3 394 409 414), (row3 384 397 400), (row3 331 123 92), (row3 305 289 305), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 289 291), (row3 132 133 137), (row3 174 174 178), (row3 299 289 299), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_00_rows b003_00_labels 3351600625743653117707571759460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_00_rows b003_00_labels]
    decide +kernel

def b003_01_rows : List Row := [(row3 1 16 38), (row3 1 16 39), (row3 1 16 40), (row3 1 16 41), (row3 1 16 42), (row3 1 16 43), (row3 1 16 44), (row3 1 16 45), (row3 1 16 46), (row3 1 16 47), (row3 1 16 48), (row3 1 16 49), (row3 1 16 50), (row3 1 16 51), (row3 1 16 52), (row3 1 16 53)]

def b003_01_labels : List Row := [(row3 462 234 234), (row3 291 289 291), (row3 329 340 344), (row3 332 155 93), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 191 235), (row3 79 67 67), (row3 78 401 427), (row3 368 114 86), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462)]

theorem b003_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_01_rows b003_01_labels 182970360725761000915089087690 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_01_rows b003_01_labels]
    decide +kernel

def b003_02_rows : List Row := [(row3 1 16 54), (row3 1 16 55), (row3 1 16 56), (row3 1 16 57), (row3 1 16 58), (row3 1 16 59), (row3 1 16 60), (row3 1 16 61), (row3 1 16 62), (row3 1 16 63), (row3 1 17 18), (row3 1 17 19), (row3 1 17 20), (row3 1 17 21), (row3 1 17 22), (row3 1 17 23)]

def b003_02_labels : List Row := [(row3 180 180 462), (row3 361 387 391), (row3 448 454 449), (row3 443 34 27), (row3 59 410 431), (row3 369 122 86), (row3 284 462 284), (row3 193 193 462), (row3 360 387 390), (row3 62 49 52), (row3 394 414 409), (row3 140 178 140), (row3 266 266 265), (row3 462 237 237), (row3 302 302 265), (row3 367 84 108)]

theorem b003_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_02_rows b003_02_labels 14661675737032948356589067194620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_02_rows b003_02_labels]
    decide +kernel

def b003_03_rows : List Row := [(row3 1 17 24), (row3 1 17 25), (row3 1 17 26), (row3 1 17 27), (row3 1 17 28), (row3 1 17 29), (row3 1 17 30), (row3 1 17 31), (row3 1 17 32), (row3 1 17 33), (row3 1 17 34), (row3 1 17 35), (row3 1 17 36), (row3 1 17 37), (row3 1 17 38), (row3 1 17 39)]

def b003_03_labels : List Row := [(row3 331 92 123), (row3 384 400 397), (row3 132 137 133), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 305 305 289), (row3 299 299 289), (row3 174 178 174), (row3 291 291 289), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234)]

theorem b003_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_03_rows b003_03_labels 1388511479958756098760300451680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_03_rows b003_03_labels]
    decide +kernel

def b003_04_rows : List Row := [(row3 1 17 40), (row3 1 17 41), (row3 1 17 42), (row3 1 17 43), (row3 1 17 44), (row3 1 17 45), (row3 1 17 46), (row3 1 17 47), (row3 1 17 48), (row3 1 17 49), (row3 1 17 50), (row3 1 17 51), (row3 1 17 52), (row3 1 17 53), (row3 1 17 54), (row3 1 17 55)]

def b003_04_labels : List Row := [(row3 332 93 155), (row3 329 344 340), (row3 193 235 191), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 78 427 401), (row3 79 67 67), (row3 361 391 387), (row3 180 462 180), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 368 86 114)]

theorem b003_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_04_rows b003_04_labels 197821738337751704199071533140 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_04_rows b003_04_labels]
    decide +kernel

def b003_05_rows : List Row := [(row3 1 17 56), (row3 1 17 57), (row3 1 17 58), (row3 1 17 59), (row3 1 17 60), (row3 1 17 61), (row3 1 17 62), (row3 1 17 63), (row3 1 18 19), (row3 1 18 20), (row3 1 18 21), (row3 1 18 22), (row3 1 18 23), (row3 1 18 24), (row3 1 18 25), (row3 1 18 26)]

def b003_05_labels : List Row := [(row3 443 27 34), (row3 448 449 454), (row3 62 52 49), (row3 360 390 387), (row3 193 462 193), (row3 284 284 462), (row3 369 86 122), (row3 59 431 410), (row3 316 462 316), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 119 11 216), (row3 173 10 260), (row3 177 152 150), (row3 307 462 307)]

theorem b003_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_05_rows b003_05_labels 12673894664574393782276753520000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_05_rows b003_05_labels]
    decide +kernel

def b003_06_rows : List Row := [(row3 1 18 27), (row3 1 18 28), (row3 1 18 29), (row3 1 18 30), (row3 1 18 31), (row3 1 18 32), (row3 1 18 33), (row3 1 18 34), (row3 1 18 35), (row3 1 18 36), (row3 1 18 37), (row3 1 18 38), (row3 1 18 39), (row3 1 18 40), (row3 1 18 41), (row3 1 18 42)]

def b003_06_labels : List Row := [(row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 272 462 272), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 172 10 258), (row3 180 154 154), (row3 285 462 285)]

theorem b003_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_06_rows b003_06_labels 1529504336844929565178740000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_06_rows b003_06_labels]
    decide +kernel

def b003_07_rows : List Row := [(row3 1 18 43), (row3 1 18 44), (row3 1 18 45), (row3 1 18 46), (row3 1 18 47), (row3 1 18 48), (row3 1 18 49), (row3 1 18 50), (row3 1 18 51), (row3 1 18 52), (row3 1 18 53), (row3 1 18 54), (row3 1 18 55), (row3 1 18 56), (row3 1 18 57), (row3 1 18 58)]

def b003_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 368 86 114), (row3 361 387 391), (row3 131 105 105), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 118 11 215), (row3 45 436 389), (row3 35 36 31), (row3 395 407 415)]

theorem b003_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_07_rows b003_07_labels 1237456388514965068582156717650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_07_rows b003_07_labels]
    decide +kernel

def b003_08_rows : List Row := [(row3 1 18 59), (row3 1 18 60), (row3 1 18 61), (row3 1 18 62), (row3 1 18 63), (row3 1 19 20), (row3 1 19 21), (row3 1 19 22), (row3 1 19 23), (row3 1 19 24), (row3 1 19 25), (row3 1 19 26), (row3 1 19 27), (row3 1 19 28), (row3 1 19 29), (row3 1 19 30)]

def b003_08_labels : List Row := [(row3 131 105 105), (row3 284 462 284), (row3 462 462 462), (row3 117 11 214), (row3 398 83 135), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 271 271 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_08_rows b003_08_labels 24285498273041051116914626250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_08_rows b003_08_labels]
    decide +kernel

def b003_09_rows : List Row := [(row3 1 19 31), (row3 1 19 32), (row3 1 19 33), (row3 1 19 34), (row3 1 19 35), (row3 1 19 36), (row3 1 19 37), (row3 1 19 38), (row3 1 19 39), (row3 1 19 40), (row3 1 19 41), (row3 1 19 42), (row3 1 19 43), (row3 1 19 44), (row3 1 19 45), (row3 1 19 46)]

def b003_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_09_rows b003_09_labels 29570949389683955255512500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_09_rows b003_09_labels]
    decide +kernel

def b003_10_rows : List Row := [(row3 1 19 47), (row3 1 19 48), (row3 1 19 49), (row3 1 19 50), (row3 1 19 51), (row3 1 19 52), (row3 1 19 53), (row3 1 19 54), (row3 1 19 55), (row3 1 19 56), (row3 1 19 57), (row3 1 19 58), (row3 1 19 59), (row3 1 19 60), (row3 1 19 61), (row3 1 19 62)]

def b003_10_labels : List Row := [(row3 462 462 462), (row3 293 293 462), (row3 180 180 462), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 139 139 462), (row3 377 377 462), (row3 139 138 232), (row3 294 294 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_10_rows b003_10_labels 23502941759293581115256958000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_10_rows b003_10_labels]
    decide +kernel

def b003_11_rows : List Row := [(row3 1 19 63), (row3 1 20 21), (row3 1 20 22), (row3 1 20 23), (row3 1 20 24), (row3 1 20 25), (row3 1 20 26), (row3 1 20 27), (row3 1 20 28), (row3 1 20 29), (row3 1 20 30), (row3 1 20 31), (row3 1 20 32), (row3 1 20 33), (row3 1 20 34), (row3 1 20 35)]

def b003_11_labels : List Row := [(row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_11_rows b003_11_labels 93810292847365445590635000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_11_rows b003_11_labels]
    decide +kernel

def b003_12_rows : List Row := [(row3 1 20 36), (row3 1 20 37), (row3 1 20 38), (row3 1 20 39), (row3 1 20 40), (row3 1 20 41), (row3 1 20 42), (row3 1 20 43), (row3 1 20 44), (row3 1 20 45), (row3 1 20 46), (row3 1 20 47), (row3 1 20 48), (row3 1 20 49), (row3 1 20 50), (row3 1 20 51)]

def b003_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_12_rows b003_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_12_rows b003_12_labels]
    decide +kernel

def b003_13_rows : List Row := [(row3 1 20 52), (row3 1 20 53), (row3 1 20 54), (row3 1 20 55), (row3 1 20 56), (row3 1 20 57), (row3 1 20 58), (row3 1 20 59), (row3 1 20 60), (row3 1 20 61), (row3 1 20 62), (row3 1 20 63), (row3 1 21 22), (row3 1 21 23), (row3 1 21 24), (row3 1 21 25)]

def b003_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462)]

theorem b003_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_13_rows b003_13_labels 20600849112447846028878000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_13_rows b003_13_labels]
    decide +kernel

def b003_14_rows : List Row := [(row3 1 21 26), (row3 1 21 27), (row3 1 21 28), (row3 1 21 29), (row3 1 21 30), (row3 1 21 31), (row3 1 21 32), (row3 1 21 33), (row3 1 21 34), (row3 1 21 35), (row3 1 21 36), (row3 1 21 37), (row3 1 21 38), (row3 1 21 39), (row3 1 21 40), (row3 1 21 41)]

def b003_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_14_rows b003_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_14_rows b003_14_labels]
    decide +kernel

def b003_15_rows : List Row := [(row3 1 21 42), (row3 1 21 43), (row3 1 21 44), (row3 1 21 45), (row3 1 21 46), (row3 1 21 47), (row3 1 21 48), (row3 1 21 49), (row3 1 21 50), (row3 1 21 51), (row3 1 21 52), (row3 1 21 53), (row3 1 21 54), (row3 1 21 55), (row3 1 21 56), (row3 1 21 57)]

def b003_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b003_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b003_15_rows b003_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b003_15_rows b003_15_labels]
    decide +kernel

theorem checked003 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_003 QuarticIntegerComputationalData.ids64_003 33743392921348758188074235613990 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b003_00_rows ++ b003_01_rows) ++ (b003_02_rows ++ b003_03_rows)) ++ ((b003_04_rows ++ b003_05_rows) ++ (b003_06_rows ++ b003_07_rows))) ++ (((b003_08_rows ++ b003_09_rows) ++ (b003_10_rows ++ b003_11_rows)) ++ ((b003_12_rows ++ b003_13_rows) ++ (b003_14_rows ++ b003_15_rows))))
    ((((b003_00_labels ++ b003_01_labels) ++ (b003_02_labels ++ b003_03_labels)) ++ ((b003_04_labels ++ b003_05_labels) ++ (b003_06_labels ++ b003_07_labels))) ++ (((b003_08_labels ++ b003_09_labels) ++ (b003_10_labels ++ b003_11_labels)) ++ ((b003_12_labels ++ b003_13_labels) ++ (b003_14_labels ++ b003_15_labels)))) 33743392921348758188074235613990
  exact ((((b003_00_checked.append (c := 3534570986469414118622660847150) b003_01_checked (by decide +kernel)).append (c := 19584758203461118573972028493450) (b003_02_checked.append (c := 16050187216991704455349367646300) b003_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 33695460499225074058595189004240) ((b003_04_checked.append (c := 12871716402912145486475825053140) b003_05_checked (by decide +kernel)).append (c := 14110702295763955484623160510790) (b003_06_checked.append (c := 1238985892851809998147335457650) b003_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 33743392921348758188074235613990) (((b003_08_checked.append (c := 24315069222430735072170138750) b003_09_checked (by decide +kernel)).append (c := 47911821274571681633017731750) (b003_10_checked.append (c := 23596752052140946560847593000) b003_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 47932422123684129479046609750) ((b003_12_checked.append (c := 20600849112447846028878000) b003_13_checked (by decide +kernel)).append (c := 20600849112447846028878000) (b003_14_checked.append (c := 0) b003_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b004_00_rows : List Row := [(row3 1 21 58), (row3 1 21 59), (row3 1 21 60), (row3 1 21 61), (row3 1 21 62), (row3 1 21 63), (row3 1 22 23), (row3 1 22 24), (row3 1 22 25), (row3 1 22 26), (row3 1 22 27), (row3 1 22 28), (row3 1 22 29), (row3 1 22 30), (row3 1 22 31), (row3 1 22 32)]

def b004_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 316 462 316), (row3 271 462 271), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_00_rows b004_00_labels 13227057679456160645607112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_00_rows b004_00_labels]
    decide +kernel

def b004_01_rows : List Row := [(row3 1 22 33), (row3 1 22 34), (row3 1 22 35), (row3 1 22 36), (row3 1 22 37), (row3 1 22 38), (row3 1 22 39), (row3 1 22 40), (row3 1 22 41), (row3 1 22 42), (row3 1 22 43), (row3 1 22 44), (row3 1 22 45), (row3 1 22 46), (row3 1 22 47), (row3 1 22 48)]

def b004_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 462 180)]

theorem b004_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_01_rows b004_01_labels 550971772973066558035768500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_01_rows b004_01_labels]
    decide +kernel

def b004_02_rows : List Row := [(row3 1 22 49), (row3 1 22 50), (row3 1 22 51), (row3 1 22 52), (row3 1 22 53), (row3 1 22 54), (row3 1 22 55), (row3 1 22 56), (row3 1 22 57), (row3 1 22 58), (row3 1 22 59), (row3 1 22 60), (row3 1 22 61), (row3 1 22 62), (row3 1 22 63), (row3 1 23 24)]

def b004_02_labels : List Row := [(row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 377 462 377), (row3 139 462 139), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 294 462 294), (row3 139 232 138), (row3 177 150 152)]

theorem b004_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_02_rows b004_02_labels 29655609567622310651034451500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_02_rows b004_02_labels]
    decide +kernel

def b004_03_rows : List Row := [(row3 1 23 25), (row3 1 23 26), (row3 1 23 27), (row3 1 23 28), (row3 1 23 29), (row3 1 23 30), (row3 1 23 31), (row3 1 23 32), (row3 1 23 33), (row3 1 23 34), (row3 1 23 35), (row3 1 23 36), (row3 1 23 37), (row3 1 23 38), (row3 1 23 39), (row3 1 23 40)]

def b004_03_labels : List Row := [(row3 173 260 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 228 228 462), (row3 307 307 462), (row3 272 272 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 180 154 154)]

theorem b004_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_03_rows b004_03_labels 12770190986113558673550990000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_03_rows b004_03_labels]
    decide +kernel

def b004_04_rows : List Row := [(row3 1 23 41), (row3 1 23 42), (row3 1 23 43), (row3 1 23 44), (row3 1 23 45), (row3 1 23 46), (row3 1 23 47), (row3 1 23 48), (row3 1 23 49), (row3 1 23 50), (row3 1 23 51), (row3 1 23 52), (row3 1 23 53), (row3 1 23 54), (row3 1 23 55), (row3 1 23 56)]

def b004_04_labels : List Row := [(row3 172 258 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 285 285 462), (row3 361 391 387), (row3 368 114 86), (row3 118 215 11), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 131 105 105), (row3 35 31 36)]

theorem b004_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_04_rows b004_04_labels 827047889533290310819406591400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_04_rows b004_04_labels]
    decide +kernel

def b004_05_rows : List Row := [(row3 1 23 57), (row3 1 23 58), (row3 1 23 59), (row3 1 23 60), (row3 1 23 61), (row3 1 23 62), (row3 1 23 63), (row3 1 24 25), (row3 1 24 26), (row3 1 24 27), (row3 1 24 28), (row3 1 24 29), (row3 1 24 30), (row3 1 24 31), (row3 1 24 32), (row3 1 24 33)]

def b004_05_labels : List Row := [(row3 45 389 436), (row3 398 135 83), (row3 117 214 11), (row3 462 462 462), (row3 284 284 462), (row3 131 105 105), (row3 395 415 407), (row3 186 269 9), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 274 274 462), (row3 269 269 462), (row3 236 236 462)]

theorem b004_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_05_rows b004_05_labels 464891912301051045509970286500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_05_rows b004_05_labels]
    decide +kernel

def b004_06_rows : List Row := [(row3 1 24 34), (row3 1 24 35), (row3 1 24 36), (row3 1 24 37), (row3 1 24 38), (row3 1 24 39), (row3 1 24 40), (row3 1 24 41), (row3 1 24 42), (row3 1 24 43), (row3 1 24 44), (row3 1 24 45), (row3 1 24 46), (row3 1 24 47), (row3 1 24 48), (row3 1 24 49)]

def b004_06_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 207 200 200), (row3 204 259 8), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 264 462), (row3 329 344 340), (row3 332 155 93)]

theorem b004_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_06_rows b004_06_labels 10509029798127878203636423950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_06_rows b004_06_labels]
    decide +kernel

def b004_07_rows : List Row := [(row3 1 24 50), (row3 1 24 51), (row3 1 24 52), (row3 1 24 53), (row3 1 24 54), (row3 1 24 55), (row3 1 24 56), (row3 1 24 57), (row3 1 24 58), (row3 1 24 59), (row3 1 24 60), (row3 1 24 61), (row3 1 24 62), (row3 1 24 63), (row3 1 25 26), (row3 1 25 27)]

def b004_07_labels : List Row := [(row3 172 258 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462), (row3 180 154 154), (row3 64 55 66), (row3 73 359 429), (row3 356 159 91), (row3 171 254 10), (row3 462 462 462), (row3 263 263 462), (row3 180 154 154), (row3 352 373 365), (row3 274 462 274), (row3 238 462 238)]

theorem b004_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_07_rows b004_07_labels 391825887858472861212576520050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_07_rows b004_07_labels]
    decide +kernel

def b004_08_rows : List Row := [(row3 1 25 28), (row3 1 25 29), (row3 1 25 30), (row3 1 25 31), (row3 1 25 32), (row3 1 25 33), (row3 1 25 34), (row3 1 25 35), (row3 1 25 36), (row3 1 25 37), (row3 1 25 38), (row3 1 25 39), (row3 1 25 40), (row3 1 25 41), (row3 1 25 42), (row3 1 25 43)]

def b004_08_labels : List Row := [(row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 238 462 238), (row3 236 462 236), (row3 269 462 269), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 204 8 259), (row3 207 200 200), (row3 264 462 264), (row3 462 462 462)]

theorem b004_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_08_rows b004_08_labels 3761836013094913529999463000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_08_rows b004_08_labels]
    decide +kernel

def b004_09_rows : List Row := [(row3 1 25 44), (row3 1 25 45), (row3 1 25 46), (row3 1 25 47), (row3 1 25 48), (row3 1 25 49), (row3 1 25 50), (row3 1 25 51), (row3 1 25 52), (row3 1 25 53), (row3 1 25 54), (row3 1 25 55), (row3 1 25 56), (row3 1 25 57), (row3 1 25 58), (row3 1 25 59)]

def b004_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 332 93 155), (row3 329 340 344), (row3 180 154 154), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 172 10 258), (row3 73 429 359), (row3 64 66 55), (row3 352 365 373), (row3 180 154 154)]

theorem b004_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_09_rows b004_09_labels 390917015731995770463525819000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_09_rows b004_09_labels]
    decide +kernel

def b004_10_rows : List Row := [(row3 1 25 60), (row3 1 25 61), (row3 1 25 62), (row3 1 25 63), (row3 1 26 27), (row3 1 26 28), (row3 1 26 29), (row3 1 26 30), (row3 1 26 31), (row3 1 26 32), (row3 1 26 33), (row3 1 26 34), (row3 1 26 35), (row3 1 26 36), (row3 1 26 37), (row3 1 26 38)]

def b004_10_labels : List Row := [(row3 263 462 263), (row3 462 462 462), (row3 171 10 254), (row3 356 91 159), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_10_rows b004_10_labels 6940482503272197706782550500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_10_rows b004_10_labels]
    decide +kernel

def b004_11_rows : List Row := [(row3 1 26 39), (row3 1 26 40), (row3 1 26 41), (row3 1 26 42), (row3 1 26 43), (row3 1 26 44), (row3 1 26 45), (row3 1 26 46), (row3 1 26 47), (row3 1 26 48), (row3 1 26 49), (row3 1 26 50), (row3 1 26 51), (row3 1 26 52), (row3 1 26 53), (row3 1 26 54)]

def b004_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 264 264 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 193 191 235), (row3 285 285 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_11_rows b004_11_labels 515710713067513015914397500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_11_rows b004_11_labels]
    decide +kernel

def b004_12_rows : List Row := [(row3 1 26 55), (row3 1 26 56), (row3 1 26 57), (row3 1 26 58), (row3 1 26 59), (row3 1 26 60), (row3 1 26 61), (row3 1 26 62), (row3 1 26 63), (row3 1 27 28), (row3 1 27 29), (row3 1 27 30), (row3 1 27 31), (row3 1 27 32), (row3 1 27 33), (row3 1 27 34)]

def b004_12_labels : List Row := [(row3 462 462 462), (row3 163 163 462), (row3 358 358 462), (row3 163 162 235), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_12_rows b004_12_labels 15249359259447323413094349000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_12_rows b004_12_labels]
    decide +kernel

def b004_13_rows : List Row := [(row3 1 27 35), (row3 1 27 36), (row3 1 27 37), (row3 1 27 38), (row3 1 27 39), (row3 1 27 40), (row3 1 27 41), (row3 1 27 42), (row3 1 27 43), (row3 1 27 44), (row3 1 27 45), (row3 1 27 46), (row3 1 27 47), (row3 1 27 48), (row3 1 27 49), (row3 1 27 50)]

def b004_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_13_rows b004_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_13_rows b004_13_labels]
    decide +kernel

def b004_14_rows : List Row := [(row3 1 27 51), (row3 1 27 52), (row3 1 27 53), (row3 1 27 54), (row3 1 27 55), (row3 1 27 56), (row3 1 27 57), (row3 1 27 58), (row3 1 27 59), (row3 1 27 60), (row3 1 27 61), (row3 1 27 62), (row3 1 27 63), (row3 1 28 29), (row3 1 28 30), (row3 1 28 31)]

def b004_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_14_rows b004_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_14_rows b004_14_labels]
    decide +kernel

def b004_15_rows : List Row := [(row3 1 28 32), (row3 1 28 33), (row3 1 28 34), (row3 1 28 35), (row3 1 28 36), (row3 1 28 37), (row3 1 28 38), (row3 1 28 39), (row3 1 28 40), (row3 1 28 41), (row3 1 28 42), (row3 1 28 43), (row3 1 28 44), (row3 1 28 45), (row3 1 28 46), (row3 1 28 47)]

def b004_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b004_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b004_15_rows b004_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b004_15_rows b004_15_labels]
    decide +kernel

theorem checked004 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_004 QuarticIntegerComputationalData.ids64_004 2167862953717984910403134723400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b004_00_rows ++ b004_01_rows) ++ (b004_02_rows ++ b004_03_rows)) ++ ((b004_04_rows ++ b004_05_rows) ++ (b004_06_rows ++ b004_07_rows))) ++ (((b004_08_rows ++ b004_09_rows) ++ (b004_10_rows ++ b004_11_rows)) ++ ((b004_12_rows ++ b004_13_rows) ++ (b004_14_rows ++ b004_15_rows))))
    ((((b004_00_labels ++ b004_01_labels) ++ (b004_02_labels ++ b004_03_labels)) ++ ((b004_04_labels ++ b004_05_labels) ++ (b004_06_labels ++ b004_07_labels))) ++ (((b004_08_labels ++ b004_09_labels) ++ (b004_10_labels ++ b004_11_labels)) ++ ((b004_12_labels ++ b004_13_labels) ++ (b004_14_labels ++ b004_15_labels)))) 2167862953717984910403134723400
  exact ((((b004_00_checked.append (c := 13778029452429227203642881000) b004_01_checked (by decide +kernel)).append (c := 56203830006165096528228322500) (b004_02_checked.append (c := 42425800553735869324585441500) b004_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1750478549497107192273818144400) ((b004_04_checked.append (c := 1291939801834341356329376877900) b004_05_checked (by decide +kernel)).append (c := 1694274719490942095745589821900) (b004_06_checked.append (c := 402334917656600739416212944000) b004_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2167862953717984910403134723400) (((b004_08_checked.append (c := 394678851745090683993525282000) b004_09_checked (by decide +kernel)).append (c := 402135044961430394716222230000) (b004_10_checked.append (c := 7456193216339710722696948000) b004_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 417384404220877718129316579000) ((b004_12_checked.append (c := 15249359259447323413094349000) b004_13_checked (by decide +kernel)).append (c := 15249359259447323413094349000) (b004_14_checked.append (c := 0) b004_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b005_00_rows : List Row := [(row3 1 28 48), (row3 1 28 49), (row3 1 28 50), (row3 1 28 51), (row3 1 28 52), (row3 1 28 53), (row3 1 28 54), (row3 1 28 55), (row3 1 28 56), (row3 1 28 57), (row3 1 28 58), (row3 1 28 59), (row3 1 28 60), (row3 1 28 61), (row3 1 28 62), (row3 1 28 63)]

def b005_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_00_rows b005_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_00_rows b005_00_labels]
    decide +kernel

def b005_01_rows : List Row := [(row3 1 29 30), (row3 1 29 31), (row3 1 29 32), (row3 1 29 33), (row3 1 29 34), (row3 1 29 35), (row3 1 29 36), (row3 1 29 37), (row3 1 29 38), (row3 1 29 39), (row3 1 29 40), (row3 1 29 41), (row3 1 29 42), (row3 1 29 43), (row3 1 29 44), (row3 1 29 45)]

def b005_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_01_rows b005_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_01_rows b005_01_labels]
    decide +kernel

def b005_02_rows : List Row := [(row3 1 29 46), (row3 1 29 47), (row3 1 29 48), (row3 1 29 49), (row3 1 29 50), (row3 1 29 51), (row3 1 29 52), (row3 1 29 53), (row3 1 29 54), (row3 1 29 55), (row3 1 29 56), (row3 1 29 57), (row3 1 29 58), (row3 1 29 59), (row3 1 29 60), (row3 1 29 61)]

def b005_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_02_rows b005_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_02_rows b005_02_labels]
    decide +kernel

def b005_03_rows : List Row := [(row3 1 29 62), (row3 1 29 63), (row3 1 30 31), (row3 1 30 32), (row3 1 30 33), (row3 1 30 34), (row3 1 30 35), (row3 1 30 36), (row3 1 30 37), (row3 1 30 38), (row3 1 30 39), (row3 1 30 40), (row3 1 30 41), (row3 1 30 42), (row3 1 30 43), (row3 1 30 44)]

def b005_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_03_rows b005_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_03_rows b005_03_labels]
    decide +kernel

def b005_04_rows : List Row := [(row3 1 30 45), (row3 1 30 46), (row3 1 30 47), (row3 1 30 48), (row3 1 30 49), (row3 1 30 50), (row3 1 30 51), (row3 1 30 52), (row3 1 30 53), (row3 1 30 54), (row3 1 30 55), (row3 1 30 56), (row3 1 30 57), (row3 1 30 58), (row3 1 30 59), (row3 1 30 60)]

def b005_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_04_rows b005_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_04_rows b005_04_labels]
    decide +kernel

def b005_05_rows : List Row := [(row3 1 30 61), (row3 1 30 62), (row3 1 30 63), (row3 1 31 32), (row3 1 31 33), (row3 1 31 34), (row3 1 31 35), (row3 1 31 36), (row3 1 31 37), (row3 1 31 38), (row3 1 31 39), (row3 1 31 40), (row3 1 31 41), (row3 1 31 42), (row3 1 31 43), (row3 1 31 44)]

def b005_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 462 264), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_05_rows b005_05_labels 32861954329140895345500000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_05_rows b005_05_labels]
    decide +kernel

def b005_06_rows : List Row := [(row3 1 31 45), (row3 1 31 46), (row3 1 31 47), (row3 1 31 48), (row3 1 31 49), (row3 1 31 50), (row3 1 31 51), (row3 1 31 52), (row3 1 31 53), (row3 1 31 54), (row3 1 31 55), (row3 1 31 56), (row3 1 31 57), (row3 1 31 58), (row3 1 31 59), (row3 1 31 60)]

def b005_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 235 191), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 285 462 285), (row3 358 462 358), (row3 163 462 163), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462)]

theorem b005_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_06_rows b005_06_labels 14943836445665834816992873500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_06_rows b005_06_labels]
    decide +kernel

def b005_07_rows : List Row := [(row3 1 31 61), (row3 1 31 62), (row3 1 31 63), (row3 1 32 33), (row3 1 32 34), (row3 1 32 35), (row3 1 32 36), (row3 1 32 37), (row3 1 32 38), (row3 1 32 39), (row3 1 32 40), (row3 1 32 41), (row3 1 32 42), (row3 1 32 43), (row3 1 32 44), (row3 1 32 45)]

def b005_07_labels : List Row := [(row3 462 462 462), (row3 284 462 284), (row3 163 235 162), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_07_rows b005_07_labels 3000844324805891454063661500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_07_rows b005_07_labels]
    decide +kernel

def b005_08_rows : List Row := [(row3 1 32 46), (row3 1 32 47), (row3 1 32 48), (row3 1 32 49), (row3 1 32 50), (row3 1 32 51), (row3 1 32 52), (row3 1 32 53), (row3 1 32 54), (row3 1 32 55), (row3 1 32 56), (row3 1 32 57), (row3 1 32 58), (row3 1 32 59), (row3 1 32 60), (row3 1 32 61)]

def b005_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 174 178 174), (row3 299 289 299), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 272 462 272), (row3 341 429 71), (row3 193 163 139), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_08_rows b005_08_labels 114617724559628420620137322980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_08_rows b005_08_labels]
    decide +kernel

def b005_09_rows : List Row := [(row3 1 32 62), (row3 1 32 63), (row3 1 33 34), (row3 1 33 35), (row3 1 33 36), (row3 1 33 37), (row3 1 33 38), (row3 1 33 39), (row3 1 33 40), (row3 1 33 41), (row3 1 33 42), (row3 1 33 43), (row3 1 33 44), (row3 1 33 45), (row3 1 33 46), (row3 1 33 47)]

def b005_09_labels : List Row := [(row3 269 462 269), (row3 193 232 189), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_09_rows b005_09_labels 2609398104624272629368063000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_09_rows b005_09_labels]
    decide +kernel

def b005_10_rows : List Row := [(row3 1 33 48), (row3 1 33 49), (row3 1 33 50), (row3 1 33 51), (row3 1 33 52), (row3 1 33 53), (row3 1 33 54), (row3 1 33 55), (row3 1 33 56), (row3 1 33 57), (row3 1 33 58), (row3 1 33 59), (row3 1 33 60), (row3 1 33 61), (row3 1 33 62), (row3 1 33 63)]

def b005_10_labels : List Row := [(row3 299 299 289), (row3 174 174 178), (row3 272 272 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 139 163), (row3 341 71 429), (row3 193 189 232), (row3 269 269 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 269 462)]

theorem b005_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_10_rows b005_10_labels 115014649911966662512112097480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_10_rows b005_10_labels]
    decide +kernel

def b005_11_rows : List Row := [(row3 1 34 35), (row3 1 34 36), (row3 1 34 37), (row3 1 34 38), (row3 1 34 39), (row3 1 34 40), (row3 1 34 41), (row3 1 34 42), (row3 1 34 43), (row3 1 34 44), (row3 1 34 45), (row3 1 34 46), (row3 1 34 47), (row3 1 34 48), (row3 1 34 49), (row3 1 34 50)]

def b005_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 291 289 291), (row3 234 234 462)]

theorem b005_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_11_rows b005_11_labels 212457744076087982947192200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_11_rows b005_11_labels]
    decide +kernel

def b005_12_rows : List Row := [(row3 1 34 51), (row3 1 34 52), (row3 1 34 53), (row3 1 34 54), (row3 1 34 55), (row3 1 34 56), (row3 1 34 57), (row3 1 34 58), (row3 1 34 59), (row3 1 34 60), (row3 1 34 61), (row3 1 34 62), (row3 1 34 63), (row3 1 35 36), (row3 1 35 37), (row3 1 35 38)]

def b005_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 279 278 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_12_rows b005_12_labels 1132331642468224014744651600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_12_rows b005_12_labels]
    decide +kernel

def b005_13_rows : List Row := [(row3 1 35 39), (row3 1 35 40), (row3 1 35 41), (row3 1 35 42), (row3 1 35 43), (row3 1 35 44), (row3 1 35 45), (row3 1 35 46), (row3 1 35 47), (row3 1 35 48), (row3 1 35 49), (row3 1 35 50), (row3 1 35 51), (row3 1 35 52), (row3 1 35 53), (row3 1 35 54)]

def b005_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_13_rows b005_13_labels 4126121307428863469791500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_13_rows b005_13_labels]
    decide +kernel

def b005_14_rows : List Row := [(row3 1 35 55), (row3 1 35 56), (row3 1 35 57), (row3 1 35 58), (row3 1 35 59), (row3 1 35 60), (row3 1 35 61), (row3 1 35 62), (row3 1 35 63), (row3 1 36 37), (row3 1 36 38), (row3 1 36 39), (row3 1 36 40), (row3 1 36 41), (row3 1 36 42), (row3 1 36 43)]

def b005_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_14_rows b005_14_labels 3867409411222473623709000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_14_rows b005_14_labels]
    decide +kernel

def b005_15_rows : List Row := [(row3 1 36 44), (row3 1 36 45), (row3 1 36 46), (row3 1 36 47), (row3 1 36 48), (row3 1 36 49), (row3 1 36 50), (row3 1 36 51), (row3 1 36 52), (row3 1 36 53), (row3 1 36 54), (row3 1 36 55), (row3 1 36 56), (row3 1 36 57), (row3 1 36 58), (row3 1 36 59)]

def b005_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b005_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b005_15_rows b005_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b005_15_rows b005_15_labels]
    decide +kernel

theorem checked005 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_005 QuarticIntegerComputationalData.ids64_005 251572098218283186262804862760 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b005_00_rows ++ b005_01_rows) ++ (b005_02_rows ++ b005_03_rows)) ++ ((b005_04_rows ++ b005_05_rows) ++ (b005_06_rows ++ b005_07_rows))) ++ (((b005_08_rows ++ b005_09_rows) ++ (b005_10_rows ++ b005_11_rows)) ++ ((b005_12_rows ++ b005_13_rows) ++ (b005_14_rows ++ b005_15_rows))))
    ((((b005_00_labels ++ b005_01_labels) ++ (b005_02_labels ++ b005_03_labels)) ++ ((b005_04_labels ++ b005_05_labels) ++ (b005_06_labels ++ b005_07_labels))) ++ (((b005_08_labels ++ b005_09_labels) ++ (b005_10_labels ++ b005_11_labels)) ++ ((b005_12_labels ++ b005_13_labels) ++ (b005_14_labels ++ b005_15_labels)))) 251572098218283186262804862760
  exact ((((b005_00_checked.append (c := 0) b005_01_checked (by decide +kernel)).append (c := 0) (b005_02_checked.append (c := 0) b005_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 17977542724800867166402035000) ((b005_04_checked.append (c := 32861954329140895345500000) b005_05_checked (by decide +kernel)).append (c := 17977542724800867166402035000) (b005_06_checked.append (c := 17944680770471726271056535000) b005_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 251572098218283186262804862760) (((b005_08_checked.append (c := 117227122664252693249505385980) b005_09_checked (by decide +kernel)).append (c := 232454230320295443744564675660) (b005_10_checked.append (c := 115227107656042750495059289680) b005_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 233594555493482319096402827760) ((b005_12_checked.append (c := 1136457763775652878214443100) b005_13_checked (by decide +kernel)).append (c := 1140325173186875351838152100) (b005_14_checked.append (c := 3867409411222473623709000) b005_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b006_00_rows : List Row := [(row3 1 36 60), (row3 1 36 61), (row3 1 36 62), (row3 1 36 63), (row3 1 37 38), (row3 1 37 39), (row3 1 37 40), (row3 1 37 41), (row3 1 37 42), (row3 1 37 43), (row3 1 37 44), (row3 1 37 45), (row3 1 37 46), (row3 1 37 47), (row3 1 37 48), (row3 1 37 49)]

def b006_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_00_rows b006_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_00_rows b006_00_labels]
    decide +kernel

def b006_01_rows : List Row := [(row3 1 37 50), (row3 1 37 51), (row3 1 37 52), (row3 1 37 53), (row3 1 37 54), (row3 1 37 55), (row3 1 37 56), (row3 1 37 57), (row3 1 37 58), (row3 1 37 59), (row3 1 37 60), (row3 1 37 61), (row3 1 37 62), (row3 1 37 63), (row3 1 38 39), (row3 1 38 40)]

def b006_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b006_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_01_rows b006_01_labels 289958420551243194225000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_01_rows b006_01_labels]
    decide +kernel

def b006_02_rows : List Row := [(row3 1 38 41), (row3 1 38 42), (row3 1 38 43), (row3 1 38 44), (row3 1 38 45), (row3 1 38 46), (row3 1 38 47), (row3 1 38 48), (row3 1 38 49), (row3 1 38 50), (row3 1 38 51), (row3 1 38 52), (row3 1 38 53), (row3 1 38 54), (row3 1 38 55), (row3 1 38 56)]

def b006_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462)]

theorem b006_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_02_rows b006_02_labels 3836162886877620275566500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_02_rows b006_02_labels]
    decide +kernel

def b006_03_rows : List Row := [(row3 1 38 57), (row3 1 38 58), (row3 1 38 59), (row3 1 38 60), (row3 1 38 61), (row3 1 38 62), (row3 1 38 63), (row3 1 39 40), (row3 1 39 41), (row3 1 39 42), (row3 1 39 43), (row3 1 39 44), (row3 1 39 45), (row3 1 39 46), (row3 1 39 47), (row3 1 39 48)]

def b006_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 232 232), (row3 236 462 236), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 291 291 289)]

theorem b006_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_03_rows b006_03_labels 193197476884460252488819200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_03_rows b006_03_labels]
    decide +kernel

def b006_04_rows : List Row := [(row3 1 39 49), (row3 1 39 50), (row3 1 39 51), (row3 1 39 52), (row3 1 39 53), (row3 1 39 54), (row3 1 39 55), (row3 1 39 56), (row3 1 39 57), (row3 1 39 58), (row3 1 39 59), (row3 1 39 60), (row3 1 39 61), (row3 1 39 62), (row3 1 39 63), (row3 1 40 41)]

def b006_04_labels : List Row := [(row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 163 163), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 279 278), (row3 186 269 9)]

theorem b006_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_04_rows b006_04_labels 25667159927264824478406258600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_04_rows b006_04_labels]
    decide +kernel

def b006_05_rows : List Row := [(row3 1 40 42), (row3 1 40 43), (row3 1 40 44), (row3 1 40 45), (row3 1 40 46), (row3 1 40 47), (row3 1 40 48), (row3 1 40 49), (row3 1 40 50), (row3 1 40 51), (row3 1 40 52), (row3 1 40 53), (row3 1 40 54), (row3 1 40 55), (row3 1 40 56), (row3 1 40 57)]

def b006_05_labels : List Row := [(row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 274 274 462), (row3 384 400 397), (row3 331 123 92), (row3 173 260 10), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 271 271 462), (row3 177 152 150), (row3 56 29 445), (row3 74 44 439)]

theorem b006_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_05_rows b006_05_labels 6064545958915124209149826702500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_05_rows b006_05_labels]
    decide +kernel

def b006_06_rows : List Row := [(row3 1 40 58), (row3 1 40 59), (row3 1 40 60), (row3 1 40 61), (row3 1 40 62), (row3 1 40 63), (row3 1 41 42), (row3 1 41 43), (row3 1 41 44), (row3 1 41 45), (row3 1 41 46), (row3 1 41 47), (row3 1 41 48), (row3 1 41 49), (row3 1 41 50), (row3 1 41 51)]

def b006_06_labels : List Row := [(row3 356 158 89), (row3 171 254 10), (row3 462 462 462), (row3 263 263 462), (row3 180 154 154), (row3 354 376 366), (row3 274 462 274), (row3 238 462 238), (row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 238 462 238), (row3 331 92 123), (row3 384 397 400), (row3 177 150 152), (row3 271 462 271)]

theorem b006_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_06_rows b006_06_labels 1405436083210345881107239855350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_06_rows b006_06_labels]
    decide +kernel

def b006_07_rows : List Row := [(row3 1 41 52), (row3 1 41 53), (row3 1 41 54), (row3 1 41 55), (row3 1 41 56), (row3 1 41 57), (row3 1 41 58), (row3 1 41 59), (row3 1 41 60), (row3 1 41 61), (row3 1 41 62), (row3 1 41 63), (row3 1 42 43), (row3 1 42 44), (row3 1 42 45), (row3 1 42 46)]

def b006_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 173 10 260), (row3 74 439 44), (row3 56 445 29), (row3 354 366 376), (row3 180 154 154), (row3 263 462 263), (row3 462 462 462), (row3 171 10 254), (row3 356 89 158), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_07_rows b006_07_labels 4707798971851275234021574150650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_07_rows b006_07_labels]
    decide +kernel

def b006_08_rows : List Row := [(row3 1 42 47), (row3 1 42 48), (row3 1 42 49), (row3 1 42 50), (row3 1 42 51), (row3 1 42 52), (row3 1 42 53), (row3 1 42 54), (row3 1 42 55), (row3 1 42 56), (row3 1 42 57), (row3 1 42 58), (row3 1 42 59), (row3 1 42 60), (row3 1 42 61), (row3 1 42 62)]

def b006_08_labels : List Row := [(row3 462 462 462), (row3 305 305 289), (row3 132 133 137), (row3 307 307 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 124 139), (row3 383 43 436), (row3 127 126 137), (row3 286 286 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_08_rows b006_08_labels 407949545479994918740321276680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_08_rows b006_08_labels]
    decide +kernel

def b006_09_rows : List Row := [(row3 1 42 63), (row3 1 43 44), (row3 1 43 45), (row3 1 43 46), (row3 1 43 47), (row3 1 43 48), (row3 1 43 49), (row3 1 43 50), (row3 1 43 51), (row3 1 43 52), (row3 1 43 53), (row3 1 43 54), (row3 1 43 55), (row3 1 43 56), (row3 1 43 57), (row3 1 43 58)]

def b006_09_labels : List Row := [(row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 291 289 291), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 139 139), (row3 309 306 309)]

theorem b006_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_09_rows b006_09_labels 2228901058209005169276897000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_09_rows b006_09_labels]
    decide +kernel

def b006_10_rows : List Row := [(row3 1 43 59), (row3 1 43 60), (row3 1 43 61), (row3 1 43 62), (row3 1 43 63), (row3 1 44 45), (row3 1 44 46), (row3 1 44 47), (row3 1 44 48), (row3 1 44 49), (row3 1 44 50), (row3 1 44 51), (row3 1 44 52), (row3 1 44 53), (row3 1 44 54), (row3 1 44 55)]

def b006_10_labels : List Row := [(row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_10_rows b006_10_labels 16727786465042064943750500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_10_rows b006_10_labels]
    decide +kernel

def b006_11_rows : List Row := [(row3 1 44 56), (row3 1 44 57), (row3 1 44 58), (row3 1 44 59), (row3 1 44 60), (row3 1 44 61), (row3 1 44 62), (row3 1 44 63), (row3 1 45 46), (row3 1 45 47), (row3 1 45 48), (row3 1 45 49), (row3 1 45 50), (row3 1 45 51), (row3 1 45 52), (row3 1 45 53)]

def b006_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_11_rows b006_11_labels 8036574081208147462887000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_11_rows b006_11_labels]
    decide +kernel

def b006_12_rows : List Row := [(row3 1 45 54), (row3 1 45 55), (row3 1 45 56), (row3 1 45 57), (row3 1 45 58), (row3 1 45 59), (row3 1 45 60), (row3 1 45 61), (row3 1 45 62), (row3 1 45 63), (row3 1 46 47), (row3 1 46 48), (row3 1 46 49), (row3 1 46 50), (row3 1 46 51), (row3 1 46 52)]

def b006_12_labels : List Row := [(row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 228 228), (row3 462 462 462), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_12_rows b006_12_labels 182062211456881910338958700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_12_rows b006_12_labels]
    decide +kernel

def b006_13_rows : List Row := [(row3 1 46 53), (row3 1 46 54), (row3 1 46 55), (row3 1 46 56), (row3 1 46 57), (row3 1 46 58), (row3 1 46 59), (row3 1 46 60), (row3 1 46 61), (row3 1 46 62), (row3 1 46 63), (row3 1 47 48), (row3 1 47 49), (row3 1 47 50), (row3 1 47 51), (row3 1 47 52)]

def b006_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 462 139 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 309 309 306), (row3 132 137 133), (row3 305 289 305), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b006_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_13_rows b006_13_labels 14864798277141488502227274600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_13_rows b006_13_labels]
    decide +kernel

def b006_14_rows : List Row := [(row3 1 47 53), (row3 1 47 54), (row3 1 47 55), (row3 1 47 56), (row3 1 47 57), (row3 1 47 58), (row3 1 47 59), (row3 1 47 60), (row3 1 47 61), (row3 1 47 62), (row3 1 47 63), (row3 1 48 49), (row3 1 48 50), (row3 1 48 51), (row3 1 48 52), (row3 1 48 53)]

def b006_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 307 462 307), (row3 383 436 43), (row3 163 139 124), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 127 137 126), (row3 63 419 433), (row3 367 108 84), (row3 302 265 302), (row3 462 237 237), (row3 266 265 266)]

theorem b006_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_14_rows b006_14_labels 8494565548163392183073074688700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_14_rows b006_14_labels]
    decide +kernel

def b006_15_rows : List Row := [(row3 1 48 54), (row3 1 48 55), (row3 1 48 56), (row3 1 48 57), (row3 1 48 58), (row3 1 48 59), (row3 1 48 60), (row3 1 48 61), (row3 1 48 62), (row3 1 48 63), (row3 1 49 50), (row3 1 49 51), (row3 1 49 52), (row3 1 49 53), (row3 1 49 54), (row3 1 49 55)]

def b006_15_labels : List Row := [(row3 140 140 178), (row3 394 409 414), (row3 450 460 22), (row3 442 451 24), (row3 60 411 432), (row3 369 121 85), (row3 284 462 284), (row3 193 191 235), (row3 362 388 392), (row3 61 48 50), (row3 394 414 409), (row3 140 178 140), (row3 266 266 265), (row3 462 237 237), (row3 302 302 265), (row3 367 84 108)]

theorem b006_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b006_15_rows b006_15_labels 1002605383961726573300777969627970 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b006_15_rows b006_15_labels]
    decide +kernel

theorem checked006 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_006 QuarticIntegerComputationalData.ids64_006 1023728845078779516066258620938950 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b006_00_rows ++ b006_01_rows) ++ (b006_02_rows ++ b006_03_rows)) ++ ((b006_04_rows ++ b006_05_rows) ++ (b006_06_rows ++ b006_07_rows))) ++ (((b006_08_rows ++ b006_09_rows) ++ (b006_10_rows ++ b006_11_rows)) ++ ((b006_12_rows ++ b006_13_rows) ++ (b006_14_rows ++ b006_15_rows))))
    ((((b006_00_labels ++ b006_01_labels) ++ (b006_02_labels ++ b006_03_labels)) ++ ((b006_04_labels ++ b006_05_labels) ++ (b006_06_labels ++ b006_07_labels))) ++ (((b006_08_labels ++ b006_09_labels) ++ (b006_10_labels ++ b006_11_labels)) ++ ((b006_12_labels ++ b006_13_labels) ++ (b006_14_labels ++ b006_15_labels)))) 1023728845078779516066258620938950
  exact ((((b006_00_checked.append (c := 289958420551243194225000) b006_01_checked (by decide +kernel)).append (c := 197323598191889115958610700) (b006_02_checked.append (c := 197033639771337872764385700) b006_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 12203645497502202037873005577800) ((b006_04_checked.append (c := 6090213118842389033628232961100) b006_05_checked (by decide +kernel)).append (c := 12203448173904010148757046967100) (b006_06_checked.append (c := 6113235055061621115128814006000) b006_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1023728845078779516066258620938950) (((b006_08_checked.append (c := 410178446538203923909598173680) b006_09_checked (by decide +kernel)).append (c := 410203210898750174122004811180) (b006_10_checked.append (c := 24764360546250212406637500) b006_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1011525199581277314028385615361150) ((b006_12_checked.append (c := 15046860488598370412566233300) b006_13_checked (by decide +kernel)).append (c := 1011114996370378563854263610549970) (b006_14_checked.append (c := 1011099949509889965483851044316670) b006_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b007_00_rows : List Row := [(row3 1 49 56), (row3 1 49 57), (row3 1 49 58), (row3 1 49 59), (row3 1 49 60), (row3 1 49 61), (row3 1 49 62), (row3 1 49 63), (row3 1 50 51), (row3 1 50 52), (row3 1 50 53), (row3 1 50 54), (row3 1 50 55), (row3 1 50 56), (row3 1 50 57), (row3 1 50 58)]

def b007_00_labels : List Row := [(row3 442 24 451), (row3 450 22 460), (row3 61 50 48), (row3 362 392 388), (row3 193 235 191), (row3 284 284 462), (row3 369 85 121), (row3 60 432 411), (row3 316 462 316), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 119 11 216), (row3 46 440 46), (row3 32 452 25), (row3 418 422 424)]

theorem b007_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_00_rows b007_00_labels 1017385229829693043475815457604420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_00_rows b007_00_labels]
    decide +kernel

def b007_01_rows : List Row := [(row3 1 50 59), (row3 1 50 60), (row3 1 50 61), (row3 1 50 62), (row3 1 50 63), (row3 1 51 52), (row3 1 51 53), (row3 1 51 54), (row3 1 51 55), (row3 1 51 56), (row3 1 51 57), (row3 1 51 58), (row3 1 51 59), (row3 1 51 60), (row3 1 51 61), (row3 1 51 62)]

def b007_01_labels : List Row := [(row3 129 103 102), (row3 287 462 287), (row3 462 462 462), (row3 117 11 214), (row3 398 81 134), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 139 124 163), (row3 389 45 436), (row3 100 100 113), (row3 307 307 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b007_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_01_rows b007_01_labels 456839284607330333084689746690 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_01_rows b007_01_labels]
    decide +kernel

def b007_02_rows : List Row := [(row3 1 51 63), (row3 1 52 53), (row3 1 52 54), (row3 1 52 55), (row3 1 52 56), (row3 1 52 57), (row3 1 52 58), (row3 1 52 59), (row3 1 52 60), (row3 1 52 61), (row3 1 52 62), (row3 1 52 63), (row3 1 53 54), (row3 1 53 55), (row3 1 53 56), (row3 1 53 57)]

def b007_02_labels : List Row := [(row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 163 163), (row3 309 306 309), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 232 232), (row3 462 462 462), (row3 234 462 234), (row3 462 163 163), (row3 462 462 462)]

theorem b007_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_02_rows b007_02_labels 2608510407761522621617642800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_02_rows b007_02_labels]
    decide +kernel

def b007_03_rows : List Row := [(row3 1 53 58), (row3 1 53 59), (row3 1 53 60), (row3 1 53 61), (row3 1 53 62), (row3 1 53 63), (row3 1 54 55), (row3 1 54 56), (row3 1 54 57), (row3 1 54 58), (row3 1 54 59), (row3 1 54 60), (row3 1 54 61), (row3 1 54 62), (row3 1 54 63), (row3 1 55 56)]

def b007_03_labels : List Row := [(row3 462 232 232), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 309 309 306), (row3 316 462 316), (row3 389 436 45), (row3 139 163 124), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 307 462 307), (row3 100 113 100), (row3 32 25 452)]

theorem b007_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_03_rows b007_03_labels 14211792781493261463261699671340 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_03_rows b007_03_labels]
    decide +kernel

def b007_04_rows : List Row := [(row3 1 55 57), (row3 1 55 58), (row3 1 55 59), (row3 1 55 60), (row3 1 55 61), (row3 1 55 62), (row3 1 55 63), (row3 1 56 57), (row3 1 56 58), (row3 1 56 59), (row3 1 56 60), (row3 1 56 61), (row3 1 56 62), (row3 1 56 63), (row3 1 57 58), (row3 1 57 59)]

def b007_04_labels : List Row := [(row3 46 46 440), (row3 398 134 81), (row3 117 214 11), (row3 462 462 462), (row3 287 287 462), (row3 129 102 103), (row3 418 424 422), (row3 20 20 17), (row3 451 442 24), (row3 44 74 439), (row3 163 193 139), (row3 359 73 429), (row3 34 443 27), (row3 457 23 461), (row3 457 461 23), (row3 34 27 443)]

theorem b007_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_04_rows b007_04_labels 11435669999527700520976815661879110 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_04_rows b007_04_labels]
    decide +kernel

def b007_05_rows : List Row := [(row3 1 57 60), (row3 1 57 61), (row3 1 57 62), (row3 1 57 63), (row3 1 58 59), (row3 1 58 60), (row3 1 58 61), (row3 1 58 62), (row3 1 58 63), (row3 1 59 60), (row3 1 59 61), (row3 1 59 62), (row3 1 59 63), (row3 1 60 61), (row3 1 60 62), (row3 1 60 63)]

def b007_05_labels : List Row := [(row3 359 429 73), (row3 163 139 193), (row3 44 439 74), (row3 451 24 442), (row3 417 423 422), (row3 127 137 126), (row3 301 301 278), (row3 399 82 156), (row3 40 438 413), (row3 303 462 303), (row3 235 462 235), (row3 116 11 213), (row3 399 82 156), (row3 462 462 462), (row3 235 462 235), (row3 301 301 278)]

theorem b007_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_05_rows b007_05_labels 32796235895250119938433723583390 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_05_rows b007_05_labels]
    decide +kernel

def b007_06_rows : List Row := [(row3 1 61 62), (row3 1 61 63), (row3 1 62 63), (row3 2 3 4), (row3 2 3 5), (row3 2 3 6), (row3 2 3 7), (row3 2 3 8), (row3 2 3 9), (row3 2 3 10), (row3 2 3 11), (row3 2 3 12), (row3 2 3 13), (row3 2 3 14), (row3 2 3 15), (row3 2 3 16)]

def b007_06_labels : List Row := [(row3 303 462 303), (row3 127 137 126), (row3 417 423 422), (row3 80 30 446), (row3 326 425 75), (row3 205 96 335), (row3 364 374 355), (row3 397 400 384), (row3 53 51 57), (row3 454 448 449), (row3 56 29 445), (row3 372 430 58), (row3 325 87 371), (row3 265 277 277), (row3 167 190 166), (row3 164 206 164)]

theorem b007_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_06_rows b007_06_labels 22942170028290943047362064814260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_06_rows b007_06_labels]
    decide +kernel

def b007_07_rows : List Row := [(row3 2 3 17), (row3 2 3 18), (row3 2 3 19), (row3 2 3 20), (row3 2 3 21), (row3 2 3 22), (row3 2 3 23), (row3 2 3 24), (row3 2 3 25), (row3 2 3 26), (row3 2 3 27), (row3 2 3 28), (row3 2 3 29), (row3 2 3 30), (row3 2 3 31), (row3 2 3 32)]

def b007_07_labels : List Row := [(row3 386 393 363), (row3 69 68 76), (row3 385 426 77), (row3 211 88 370), (row3 462 269 269), (row3 237 237 462), (row3 265 266 266), (row3 255 256 256), (row3 192 238 193), (row3 338 343 330), (row3 202 97 334), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 239 239 462)]

theorem b007_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_07_rows b007_07_labels 199246121218874740688590257120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_07_rows b007_07_labels]
    decide +kernel

def b007_08_rows : List Row := [(row3 2 3 33), (row3 2 3 34), (row3 2 3 35), (row3 2 3 36), (row3 2 3 37), (row3 2 3 38), (row3 2 3 39), (row3 2 3 40), (row3 2 3 41), (row3 2 3 42), (row3 2 3 43), (row3 2 3 44), (row3 2 3 45), (row3 2 3 46), (row3 2 3 47), (row3 2 3 48)]

def b007_08_labels : List Row := [(row3 462 462 462), (row3 208 462 208), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 192 238 193), (row3 338 343 330), (row3 202 97 334), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 164 206 164)]

theorem b007_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_08_rows b007_08_labels 11810232369858493475716748010 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_08_rows b007_08_labels]
    decide +kernel

def b007_09_rows : List Row := [(row3 2 3 49), (row3 2 3 50), (row3 2 3 51), (row3 2 3 52), (row3 2 3 53), (row3 2 3 54), (row3 2 3 55), (row3 2 3 56), (row3 2 3 57), (row3 2 3 58), (row3 2 3 59), (row3 2 3 60), (row3 2 3 61), (row3 2 3 62), (row3 2 3 63), (row3 2 4 5)]

def b007_09_labels : List Row := [(row3 386 393 363), (row3 69 68 76), (row3 385 426 77), (row3 211 88 370), (row3 462 269 269), (row3 237 237 462), (row3 265 266 266), (row3 397 400 384), (row3 53 51 57), (row3 454 448 449), (row3 56 29 445), (row3 372 430 58), (row3 325 87 371), (row3 265 277 277), (row3 167 190 166), (row3 335 96 205)]

theorem b007_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_09_rows b007_09_labels 14569187749874770617039854880210 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_09_rows b007_09_labels]
    decide +kernel

def b007_10_rows : List Row := [(row3 2 4 6), (row3 2 4 7), (row3 2 4 8), (row3 2 4 9), (row3 2 4 10), (row3 2 4 11), (row3 2 4 12), (row3 2 4 13), (row3 2 4 14), (row3 2 4 15), (row3 2 4 16), (row3 2 4 17), (row3 2 4 18), (row3 2 4 19), (row3 2 4 20), (row3 2 4 21)]

def b007_10_labels : List Row := [(row3 273 462 273), (row3 205 96 335), (row3 174 178 174), (row3 346 350 349), (row3 67 79 67), (row3 349 350 346), (row3 174 178 174), (row3 273 462 273), (row3 235 462 235), (row3 273 462 273), (row3 273 462 273), (row3 183 178 183), (row3 327 327 327), (row3 183 178 183), (row3 273 462 273), (row3 237 462 237)]

theorem b007_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_10_rows b007_10_labels 126474913849943813641366887120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_10_rows b007_10_labels]
    decide +kernel

def b007_11_rows : List Row := [(row3 2 4 22), (row3 2 4 23), (row3 2 4 24), (row3 2 4 25), (row3 2 4 26), (row3 2 4 27), (row3 2 4 28), (row3 2 4 29), (row3 2 4 30), (row3 2 4 31), (row3 2 4 32), (row3 2 4 33), (row3 2 4 34), (row3 2 4 35), (row3 2 4 36), (row3 2 4 37)]

def b007_11_labels : List Row := [(row3 462 462 462), (row3 237 462 237), (row3 239 462 239), (row3 261 462 261), (row3 210 206 210), (row3 261 462 261), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 462 255), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b007_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_11_rows b007_11_labels 32815303180733009845495440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_11_rows b007_11_labels]
    decide +kernel

def b007_12_rows : List Row := [(row3 2 4 38), (row3 2 4 39), (row3 2 4 40), (row3 2 4 41), (row3 2 4 42), (row3 2 4 43), (row3 2 4 44), (row3 2 4 45), (row3 2 4 46), (row3 2 4 47), (row3 2 4 48), (row3 2 4 49), (row3 2 4 50), (row3 2 4 51), (row3 2 4 52), (row3 2 4 53)]

def b007_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 261 462 261), (row3 210 206 210), (row3 261 462 261), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 183 178 183), (row3 327 327 327), (row3 183 178 183), (row3 273 462 273), (row3 237 462 237)]

theorem b007_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_12_rows b007_12_labels 922831374668440919439456720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_12_rows b007_12_labels]
    decide +kernel

def b007_13_rows : List Row := [(row3 2 4 54), (row3 2 4 55), (row3 2 4 56), (row3 2 4 57), (row3 2 4 58), (row3 2 4 59), (row3 2 4 60), (row3 2 4 61), (row3 2 4 62), (row3 2 4 63), (row3 2 5 6), (row3 2 5 7), (row3 2 5 8), (row3 2 5 9), (row3 2 5 10), (row3 2 5 11)]

def b007_13_labels : List Row := [(row3 462 462 462), (row3 237 462 237), (row3 174 178 174), (row3 346 350 349), (row3 67 79 67), (row3 349 350 346), (row3 174 178 174), (row3 273 462 273), (row3 235 462 235), (row3 273 462 273), (row3 335 96 205), (row3 326 425 75), (row3 340 344 329), (row3 176 165 165), (row3 340 329 344), (row3 195 194 188)]

theorem b007_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_13_rows b007_13_labels 209839423225822031570048244120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_13_rows b007_13_labels]
    decide +kernel

def b007_14_rows : List Row := [(row3 2 5 12), (row3 2 5 13), (row3 2 5 14), (row3 2 5 15), (row3 2 5 16), (row3 2 5 17), (row3 2 5 18), (row3 2 5 19), (row3 2 5 20), (row3 2 5 21), (row3 2 5 22), (row3 2 5 23), (row3 2 5 24), (row3 2 5 25), (row3 2 5 26), (row3 2 5 27)]

def b007_14_labels : List Row := [(row3 275 276 276), (row3 207 200 200), (row3 275 276 276), (row3 195 188 194), (row3 209 206 209), (row3 278 281 281), (row3 209 209 206), (row3 265 267 267), (row3 235 237 235), (row3 255 256 256), (row3 235 235 237), (row3 265 267 267), (row3 255 256 256), (row3 236 238 238), (row3 255 256 256), (row3 238 462 238)]

theorem b007_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_14_rows b007_14_labels 1463545410208729722960058440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_14_rows b007_14_labels]
    decide +kernel

def b007_15_rows : List Row := [(row3 2 5 28), (row3 2 5 29), (row3 2 5 30), (row3 2 5 31), (row3 2 5 32), (row3 2 5 33), (row3 2 5 34), (row3 2 5 35), (row3 2 5 36), (row3 2 5 37), (row3 2 5 38), (row3 2 5 39), (row3 2 5 40), (row3 2 5 41), (row3 2 5 42), (row3 2 5 43)]

def b007_15_labels : List Row := [(row3 462 241 241), (row3 239 239 239), (row3 462 241 241), (row3 238 238 462), (row3 239 239 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 236 238 238), (row3 255 256 256), (row3 238 462 238)]

theorem b007_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b007_15_rows b007_15_labels 2588687633096754814955100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b007_15_rows b007_15_labels]
    decide +kernel

theorem checked007 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_007 QuarticIntegerComputationalData.ids64_007 12538583856078757941454217551924290 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b007_00_rows ++ b007_01_rows) ++ (b007_02_rows ++ b007_03_rows)) ++ ((b007_04_rows ++ b007_05_rows) ++ (b007_06_rows ++ b007_07_rows))) ++ (((b007_08_rows ++ b007_09_rows) ++ (b007_10_rows ++ b007_11_rows)) ++ ((b007_12_rows ++ b007_13_rows) ++ (b007_14_rows ++ b007_15_rows))))
    ((((b007_00_labels ++ b007_01_labels) ++ (b007_02_labels ++ b007_03_labels)) ++ ((b007_04_labels ++ b007_05_labels) ++ (b007_06_labels ++ b007_07_labels))) ++ (((b007_08_labels ++ b007_09_labels) ++ (b007_10_labels ++ b007_11_labels)) ++ ((b007_12_labels ++ b007_13_labels) ++ (b007_14_labels ++ b007_15_labels)))) 12538583856078757941454217551924290
  exact ((((b007_00_checked.append (c := 1017842069114300373808900147351110) b007_01_checked (by decide +kernel)).append (c := 1032056470406201396794783464665250) (b007_02_checked.append (c := 14214401291901022985883317314140) b007_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 12523664121978661855498083505199130) ((b007_04_checked.append (c := 11468466235422950640915249385462500) b007_05_checked (by decide +kernel)).append (c := 11491607651572460458703300040533880) (b007_06_checked.append (c := 23141416149509817788050655071380) b007_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 12538583856078757941454217551924290) (((b007_08_checked.append (c := 14580997982244629110515571628220) b007_09_checked (by decide +kernel)).append (c := 14707505711397753657166784010780) (b007_10_checked.append (c := 126507729153124546651212382560) b007_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 14919734100096085956134046725160) ((b007_12_checked.append (c := 210762254600490472489487700840) b007_13_checked (by decide +kernel)).append (c := 212228388698332298967262714380) (b007_14_checked.append (c := 1466134097841826477775013540) b007_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b008_00_rows : List Row := [(row3 2 5 44), (row3 2 5 45), (row3 2 5 46), (row3 2 5 47), (row3 2 5 48), (row3 2 5 49), (row3 2 5 50), (row3 2 5 51), (row3 2 5 52), (row3 2 5 53), (row3 2 5 54), (row3 2 5 55), (row3 2 5 56), (row3 2 5 57), (row3 2 5 58), (row3 2 5 59)]

def b008_00_labels : List Row := [(row3 462 241 241), (row3 239 239 239), (row3 462 241 241), (row3 238 238 462), (row3 209 206 209), (row3 278 281 281), (row3 209 209 206), (row3 265 267 267), (row3 235 237 235), (row3 255 256 256), (row3 235 235 237), (row3 265 267 267), (row3 340 344 329), (row3 176 165 165), (row3 340 329 344), (row3 195 194 188)]

theorem b008_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_00_rows b008_00_labels 12072313048617473784987521580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_00_rows b008_00_labels]
    decide +kernel

def b008_01_rows : List Row := [(row3 2 5 60), (row3 2 5 61), (row3 2 5 62), (row3 2 5 63), (row3 2 6 7), (row3 2 6 8), (row3 2 6 9), (row3 2 6 10), (row3 2 6 11), (row3 2 6 12), (row3 2 6 13), (row3 2 6 14), (row3 2 6 15), (row3 2 6 16), (row3 2 6 17), (row3 2 6 18)]

def b008_01_labels : List Row := [(row3 275 276 276), (row3 207 200 200), (row3 275 276 276), (row3 195 188 194), (row3 80 30 446), (row3 67 67 79), (row3 346 349 350), (row3 174 174 178), (row3 273 273 462), (row3 235 235 462), (row3 273 273 462), (row3 174 174 178), (row3 349 346 350), (row3 327 327 327), (row3 183 183 178), (row3 273 273 462)]

theorem b008_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_01_rows b008_01_labels 3881642077857476105626550506320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_01_rows b008_01_labels]
    decide +kernel

def b008_02_rows : List Row := [(row3 2 6 19), (row3 2 6 20), (row3 2 6 21), (row3 2 6 22), (row3 2 6 23), (row3 2 6 24), (row3 2 6 25), (row3 2 6 26), (row3 2 6 27), (row3 2 6 28), (row3 2 6 29), (row3 2 6 30), (row3 2 6 31), (row3 2 6 32), (row3 2 6 33), (row3 2 6 34)]

def b008_02_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 237 237 462), (row3 273 273 462), (row3 183 183 178), (row3 210 210 206), (row3 261 261 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 462), (row3 261 261 462), (row3 255 255 462), (row3 462 462 462), (row3 462 462 462)]

theorem b008_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_02_rows b008_02_labels 153893927185355017595954880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_02_rows b008_02_labels]
    decide +kernel

def b008_03_rows : List Row := [(row3 2 6 35), (row3 2 6 36), (row3 2 6 37), (row3 2 6 38), (row3 2 6 39), (row3 2 6 40), (row3 2 6 41), (row3 2 6 42), (row3 2 6 43), (row3 2 6 44), (row3 2 6 45), (row3 2 6 46), (row3 2 6 47), (row3 2 6 48), (row3 2 6 49), (row3 2 6 50)]

def b008_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 210 210 206), (row3 261 261 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 462), (row3 261 261 462), (row3 327 327 327), (row3 183 183 178), (row3 273 273 462)]

theorem b008_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_03_rows b008_03_labels 801752750663818911688997280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_03_rows b008_03_labels]
    decide +kernel

def b008_04_rows : List Row := [(row3 2 6 51), (row3 2 6 52), (row3 2 6 53), (row3 2 6 54), (row3 2 6 55), (row3 2 6 56), (row3 2 6 57), (row3 2 6 58), (row3 2 6 59), (row3 2 6 60), (row3 2 6 61), (row3 2 6 62), (row3 2 6 63), (row3 2 7 8), (row3 2 7 9), (row3 2 7 10)]

def b008_04_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 237 237 462), (row3 273 273 462), (row3 183 183 178), (row3 67 67 79), (row3 346 349 350), (row3 174 174 178), (row3 273 273 462), (row3 235 235 462), (row3 273 273 462), (row3 174 174 178), (row3 349 346 350), (row3 454 449 448), (row3 53 57 51), (row3 397 384 400)]

theorem b008_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_04_rows b008_04_labels 10164080346329253863971336040700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_04_rows b008_04_labels]
    decide +kernel

def b008_05_rows : List Row := [(row3 2 7 11), (row3 2 7 12), (row3 2 7 13), (row3 2 7 14), (row3 2 7 15), (row3 2 7 16), (row3 2 7 17), (row3 2 7 18), (row3 2 7 19), (row3 2 7 20), (row3 2 7 21), (row3 2 7 22), (row3 2 7 23), (row3 2 7 24), (row3 2 7 25), (row3 2 7 26)]

def b008_05_labels : List Row := [(row3 167 166 190), (row3 265 277 277), (row3 325 371 87), (row3 372 58 430), (row3 56 445 29), (row3 69 76 68), (row3 386 363 393), (row3 164 164 206), (row3 265 266 266), (row3 237 462 237), (row3 462 269 269), (row3 211 370 88), (row3 385 77 426), (row3 338 330 343), (row3 192 193 238), (row3 255 256 256)]

theorem b008_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_05_rows b008_05_labels 4511219428728158920871242789500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_05_rows b008_05_labels]
    decide +kernel

def b008_06_rows : List Row := [(row3 2 7 27), (row3 2 7 28), (row3 2 7 29), (row3 2 7 30), (row3 2 7 31), (row3 2 7 32), (row3 2 7 33), (row3 2 7 34), (row3 2 7 35), (row3 2 7 36), (row3 2 7 37), (row3 2 7 38), (row3 2 7 39), (row3 2 7 40), (row3 2 7 41), (row3 2 7 42)]

def b008_06_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 202 334 97), (row3 208 208 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 338 330 343), (row3 192 193 238), (row3 255 256 256)]

theorem b008_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_06_rows b008_06_labels 8552734446049683410408159850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_06_rows b008_06_labels]
    decide +kernel

def b008_07_rows : List Row := [(row3 2 7 43), (row3 2 7 44), (row3 2 7 45), (row3 2 7 46), (row3 2 7 47), (row3 2 7 48), (row3 2 7 49), (row3 2 7 50), (row3 2 7 51), (row3 2 7 52), (row3 2 7 53), (row3 2 7 54), (row3 2 7 55), (row3 2 7 56), (row3 2 7 57), (row3 2 7 58)]

def b008_07_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 202 334 97), (row3 69 76 68), (row3 386 363 393), (row3 164 164 206), (row3 265 266 266), (row3 237 462 237), (row3 462 269 269), (row3 211 370 88), (row3 385 77 426), (row3 454 449 448), (row3 53 57 51), (row3 397 384 400)]

theorem b008_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_07_rows b008_07_labels 10249670267246308608614146438230 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_07_rows b008_07_labels]
    decide +kernel

def b008_08_rows : List Row := [(row3 2 7 59), (row3 2 7 60), (row3 2 7 61), (row3 2 7 62), (row3 2 7 63), (row3 2 8 9), (row3 2 8 10), (row3 2 8 11), (row3 2 8 12), (row3 2 8 13), (row3 2 8 14), (row3 2 8 15), (row3 2 8 16), (row3 2 8 17), (row3 2 8 18), (row3 2 8 19)]

def b008_08_labels : List Row := [(row3 167 166 190), (row3 265 277 277), (row3 325 371 87), (row3 372 58 430), (row3 56 445 29), (row3 451 442 24), (row3 419 63 433), (row3 123 331 92), (row3 289 299 299), (row3 155 332 93), (row3 401 78 427), (row3 34 443 27), (row3 37 444 28), (row3 411 60 432), (row3 108 367 84), (row3 289 305 305)]

theorem b008_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_08_rows b008_08_labels 49864505827972010865465177059520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_08_rows b008_08_labels]
    decide +kernel

def b008_09_rows : List Row := [(row3 2 8 20), (row3 2 8 21), (row3 2 8 22), (row3 2 8 23), (row3 2 8 24), (row3 2 8 25), (row3 2 8 26), (row3 2 8 27), (row3 2 8 28), (row3 2 8 29), (row3 2 8 30), (row3 2 8 31), (row3 2 8 32), (row3 2 8 33), (row3 2 8 34), (row3 2 8 35)]

def b008_09_labels : List Row := [(row3 234 462 234), (row3 462 284 284), (row3 114 368 86), (row3 410 59 431), (row3 385 77 426), (row3 121 369 85), (row3 265 302 302), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 122 369 86), (row3 168 333 94), (row3 462 284 284), (row3 237 462 237), (row3 462 462 462)]

theorem b008_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_09_rows b008_09_labels 247576746150486695257157391120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_09_rows b008_09_labels]
    decide +kernel

def b008_10_rows : List Row := [(row3 2 8 36), (row3 2 8 37), (row3 2 8 38), (row3 2 8 39), (row3 2 8 40), (row3 2 8 41), (row3 2 8 42), (row3 2 8 43), (row3 2 8 44), (row3 2 8 45), (row3 2 8 46), (row3 2 8 47), (row3 2 8 48), (row3 2 8 49), (row3 2 8 50), (row3 2 8 51)]

def b008_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 339 328 342), (row3 191 193 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 68 76 69), (row3 388 362 392), (row3 140 140 178), (row3 289 291 291)]

theorem b008_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_10_rows b008_10_labels 127163076356523030666712388580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_10_rows b008_10_labels]
    decide +kernel

def b008_11_rows : List Row := [(row3 2 8 52), (row3 2 8 53), (row3 2 8 54), (row3 2 8 55), (row3 2 8 56), (row3 2 8 57), (row3 2 8 58), (row3 2 8 59), (row3 2 8 60), (row3 2 8 61), (row3 2 8 62), (row3 2 8 63), (row3 2 9 10), (row3 2 9 11), (row3 2 9 12), (row3 2 9 13)]

def b008_11_labels : List Row := [(row3 234 462 234), (row3 462 462 462), (row3 180 180 462), (row3 387 360 390), (row3 455 447 447), (row3 48 61 50), (row3 409 394 414), (row3 133 132 137), (row3 289 291 291), (row3 191 193 235), (row3 387 361 391), (row3 49 62 52), (row3 451 442 24), (row3 402 404 403), (row3 126 125 128), (row3 288 288 288)]

theorem b008_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_11_rows b008_11_labels 38804678492037025313865243726840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_11_rows b008_11_labels]
    decide +kernel

def b008_12_rows : List Row := [(row3 2 9 14), (row3 2 9 15), (row3 2 9 16), (row3 2 9 17), (row3 2 9 18), (row3 2 9 19), (row3 2 9 20), (row3 2 9 21), (row3 2 9 22), (row3 2 9 23), (row3 2 9 24), (row3 2 9 25), (row3 2 9 26), (row3 2 9 27), (row3 2 9 28), (row3 2 9 29)]

def b008_12_labels : List Row := [(row3 126 128 125), (row3 402 403 404), (row3 406 405 406), (row3 38 33 33), (row3 406 406 405), (row3 98 99 101), (row3 278 288 300), (row3 462 462 462), (row3 278 300 288), (row3 98 101 99), (row3 109 111 110), (row3 379 380 380), (row3 109 110 111), (row3 273 295 304), (row3 462 462 462), (row3 462 462 462)]

theorem b008_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_12_rows b008_12_labels 1734000100539292895309360834400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_12_rows b008_12_labels]
    decide +kernel

def b008_13_rows : List Row := [(row3 2 9 30), (row3 2 9 31), (row3 2 9 32), (row3 2 9 33), (row3 2 9 34), (row3 2 9 35), (row3 2 9 36), (row3 2 9 37), (row3 2 9 38), (row3 2 9 39), (row3 2 9 40), (row3 2 9 41), (row3 2 9 42), (row3 2 9 43), (row3 2 9 44), (row3 2 9 45)]

def b008_13_labels : List Row := [(row3 462 462 462), (row3 273 304 295), (row3 261 290 288), (row3 161 176 176), (row3 261 288 290), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 199 198 190), (row3 288 288 288), (row3 199 190 198), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462)]

theorem b008_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_13_rows b008_13_labels 573881712299120310819027840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_13_rows b008_13_labels]
    decide +kernel

def b008_14_rows : List Row := [(row3 2 9 46), (row3 2 9 47), (row3 2 9 48), (row3 2 9 49), (row3 2 9 50), (row3 2 9 51), (row3 2 9 52), (row3 2 9 53), (row3 2 9 54), (row3 2 9 55), (row3 2 9 56), (row3 2 9 57), (row3 2 9 58), (row3 2 9 59), (row3 2 9 60), (row3 2 9 61)]

def b008_14_labels : List Row := [(row3 462 462 462), (row3 273 273 462), (row3 348 350 351), (row3 107 106 106), (row3 348 351 350), (row3 149 137 146), (row3 278 462 278), (row3 462 462 462), (row3 278 278 462), (row3 149 146 137), (row3 48 50 61), (row3 420 421 421), (row3 48 61 50), (row3 378 382 381), (row3 149 137 146), (row3 288 273 273)]

theorem b008_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_14_rows b008_14_labels 2858216460039059572572952659840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_14_rows b008_14_labels]
    decide +kernel

def b008_15_rows : List Row := [(row3 2 9 62), (row3 2 9 63), (row3 2 10 11), (row3 2 10 12), (row3 2 10 13), (row3 2 10 14), (row3 2 10 15), (row3 2 10 16), (row3 2 10 17), (row3 2 10 18), (row3 2 10 19), (row3 2 10 20), (row3 2 10 21), (row3 2 10 22), (row3 2 10 23), (row3 2 10 24)]

def b008_15_labels : List Row := [(row3 149 146 137), (row3 378 381 382), (row3 34 27 443), (row3 401 427 78), (row3 155 93 332), (row3 289 299 299), (row3 123 92 331), (row3 108 84 367), (row3 411 432 60), (row3 37 28 444), (row3 410 431 59), (row3 114 86 368), (row3 462 284 284), (row3 234 234 462), (row3 289 305 305), (row3 265 302 302)]

theorem b008_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b008_15_rows b008_15_labels 9980417491286205744078252719220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b008_15_rows b008_15_labels]
    decide +kernel

theorem checked008 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_008 QuarticIntegerComputationalData.ids64_008 132445324890426617067733632215700 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b008_00_rows ++ b008_01_rows) ++ (b008_02_rows ++ b008_03_rows)) ++ ((b008_04_rows ++ b008_05_rows) ++ (b008_06_rows ++ b008_07_rows))) ++ (((b008_08_rows ++ b008_09_rows) ++ (b008_10_rows ++ b008_11_rows)) ++ ((b008_12_rows ++ b008_13_rows) ++ (b008_14_rows ++ b008_15_rows))))
    ((((b008_00_labels ++ b008_01_labels) ++ (b008_02_labels ++ b008_03_labels)) ++ ((b008_04_labels ++ b008_05_labels) ++ (b008_06_labels ++ b008_07_labels))) ++ (((b008_08_labels ++ b008_09_labels) ++ (b008_10_labels ++ b008_11_labels)) ++ ((b008_12_labels ++ b008_13_labels) ++ (b008_14_labels ++ b008_15_labels)))) 132445324890426617067733632215700
  exact ((((b008_00_checked.append (c := 3893714390906093579411538027900) b008_01_checked (by decide +kernel)).append (c := 3894670037583942753340822980060) (b008_02_checked.append (c := 955646677849173929284952160) b008_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 28828192814333713830207956408340) ((b008_04_checked.append (c := 14675299775057412784842578830200) b008_05_checked (by decide +kernel)).append (c := 24933522776749771076867133428280) (b008_06_checked.append (c := 10258223001692358292024554598080) b008_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 132445324890426617067733632215700) (((b008_08_checked.append (c := 50112082574122497560722334450640) b008_09_checked (by decide +kernel)).append (c := 89043924142516045905254290566060) (b008_10_checked.append (c := 38931841568393548344531956115420) b008_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 103617132076092903237525675807360) ((b008_12_checked.append (c := 1734573982251592015620179862240) b008_13_checked (by decide +kernel)).append (c := 14573207933576857332271385241300) (b008_14_checked.append (c := 12838633951325265316651205379060) b008_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
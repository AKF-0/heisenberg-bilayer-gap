import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Block000

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b000_00_rows : List Row := [(row3 1 2 3), (row3 1 2 4), (row3 1 2 5), (row3 1 2 6), (row3 1 2 7), (row3 1 2 8), (row3 1 2 9), (row3 1 2 10), (row3 1 2 11), (row3 1 2 12), (row3 1 2 13), (row3 1 2 14), (row3 1 2 15), (row3 1 2 16), (row3 1 2 17), (row3 1 2 18)]

def b000_00_labels : List Row := [(row3 441 459 21), (row3 80 30 446), (row3 70 434 70), (row3 446 30 80), (row3 21 459 441), (row3 22 460 450), (row3 19 18 19), (row3 450 460 22), (row3 47 26 453), (row3 95 435 41), (row3 193 163 193), (row3 41 435 95), (row3 453 26 47), (row3 444 28 37), (row3 447 455 447), (row3 37 28 444)]

theorem b000_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_00_rows b000_00_labels 4857301602465002330477140020367740 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_00_rows b000_00_labels]
    decide +kernel

def b000_01_rows : List Row := [(row3 1 2 19), (row3 1 2 20), (row3 1 2 21), (row3 1 2 22), (row3 1 2 23), (row3 1 2 24), (row3 1 2 25), (row3 1 2 26), (row3 1 2 27), (row3 1 2 28), (row3 1 2 29), (row3 1 2 30), (row3 1 2 31), (row3 1 2 32), (row3 1 2 33), (row3 1 2 34)]

def b000_01_labels : List Row := [(row3 181 435 42), (row3 462 180 180), (row3 462 462 462), (row3 180 180 462), (row3 42 435 181), (row3 72 428 336), (row3 65 54 65), (row3 336 428 72), (row3 462 193 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 208 208 462), (row3 337 462 337), (row3 462 208 208)]

theorem b000_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_01_rows b000_01_labels 1152627973753320030576071338200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_01_rows b000_01_labels]
    decide +kernel

def b000_02_rows : List Row := [(row3 1 2 35), (row3 1 2 36), (row3 1 2 37), (row3 1 2 38), (row3 1 2 39), (row3 1 2 40), (row3 1 2 41), (row3 1 2 42), (row3 1 2 43), (row3 1 2 44), (row3 1 2 45), (row3 1 2 46), (row3 1 2 47), (row3 1 2 48), (row3 1 2 49), (row3 1 2 50)]

def b000_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 72 428 336), (row3 65 54 65), (row3 336 428 72), (row3 462 193 193), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 193 462), (row3 444 28 37), (row3 447 455 447), (row3 37 28 444)]

theorem b000_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_02_rows b000_02_labels 16985439728061653708331619964940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_02_rows b000_02_labels]
    decide +kernel

def b000_03_rows : List Row := [(row3 1 2 51), (row3 1 2 52), (row3 1 2 53), (row3 1 2 54), (row3 1 2 55), (row3 1 2 56), (row3 1 2 57), (row3 1 2 58), (row3 1 2 59), (row3 1 2 60), (row3 1 2 61), (row3 1 2 62), (row3 1 2 63), (row3 1 3 4), (row3 1 3 5), (row3 1 3 6)]

def b000_03_labels : List Row := [(row3 181 435 42), (row3 462 180 180), (row3 462 462 462), (row3 180 180 462), (row3 42 435 181), (row3 22 460 450), (row3 19 18 19), (row3 450 460 22), (row3 47 26 453), (row3 95 435 41), (row3 193 163 193), (row3 41 435 95), (row3 453 26 47), (row3 355 374 364), (row3 335 96 205), (row3 75 425 326)]

theorem b000_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_03_rows b000_03_labels 3100134719403839109797617615232880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_03_rows b000_03_labels]
    decide +kernel

def b000_04_rows : List Row := [(row3 1 3 7), (row3 1 3 8), (row3 1 3 9), (row3 1 3 10), (row3 1 3 11), (row3 1 3 12), (row3 1 3 13), (row3 1 3 14), (row3 1 3 15), (row3 1 3 16), (row3 1 3 17), (row3 1 3 18), (row3 1 3 19), (row3 1 3 20), (row3 1 3 21), (row3 1 3 22)]

def b000_04_labels : List Row := [(row3 446 30 80), (row3 445 29 56), (row3 449 448 454), (row3 57 51 53), (row3 384 400 397), (row3 166 190 167), (row3 277 277 265), (row3 371 87 325), (row3 58 430 372), (row3 77 426 385), (row3 76 68 69), (row3 363 393 386), (row3 164 206 164), (row3 266 266 265), (row3 462 237 237), (row3 269 269 462)]

theorem b000_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_04_rows b000_04_labels 18316833944132563499722499116050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_04_rows b000_04_labels]
    decide +kernel

def b000_05_rows : List Row := [(row3 1 3 23), (row3 1 3 24), (row3 1 3 25), (row3 1 3 26), (row3 1 3 27), (row3 1 3 28), (row3 1 3 29), (row3 1 3 30), (row3 1 3 31), (row3 1 3 32), (row3 1 3 33), (row3 1 3 34), (row3 1 3 35), (row3 1 3 36), (row3 1 3 37), (row3 1 3 38)]

def b000_05_labels : List Row := [(row3 370 88 211), (row3 334 97 202), (row3 330 343 338), (row3 193 238 192), (row3 256 256 255), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 257 257 462), (row3 208 462 208), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b000_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_05_rows b000_05_labels 18089218245092446552444139850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_05_rows b000_05_labels]
    decide +kernel

def b000_06_rows : List Row := [(row3 1 3 39), (row3 1 3 40), (row3 1 3 41), (row3 1 3 42), (row3 1 3 43), (row3 1 3 44), (row3 1 3 45), (row3 1 3 46), (row3 1 3 47), (row3 1 3 48), (row3 1 3 49), (row3 1 3 50), (row3 1 3 51), (row3 1 3 52), (row3 1 3 53), (row3 1 3 54)]

def b000_06_labels : List Row := [(row3 462 462 462), (row3 334 97 202), (row3 330 343 338), (row3 193 238 192), (row3 256 256 255), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 77 426 385), (row3 76 68 69), (row3 363 393 386), (row3 164 206 164), (row3 266 266 265), (row3 462 237 237), (row3 269 269 462)]

theorem b000_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_06_rows b000_06_labels 192967135343640787611862865280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_06_rows b000_06_labels]
    decide +kernel

def b000_07_rows : List Row := [(row3 1 3 55), (row3 1 3 56), (row3 1 3 57), (row3 1 3 58), (row3 1 3 59), (row3 1 3 60), (row3 1 3 61), (row3 1 3 62), (row3 1 3 63), (row3 1 4 5), (row3 1 4 6), (row3 1 4 7), (row3 1 4 8), (row3 1 4 9), (row3 1 4 10), (row3 1 4 11)]

def b000_07_labels : List Row := [(row3 370 88 211), (row3 445 29 56), (row3 449 448 454), (row3 57 51 53), (row3 384 400 397), (row3 166 190 167), (row3 277 277 265), (row3 371 87 325), (row3 58 430 372), (row3 185 9 219), (row3 335 96 205), (row3 70 434 70), (row3 71 429 341), (row3 66 64 55), (row3 353 366 375), (row3 179 151 153)]

theorem b000_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_07_rows b000_07_labels 15042999054744117349822214860590 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_07_rows b000_07_labels]
    decide +kernel

def b000_08_rows : List Row := [(row3 1 4 12), (row3 1 4 13), (row3 1 4 14), (row3 1 4 15), (row3 1 4 16), (row3 1 4 17), (row3 1 4 18), (row3 1 4 19), (row3 1 4 20), (row3 1 4 21), (row3 1 4 22), (row3 1 4 23), (row3 1 4 24), (row3 1 4 25), (row3 1 4 26), (row3 1 4 27)]

def b000_08_labels : List Row := [(row3 269 462 269), (row3 238 462 238), (row3 169 10 217), (row3 357 90 187), (row3 333 94 168), (row3 328 339 342), (row3 180 154 154), (row3 270 462 270), (row3 239 462 239), (row3 242 462 242), (row3 462 462 462), (row3 170 10 218), (row3 203 8 254), (row3 208 201 201), (row3 263 462 263), (row3 462 462 462)]

theorem b000_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_08_rows b000_08_labels 19488616908648945847535066550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_08_rows b000_08_labels]
    decide +kernel

def b000_09_rows : List Row := [(row3 1 4 28), (row3 1 4 29), (row3 1 4 30), (row3 1 4 31), (row3 1 4 32), (row3 1 4 33), (row3 1 4 34), (row3 1 4 35), (row3 1 4 36), (row3 1 4 37), (row3 1 4 38), (row3 1 4 39), (row3 1 4 40), (row3 1 4 41), (row3 1 4 42), (row3 1 4 43)]

def b000_09_labels : List Row := [(row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 257 462 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 203 8 254), (row3 208 201 201), (row3 263 462 263), (row3 462 462 462)]

theorem b000_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_09_rows b000_09_labels 463771611686668379741902500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_09_rows b000_09_labels]
    decide +kernel

def b000_10_rows : List Row := [(row3 1 4 44), (row3 1 4 45), (row3 1 4 46), (row3 1 4 47), (row3 1 4 48), (row3 1 4 49), (row3 1 4 50), (row3 1 4 51), (row3 1 4 52), (row3 1 4 53), (row3 1 4 54), (row3 1 4 55), (row3 1 4 56), (row3 1 4 57), (row3 1 4 58), (row3 1 4 59)]

def b000_10_labels : List Row := [(row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 333 94 168), (row3 328 339 342), (row3 180 154 154), (row3 270 462 270), (row3 239 462 239), (row3 242 462 242), (row3 462 462 462), (row3 170 10 218), (row3 71 429 341), (row3 66 64 55), (row3 353 366 375), (row3 179 151 153)]

theorem b000_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_10_rows b000_10_labels 401594121833200128938618842650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_10_rows b000_10_labels]
    decide +kernel

def b000_11_rows : List Row := [(row3 1 4 60), (row3 1 4 61), (row3 1 4 62), (row3 1 4 63), (row3 1 5 6), (row3 1 5 7), (row3 1 5 8), (row3 1 5 9), (row3 1 5 10), (row3 1 5 11), (row3 1 5 12), (row3 1 5 13), (row3 1 5 14), (row3 1 5 15), (row3 1 5 16), (row3 1 5 17)]

def b000_11_labels : List Row := [(row3 269 462 269), (row3 238 462 238), (row3 169 10 217), (row3 357 90 187), (row3 355 374 364), (row3 80 30 446), (row3 66 55 64), (row3 71 341 429), (row3 357 187 90), (row3 169 217 10), (row3 238 238 462), (row3 269 269 462), (row3 179 153 151), (row3 353 375 366), (row3 328 342 339), (row3 333 168 94)]

theorem b000_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_11_rows b000_11_labels 4867802543869725026603177060100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_11_rows b000_11_labels]
    decide +kernel

def b000_12_rows : List Row := [(row3 1 5 18), (row3 1 5 19), (row3 1 5 20), (row3 1 5 21), (row3 1 5 22), (row3 1 5 23), (row3 1 5 24), (row3 1 5 25), (row3 1 5 26), (row3 1 5 27), (row3 1 5 28), (row3 1 5 29), (row3 1 5 30), (row3 1 5 31), (row3 1 5 32), (row3 1 5 33)]

def b000_12_labels : List Row := [(row3 170 218 10), (row3 462 462 462), (row3 242 242 462), (row3 239 239 462), (row3 270 270 462), (row3 180 154 154), (row3 208 201 201), (row3 203 254 8), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 240 462), (row3 462 462 462), (row3 263 263 462), (row3 257 257 462), (row3 462 462 462)]

theorem b000_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_12_rows b000_12_labels 1846960987599498486099135750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_12_rows b000_12_labels]
    decide +kernel

def b000_13_rows : List Row := [(row3 1 5 34), (row3 1 5 35), (row3 1 5 36), (row3 1 5 37), (row3 1 5 38), (row3 1 5 39), (row3 1 5 40), (row3 1 5 41), (row3 1 5 42), (row3 1 5 43), (row3 1 5 44), (row3 1 5 45), (row3 1 5 46), (row3 1 5 47), (row3 1 5 48), (row3 1 5 49)]

def b000_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 208 201 201), (row3 203 254 8), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 240 462), (row3 462 462 462), (row3 263 263 462), (row3 328 342 339), (row3 333 168 94)]

theorem b000_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_13_rows b000_13_labels 8457095522588444794370498550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_13_rows b000_13_labels]
    decide +kernel

def b000_14_rows : List Row := [(row3 1 5 50), (row3 1 5 51), (row3 1 5 52), (row3 1 5 53), (row3 1 5 54), (row3 1 5 55), (row3 1 5 56), (row3 1 5 57), (row3 1 5 58), (row3 1 5 59), (row3 1 5 60), (row3 1 5 61), (row3 1 5 62), (row3 1 5 63), (row3 1 6 7), (row3 1 6 8)]

def b000_14_labels : List Row := [(row3 170 218 10), (row3 462 462 462), (row3 242 242 462), (row3 239 239 462), (row3 270 270 462), (row3 180 154 154), (row3 66 55 64), (row3 71 341 429), (row3 357 187 90), (row3 169 217 10), (row3 238 238 462), (row3 269 269 462), (row3 179 153 151), (row3 353 375 366), (row3 441 459 21), (row3 449 454 448)]

theorem b000_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_14_rows b000_14_labels 874885616159387859103296741746910 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_14_rows b000_14_labels]
    decide +kernel

def b000_15_rows : List Row := [(row3 1 6 9), (row3 1 6 10), (row3 1 6 11), (row3 1 6 12), (row3 1 6 13), (row3 1 6 14), (row3 1 6 15), (row3 1 6 16), (row3 1 6 17), (row3 1 6 18), (row3 1 6 19), (row3 1 6 20), (row3 1 6 21), (row3 1 6 22), (row3 1 6 23), (row3 1 6 24)]

def b000_15_labels : List Row := [(row3 445 56 29), (row3 58 372 430), (row3 371 325 87), (row3 277 265 277), (row3 166 167 190), (row3 384 397 400), (row3 57 53 51), (row3 76 69 68), (row3 77 385 426), (row3 370 211 88), (row3 269 462 269), (row3 462 237 237), (row3 266 265 266), (row3 164 164 206), (row3 363 386 393), (row3 330 338 343)]

theorem b000_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b000_15_rows b000_15_labels 7241459115048302717759601735600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b000_15_rows b000_15_labels]
    decide +kernel

theorem checked000 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_000 QuarticIntegerComputationalData.ids64_000 8896572007308291438631480233874140 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b000_00_rows ++ b000_01_rows) ++ (b000_02_rows ++ b000_03_rows)) ++ ((b000_04_rows ++ b000_05_rows) ++ (b000_06_rows ++ b000_07_rows))) ++ (((b000_08_rows ++ b000_09_rows) ++ (b000_10_rows ++ b000_11_rows)) ++ ((b000_12_rows ++ b000_13_rows) ++ (b000_14_rows ++ b000_15_rows))))
    ((((b000_00_labels ++ b000_01_labels) ++ (b000_02_labels ++ b000_03_labels)) ++ ((b000_04_labels ++ b000_05_labels) ++ (b000_06_labels ++ b000_07_labels))) ++ (((b000_08_labels ++ b000_09_labels) ++ (b000_10_labels ++ b000_11_labels)) ++ ((b000_12_labels ++ b000_13_labels) ++ (b000_14_labels ++ b000_15_labels)))) 8896572007308291438631480233874140
  exact ((((b000_00_checked.append (c := 4858454230438755650507716091705940) b000_01_checked (by decide +kernel)).append (c := 7975574389570656414013665326903760) (b000_02_checked.append (c := 3117120159131900763505949235197820) b000_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 8009145278923121828097374347885530) ((b000_04_checked.append (c := 18334923162377655946274943255900) b000_05_checked (by decide +kernel)).append (c := 33570889352465414083709020981770) (b000_06_checked.append (c := 15235966190087758137434077725870) b000_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 8896572007308291438631480233874140) (((b000_08_checked.append (c := 19952388520335614227276969050) b000_09_checked (by decide +kernel)).append (c := 5289349054223260769769072871800) (b000_10_checked.append (c := 5269396665702925155541795902750) b000_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 887426728385169610534105885988610) ((b000_12_checked.append (c := 10304056510187943280469634300) b000_13_checked (by decide +kernel)).append (c := 882137379330946349764336813116810) (b000_14_checked.append (c := 882127075274436161821056343482510) b000_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

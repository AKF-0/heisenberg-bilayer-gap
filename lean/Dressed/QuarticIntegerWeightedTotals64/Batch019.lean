import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch018
import Dressed.QuarticIntegerComputationalData64.Batch019


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b153_00_rows : List Row := [(row3 48 50 54), (row3 48 50 55), (row3 48 50 56), (row3 48 50 57), (row3 48 50 58), (row3 48 50 59), (row3 48 50 60), (row3 48 50 61), (row3 48 50 62), (row3 48 50 63), (row3 48 51 52), (row3 48 51 53), (row3 48 51 54), (row3 48 51 55), (row3 48 51 56), (row3 48 51 57)]

def b153_00_labels : List Row := [(row3 327 327 327), (row3 68 76 69), (row3 28 444 37), (row3 406 405 406), (row3 367 84 108), (row3 288 462 288), (row3 234 462 234), (row3 261 462 261), (row3 182 178 182), (row3 348 350 351), (row3 239 462 239), (row3 255 256 256), (row3 209 209 206), (row3 339 328 342), (row3 428 72 336), (row3 109 111 110)]

theorem b153_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_00_rows b153_00_labels 4797520490151279687741101531970 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_00_rows b153_00_labels]
    decide +kernel

def b153_01_rows : List Row := [(row3 48 51 58), (row3 48 51 59), (row3 48 51 60), (row3 48 51 61), (row3 48 51 62), (row3 48 51 63), (row3 48 52 53), (row3 48 52 54), (row3 48 52 55), (row3 48 52 56), (row3 48 52 57), (row3 48 52 58), (row3 48 52 59), (row3 48 52 60), (row3 48 52 61), (row3 48 52 62)]

def b153_01_labels : List Row := [(row3 315 318 318), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 265 268 268), (row3 199 198 190), (row3 239 239 462), (row3 273 273 462), (row3 168 333 94), (row3 208 208 462), (row3 261 290 288), (row3 223 223 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 223 224)]

theorem b153_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_01_rows b153_01_labels 3769839386156605365074961000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_01_rows b153_01_labels]
    decide +kernel

def b153_02_rows : List Row := [(row3 48 52 63), (row3 48 53 54), (row3 48 53 55), (row3 48 53 56), (row3 48 53 57), (row3 48 53 58), (row3 48 53 59), (row3 48 53 60), (row3 48 53 61), (row3 48 53 62), (row3 48 53 63), (row3 48 54 55), (row3 48 54 56), (row3 48 54 57), (row3 48 54 58), (row3 48 54 59)]

def b153_02_labels : List Row := [(row3 261 290 288), (row3 164 164 206), (row3 385 77 426), (row3 428 72 336), (row3 199 198 190), (row3 265 268 268), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 315 318 318), (row3 109 111 110), (row3 37 444 28), (row3 28 444 37), (row3 348 350 351), (row3 182 178 182), (row3 261 462 261)]

theorem b153_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_02_rows b153_02_labels 9192351067870095497575058985000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_02_rows b153_02_labels]
    decide +kernel

def b153_03_rows : List Row := [(row3 48 54 60), (row3 48 54 61), (row3 48 54 62), (row3 48 54 63), (row3 48 55 56), (row3 48 55 57), (row3 48 55 58), (row3 48 55 59), (row3 48 55 60), (row3 48 55 61), (row3 48 55 62), (row3 48 55 63), (row3 48 56 57), (row3 48 56 58), (row3 48 56 59), (row3 48 56 60)]

def b153_03_labels : List Row := [(row3 234 462 234), (row3 288 462 288), (row3 367 84 108), (row3 406 405 406), (row3 460 22 450), (row3 48 50 61), (row3 388 392 362), (row3 191 235 193), (row3 462 284 284), (row3 121 85 369), (row3 411 432 60), (row3 451 24 442), (row3 18 19 19), (row3 455 447 447), (row3 54 65 65), (row3 462 337 337)]

theorem b153_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_03_rows b153_03_labels 2140885180411775137424530740941310 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_03_rows b153_03_labels]
    decide +kernel

def b153_04_rows : List Row := [(row3 48 56 61), (row3 48 56 62), (row3 48 56 63), (row3 48 57 58), (row3 48 57 59), (row3 48 57 60), (row3 48 57 61), (row3 48 57 62), (row3 48 57 63), (row3 48 58 59), (row3 48 58 60), (row3 48 58 61), (row3 48 58 62), (row3 48 58 63), (row3 48 59 60), (row3 48 59 61)]

def b153_04_labels : List Row := [(row3 54 65 65), (row3 455 447 447), (row3 18 19 19), (row3 38 33 33), (row3 379 380 380), (row3 161 176 176), (row3 288 288 288), (row3 107 106 106), (row3 420 421 421), (row3 130 104 104), (row3 289 291 291), (row3 226 229 229), (row3 306 314 314), (row3 107 106 106), (row3 462 462 462), (row3 462 462 462)]

theorem b153_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_04_rows b153_04_labels 1143904874185518984732320037024300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_04_rows b153_04_labels]
    decide +kernel

def b153_05_rows : List Row := [(row3 48 59 62), (row3 48 59 63), (row3 48 60 61), (row3 48 60 62), (row3 48 60 63), (row3 48 61 62), (row3 48 61 63), (row3 48 62 63), (row3 49 50 51), (row3 49 50 52), (row3 49 50 53), (row3 49 50 54), (row3 49 50 55), (row3 49 50 56), (row3 49 50 57), (row3 49 50 58)]

def b153_05_labels : List Row := [(row3 226 229 229), (row3 288 288 288), (row3 462 462 462), (row3 289 291 291), (row3 161 176 176), (row3 130 104 104), (row3 379 380 380), (row3 38 33 33), (row3 181 435 42), (row3 211 88 370), (row3 218 10 170), (row3 154 154 180), (row3 393 386 363), (row3 424 422 418), (row3 25 452 32), (row3 46 440 46)]

theorem b153_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_05_rows b153_05_labels 20735417205711560080904641397730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_05_rows b153_05_labels]
    decide +kernel

def b153_06_rows : List Row := [(row3 49 50 59), (row3 49 50 60), (row3 49 50 61), (row3 49 50 62), (row3 49 50 63), (row3 49 51 52), (row3 49 51 53), (row3 49 51 54), (row3 49 51 55), (row3 49 51 56), (row3 49 51 57), (row3 49 51 58), (row3 49 51 59), (row3 49 51 60), (row3 49 51 61), (row3 49 51 62)]

def b153_06_labels : List Row := [(row3 134 81 398), (row3 214 11 117), (row3 462 462 462), (row3 287 462 287), (row3 102 103 129), (row3 266 266 265), (row3 237 462 237), (row3 267 267 265), (row3 178 183 183), (row3 137 126 127), (row3 431 59 410), (row3 99 101 98), (row3 305 305 289), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235)]

theorem b153_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_06_rows b153_06_labels 202095133404439272211444223610 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_06_rows b153_06_labels]
    decide +kernel

def b153_07_rows : List Row := [(row3 49 51 63), (row3 49 52 53), (row3 49 52 54), (row3 49 52 55), (row3 49 52 56), (row3 49 52 57), (row3 49 52 58), (row3 49 52 59), (row3 49 52 60), (row3 49 52 61), (row3 49 52 62), (row3 49 52 63), (row3 49 53 54), (row3 49 53 55), (row3 49 53 56), (row3 49 53 57)]

def b153_07_labels : List Row := [(row3 291 291 289), (row3 242 462 242), (row3 235 235 237), (row3 281 278 281), (row3 279 278 279), (row3 91 356 159), (row3 320 319 320), (row3 226 226 234), (row3 243 462 243), (row3 462 462 462), (row3 247 462 247), (row3 234 226 226), (row3 270 270 462), (row3 183 183 178), (row3 235 162 163), (row3 269 269 462)]

theorem b153_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_07_rows b153_07_labels 7521934227392035301578335720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_07_rows b153_07_labels]
    decide +kernel

def b153_08_rows : List Row := [(row3 49 53 58), (row3 49 53 59), (row3 49 53 60), (row3 49 53 61), (row3 49 53 62), (row3 49 53 63), (row3 49 54 55), (row3 49 54 56), (row3 49 54 57), (row3 49 54 58), (row3 49 54 59), (row3 49 54 60), (row3 49 54 61), (row3 49 54 62), (row3 49 54 63), (row3 49 55 56)]

def b153_08_labels : List Row := [(row3 235 228 232), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 311 311 306), (row3 363 386 393), (row3 415 407 395), (row3 89 356 158), (row3 283 278 283), (row3 234 234 234), (row3 245 462 245), (row3 235 462 235), (row3 173 10 260), (row3 120 112 120), (row3 33 33 38)]

theorem b153_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_08_rows b153_08_labels 1672715577410815159739553920100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_08_rows b153_08_labels]
    decide +kernel

def b153_09_rows : List Row := [(row3 49 55 57), (row3 49 55 58), (row3 49 55 59), (row3 49 55 60), (row3 49 55 61), (row3 49 55 62), (row3 49 55 63), (row3 49 56 57), (row3 49 56 58), (row3 49 56 59), (row3 49 56 60), (row3 49 56 61), (row3 49 56 62), (row3 49 56 63), (row3 49 57 58), (row3 49 57 59)]

def b153_09_labels : List Row := [(row3 432 60 411), (row3 136 141 142), (row3 292 292 289), (row3 235 235 232), (row3 292 292 289), (row3 141 136 142), (row3 60 432 411), (row3 23 457 461), (row3 48 61 50), (row3 376 354 366), (row3 232 193 189), (row3 373 352 365), (row3 49 62 52), (row3 456 456 458), (row3 456 458 456), (row3 49 52 62)]

theorem b153_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_09_rows b153_09_labels 1111291856443688522454528179918520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_09_rows b153_09_labels]
    decide +kernel

def b153_10_rows : List Row := [(row3 49 57 60), (row3 49 57 61), (row3 49 57 62), (row3 49 57 63), (row3 49 58 59), (row3 49 58 60), (row3 49 58 61), (row3 49 58 62), (row3 49 58 63), (row3 49 59 60), (row3 49 59 61), (row3 49 59 62), (row3 49 59 63), (row3 49 60 61), (row3 49 60 62), (row3 49 60 63)]

def b153_10_labels : List Row := [(row3 373 365 352), (row3 232 189 193), (row3 376 366 354), (row3 48 50 61), (row3 396 416 408), (row3 146 137 143), (row3 282 282 278), (row3 221 222 220), (row3 324 324 323), (row3 286 462 286), (row3 235 462 235), (row3 252 462 252), (row3 221 222 220), (row3 462 462 462), (row3 235 462 235), (row3 282 282 278)]

theorem b153_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_10_rows b153_10_labels 1432251602942839027100861554770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_10_rows b153_10_labels]
    decide +kernel

def b153_11_rows : List Row := [(row3 49 61 62), (row3 49 61 63), (row3 49 62 63), (row3 50 51 52), (row3 50 51 53), (row3 50 51 54), (row3 50 51 55), (row3 50 51 56), (row3 50 51 57), (row3 50 51 58), (row3 50 51 59), (row3 50 51 60), (row3 50 51 61), (row3 50 51 62), (row3 50 51 63), (row3 50 52 53)]

def b153_11_labels : List Row := [(row3 286 462 286), (row3 146 137 143), (row3 396 416 408), (row3 462 180 180), (row3 462 269 269), (row3 462 462 462), (row3 462 270 270), (row3 462 307 307), (row3 113 100 100), (row3 436 45 389), (row3 163 124 139), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237)]

theorem b153_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_11_rows b153_11_labels 465873026697945977508456428430 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_11_rows b153_11_labels]
    decide +kernel

def b153_12_rows : List Row := [(row3 50 52 54), (row3 50 52 55), (row3 50 52 56), (row3 50 52 57), (row3 50 52 58), (row3 50 52 59), (row3 50 52 60), (row3 50 52 61), (row3 50 52 62), (row3 50 52 63), (row3 50 53 54), (row3 50 53 55), (row3 50 53 56), (row3 50 53 57), (row3 50 53 58), (row3 50 53 59)]

def b153_12_labels : List Row := [(row3 462 462 462), (row3 237 235 235), (row3 462 234 234), (row3 462 300 300), (row3 86 368 114), (row3 288 300 278), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 267 267), (row3 462 285 285), (row3 462 235 235), (row3 10 172 258), (row3 232 228 235)]

theorem b153_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_12_rows b153_12_labels 10544683137131697932813359860 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_12_rows b153_12_labels]
    decide +kernel

def b153_13_rows : List Row := [(row3 50 53 60), (row3 50 53 61), (row3 50 53 62), (row3 50 53 63), (row3 50 54 55), (row3 50 54 56), (row3 50 54 57), (row3 50 54 58), (row3 50 54 59), (row3 50 54 60), (row3 50 54 61), (row3 50 54 62), (row3 50 54 63), (row3 50 55 56), (row3 50 55 57), (row3 50 55 58)]

def b153_13_labels : List Row := [(row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 180 154 154), (row3 105 105 131), (row3 462 288 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 407 415 395), (row3 112 120 120), (row3 10 173 260)]

theorem b153_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_13_rows b153_13_labels 42105192716560606225030553670 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_13_rows b153_13_labels]
    decide +kernel

def b153_14_rows : List Row := [(row3 50 55 59), (row3 50 55 60), (row3 50 55 61), (row3 50 55 62), (row3 50 55 63), (row3 50 56 57), (row3 50 56 58), (row3 50 56 59), (row3 50 56 60), (row3 50 56 61), (row3 50 56 62), (row3 50 56 63), (row3 50 57 58), (row3 50 57 59), (row3 50 57 60), (row3 50 57 61)]

def b153_14_labels : List Row := [(row3 462 235 235), (row3 462 245 245), (row3 234 234 234), (row3 278 283 283), (row3 356 89 158), (row3 452 32 25), (row3 409 394 414), (row3 152 177 150), (row3 462 272 272), (row3 154 180 154), (row3 387 361 391), (row3 36 35 31), (row3 452 32 25), (row3 378 382 381), (row3 161 175 175), (row3 462 273 273)]

theorem b153_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_14_rows b153_14_labels 30365860395438829116612635902830 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_14_rows b153_14_labels]
    decide +kernel

def b153_15_rows : List Row := [(row3 50 57 62), (row3 50 57 63), (row3 50 58 59), (row3 50 58 60), (row3 50 58 61), (row3 50 58 62), (row3 50 58 63), (row3 50 59 60), (row3 50 59 61), (row3 50 59 62), (row3 50 59 63), (row3 50 60 61), (row3 50 60 62), (row3 50 60 63), (row3 50 61 62), (row3 50 61 63)]

def b153_15_labels : List Row := [(row3 161 175 175), (row3 378 381 382), (row3 36 31 35), (row3 387 391 361), (row3 154 154 180), (row3 462 272 272), (row3 152 150 177), (row3 163 228 160), (row3 273 462 273), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 273 462 273)]

theorem b153_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b153_15_rows b153_15_labels 836503405417572416642702534130 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b153_15_rows b153_15_labels]
    decide +kernel

theorem checked153 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_153 QuarticIntegerComputationalData.ids64_153 4465846440595495261792239911572950 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b153_00_rows ++ b153_01_rows) ++ (b153_02_rows ++ b153_03_rows)) ++ ((b153_04_rows ++ b153_05_rows) ++ (b153_06_rows ++ b153_07_rows))) ++ (((b153_08_rows ++ b153_09_rows) ++ (b153_10_rows ++ b153_11_rows)) ++ ((b153_12_rows ++ b153_13_rows) ++ (b153_14_rows ++ b153_15_rows))))
    ((((b153_00_labels ++ b153_01_labels) ++ (b153_02_labels ++ b153_03_labels)) ++ ((b153_04_labels ++ b153_05_labels) ++ (b153_06_labels ++ b153_07_labels))) ++ (((b153_08_labels ++ b153_09_labels) ++ (b153_10_labels ++ b153_11_labels)) ++ ((b153_12_labels ++ b153_13_labels) ++ (b153_14_labels ++ b153_15_labels)))) 4465846440595495261792239911572950
  exact ((((b153_00_checked.append (c := 4801290329537436293106176492970) b153_01_checked (by decide +kernel)).append (c := 2154878821809182669215211976419280) (b153_02_checked.append (c := 2150077531479645232922105799926310) b153_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3319728730268045045335949677400640) ((b153_04_checked.append (c := 1164640291391230544813224678422030) b153_05_checked (by decide +kernel)).append (c := 1164849908458862376120737700981360) (b153_06_checked.append (c := 209617067631831307513022559330) b153_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4465846440595495261792239911572950) (((b153_08_checked.append (c := 1112964572021099337614267733838620) b153_09_checked (by decide +kernel)).append (c := 1114862696650740122618877051821820) (b153_10_checked.append (c := 1898124629640785004609317983200) b153_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1146117710327450216456290234172310) ((b153_12_checked.append (c := 52649875853692304157843913530) b153_13_checked (by decide +kernel)).append (c := 31255013676710093837413182350490) (b153_14_checked.append (c := 31202363800856401533255338436960) b153_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b154_00_rows : List Row := [(row3 50 62 63), (row3 51 52 53), (row3 51 52 54), (row3 51 52 55), (row3 51 52 56), (row3 51 52 57), (row3 51 52 58), (row3 51 52 59), (row3 51 52 60), (row3 51 52 61), (row3 51 52 62), (row3 51 52 63), (row3 51 53 54), (row3 51 53 55), (row3 51 53 56), (row3 51 53 57)]

def b154_00_labels : List Row := [(row3 163 228 160), (row3 462 462 462), (row3 237 237 462), (row3 242 462 242), (row3 462 462 462), (row3 462 232 232), (row3 309 306 309), (row3 163 163 462), (row3 462 462 462), (row3 232 232 462), (row3 246 462 246), (row3 462 462 462), (row3 269 269 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b154_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_00_rows b154_00_labels 2214350157908872964937466800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_00_rows b154_00_labels]
    decide +kernel

def b154_01_rows : List Row := [(row3 51 53 58), (row3 51 53 59), (row3 51 53 60), (row3 51 53 61), (row3 51 53 62), (row3 51 53 63), (row3 51 54 55), (row3 51 54 56), (row3 51 54 57), (row3 51 54 58), (row3 51 54 59), (row3 51 54 60), (row3 51 54 61), (row3 51 54 62), (row3 51 54 63), (row3 51 55 56)]

def b154_01_labels : List Row := [(row3 462 232 232), (row3 284 284 462), (row3 462 462 462), (row3 284 284 462), (row3 232 462 232), (row3 462 462 462), (row3 170 10 218), (row3 285 462 285), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 228 232 235), (row3 172 10 258), (row3 235 462 235), (row3 162 235 163)]

theorem b154_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_01_rows b154_01_labels 1976305802434602990798359250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_01_rows b154_01_labels]
    decide +kernel

def b154_02_rows : List Row := [(row3 51 55 57), (row3 51 55 58), (row3 51 55 59), (row3 51 55 60), (row3 51 55 61), (row3 51 55 62), (row3 51 55 63), (row3 51 56 57), (row3 51 56 58), (row3 51 56 59), (row3 51 56 60), (row3 51 56 61), (row3 51 56 62), (row3 51 56 63), (row3 51 57 58), (row3 51 57 59)]

def b154_02_labels : List Row := [(row3 311 311 306), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 228 235 232), (row3 269 269 462), (row3 43 383 436), (row3 133 132 137), (row3 274 274 462), (row3 462 462 462), (row3 264 264 462), (row3 191 193 235), (row3 358 358 462), (row3 39 412 437), (row3 133 132 137)]

theorem b154_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_02_rows b154_02_labels 753798443073331213006036068660 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_02_rows b154_02_labels]
    decide +kernel

def b154_03_rows : List Row := [(row3 51 57 60), (row3 51 57 61), (row3 51 57 62), (row3 51 57 63), (row3 51 58 59), (row3 51 58 60), (row3 51 58 61), (row3 51 58 62), (row3 51 58 63), (row3 51 59 60), (row3 51 59 61), (row3 51 59 62), (row3 51 59 63), (row3 51 60 61), (row3 51 60 62), (row3 51 60 63)]

def b154_03_labels : List Row := [(row3 279 278 279), (row3 462 235 235), (row3 280 278 280), (row3 149 146 137), (row3 43 383 436), (row3 149 137 146), (row3 280 280 278), (row3 462 235 235), (row3 279 279 278), (row3 358 462 358), (row3 191 235 193), (row3 264 462 264), (row3 462 462 462), (row3 284 284 462), (row3 235 462 235), (row3 462 462 462)]

theorem b154_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_03_rows b154_03_labels 387466378415755963309525171980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_03_rows b154_03_labels]
    decide +kernel

def b154_04_rows : List Row := [(row3 51 61 62), (row3 51 61 63), (row3 51 62 63), (row3 52 53 54), (row3 52 53 55), (row3 52 53 56), (row3 52 53 57), (row3 52 53 58), (row3 52 53 59), (row3 52 53 60), (row3 52 53 61), (row3 52 53 62), (row3 52 53 63), (row3 52 54 55), (row3 52 54 56), (row3 52 54 57)]

def b154_04_labels : List Row := [(row3 115 11 212), (row3 235 462 235), (row3 284 284 462), (row3 180 180 462), (row3 265 266 266), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 232 232 462), (row3 462 462 462), (row3 163 163 462), (row3 306 309 309), (row3 232 462 232), (row3 370 88 211), (row3 234 462 234), (row3 462 462 462)]

theorem b154_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_04_rows b154_04_labels 13559300967530945610557649450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_04_rows b154_04_labels]
    decide +kernel

def b154_05_rows : List Row := [(row3 52 54 58), (row3 52 54 59), (row3 52 54 60), (row3 52 54 61), (row3 52 54 62), (row3 52 54 63), (row3 52 55 56), (row3 52 55 57), (row3 52 55 58), (row3 52 55 59), (row3 52 55 60), (row3 52 55 61), (row3 52 55 62), (row3 52 55 63), (row3 52 56 57), (row3 52 56 58)]

def b154_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 300 288 278), (row3 368 86 114), (row3 300 462 300), (row3 278 279 279), (row3 226 234 226), (row3 462 247 247), (row3 462 462 462), (row3 462 243 243), (row3 226 226 234), (row3 319 320 320), (row3 356 91 159), (row3 163 462 163), (row3 289 291 291)]

theorem b154_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_05_rows b154_05_labels 17690778073608919611970493160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_05_rows b154_05_labels]
    decide +kernel

def b154_06_rows : List Row := [(row3 52 56 59), (row3 52 56 60), (row3 52 56 61), (row3 52 56 62), (row3 52 56 63), (row3 52 57 58), (row3 52 57 59), (row3 52 57 60), (row3 52 57 61), (row3 52 57 62), (row3 52 57 63), (row3 52 58 59), (row3 52 58 60), (row3 52 58 61), (row3 52 58 62), (row3 52 58 63)]

def b154_06_labels : List Row := [(row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 289 291 291), (row3 163 462 163), (row3 399 157 83), (row3 288 288 462), (row3 236 236 462), (row3 462 462 462), (row3 231 231 234), (row3 288 273 273), (row3 399 157 83), (row3 289 291 291), (row3 231 231 234), (row3 462 246 246), (row3 231 234 231)]

theorem b154_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_06_rows b154_06_labels 42041614494748571643113805240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_06_rows b154_06_labels]
    decide +kernel

def b154_07_rows : List Row := [(row3 52 59 60), (row3 52 59 61), (row3 52 59 62), (row3 52 59 63), (row3 52 60 61), (row3 52 60 62), (row3 52 60 63), (row3 52 61 62), (row3 52 61 63), (row3 52 62 63), (row3 53 54 55), (row3 53 54 56), (row3 53 54 57), (row3 53 54 58), (row3 53 54 59), (row3 53 54 60)]

def b154_07_labels : List Row := [(row3 163 462 163), (row3 288 273 273), (row3 231 234 231), (row3 462 462 462), (row3 163 163 462), (row3 289 291 291), (row3 236 462 236), (row3 399 83 157), (row3 288 462 288), (row3 399 83 157), (row3 42 435 181), (row3 307 462 307), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293)]

theorem b154_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_07_rows b154_07_labels 398409432930149495258308937490 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_07_rows b154_07_labels]
    decide +kernel

def b154_08_rows : List Row := [(row3 53 54 61), (row3 53 54 62), (row3 53 54 63), (row3 53 55 56), (row3 53 55 57), (row3 53 55 58), (row3 53 55 59), (row3 53 55 60), (row3 53 55 61), (row3 53 55 62), (row3 53 55 63), (row3 53 56 57), (row3 53 56 58), (row3 53 56 59), (row3 53 56 60), (row3 53 56 61)]

def b154_08_labels : List Row := [(row3 124 163 139), (row3 45 436 389), (row3 100 113 100), (row3 126 137 127), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 305 305 289), (row3 101 99 98), (row3 59 431 410), (row3 358 358 462), (row3 191 193 235), (row3 264 264 462), (row3 462 462 462), (row3 274 274 462)]

theorem b154_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_08_rows b154_08_labels 581534424039969034133190217800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_08_rows b154_08_labels]
    decide +kernel

def b154_09_rows : List Row := [(row3 53 56 62), (row3 53 56 63), (row3 53 57 58), (row3 53 57 59), (row3 53 57 60), (row3 53 57 61), (row3 53 57 62), (row3 53 57 63), (row3 53 58 59), (row3 53 58 60), (row3 53 58 61), (row3 53 58 62), (row3 53 58 63), (row3 53 59 60), (row3 53 59 61), (row3 53 59 62)]

def b154_09_labels : List Row := [(row3 133 132 137), (row3 43 383 436), (row3 284 462 284), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279), (row3 149 137 146), (row3 115 212 11), (row3 235 235 462), (row3 264 264 462), (row3 462 235 235), (row3 280 280 278), (row3 284 462 284), (row3 191 193 235), (row3 280 278 280)]

theorem b154_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_09_rows b154_09_labels 387950501423306966940615727590 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_09_rows b154_09_labels]
    decide +kernel

def b154_10_rows : List Row := [(row3 53 59 63), (row3 53 60 61), (row3 53 60 62), (row3 53 60 63), (row3 53 61 62), (row3 53 61 63), (row3 53 62 63), (row3 54 55 56), (row3 54 55 57), (row3 54 55 58), (row3 54 55 59), (row3 54 55 60), (row3 54 55 61), (row3 54 55 62), (row3 54 55 63), (row3 54 56 57)]

def b154_10_labels : List Row := [(row3 462 235 235), (row3 358 358 462), (row3 149 146 137), (row3 279 279 278), (row3 43 436 383), (row3 133 137 132), (row3 39 437 412), (row3 422 424 418), (row3 103 102 129), (row3 462 287 287), (row3 462 462 462), (row3 11 214 117), (row3 81 134 398), (row3 440 46 46), (row3 452 25 32), (row3 36 35 31)]

theorem b154_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_10_rows b154_10_labels 20312092563902624101206269794650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_10_rows b154_10_labels]
    decide +kernel

def b154_11_rows : List Row := [(row3 54 56 58), (row3 54 56 59), (row3 54 56 60), (row3 54 56 61), (row3 54 56 62), (row3 54 56 63), (row3 54 57 58), (row3 54 57 59), (row3 54 57 60), (row3 54 57 61), (row3 54 57 62), (row3 54 57 63), (row3 54 58 59), (row3 54 58 60), (row3 54 58 61), (row3 54 58 62)]

def b154_11_labels : List Row := [(row3 387 361 391), (row3 154 180 154), (row3 462 272 272), (row3 152 177 150), (row3 409 394 414), (row3 452 32 25), (row3 163 160 228), (row3 273 273 462), (row3 236 236 462), (row3 462 462 462), (row3 152 177 150), (row3 378 382 381), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 272 272)]

theorem b154_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_11_rows b154_11_labels 15785782502522173647049015715070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_11_rows b154_11_labels]
    decide +kernel

def b154_12_rows : List Row := [(row3 54 58 63), (row3 54 59 60), (row3 54 59 61), (row3 54 59 62), (row3 54 59 63), (row3 54 60 61), (row3 54 60 62), (row3 54 60 63), (row3 54 61 62), (row3 54 61 63), (row3 54 62 63), (row3 55 56 57), (row3 55 56 58), (row3 55 56 59), (row3 55 56 60), (row3 55 56 61)]

def b154_12_labels : List Row := [(row3 161 175 175), (row3 462 462 462), (row3 273 273 462), (row3 154 180 154), (row3 462 273 273), (row3 163 160 228), (row3 387 361 391), (row3 161 175 175), (row3 36 35 31), (row3 378 381 382), (row3 452 25 32), (row3 456 456 458), (row3 49 62 52), (row3 373 352 365), (row3 232 193 189), (row3 376 354 366)]

theorem b154_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_12_rows b154_12_labels 33336736415556020594967847375530 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_12_rows b154_12_labels]
    decide +kernel

def b154_13_rows : List Row := [(row3 55 56 62), (row3 55 56 63), (row3 55 57 58), (row3 55 57 59), (row3 55 57 60), (row3 55 57 61), (row3 55 57 62), (row3 55 57 63), (row3 55 58 59), (row3 55 58 60), (row3 55 58 61), (row3 55 58 62), (row3 55 58 63), (row3 55 59 60), (row3 55 59 61), (row3 55 59 62)]

def b154_13_labels : List Row := [(row3 48 61 50), (row3 23 457 461), (row3 396 408 416), (row3 146 143 137), (row3 282 278 282), (row3 221 220 222), (row3 324 323 324), (row3 48 61 50), (row3 286 286 462), (row3 235 235 462), (row3 252 252 462), (row3 221 220 222), (row3 376 354 366), (row3 462 462 462), (row3 235 235 462), (row3 282 278 282)]

theorem b154_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_13_rows b154_13_labels 1074853424813973156580884973880340 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_13_rows b154_13_labels]
    decide +kernel

def b154_14_rows : List Row := [(row3 55 59 63), (row3 55 60 61), (row3 55 60 62), (row3 55 60 63), (row3 55 61 62), (row3 55 61 63), (row3 55 62 63), (row3 56 57 58), (row3 56 57 59), (row3 56 57 60), (row3 56 57 61), (row3 56 57 62), (row3 56 57 63), (row3 56 58 59), (row3 56 58 60), (row3 56 58 61)]

def b154_14_labels : List Row := [(row3 232 193 189), (row3 286 286 462), (row3 146 143 137), (row3 373 352 365), (row3 396 408 416), (row3 49 62 52), (row3 456 456 458), (row3 450 460 22), (row3 56 29 445), (row3 341 429 71), (row3 64 55 66), (row3 448 454 449), (row3 18 19 19), (row3 384 400 397), (row3 174 178 174), (row3 329 344 340)]

theorem b154_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_14_rows b154_14_labels 2135694015248218874551508642225850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_14_rows b154_14_labels]
    decide +kernel

def b154_15_rows : List Row := [(row3 56 58 62), (row3 56 58 63), (row3 56 59 60), (row3 56 59 61), (row3 56 59 62), (row3 56 59 63), (row3 56 60 61), (row3 56 60 62), (row3 56 60 63), (row3 56 61 62), (row3 56 61 63), (row3 56 62 63), (row3 57 58 59), (row3 57 58 60), (row3 57 58 61), (row3 57 58 62)]

def b154_15_labels : List Row := [(row3 79 67 67), (row3 448 449 454), (row3 269 462 269), (row3 207 200 200), (row3 329 340 344), (row3 64 66 55), (row3 269 269 462), (row3 174 174 178), (row3 341 71 429), (row3 384 397 400), (row3 56 445 29), (row3 450 22 460), (row3 47 26 453), (row3 372 430 58), (row3 187 90 357), (row3 366 375 353)]

theorem b154_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b154_15_rows b154_15_labels 995255572759825495237949181027540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b154_15_rows b154_15_labels]
    decide +kernel

theorem checked154 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_154 QuarticIntegerComputationalData.ids64_154 4277824265833377089299034983916400 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b154_00_rows ++ b154_01_rows) ++ (b154_02_rows ++ b154_03_rows)) ++ ((b154_04_rows ++ b154_05_rows) ++ (b154_06_rows ++ b154_07_rows))) ++ (((b154_08_rows ++ b154_09_rows) ++ (b154_10_rows ++ b154_11_rows)) ++ ((b154_12_rows ++ b154_13_rows) ++ (b154_14_rows ++ b154_15_rows))))
    ((((b154_00_labels ++ b154_01_labels) ++ (b154_02_labels ++ b154_03_labels)) ++ ((b154_04_labels ++ b154_05_labels) ++ (b154_06_labels ++ b154_07_labels))) ++ (((b154_08_labels ++ b154_09_labels) ++ (b154_10_labels ++ b154_11_labels)) ++ ((b154_12_labels ++ b154_13_labels) ++ (b154_14_labels ++ b154_15_labels)))) 4277824265833377089299034983916400
  exact ((((b154_00_checked.append (c := 4190655960343475955735826050) b154_01_checked (by decide +kernel)).append (c := 1145455477449430652271297066690) (b154_02_checked.append (c := 1141264821489087176315561240640) b154_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1617156603915468584395247952030) ((b154_04_checked.append (c := 31250079041139865222528142610) b154_05_checked (by decide +kernel)).append (c := 471701126466037932123950885340) (b154_06_checked.append (c := 440451047424898066901422742730) b154_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4277824265833377089299034983916400) (((b154_08_checked.append (c := 969484925463276001073805945390) b154_09_checked (by decide +kernel)).append (c := 37067359991888073749329091455110) (b154_10_checked.append (c := 36097875066424797748255285509720) b154_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4276207109229461620714639735964370) ((b154_12_checked.append (c := 1108190161229529177175852821255870) b154_13_checked (by decide +kernel)).append (c := 4239139749237573546965310644509260) (b154_14_checked.append (c := 3130949588008044369789457823253390) b154_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b155_00_rows : List Row := [(row3 57 58 63), (row3 57 59 60), (row3 57 59 61), (row3 57 59 62), (row3 57 59 63), (row3 57 60 61), (row3 57 60 62), (row3 57 60 63), (row3 57 61 62), (row3 57 61 63), (row3 57 62 63), (row3 58 59 60), (row3 58 59 61), (row3 58 59 62), (row3 58 59 63), (row3 58 60 61)]

def b155_00_labels : List Row := [(row3 51 53 57), (row3 166 190 167), (row3 273 462 273), (row3 194 188 195), (row3 350 346 349), (row3 238 462 238), (row3 275 276 276), (row3 165 176 165), (row3 179 153 151), (row3 349 346 350), (row3 57 53 51), (row3 95 435 41), (row3 325 87 371), (row3 217 10 169), (row3 151 153 179), (row3 277 277 265)]

theorem b155_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b155_00_rows b155_00_labels 3157743297380389480482325177500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b155_00_rows b155_00_labels]
    decide +kernel

def b155_01_rows : List Row := [(row3 58 60 62), (row3 58 60 63), (row3 58 61 62), (row3 58 61 63), (row3 58 62 63), (row3 59 60 61), (row3 59 60 62), (row3 59 60 63), (row3 59 61 62), (row3 59 61 63), (row3 59 62 63), (row3 60 61 62), (row3 60 61 63), (row3 60 62 63), (row3 61 62 63)]

def b155_01_labels : List Row := [(row3 235 462 235), (row3 276 276 275), (row3 169 10 217), (row3 195 188 194), (row3 353 375 366), (row3 193 163 193), (row3 265 277 277), (row3 238 462 238), (row3 371 87 325), (row3 273 462 273), (row3 357 90 187), (row3 41 435 95), (row3 167 190 166), (row3 58 430 372), (row3 453 26 47)]

theorem b155_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b155_01_rows b155_01_labels 12984245465744028506606314212450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b155_01_rows b155_01_labels]
    decide +kernel

theorem checked155 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_155 QuarticIntegerComputationalData.ids64_155 16141988763124417987088639389950 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    (b155_00_rows ++ b155_01_rows)
    (b155_00_labels ++ b155_01_labels) 16141988763124417987088639389950
  exact (b155_00_checked.append (c := 16141988763124417987088639389950) b155_01_checked (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
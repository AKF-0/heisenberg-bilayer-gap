import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerData32
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData32.Block000
import Dressed.QuarticIntegerComputationalData32.Block001
import Dressed.QuarticIntegerComputationalData32.Block002
import Dressed.QuarticIntegerComputationalData32.Block003
import Dressed.QuarticIntegerComputationalData32.Block004
import Dressed.QuarticIntegerComputationalData32.Block005


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b000_00_rows : List Row := [(row3 1 2 3), (row3 1 2 4), (row3 1 2 5), (row3 1 2 6), (row3 1 2 7), (row3 1 2 8), (row3 1 2 9), (row3 1 2 10), (row3 1 2 11), (row3 1 2 12), (row3 1 2 13), (row3 1 2 14), (row3 1 2 15), (row3 1 2 16), (row3 1 2 17), (row3 1 2 18)]

def b000_00_labels : List Row := [(row3 26 507 26), (row3 31 504 497), (row3 21 22 21), (row3 497 504 31), (row3 483 33 483), (row3 476 40 56), (row3 480 492 480), (row3 56 40 476), (row3 71 469 71), (row3 100 453 369), (row3 94 82 94), (row3 369 453 100), (row3 210 181 210), (row3 234 234 508), (row3 353 508 353), (row3 508 234 234)]

theorem b000_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_00_rows b000_00_labels 5745642342363129084887035112957784 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_00_rows b000_00_labels]
    decide +kernel

def b000_01_rows : List Row := [(row3 1 2 19), (row3 1 2 20), (row3 1 2 21), (row3 1 2 22), (row3 1 2 23), (row3 1 2 24), (row3 1 2 25), (row3 1 2 26), (row3 1 2 27), (row3 1 2 28), (row3 1 2 29), (row3 1 2 30), (row3 1 2 31), (row3 1 3 4), (row3 1 3 5), (row3 1 3 6)]

def b000_01_labels : List Row := [(row3 508 508 508), (row3 100 453 369), (row3 94 82 94), (row3 369 453 100), (row3 210 181 210), (row3 476 40 56), (row3 480 492 480), (row3 56 40 476), (row3 71 469 71), (row3 31 504 497), (row3 21 22 21), (row3 497 504 31), (row3 483 33 483), (row3 21 21 22), (row3 31 497 504), (row3 483 483 33)]

theorem b000_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_01_rows b000_01_labels 2687290212347838963859136807166984 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_01_rows b000_01_labels]
    decide +kernel

def b000_02_rows : List Row := [(row3 1 3 7), (row3 1 3 8), (row3 1 3 9), (row3 1 3 10), (row3 1 3 11), (row3 1 3 12), (row3 1 3 13), (row3 1 3 14), (row3 1 3 15), (row3 1 3 16), (row3 1 3 17), (row3 1 3 18), (row3 1 3 19), (row3 1 3 20), (row3 1 3 21), (row3 1 3 22)]

def b000_02_labels : List Row := [(row3 497 31 504), (row3 480 480 492), (row3 476 56 40), (row3 71 71 469), (row3 56 476 40), (row3 94 94 82), (row3 100 369 453), (row3 210 210 181), (row3 369 100 453), (row3 353 353 508), (row3 234 508 234), (row3 508 508 508), (row3 508 234 234), (row3 94 94 82), (row3 100 369 453), (row3 210 210 181)]

theorem b000_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_02_rows b000_02_labels 489041389864857369140088215948184 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_02_rows b000_02_labels]
    decide +kernel

def b000_03_rows : List Row := [(row3 1 3 23), (row3 1 3 24), (row3 1 3 25), (row3 1 3 26), (row3 1 3 27), (row3 1 3 28), (row3 1 3 29), (row3 1 3 30), (row3 1 3 31), (row3 1 4 5), (row3 1 4 6), (row3 1 4 7), (row3 1 4 8), (row3 1 4 9), (row3 1 4 10), (row3 1 4 11)]

def b000_03_labels : List Row := [(row3 369 100 453), (row3 480 480 492), (row3 476 56 40), (row3 71 71 469), (row3 56 476 40), (row3 21 21 22), (row3 31 497 504), (row3 483 483 33), (row3 497 31 504), (row3 27 25 506), (row3 482 484 34), (row3 496 30 505), (row3 487 29 502), (row3 474 488 35), (row3 72 50 472), (row3 51 489 38)]

theorem b000_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_03_rows b000_03_labels 6677998501076799365861918519352588 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_03_rows b000_03_labels]
    decide +kernel

def b000_04_rows : List Row := [(row3 1 4 12), (row3 1 4 13), (row3 1 4 14), (row3 1 4 15), (row3 1 4 16), (row3 1 4 17), (row3 1 4 18), (row3 1 4 19), (row3 1 4 20), (row3 1 4 21), (row3 1 4 22), (row3 1 4 23), (row3 1 4 24), (row3 1 4 25), (row3 1 4 26), (row3 1 4 27)]

def b000_04_labels : List Row := [(row3 84 477 42), (row3 102 69 467), (row3 210 163 148), (row3 391 68 462), (row3 355 99 452), (row3 234 211 189), (row3 508 508 508), (row3 508 211 211), (row3 95 96 83), (row3 101 368 451), (row3 210 508 210), (row3 367 367 508), (row3 479 481 491), (row3 475 57 41), (row3 70 411 461), (row3 58 59 48)]

theorem b000_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_04_rows b000_04_labels 8486418227178299153986386021192 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_04_rows b000_04_labels]
    decide +kernel

def b000_05_rows : List Row := [(row3 1 4 28), (row3 1 4 29), (row3 1 4 30), (row3 1 4 31), (row3 1 5 6), (row3 1 5 7), (row3 1 5 8), (row3 1 5 9), (row3 1 5 10), (row3 1 5 11), (row3 1 5 12), (row3 1 5 13), (row3 1 5 14), (row3 1 5 15), (row3 1 5 16), (row3 1 5 17)]

def b000_05_labels : List Row := [(row3 23 24 24), (row3 32 498 503), (row3 485 44 36), (row3 494 495 499), (row3 496 505 30), (row3 482 34 484), (row3 474 35 488), (row3 487 502 29), (row3 51 38 489), (row3 72 472 50), (row3 102 467 69), (row3 84 42 477), (row3 391 462 68), (row3 210 148 163), (row3 234 189 211), (row3 355 452 99)]

theorem b000_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_05_rows b000_05_labels 1957792526772318642366048251262192 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_05_rows b000_05_labels]
    decide +kernel

def b000_06_rows : List Row := [(row3 1 5 18), (row3 1 5 19), (row3 1 5 20), (row3 1 5 21), (row3 1 5 22), (row3 1 5 23), (row3 1 5 24), (row3 1 5 25), (row3 1 5 26), (row3 1 5 27), (row3 1 5 28), (row3 1 5 29), (row3 1 5 30), (row3 1 5 31), (row3 1 6 7), (row3 1 6 8)]

def b000_06_labels : List Row := [(row3 508 211 211), (row3 508 508 508), (row3 101 451 368), (row3 95 83 96), (row3 367 508 367), (row3 210 210 508), (row3 475 41 57), (row3 479 491 481), (row3 58 48 59), (row3 70 461 411), (row3 32 503 498), (row3 23 24 24), (row3 494 499 495), (row3 485 36 44), (row3 46 470 448), (row3 91 458 430)]

theorem b000_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_06_rows b000_06_labels 1020392901269255576511233890672140 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_06_rows b000_06_labels]
    decide +kernel

def b000_07_rows : List Row := [(row3 1 6 9), (row3 1 6 10), (row3 1 6 11), (row3 1 6 12), (row3 1 6 13), (row3 1 6 14), (row3 1 6 15), (row3 1 6 16), (row3 1 6 17), (row3 1 6 18), (row3 1 6 19), (row3 1 6 20), (row3 1 6 21), (row3 1 6 22), (row3 1 6 23), (row3 1 6 24)]

def b000_07_labels : List Row := [(row3 92 75 74), (row3 433 444 440), (row3 401 109 127), (row3 364 118 173), (row3 361 384 375), (row3 154 161 153), (row3 339 339 335), (row3 304 304 508), (row3 234 262 229), (row3 311 311 310), (row3 508 262 262), (row3 364 119 174), (row3 360 381 374), (row3 210 268 209), (row3 317 317 508), (row3 89 456 429)]

theorem b000_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_07_rows b000_07_labels 3451383132696415954001935214532 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_07_rows b000_07_labels]
    decide +kernel

def b000_08_rows : List Row := [(row3 1 6 25), (row3 1 6 26), (row3 1 6 27), (row3 1 6 28), (row3 1 6 29), (row3 1 6 30), (row3 1 6 31), (row3 1 7 8), (row3 1 7 9), (row3 1 7 10), (row3 1 7 11), (row3 1 7 12), (row3 1 7 13), (row3 1 7 14), (row3 1 7 15), (row3 1 7 16)]

def b000_08_labels : List Row := [(row3 93 77 76), (row3 397 422 415), (row3 402 110 133), (row3 485 36 44), (row3 494 495 499), (row3 66 52 52), (row3 65 466 441), (row3 92 74 75), (row3 91 430 458), (row3 401 127 109), (row3 433 440 444), (row3 361 375 384), (row3 364 173 118), (row3 339 335 339), (row3 154 153 161), (row3 234 229 262)]

theorem b000_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_08_rows b000_08_labels 21206204988862219422958694446704 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_08_rows b000_08_labels]
    decide +kernel

def b000_09_rows : List Row := [(row3 1 7 17), (row3 1 7 18), (row3 1 7 19), (row3 1 7 20), (row3 1 7 21), (row3 1 7 22), (row3 1 7 23), (row3 1 7 24), (row3 1 7 25), (row3 1 7 26), (row3 1 7 27), (row3 1 7 28), (row3 1 7 29), (row3 1 7 30), (row3 1 7 31), (row3 1 8 9)]

def b000_09_labels : List Row := [(row3 304 508 304), (row3 508 262 262), (row3 311 310 311), (row3 360 374 381), (row3 364 174 119), (row3 317 508 317), (row3 210 209 268), (row3 93 76 77), (row3 89 429 456), (row3 402 133 110), (row3 397 415 422), (row3 494 499 495), (row3 485 44 36), (row3 65 441 466), (row3 66 52 52), (row3 90 429 457)]

theorem b000_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_09_rows b000_09_labels 21381045367173862423231695638412 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_09_rows b000_09_labels]
    decide +kernel

def b000_10_rows : List Row := [(row3 1 8 10), (row3 1 8 11), (row3 1 8 12), (row3 1 8 13), (row3 1 8 14), (row3 1 8 15), (row3 1 8 16), (row3 1 8 17), (row3 1 8 18), (row3 1 8 19), (row3 1 8 20), (row3 1 8 21), (row3 1 8 22), (row3 1 8 23), (row3 1 8 24), (row3 1 8 25)]

def b000_10_labels : List Row := [(row3 376 146 115), (row3 395 414 419), (row3 392 400 406), (row3 350 171 122), (row3 329 321 329), (row3 185 186 188), (row3 218 218 223), (row3 314 308 314), (row3 508 265 265), (row3 309 308 309), (row3 349 354 356), (row3 351 203 123), (row3 304 508 304), (row3 234 233 271), (row3 105 97 97), (row3 104 407 450)]

theorem b000_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_10_rows b000_10_labels 1613099320957658804870734483530 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_10_rows b000_10_labels]
    decide +kernel

def b000_11_rows : List Row := [(row3 1 8 26), (row3 1 8 27), (row3 1 8 28), (row3 1 8 29), (row3 1 8 30), (row3 1 8 31), (row3 1 9 10), (row3 1 9 11), (row3 1 9 12), (row3 1 9 13), (row3 1 9 14), (row3 1 9 15), (row3 1 9 16), (row3 1 9 17), (row3 1 9 18), (row3 1 9 19)]

def b000_11_labels : List Row := [(row3 377 156 116), (row3 370 393 394), (row3 479 491 481), (row3 475 57 41), (row3 89 429 456), (row3 93 77 76), (row3 395 419 414), (row3 376 115 146), (row3 350 122 171), (row3 392 406 400), (row3 185 188 186), (row3 329 329 321), (row3 314 314 308), (row3 218 223 218), (row3 309 309 308), (row3 508 265 265)]

theorem b000_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_11_rows b000_11_labels 7188363000258813275569298681610 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_11_rows b000_11_labels]
    decide +kernel

def b000_12_rows : List Row := [(row3 1 9 20), (row3 1 9 21), (row3 1 9 22), (row3 1 9 23), (row3 1 9 24), (row3 1 9 25), (row3 1 9 26), (row3 1 9 27), (row3 1 9 28), (row3 1 9 29), (row3 1 9 30), (row3 1 9 31), (row3 1 10 11), (row3 1 10 12), (row3 1 10 13), (row3 1 10 14)]

def b000_12_labels : List Row := [(row3 351 123 203), (row3 349 356 354), (row3 234 271 233), (row3 304 304 508), (row3 104 450 407), (row3 105 97 97), (row3 370 394 393), (row3 377 116 156), (row3 475 41 57), (row3 479 481 491), (row3 93 76 77), (row3 89 456 429), (row3 142 14 333), (row3 217 11 294), (row3 222 200 198), (row3 330 508 330)]

theorem b000_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_12_rows b000_12_labels 5840046183331219230954000284088 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_12_rows b000_12_labels]
    decide +kernel

def b000_13_rows : List Row := [(row3 1 10 15), (row3 1 10 16), (row3 1 10 17), (row3 1 10 18), (row3 1 10 19), (row3 1 10 20), (row3 1 10 21), (row3 1 10 22), (row3 1 10 23), (row3 1 10 24), (row3 1 10 25), (row3 1 10 26), (row3 1 10 27), (row3 1 10 28), (row3 1 10 29), (row3 1 10 30)]

def b000_13_labels : List Row := [(row3 258 508 258), (row3 508 508 508), (row3 289 508 289), (row3 265 508 265), (row3 279 508 279), (row3 216 11 293), (row3 225 201 201), (row3 305 508 305), (row3 508 508 508), (row3 377 116 156), (row3 370 393 394), (row3 180 150 150), (row3 166 13 320), (row3 70 461 411), (row3 58 59 48), (row3 397 415 422)]

theorem b000_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_13_rows b000_13_labels 556555781970098435300098004820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_13_rows b000_13_labels]
    decide +kernel

def b000_14_rows : List Row := [(row3 1 10 31), (row3 1 11 12), (row3 1 11 13), (row3 1 11 14), (row3 1 11 15), (row3 1 11 16), (row3 1 11 17), (row3 1 11 18), (row3 1 11 19), (row3 1 11 20), (row3 1 11 21), (row3 1 11 22), (row3 1 11 23), (row3 1 11 24), (row3 1 11 25), (row3 1 11 26)]

def b000_14_labels : List Row := [(row3 402 110 133), (row3 222 198 200), (row3 217 294 11), (row3 258 258 508), (row3 330 330 508), (row3 289 289 508), (row3 508 508 508), (row3 279 279 508), (row3 265 265 508), (row3 225 201 201), (row3 216 293 11), (row3 508 508 508), (row3 305 305 508), (row3 370 394 393), (row3 377 156 116), (row3 166 320 13)]

theorem b000_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_14_rows b000_14_labels 32717335687253286511519240380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_14_rows b000_14_labels]
    decide +kernel

def b000_15_rows : List Row := [(row3 1 11 27), (row3 1 11 28), (row3 1 11 29), (row3 1 11 30), (row3 1 11 31), (row3 1 12 13), (row3 1 12 14), (row3 1 12 15), (row3 1 12 16), (row3 1 12 17), (row3 1 12 18), (row3 1 12 19), (row3 1 12 20), (row3 1 12 21), (row3 1 12 22), (row3 1 12 23)]

def b000_15_labels : List Row := [(row3 180 150 150), (row3 58 48 59), (row3 70 411 461), (row3 402 133 110), (row3 397 422 415), (row3 227 288 10), (row3 272 272 508), (row3 291 291 508), (row3 287 287 508), (row3 272 272 508), (row3 275 275 508), (row3 272 272 508), (row3 243 239 239), (row3 241 282 9), (row3 508 508 508), (row3 285 285 508)]

theorem b000_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b000_15_rows b000_15_labels 567413669206506156574149147840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b000_15_rows b000_15_labels]
    decide +kernel

theorem checked000 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_000 QuarticIntegerComputationalData.ids32_000 18648481120701521348769419308522980 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b000_00_rows ++ b000_01_rows) ++ (b000_02_rows ++ b000_03_rows)) ++ ((b000_04_rows ++ b000_05_rows) ++ (b000_06_rows ++ b000_07_rows))) ++ (((b000_08_rows ++ b000_09_rows) ++ (b000_10_rows ++ b000_11_rows)) ++ ((b000_12_rows ++ b000_13_rows) ++ (b000_14_rows ++ b000_15_rows))))
    ((((b000_00_labels ++ b000_01_labels) ++ (b000_02_labels ++ b000_03_labels)) ++ ((b000_04_labels ++ b000_05_labels) ++ (b000_06_labels ++ b000_07_labels))) ++ (((b000_08_labels ++ b000_09_labels) ++ (b000_10_labels ++ b000_11_labels)) ++ ((b000_12_labels ++ b000_13_labels) ++ (b000_14_labels ++ b000_15_labels)))) 18648481120701521348769419308522980
  exact ((((b000_00_checked.append (c := 8432932554710968048746171920124768) b000_01_checked (by decide +kernel)).append (c := 15599972445652624783748178655425540) (b000_02_checked.append (c := 7167039890941656735002006735300772) b000_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 18590095675054073717733449118595596) ((b000_04_checked.append (c := 1966278944999496941520034637283384) b000_05_checked (by decide +kernel)).append (c := 2990123229401448933985270463170056) (b000_06_checked.append (c := 1023844284401951992465235825886672) b000_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 18648481120701521348769419308522980) (((b000_08_checked.append (c := 42587250356036081846190390085116) b000_09_checked (by decide +kernel)).append (c := 51388712677252553926630423250256) (b000_10_checked.append (c := 8801462321216472080440033165140) b000_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 58385445647447631035970189927384) ((b000_12_checked.append (c := 6396601965301317666254098288908) b000_13_checked (by decide +kernel)).append (c := 6996732970195077109339766677128) (b000_14_checked.append (c := 600131004893759443085668388220) b000_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b001_00_rows : List Row := [(row3 1 12 24), (row3 1 12 25), (row3 1 12 26), (row3 1 12 27), (row3 1 12 28), (row3 1 12 29), (row3 1 12 30), (row3 1 12 31), (row3 1 13 14), (row3 1 13 15), (row3 1 13 16), (row3 1 13 17), (row3 1 13 18), (row3 1 13 19), (row3 1 13 20), (row3 1 13 21)]

def b001_00_labels : List Row := [(row3 349 356 354), (row3 351 203 123), (row3 216 293 11), (row3 225 201 201), (row3 95 83 96), (row3 101 368 451), (row3 364 174 119), (row3 360 381 374), (row3 291 508 291), (row3 272 508 272), (row3 272 508 272), (row3 287 508 287), (row3 272 508 272), (row3 275 508 275), (row3 241 9 282), (row3 243 239 239)]

theorem b001_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_00_rows b001_00_labels 180540928890483084089233889940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_00_rows b001_00_labels]
    decide +kernel

def b001_01_rows : List Row := [(row3 1 13 22), (row3 1 13 23), (row3 1 13 24), (row3 1 13 25), (row3 1 13 26), (row3 1 13 27), (row3 1 13 28), (row3 1 13 29), (row3 1 13 30), (row3 1 13 31), (row3 1 14 15), (row3 1 14 16), (row3 1 14 17), (row3 1 14 18), (row3 1 14 19), (row3 1 14 20)]

def b001_01_labels : List Row := [(row3 285 508 285), (row3 508 508 508), (row3 351 123 203), (row3 349 354 356), (row3 225 201 201), (row3 216 11 293), (row3 101 451 368), (row3 95 96 83), (row3 360 374 381), (row3 364 119 174), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b001_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_01_rows b001_01_labels 177571945043457469313072384940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_01_rows b001_01_labels]
    decide +kernel

def b001_02_rows : List Row := [(row3 1 14 21), (row3 1 14 22), (row3 1 14 23), (row3 1 14 24), (row3 1 14 25), (row3 1 14 26), (row3 1 14 27), (row3 1 14 28), (row3 1 14 29), (row3 1 14 30), (row3 1 14 31), (row3 1 15 16), (row3 1 15 17), (row3 1 15 18), (row3 1 15 19), (row3 1 15 20)]

def b001_02_labels : List Row := [(row3 285 285 508), (row3 508 508 508), (row3 508 508 508), (row3 304 304 508), (row3 234 233 271), (row3 305 305 508), (row3 508 508 508), (row3 210 210 508), (row3 367 367 508), (row3 210 209 268), (row3 317 317 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 285 508 285)]

theorem b001_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_02_rows b001_02_labels 7087445966936739101073341400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_02_rows b001_02_labels]
    decide +kernel

def b001_03_rows : List Row := [(row3 1 15 21), (row3 1 15 22), (row3 1 15 23), (row3 1 15 24), (row3 1 15 25), (row3 1 15 26), (row3 1 15 27), (row3 1 15 28), (row3 1 15 29), (row3 1 15 30), (row3 1 15 31), (row3 1 16 17), (row3 1 16 18), (row3 1 16 19), (row3 1 16 20), (row3 1 16 21)]

def b001_03_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 234 271 233), (row3 304 508 304), (row3 508 508 508), (row3 305 508 305), (row3 367 508 367), (row3 210 508 210), (row3 317 508 317), (row3 210 268 209), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 287 508 287), (row3 272 272 508)]

theorem b001_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_03_rows b001_03_labels 8045270062436833903737250200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_03_rows b001_03_labels]
    decide +kernel

def b001_04_rows : List Row := [(row3 1 16 22), (row3 1 16 23), (row3 1 16 24), (row3 1 16 25), (row3 1 16 26), (row3 1 16 27), (row3 1 16 28), (row3 1 16 29), (row3 1 16 30), (row3 1 16 31), (row3 1 17 18), (row3 1 17 19), (row3 1 17 20), (row3 1 17 21), (row3 1 17 22), (row3 1 17 23)]

def b001_04_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 218 223 218), (row3 314 308 314), (row3 508 508 508), (row3 289 508 289), (row3 355 452 99), (row3 234 211 189), (row3 304 508 304), (row3 234 262 229), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 287 287 508), (row3 508 508 508), (row3 508 508 508)]

theorem b001_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_04_rows b001_04_labels 52505446891888938823187064192 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_04_rows b001_04_labels]
    decide +kernel

def b001_05_rows : List Row := [(row3 1 17 24), (row3 1 17 25), (row3 1 17 26), (row3 1 17 27), (row3 1 17 28), (row3 1 17 29), (row3 1 17 30), (row3 1 17 31), (row3 1 18 19), (row3 1 18 20), (row3 1 18 21), (row3 1 18 22), (row3 1 18 23), (row3 1 18 24), (row3 1 18 25), (row3 1 18 26)]

def b001_05_labels : List Row := [(row3 314 314 308), (row3 218 218 223), (row3 289 289 508), (row3 508 508 508), (row3 234 189 211), (row3 355 99 452), (row3 234 229 262), (row3 304 304 508), (row3 508 508 508), (row3 275 508 275), (row3 272 272 508), (row3 508 508 508), (row3 508 508 508), (row3 508 265 265), (row3 309 308 309), (row3 265 265 508)]

theorem b001_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_05_rows b001_05_labels 51623637583394995113118515312 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_05_rows b001_05_labels]
    decide +kernel

def b001_06_rows : List Row := [(row3 1 18 27), (row3 1 18 28), (row3 1 18 29), (row3 1 18 30), (row3 1 18 31), (row3 1 19 20), (row3 1 19 21), (row3 1 19 22), (row3 1 19 23), (row3 1 19 24), (row3 1 19 25), (row3 1 19 26), (row3 1 19 27), (row3 1 19 28), (row3 1 19 29), (row3 1 19 30)]

def b001_06_labels : List Row := [(row3 279 508 279), (row3 508 508 508), (row3 508 211 211), (row3 311 310 311), (row3 508 262 262), (row3 272 508 272), (row3 275 275 508), (row3 508 508 508), (row3 508 508 508), (row3 309 309 308), (row3 508 265 265), (row3 279 279 508), (row3 265 508 265), (row3 508 211 211), (row3 508 508 508), (row3 508 262 262)]

theorem b001_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_06_rows b001_06_labels 1127030075941816120634468640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_06_rows b001_06_labels]
    decide +kernel

def b001_07_rows : List Row := [(row3 1 19 31), (row3 1 20 21), (row3 1 20 22), (row3 1 20 23), (row3 1 20 24), (row3 1 20 25), (row3 1 20 26), (row3 1 20 27), (row3 1 20 28), (row3 1 20 29), (row3 1 20 30), (row3 1 20 31), (row3 1 21 22), (row3 1 21 23), (row3 1 21 24), (row3 1 21 25)]

def b001_07_labels : List Row := [(row3 311 311 310), (row3 227 288 10), (row3 272 272 508), (row3 291 291 508), (row3 392 406 400), (row3 350 171 122), (row3 217 294 11), (row3 222 200 198), (row3 84 42 477), (row3 102 69 467), (row3 364 173 118), (row3 361 384 375), (row3 291 508 291), (row3 272 508 272), (row3 350 122 171), (row3 392 400 406)]

theorem b001_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_07_rows b001_07_labels 3346222383295219818908808815028 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_07_rows b001_07_labels]
    decide +kernel

def b001_08_rows : List Row := [(row3 1 21 26), (row3 1 21 27), (row3 1 21 28), (row3 1 21 29), (row3 1 21 30), (row3 1 21 31), (row3 1 22 23), (row3 1 22 24), (row3 1 22 25), (row3 1 22 26), (row3 1 22 27), (row3 1 22 28), (row3 1 22 29), (row3 1 22 30), (row3 1 22 31), (row3 1 23 24)]

def b001_08_labels : List Row := [(row3 222 198 200), (row3 217 11 294), (row3 102 467 69), (row3 84 477 42), (row3 361 375 384), (row3 364 118 173), (row3 508 508 508), (row3 329 329 321), (row3 185 186 188), (row3 330 330 508), (row3 258 508 258), (row3 210 148 163), (row3 391 68 462), (row3 154 153 161), (row3 339 339 335), (row3 185 188 186)]

theorem b001_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_08_rows b001_08_labels 2303939380353742992748022394504 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_08_rows b001_08_labels]
    decide +kernel

def b001_09_rows : List Row := [(row3 1 23 25), (row3 1 23 26), (row3 1 23 27), (row3 1 23 28), (row3 1 23 29), (row3 1 23 30), (row3 1 23 31), (row3 1 24 25), (row3 1 24 26), (row3 1 24 27), (row3 1 24 28), (row3 1 24 29), (row3 1 24 30), (row3 1 24 31), (row3 1 25 26), (row3 1 25 27)]

def b001_09_labels : List Row := [(row3 329 321 329), (row3 258 258 508), (row3 330 508 330), (row3 391 462 68), (row3 210 163 148), (row3 339 335 339), (row3 154 161 153), (row3 90 429 457), (row3 376 146 115), (row3 395 414 419), (row3 487 502 29), (row3 474 488 35), (row3 91 430 458), (row3 92 75 74), (row3 395 419 414), (row3 376 115 146)]

theorem b001_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_09_rows b001_09_labels 451982195075438717994165518713464 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_09_rows b001_09_labels]
    decide +kernel

def b001_10_rows : List Row := [(row3 1 25 28), (row3 1 25 29), (row3 1 25 30), (row3 1 25 31), (row3 1 26 27), (row3 1 26 28), (row3 1 26 29), (row3 1 26 30), (row3 1 26 31), (row3 1 27 28), (row3 1 27 29), (row3 1 27 30), (row3 1 27 31), (row3 1 28 29), (row3 1 28 30), (row3 1 28 31)]

def b001_10_labels : List Row := [(row3 474 35 488), (row3 487 29 502), (row3 92 74 75), (row3 91 458 430), (row3 142 14 333), (row3 72 472 50), (row3 51 489 38), (row3 433 440 444), (row3 401 109 127), (row3 51 38 489), (row3 72 50 472), (row3 401 127 109), (row3 433 444 440), (row3 27 25 506), (row3 482 484 34), (row3 496 30 505)]

theorem b001_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_10_rows b001_10_labels 5103300203368936197917060001957024 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_10_rows b001_10_labels]
    decide +kernel

def b001_11_rows : List Row := [(row3 1 29 30), (row3 1 29 31), (row3 1 30 31), (row3 2 3 4), (row3 2 3 5), (row3 2 3 6), (row3 2 3 7), (row3 2 3 8), (row3 2 3 9), (row3 2 3 10), (row3 2 3 11), (row3 2 3 12), (row3 2 3 13), (row3 2 3 14), (row3 2 3 15), (row3 2 3 16)]

def b001_11_labels : List Row := [(row3 496 505 30), (row3 482 34 484), (row3 46 470 448), (row3 504 31 497), (row3 33 483 483), (row3 504 497 31), (row3 22 21 21), (row3 40 476 56), (row3 469 71 71), (row3 40 56 476), (row3 492 480 480), (row3 453 100 369), (row3 181 210 210), (row3 453 369 100), (row3 82 94 94), (row3 234 234 508)]

theorem b001_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_11_rows b001_11_labels 2106021070659008515250673346124424 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_11_rows b001_11_labels]
    decide +kernel

def b001_12_rows : List Row := [(row3 2 3 17), (row3 2 3 18), (row3 2 3 19), (row3 2 3 20), (row3 2 3 21), (row3 2 3 22), (row3 2 3 23), (row3 2 3 24), (row3 2 3 25), (row3 2 3 26), (row3 2 3 27), (row3 2 3 28), (row3 2 3 29), (row3 2 3 30), (row3 2 3 31), (row3 2 4 5)]

def b001_12_labels : List Row := [(row3 508 508 508), (row3 234 508 234), (row3 508 353 353), (row3 453 100 369), (row3 181 210 210), (row3 453 369 100), (row3 82 94 94), (row3 40 476 56), (row3 469 71 71), (row3 40 56 476), (row3 492 480 480), (row3 504 31 497), (row3 33 483 483), (row3 504 497 31), (row3 22 21 21), (row3 482 484 34)]

theorem b001_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_12_rows b001_12_labels 1609053580146423700398916849221624 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_12_rows b001_12_labels]
    decide +kernel

def b001_13_rows : List Row := [(row3 2 4 6), (row3 2 4 7), (row3 2 4 8), (row3 2 4 9), (row3 2 4 10), (row3 2 4 11), (row3 2 4 12), (row3 2 4 13), (row3 2 4 14), (row3 2 4 15), (row3 2 4 16), (row3 2 4 17), (row3 2 4 18), (row3 2 4 19), (row3 2 4 20), (row3 2 4 21)]

def b001_13_labels : List Row := [(row3 447 47 471), (row3 482 484 34), (row3 45 486 37), (row3 435 63 465), (row3 126 427 107), (row3 435 63 465), (row3 410 88 455), (row3 145 403 111), (row3 310 340 340), (row3 145 403 111), (row3 183 365 120), (row3 508 316 316), (row3 268 508 268), (row3 508 316 316), (row3 373 359 380), (row3 207 211 262)]

theorem b001_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_13_rows b001_13_labels 42472090490498930542810417900932 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_13_rows b001_13_labels]
    decide +kernel

def b001_14_rows : List Row := [(row3 2 4 22), (row3 2 4 23), (row3 2 4 24), (row3 2 4 25), (row3 2 4 26), (row3 2 4 27), (row3 2 4 28), (row3 2 4 29), (row3 2 4 30), (row3 2 4 31), (row3 2 5 6), (row3 2 5 7), (row3 2 5 8), (row3 2 5 9), (row3 2 5 10), (row3 2 5 11)]

def b001_14_labels : List Row := [(row3 310 312 312), (row3 207 211 262), (row3 78 87 81), (row3 416 396 421), (row3 139 139 159), (row3 416 396 421), (row3 500 493 493), (row3 53 64 54), (row3 445 439 446), (row3 53 64 54), (row3 482 484 34), (row3 442 443 443), (row3 425 424 425), (row3 60 55 55), (row3 425 425 424), (row3 128 130 130)]

theorem b001_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_14_rows b001_14_labels 38142884610205745839747417124472 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_14_rows b001_14_labels]
    decide +kernel

def b001_15_rows : List Row := [(row3 2 5 12), (row3 2 5 13), (row3 2 5 14), (row3 2 5 15), (row3 2 5 16), (row3 2 5 17), (row3 2 5 18), (row3 2 5 19), (row3 2 5 20), (row3 2 5 21), (row3 2 5 22), (row3 2 5 23), (row3 2 5 24), (row3 2 5 25), (row3 2 5 26), (row3 2 5 27)]

def b001_15_labels : List Row := [(row3 151 155 152), (row3 387 386 386), (row3 151 152 155), (row3 319 332 332), (row3 290 310 307), (row3 208 221 221), (row3 290 307 310), (row3 508 508 508), (row3 221 220 207), (row3 319 310 310), (row3 221 207 220), (row3 319 307 307), (row3 388 387 390), (row3 135 134 134), (row3 388 390 387), (row3 144 136 136)]

theorem b001_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b001_15_rows b001_15_labels 18016528695318475302285529560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b001_15_rows b001_15_labels]
    decide +kernel

theorem checked001 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_001 QuarticIntegerComputationalData.ids32_001 9357118704347370629106796724695656 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b001_00_rows ++ b001_01_rows) ++ (b001_02_rows ++ b001_03_rows)) ++ ((b001_04_rows ++ b001_05_rows) ++ (b001_06_rows ++ b001_07_rows))) ++ (((b001_08_rows ++ b001_09_rows) ++ (b001_10_rows ++ b001_11_rows)) ++ ((b001_12_rows ++ b001_13_rows) ++ (b001_14_rows ++ b001_15_rows))))
    ((((b001_00_labels ++ b001_01_labels) ++ (b001_02_labels ++ b001_03_labels)) ++ ((b001_04_labels ++ b001_05_labels) ++ (b001_06_labels ++ b001_07_labels))) ++ (((b001_08_labels ++ b001_09_labels) ++ (b001_10_labels ++ b001_11_labels)) ++ ((b001_12_labels ++ b001_13_labels) ++ (b001_14_labels ++ b001_15_labels)))) 9357118704347370629106796724695656
  exact ((((b001_00_checked.append (c := 358112873933940553402306274880) b001_01_checked (by decide +kernel)).append (c := 373245589963314126407116866480) (b001_02_checked.append (c := 15132716029373573004810591600) b001_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3824724087809759695372865729652) ((b001_04_checked.append (c := 104129084475283933936305579504) b001_05_checked (by decide +kernel)).append (c := 3451478497846445568965748863172) (b001_06_checked.append (c := 3347349413371161635029443283668) b001_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 9357118704347370629106796724695656) (((b001_08_checked.append (c := 454286134455792460986913541107968) b001_09_checked (by decide +kernel)).append (c := 7663607408483737174154646889189416) (b001_10_checked.append (c := 7209321274027944713167733348081448) b001_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 9353293980259560869411423858966004) ((b001_12_checked.append (c := 1651525670636922630941727267122556) b001_13_checked (by decide +kernel)).append (c := 1689686571775823695256776969776588) (b001_14_checked.append (c := 38160901138901064315049702654032) b001_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b002_00_rows : List Row := [(row3 2 5 28), (row3 2 5 29), (row3 2 5 30), (row3 2 5 31), (row3 2 6 7), (row3 2 6 8), (row3 2 6 9), (row3 2 6 10), (row3 2 6 11), (row3 2 6 12), (row3 2 6 13), (row3 2 6 14), (row3 2 6 15), (row3 2 6 16), (row3 2 6 17), (row3 2 6 18)]

def b002_00_labels : List Row := [(row3 53 54 64), (row3 437 438 438), (row3 53 64 54), (row3 431 432 432), (row3 482 34 484), (row3 126 107 427), (row3 435 465 63), (row3 45 37 486), (row3 435 465 63), (row3 310 340 340), (row3 145 111 403), (row3 410 455 88), (row3 145 111 403), (row3 268 268 508), (row3 508 316 316), (row3 183 120 365)]

theorem b002_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_00_rows b002_00_labels 30638494261763920434077663792472 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_00_rows b002_00_labels]
    decide +kernel

def b002_01_rows : List Row := [(row3 2 6 19), (row3 2 6 20), (row3 2 6 21), (row3 2 6 22), (row3 2 6 23), (row3 2 6 24), (row3 2 6 25), (row3 2 6 26), (row3 2 6 27), (row3 2 6 28), (row3 2 6 29), (row3 2 6 30), (row3 2 6 31), (row3 2 7 8), (row3 2 7 9), (row3 2 7 10)]

def b002_01_labels : List Row := [(row3 508 316 316), (row3 310 312 312), (row3 207 262 211), (row3 373 380 359), (row3 207 262 211), (row3 139 159 139), (row3 416 421 396), (row3 78 81 87), (row3 416 421 396), (row3 445 446 439), (row3 53 54 64), (row3 500 493 493), (row3 53 54 64), (row3 425 424 425), (row3 128 130 130), (row3 425 425 424)]

theorem b002_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_01_rows b002_01_labels 15798814280727006208388469720972 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_01_rows b002_01_labels]
    decide +kernel

def b002_02_rows : List Row := [(row3 2 7 11), (row3 2 7 12), (row3 2 7 13), (row3 2 7 14), (row3 2 7 15), (row3 2 7 16), (row3 2 7 17), (row3 2 7 18), (row3 2 7 19), (row3 2 7 20), (row3 2 7 21), (row3 2 7 22), (row3 2 7 23), (row3 2 7 24), (row3 2 7 25), (row3 2 7 26)]

def b002_02_labels : List Row := [(row3 60 55 55), (row3 151 155 152), (row3 319 332 332), (row3 151 152 155), (row3 387 386 386), (row3 290 310 307), (row3 508 508 508), (row3 290 307 310), (row3 208 221 221), (row3 221 220 207), (row3 319 307 307), (row3 221 207 220), (row3 319 310 310), (row3 388 387 390), (row3 144 136 136), (row3 388 390 387)]

theorem b002_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_02_rows b002_02_labels 1256386768062723416530267461720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_02_rows b002_02_labels]
    decide +kernel

def b002_03_rows : List Row := [(row3 2 7 27), (row3 2 7 28), (row3 2 7 29), (row3 2 7 30), (row3 2 7 31), (row3 2 8 9), (row3 2 8 10), (row3 2 8 11), (row3 2 8 12), (row3 2 8 13), (row3 2 8 14), (row3 2 8 15), (row3 2 8 16), (row3 2 8 17), (row3 2 8 18), (row3 2 8 19)]

def b002_03_labels : List Row := [(row3 135 134 134), (row3 53 54 64), (row3 431 432 432), (row3 53 64 54), (row3 437 438 438), (row3 376 146 115), (row3 338 338 508), (row3 376 146 115), (row3 182 182 231), (row3 319 319 508), (row3 257 257 508), (row3 319 319 508), (row3 307 307 508), (row3 265 265 508), (row3 508 508 508), (row3 265 265 508)]

theorem b002_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_03_rows b002_03_labels 2681461455068576913367104207000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_03_rows b002_03_labels]
    decide +kernel

def b002_04_rows : List Row := [(row3 2 8 20), (row3 2 8 21), (row3 2 8 22), (row3 2 8 23), (row3 2 8 24), (row3 2 8 25), (row3 2 8 26), (row3 2 8 27), (row3 2 8 28), (row3 2 8 29), (row3 2 8 30), (row3 2 8 31), (row3 2 9 10), (row3 2 9 11), (row3 2 9 12), (row3 2 9 13)]

def b002_04_labels : List Row := [(row3 238 238 231), (row3 290 290 508), (row3 268 268 508), (row3 290 290 508), (row3 357 357 357), (row3 192 192 187), (row3 327 327 508), (row3 192 192 187), (row3 78 81 87), (row3 388 390 387), (row3 139 139 159), (row3 388 390 387), (row3 376 146 115), (row3 341 343 343), (row3 327 328 328), (row3 179 149 149)]

theorem b002_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_04_rows b002_04_labels 153331116576567129780764844960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_04_rows b002_04_labels]
    decide +kernel

def b002_05_rows : List Row := [(row3 2 9 14), (row3 2 9 15), (row3 2 9 16), (row3 2 9 17), (row3 2 9 18), (row3 2 9 19), (row3 2 9 20), (row3 2 9 21), (row3 2 9 22), (row3 2 9 23), (row3 2 9 24), (row3 2 9 25), (row3 2 9 26), (row3 2 9 27), (row3 2 9 28), (row3 2 9 29)]

def b002_05_labels : List Row := [(row3 327 328 328), (row3 252 254 254), (row3 259 259 261), (row3 308 309 309), (row3 259 261 259), (row3 508 279 279), (row3 297 301 301), (row3 259 263 263), (row3 297 301 301), (row3 262 268 268), (row3 192 187 192), (row3 335 337 337), (row3 192 192 187), (row3 335 336 336), (row3 416 421 396), (row3 135 134 134)]

theorem b002_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_05_rows b002_05_labels 23503385494966057390711628892 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_05_rows b002_05_labels]
    decide +kernel

def b002_06_rows : List Row := [(row3 2 9 30), (row3 2 9 31), (row3 2 10 11), (row3 2 10 12), (row3 2 10 13), (row3 2 10 14), (row3 2 10 15), (row3 2 10 16), (row3 2 10 17), (row3 2 10 18), (row3 2 10 19), (row3 2 10 20), (row3 2 10 21), (row3 2 10 22), (row3 2 10 23), (row3 2 10 24)]

def b002_06_labels : List Row := [(row3 416 396 421), (row3 144 136 136), (row3 376 115 146), (row3 257 508 257), (row3 319 508 319), (row3 182 231 182), (row3 319 508 319), (row3 508 508 508), (row3 265 508 265), (row3 307 508 307), (row3 265 508 265), (row3 268 508 268), (row3 290 508 290), (row3 238 231 238), (row3 290 508 290), (row3 327 508 327)]

theorem b002_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_06_rows b002_06_labels 60738369213382807951643420628 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_06_rows b002_06_labels]
    decide +kernel

def b002_07_rows : List Row := [(row3 2 10 25), (row3 2 10 26), (row3 2 10 27), (row3 2 10 28), (row3 2 10 29), (row3 2 10 30), (row3 2 10 31), (row3 2 11 12), (row3 2 11 13), (row3 2 11 14), (row3 2 11 15), (row3 2 11 16), (row3 2 11 17), (row3 2 11 18), (row3 2 11 19), (row3 2 11 20)]

def b002_07_labels : List Row := [(row3 192 187 192), (row3 357 357 357), (row3 192 187 192), (row3 139 159 139), (row3 388 387 390), (row3 78 87 81), (row3 388 387 390), (row3 327 328 328), (row3 252 254 254), (row3 327 328 328), (row3 179 149 149), (row3 259 259 261), (row3 508 279 279), (row3 259 261 259), (row3 308 309 309), (row3 297 301 301)]

theorem b002_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_07_rows b002_07_labels 120493809157925278967077773864 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_07_rows b002_07_labels]
    decide +kernel

def b002_08_rows : List Row := [(row3 2 11 21), (row3 2 11 22), (row3 2 11 23), (row3 2 11 24), (row3 2 11 25), (row3 2 11 26), (row3 2 11 27), (row3 2 11 28), (row3 2 11 29), (row3 2 11 30), (row3 2 11 31), (row3 2 12 13), (row3 2 12 14), (row3 2 12 15), (row3 2 12 16), (row3 2 12 17)]

def b002_08_labels : List Row := [(row3 262 268 268), (row3 297 301 301), (row3 259 263 263), (row3 192 187 192), (row3 335 336 336), (row3 192 192 187), (row3 335 337 337), (row3 416 421 396), (row3 144 136 136), (row3 416 396 421), (row3 135 134 134), (row3 272 272 508), (row3 508 508 508), (row3 272 272 508), (row3 273 273 508), (row3 508 508 508)]

theorem b002_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_08_rows b002_08_labels 46178326924545175601643293832 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_08_rows b002_08_labels]
    decide +kernel

def b002_09_rows : List Row := [(row3 2 12 18), (row3 2 12 19), (row3 2 12 20), (row3 2 12 21), (row3 2 12 22), (row3 2 12 23), (row3 2 12 24), (row3 2 12 25), (row3 2 12 26), (row3 2 12 27), (row3 2 12 28), (row3 2 12 29), (row3 2 12 30), (row3 2 12 31), (row3 2 13 14), (row3 2 13 15)]

def b002_09_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 283 284 284), (row3 272 272 508), (row3 508 508 508), (row3 272 272 508), (row3 238 231 238), (row3 297 301 301), (row3 268 268 508), (row3 297 301 301), (row3 373 380 359), (row3 221 207 220), (row3 310 312 312), (row3 221 207 220), (row3 272 272 508), (row3 508 508 508)]

theorem b002_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_09_rows b002_09_labels 4954209506474036826957972972 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_09_rows b002_09_labels]
    decide +kernel

def b002_10_rows : List Row := [(row3 2 13 16), (row3 2 13 17), (row3 2 13 18), (row3 2 13 19), (row3 2 13 20), (row3 2 13 21), (row3 2 13 22), (row3 2 13 23), (row3 2 13 24), (row3 2 13 25), (row3 2 13 26), (row3 2 13 27), (row3 2 13 28), (row3 2 13 29), (row3 2 13 30), (row3 2 13 31)]

def b002_10_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 272 272 508), (row3 508 508 508), (row3 290 508 290), (row3 259 263 263), (row3 290 290 508), (row3 262 268 268), (row3 207 262 211), (row3 319 310 310), (row3 207 211 262), (row3 319 307 307)]

theorem b002_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_10_rows b002_10_labels 702058376096101142291176920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_10_rows b002_10_labels]
    decide +kernel

def b002_11_rows : List Row := [(row3 2 14 15), (row3 2 14 16), (row3 2 14 17), (row3 2 14 18), (row3 2 14 19), (row3 2 14 20), (row3 2 14 21), (row3 2 14 22), (row3 2 14 23), (row3 2 14 24), (row3 2 14 25), (row3 2 14 26), (row3 2 14 27), (row3 2 14 28), (row3 2 14 29), (row3 2 14 30)]

def b002_11_labels : List Row := [(row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 283 284 284), (row3 272 508 272), (row3 268 508 268), (row3 297 301 301), (row3 238 238 231), (row3 297 301 301), (row3 310 312 312), (row3 221 220 207), (row3 373 359 380)]

theorem b002_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_11_rows b002_11_labels 4833190400410961877573765132 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_11_rows b002_11_labels]
    decide +kernel

def b002_12_rows : List Row := [(row3 2 14 31), (row3 2 15 16), (row3 2 15 17), (row3 2 15 18), (row3 2 15 19), (row3 2 15 20), (row3 2 15 21), (row3 2 15 22), (row3 2 15 23), (row3 2 15 24), (row3 2 15 25), (row3 2 15 26), (row3 2 15 27), (row3 2 15 28), (row3 2 15 29), (row3 2 15 30)]

def b002_12_labels : List Row := [(row3 221 220 207), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 272 272 508), (row3 508 508 508), (row3 290 508 290), (row3 262 268 268), (row3 290 290 508), (row3 259 263 263), (row3 207 262 211), (row3 319 307 307), (row3 207 211 262)]

theorem b002_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_12_rows b002_12_labels 806600347521336939059579160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_12_rows b002_12_labels]
    decide +kernel

def b002_13_rows : List Row := [(row3 2 15 31), (row3 2 16 17), (row3 2 16 18), (row3 2 16 19), (row3 2 16 20), (row3 2 16 21), (row3 2 16 22), (row3 2 16 23), (row3 2 16 24), (row3 2 16 25), (row3 2 16 26), (row3 2 16 27), (row3 2 16 28), (row3 2 16 29), (row3 2 16 30), (row3 2 16 31)]

def b002_13_labels : List Row := [(row3 319 310 310), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 307 508 307), (row3 259 261 259), (row3 508 508 508), (row3 259 261 259), (row3 183 120 365), (row3 290 307 310), (row3 268 508 268), (row3 290 307 310)]

theorem b002_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_13_rows b002_13_labels 3082591713974482007389464480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_13_rows b002_13_labels]
    decide +kernel

def b002_14_rows : List Row := [(row3 2 17 18), (row3 2 17 19), (row3 2 17 20), (row3 2 17 21), (row3 2 17 22), (row3 2 17 23), (row3 2 17 24), (row3 2 17 25), (row3 2 17 26), (row3 2 17 27), (row3 2 17 28), (row3 2 17 29), (row3 2 17 30), (row3 2 17 31), (row3 2 18 19), (row3 2 18 20)]

def b002_14_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 265 508 265), (row3 308 309 309), (row3 265 265 508), (row3 508 279 279), (row3 508 316 316), (row3 208 221 221), (row3 508 316 316), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b002_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_14_rows b002_14_labels 262842028038403412839131960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_14_rows b002_14_labels]
    decide +kernel

def b002_15_rows : List Row := [(row3 2 18 21), (row3 2 18 22), (row3 2 18 23), (row3 2 18 24), (row3 2 18 25), (row3 2 18 26), (row3 2 18 27), (row3 2 18 28), (row3 2 18 29), (row3 2 18 30), (row3 2 18 31), (row3 2 19 20), (row3 2 19 21), (row3 2 19 22), (row3 2 19 23), (row3 2 19 24)]

def b002_15_labels : List Row := [(row3 508 508 508), (row3 273 273 508), (row3 508 508 508), (row3 508 508 508), (row3 259 259 261), (row3 307 307 508), (row3 259 259 261), (row3 268 268 508), (row3 290 310 307), (row3 183 365 120), (row3 290 310 307), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 265 508 265)]

theorem b002_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b002_15_rows b002_15_labels 3063468502219159417993130880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b002_15_rows b002_15_labels]
    decide +kernel

theorem checked002 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_002 QuarticIntegerComputationalData.ids32_002 50797106733864347903679450365844 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b002_00_rows ++ b002_01_rows) ++ (b002_02_rows ++ b002_03_rows)) ++ ((b002_04_rows ++ b002_05_rows) ++ (b002_06_rows ++ b002_07_rows))) ++ (((b002_08_rows ++ b002_09_rows) ++ (b002_10_rows ++ b002_11_rows)) ++ ((b002_12_rows ++ b002_13_rows) ++ (b002_14_rows ++ b002_15_rows))))
    ((((b002_00_labels ++ b002_01_labels) ++ (b002_02_labels ++ b002_03_labels)) ++ ((b002_04_labels ++ b002_05_labels) ++ (b002_06_labels ++ b002_07_labels))) ++ (((b002_08_labels ++ b002_09_labels) ++ (b002_10_labels ++ b002_11_labels)) ++ ((b002_12_labels ++ b002_13_labels) ++ (b002_14_labels ++ b002_15_labels)))) 50797106733864347903679450365844
  exact ((((b002_00_checked.append (c := 46437308542490926642466133513444) b002_01_checked (by decide +kernel)).append (c := 50375156765622226972363505182164) (b002_02_checked.append (c := 3937848223131300329897371668720) b002_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 50733223446065068246453702850508) ((b002_04_checked.append (c := 176834502071533187171476473852) b002_05_checked (by decide +kernel)).append (c := 358066680442841274090197668344) (b002_06_checked.append (c := 181232178371308086918721194492) b002_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 50797106733864347903679450365844) (((b002_08_checked.append (c := 51132536431019212428601266804) b002_09_checked (by decide +kernel)).append (c := 56667785207526275448466208856) (b002_10_checked.append (c := 5535248776507063019864942052) b002_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 63883287799279657225747515336) ((b002_12_checked.append (c := 3889192061495818946449043640) b002_13_checked (by decide +kernel)).append (c := 7215502591753381777281306480) (b002_14_checked.append (c := 3326310530257562830832262840) b002_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b003_00_rows : List Row := [(row3 2 19 25), (row3 2 19 26), (row3 2 19 27), (row3 2 19 28), (row3 2 19 29), (row3 2 19 30), (row3 2 19 31), (row3 2 20 21), (row3 2 20 22), (row3 2 20 23), (row3 2 20 24), (row3 2 20 25), (row3 2 20 26), (row3 2 20 27), (row3 2 20 28), (row3 2 20 29)]

def b003_00_labels : List Row := [(row3 508 279 279), (row3 265 265 508), (row3 308 309 309), (row3 508 316 316), (row3 508 508 508), (row3 508 316 316), (row3 208 221 221), (row3 272 272 508), (row3 508 508 508), (row3 272 272 508), (row3 182 231 182), (row3 327 328 328), (row3 257 257 508), (row3 327 328 328), (row3 410 455 88), (row3 151 152 155)]

theorem b003_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_00_rows b003_00_labels 71870967547025226448054975632 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_00_rows b003_00_labels]
    decide +kernel

def b003_01_rows : List Row := [(row3 2 20 30), (row3 2 20 31), (row3 2 21 22), (row3 2 21 23), (row3 2 21 24), (row3 2 21 25), (row3 2 21 26), (row3 2 21 27), (row3 2 21 28), (row3 2 21 29), (row3 2 21 30), (row3 2 21 31), (row3 2 22 23), (row3 2 22 24), (row3 2 22 25), (row3 2 22 26)]

def b003_01_labels : List Row := [(row3 310 340 340), (row3 151 152 155), (row3 272 272 508), (row3 508 508 508), (row3 319 508 319), (row3 179 149 149), (row3 319 319 508), (row3 252 254 254), (row3 145 111 403), (row3 387 386 386), (row3 145 403 111), (row3 319 332 332), (row3 272 508 272), (row3 257 508 257), (row3 327 328 328), (row3 182 182 231)]

theorem b003_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_01_rows b003_01_labels 38431576446701604224986966752 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_01_rows b003_01_labels]
    decide +kernel

def b003_02_rows : List Row := [(row3 2 22 27), (row3 2 22 28), (row3 2 22 29), (row3 2 22 30), (row3 2 22 31), (row3 2 23 24), (row3 2 23 25), (row3 2 23 26), (row3 2 23 27), (row3 2 23 28), (row3 2 23 29), (row3 2 23 30), (row3 2 23 31), (row3 2 24 25), (row3 2 24 26), (row3 2 24 27)]

def b003_02_labels : List Row := [(row3 327 328 328), (row3 310 340 340), (row3 151 155 152), (row3 410 88 455), (row3 151 155 152), (row3 319 508 319), (row3 252 254 254), (row3 319 319 508), (row3 179 149 149), (row3 145 111 403), (row3 319 332 332), (row3 145 403 111), (row3 387 386 386), (row3 376 146 115), (row3 338 338 508), (row3 376 146 115)]

theorem b003_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_02_rows b003_02_labels 164828052434788691826057418728 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_02_rows b003_02_labels]
    decide +kernel

def b003_03_rows : List Row := [(row3 2 24 28), (row3 2 24 29), (row3 2 24 30), (row3 2 24 31), (row3 2 25 26), (row3 2 25 27), (row3 2 25 28), (row3 2 25 29), (row3 2 25 30), (row3 2 25 31), (row3 2 26 27), (row3 2 26 28), (row3 2 26 29), (row3 2 26 30), (row3 2 26 31), (row3 2 27 28)]

def b003_03_labels : List Row := [(row3 45 37 486), (row3 425 425 424), (row3 126 427 107), (row3 425 425 424), (row3 376 146 115), (row3 341 343 343), (row3 435 465 63), (row3 60 55 55), (row3 435 63 465), (row3 128 130 130), (row3 376 115 146), (row3 126 107 427), (row3 425 424 425), (row3 45 486 37), (row3 425 424 425), (row3 435 465 63)]

theorem b003_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_03_rows b003_03_labels 15142022988144425980648562046312 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_03_rows b003_03_labels]
    decide +kernel

def b003_04_rows : List Row := [(row3 2 27 29), (row3 2 27 30), (row3 2 27 31), (row3 2 28 29), (row3 2 28 30), (row3 2 28 31), (row3 2 29 30), (row3 2 29 31), (row3 2 30 31), (row3 3 4 5), (row3 3 4 6), (row3 3 4 7), (row3 3 4 8), (row3 3 4 9), (row3 3 4 10), (row3 3 4 11)]

def b003_04_labels : List Row := [(row3 128 130 130), (row3 435 63 465), (row3 60 55 55), (row3 482 484 34), (row3 447 47 471), (row3 482 484 34), (row3 482 484 34), (row3 442 443 443), (row3 482 34 484), (row3 496 30 505), (row3 482 484 34), (row3 27 25 506), (row3 487 29 502), (row3 51 489 38), (row3 72 50 472), (row3 474 488 35)]

theorem b003_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_04_rows b003_04_labels 5190010831842912136323446683990764 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_04_rows b003_04_labels]
    decide +kernel

def b003_05_rows : List Row := [(row3 3 4 12), (row3 3 4 13), (row3 3 4 14), (row3 3 4 15), (row3 3 4 16), (row3 3 4 17), (row3 3 4 18), (row3 3 4 19), (row3 3 4 20), (row3 3 4 21), (row3 3 4 22), (row3 3 4 23), (row3 3 4 24), (row3 3 4 25), (row3 3 4 26), (row3 3 4 27)]

def b003_05_labels : List Row := [(row3 84 477 42), (row3 391 68 462), (row3 210 163 148), (row3 102 69 467), (row3 355 99 452), (row3 508 211 211), (row3 508 508 508), (row3 234 211 189), (row3 95 96 83), (row3 367 367 508), (row3 210 508 210), (row3 101 368 451), (row3 479 481 491), (row3 58 59 48), (row3 70 411 461), (row3 475 57 41)]

theorem b003_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_05_rows b003_05_labels 8486418227178299153986386021192 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_05_rows b003_05_labels]
    decide +kernel

def b003_06_rows : List Row := [(row3 3 4 28), (row3 3 4 29), (row3 3 4 30), (row3 3 4 31), (row3 3 5 6), (row3 3 5 7), (row3 3 5 8), (row3 3 5 9), (row3 3 5 10), (row3 3 5 11), (row3 3 5 12), (row3 3 5 13), (row3 3 5 14), (row3 3 5 15), (row3 3 5 16), (row3 3 5 17)]

def b003_06_labels : List Row := [(row3 23 24 24), (row3 494 495 499), (row3 485 44 36), (row3 32 498 503), (row3 46 448 470), (row3 482 484 34), (row3 92 74 75), (row3 433 440 444), (row3 401 127 109), (row3 91 430 458), (row3 361 375 384), (row3 154 153 161), (row3 339 335 339), (row3 364 173 118), (row3 234 229 262), (row3 311 310 311)]

theorem b003_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_06_rows b003_06_labels 1038561082990205990837979131213520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_06_rows b003_06_labels]
    decide +kernel

def b003_07_rows : List Row := [(row3 3 5 18), (row3 3 5 19), (row3 3 5 20), (row3 3 5 21), (row3 3 5 22), (row3 3 5 23), (row3 3 5 24), (row3 3 5 25), (row3 3 5 26), (row3 3 5 27), (row3 3 5 28), (row3 3 5 29), (row3 3 5 30), (row3 3 5 31), (row3 3 6 7), (row3 3 6 8)]

def b003_07_labels : List Row := [(row3 508 262 262), (row3 304 508 304), (row3 360 374 381), (row3 210 209 268), (row3 317 508 317), (row3 364 174 119), (row3 93 76 77), (row3 397 415 422), (row3 402 133 110), (row3 89 429 456), (row3 494 499 495), (row3 66 52 52), (row3 65 441 466), (row3 485 44 36), (row3 496 30 505), (row3 91 458 430)]

theorem b003_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_07_rows b003_07_labels 500360148379540519073353115011692 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_07_rows b003_07_labels]
    decide +kernel

def b003_08_rows : List Row := [(row3 3 6 9), (row3 3 6 10), (row3 3 6 11), (row3 3 6 12), (row3 3 6 13), (row3 3 6 14), (row3 3 6 15), (row3 3 6 16), (row3 3 6 17), (row3 3 6 18), (row3 3 6 19), (row3 3 6 20), (row3 3 6 21), (row3 3 6 22), (row3 3 6 23), (row3 3 6 24)]

def b003_08_labels : List Row := [(row3 401 109 127), (row3 433 444 440), (row3 92 75 74), (row3 364 118 173), (row3 339 339 335), (row3 154 161 153), (row3 361 384 375), (row3 304 304 508), (row3 508 262 262), (row3 311 311 310), (row3 234 262 229), (row3 364 119 174), (row3 317 317 508), (row3 210 268 209), (row3 360 381 374), (row3 89 456 429)]

theorem b003_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_08_rows b003_08_labels 3451383132696415954001935214532 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_08_rows b003_08_labels]
    decide +kernel

def b003_09_rows : List Row := [(row3 3 6 25), (row3 3 6 26), (row3 3 6 27), (row3 3 6 28), (row3 3 6 29), (row3 3 6 30), (row3 3 6 31), (row3 3 7 8), (row3 3 7 9), (row3 3 7 10), (row3 3 7 11), (row3 3 7 12), (row3 3 7 13), (row3 3 7 14), (row3 3 7 15), (row3 3 7 16)]

def b003_09_labels : List Row := [(row3 402 110 133), (row3 397 422 415), (row3 93 77 76), (row3 485 36 44), (row3 65 466 441), (row3 66 52 52), (row3 494 495 499), (row3 474 35 488), (row3 72 472 50), (row3 51 38 489), (row3 487 502 29), (row3 102 467 69), (row3 210 148 163), (row3 391 462 68), (row3 84 42 477), (row3 234 189 211)]

theorem b003_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_09_rows b003_09_labels 472468903071792642234461323620936 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_09_rows b003_09_labels]
    decide +kernel

def b003_10_rows : List Row := [(row3 3 7 17), (row3 3 7 18), (row3 3 7 19), (row3 3 7 20), (row3 3 7 21), (row3 3 7 22), (row3 3 7 23), (row3 3 7 24), (row3 3 7 25), (row3 3 7 26), (row3 3 7 27), (row3 3 7 28), (row3 3 7 29), (row3 3 7 30), (row3 3 7 31), (row3 3 8 9)]

def b003_10_labels : List Row := [(row3 508 508 508), (row3 508 211 211), (row3 355 452 99), (row3 101 451 368), (row3 210 210 508), (row3 367 508 367), (row3 95 83 96), (row3 475 41 57), (row3 70 461 411), (row3 58 48 59), (row3 479 491 481), (row3 32 503 498), (row3 485 36 44), (row3 494 499 495), (row3 23 24 24), (row3 395 414 419)]

theorem b003_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_10_rows b003_10_labels 1006665369281664925224528260931900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_10_rows b003_10_labels]
    decide +kernel

def b003_11_rows : List Row := [(row3 3 8 10), (row3 3 8 11), (row3 3 8 12), (row3 3 8 13), (row3 3 8 14), (row3 3 8 15), (row3 3 8 16), (row3 3 8 17), (row3 3 8 18), (row3 3 8 19), (row3 3 8 20), (row3 3 8 21), (row3 3 8 22), (row3 3 8 23), (row3 3 8 24), (row3 3 8 25)]

def b003_11_labels : List Row := [(row3 376 146 115), (row3 90 429 457), (row3 392 400 406), (row3 185 186 188), (row3 329 321 329), (row3 350 171 122), (row3 218 218 223), (row3 309 308 309), (row3 508 265 265), (row3 314 308 314), (row3 349 354 356), (row3 234 233 271), (row3 304 508 304), (row3 351 203 123), (row3 105 97 97), (row3 370 393 394)]

theorem b003_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_11_rows b003_11_labels 4305995240206555714216117599030 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_11_rows b003_11_labels]
    decide +kernel

def b003_12_rows : List Row := [(row3 3 8 26), (row3 3 8 27), (row3 3 8 28), (row3 3 8 29), (row3 3 8 30), (row3 3 8 31), (row3 3 9 10), (row3 3 9 11), (row3 3 9 12), (row3 3 9 13), (row3 3 9 14), (row3 3 9 15), (row3 3 9 16), (row3 3 9 17), (row3 3 9 18), (row3 3 9 19)]

def b003_12_labels : List Row := [(row3 377 156 116), (row3 104 407 450), (row3 479 491 481), (row3 93 77 76), (row3 89 429 456), (row3 475 57 41), (row3 142 333 14), (row3 376 146 115), (row3 222 198 200), (row3 330 330 508), (row3 258 258 508), (row3 217 294 11), (row3 289 289 508), (row3 265 265 508), (row3 279 279 508), (row3 508 508 508)]

theorem b003_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_12_rows b003_12_labels 5819571025446802650412869185208 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_12_rows b003_12_labels]
    decide +kernel

def b003_13_rows : List Row := [(row3 3 9 20), (row3 3 9 21), (row3 3 9 22), (row3 3 9 23), (row3 3 9 24), (row3 3 9 25), (row3 3 9 26), (row3 3 9 27), (row3 3 9 28), (row3 3 9 29), (row3 3 9 30), (row3 3 9 31), (row3 3 10 11), (row3 3 10 12), (row3 3 10 13), (row3 3 10 14)]

def b003_13_labels : List Row := [(row3 225 201 201), (row3 305 305 508), (row3 508 508 508), (row3 216 293 11), (row3 370 394 393), (row3 180 150 150), (row3 166 320 13), (row3 377 156 116), (row3 58 48 59), (row3 397 422 415), (row3 402 133 110), (row3 70 411 461), (row3 395 414 419), (row3 217 11 294), (row3 258 508 258), (row3 330 508 330)]

theorem b003_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_13_rows b003_13_labels 1457652726834386762094436443780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_13_rows b003_13_labels]
    decide +kernel

def b003_14_rows : List Row := [(row3 3 10 15), (row3 3 10 16), (row3 3 10 17), (row3 3 10 18), (row3 3 10 19), (row3 3 10 20), (row3 3 10 21), (row3 3 10 22), (row3 3 10 23), (row3 3 10 24), (row3 3 10 25), (row3 3 10 26), (row3 3 10 27), (row3 3 10 28), (row3 3 10 29), (row3 3 10 30)]

def b003_14_labels : List Row := [(row3 222 200 198), (row3 508 508 508), (row3 279 508 279), (row3 265 508 265), (row3 289 508 289), (row3 216 11 293), (row3 508 508 508), (row3 305 508 305), (row3 225 201 201), (row3 377 116 156), (row3 166 13 320), (row3 180 150 150), (row3 370 393 394), (row3 70 461 411), (row3 402 110 133), (row3 397 415 422)]

theorem b003_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_14_rows b003_14_labels 210427491061220000106675439620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_14_rows b003_14_labels]
    decide +kernel

def b003_15_rows : List Row := [(row3 3 10 31), (row3 3 11 12), (row3 3 11 13), (row3 3 11 14), (row3 3 11 15), (row3 3 11 16), (row3 3 11 17), (row3 3 11 18), (row3 3 11 19), (row3 3 11 20), (row3 3 11 21), (row3 3 11 22), (row3 3 11 23), (row3 3 11 24), (row3 3 11 25), (row3 3 11 26)]

def b003_15_labels : List Row := [(row3 58 59 48), (row3 350 122 171), (row3 329 329 321), (row3 185 188 186), (row3 392 406 400), (row3 314 314 308), (row3 508 265 265), (row3 309 309 308), (row3 218 223 218), (row3 351 123 203), (row3 304 304 508), (row3 234 271 233), (row3 349 356 354), (row3 104 450 407), (row3 377 116 156), (row3 370 394 393)]

theorem b003_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b003_15_rows b003_15_labels 1023532083943487530197433590702 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b003_15_rows b003_15_labels]
    decide +kernel

theorem checked003 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_003 QuarticIntegerComputationalData.ids32_003 8248238469078056322961932029670300 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b003_00_rows ++ b003_01_rows) ++ (b003_02_rows ++ b003_03_rows)) ++ ((b003_04_rows ++ b003_05_rows) ++ (b003_06_rows ++ b003_07_rows))) ++ (((b003_08_rows ++ b003_09_rows) ++ (b003_10_rows ++ b003_11_rows)) ++ ((b003_12_rows ++ b003_13_rows) ++ (b003_14_rows ++ b003_15_rows))))
    ((((b003_00_labels ++ b003_01_labels) ++ (b003_02_labels ++ b003_03_labels)) ++ ((b003_04_labels ++ b003_05_labels) ++ (b003_06_labels ++ b003_07_labels))) ++ (((b003_08_labels ++ b003_09_labels) ++ (b003_10_labels ++ b003_11_labels)) ++ ((b003_12_labels ++ b003_13_labels) ++ (b003_14_labels ++ b003_15_labels)))) 8248238469078056322961932029670300
  exact ((((b003_00_checked.append (c := 110302543993726830673041942384) b003_01_checked (by decide +kernel)).append (c := 15417153584572941503147661407424) (b003_02_checked.append (c := 15306851040579214672474619465040) b003_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6752835635024409886891912977644592) ((b003_04_checked.append (c := 5198497250070090435477433070011956) b003_05_checked (by decide +kernel)).append (c := 6737418481439836945388765316237168) (b003_06_checked.append (c := 1538921231369746509911332246225212) b003_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 8248238469078056322961932029670300) (((b003_08_checked.append (c := 475920286204489058188463258835468) b003_09_checked (by decide +kernel)).append (c := 1486891650726360539127207637366398) (b003_10_checked.append (c := 1010971364521871480938744378530930) b003_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1495402834053646436070019052025708) ((b003_12_checked.append (c := 7277223752281189412507305628988) b003_13_checked (by decide +kernel)).append (c := 8511183327285896942811414659310) (b003_14_checked.append (c := 1233959575004707530304109030322) b003_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b004_00_rows : List Row := [(row3 3 11 27), (row3 3 11 28), (row3 3 11 29), (row3 3 11 30), (row3 3 11 31), (row3 3 12 13), (row3 3 12 14), (row3 3 12 15), (row3 3 12 16), (row3 3 12 17), (row3 3 12 18), (row3 3 12 19), (row3 3 12 20), (row3 3 12 21), (row3 3 12 22), (row3 3 12 23)]

def b004_00_labels : List Row := [(row3 105 97 97), (row3 475 41 57), (row3 89 456 429), (row3 93 76 77), (row3 479 481 491), (row3 291 291 508), (row3 272 272 508), (row3 227 288 10), (row3 287 287 508), (row3 272 272 508), (row3 275 275 508), (row3 272 272 508), (row3 243 239 239), (row3 285 285 508), (row3 508 508 508), (row3 241 282 9)]

theorem b004_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_00_rows b004_00_labels 5698191398325319885902968825328 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_00_rows b004_00_labels]
    decide +kernel

def b004_01_rows : List Row := [(row3 3 12 24), (row3 3 12 25), (row3 3 12 26), (row3 3 12 27), (row3 3 12 28), (row3 3 12 29), (row3 3 12 30), (row3 3 12 31), (row3 3 13 14), (row3 3 13 15), (row3 3 13 16), (row3 3 13 17), (row3 3 13 18), (row3 3 13 19), (row3 3 13 20), (row3 3 13 21)]

def b004_01_labels : List Row := [(row3 349 356 354), (row3 225 201 201), (row3 216 293 11), (row3 351 203 123), (row3 95 83 96), (row3 360 381 374), (row3 364 174 119), (row3 101 368 451), (row3 508 508 508), (row3 272 272 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 285 508 285), (row3 508 508 508)]

theorem b004_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_01_rows b004_01_labels 177579225443396450129655973740 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_01_rows b004_01_labels]
    decide +kernel

def b004_02_rows : List Row := [(row3 3 13 22), (row3 3 13 23), (row3 3 13 24), (row3 3 13 25), (row3 3 13 26), (row3 3 13 27), (row3 3 13 28), (row3 3 13 29), (row3 3 13 30), (row3 3 13 31), (row3 3 14 15), (row3 3 14 16), (row3 3 14 17), (row3 3 14 18), (row3 3 14 19), (row3 3 14 20)]

def b004_02_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 234 271 233), (row3 305 508 305), (row3 508 508 508), (row3 304 508 304), (row3 367 508 367), (row3 210 268 209), (row3 317 508 317), (row3 210 508 210), (row3 291 291 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b004_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_02_rows b004_02_labels 8371072266505668212205491400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_02_rows b004_02_labels]
    decide +kernel

def b004_03_rows : List Row := [(row3 3 14 21), (row3 3 14 22), (row3 3 14 23), (row3 3 14 24), (row3 3 14 25), (row3 3 14 26), (row3 3 14 27), (row3 3 14 28), (row3 3 14 29), (row3 3 14 30), (row3 3 14 31), (row3 3 15 16), (row3 3 15 17), (row3 3 15 18), (row3 3 15 19), (row3 3 15 20)]

def b004_03_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 285 285 508), (row3 304 304 508), (row3 508 508 508), (row3 305 305 508), (row3 234 233 271), (row3 210 210 508), (row3 317 317 508), (row3 210 209 268), (row3 367 367 508), (row3 272 508 272), (row3 275 508 275), (row3 272 508 272), (row3 287 508 287), (row3 241 9 282)]

theorem b004_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_03_rows b004_03_labels 8189556908296405180331574000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_03_rows b004_03_labels]
    decide +kernel

def b004_04_rows : List Row := [(row3 3 15 21), (row3 3 15 22), (row3 3 15 23), (row3 3 15 24), (row3 3 15 25), (row3 3 15 26), (row3 3 15 27), (row3 3 15 28), (row3 3 15 29), (row3 3 15 30), (row3 3 15 31), (row3 3 16 17), (row3 3 16 18), (row3 3 16 19), (row3 3 16 20), (row3 3 16 21)]

def b004_04_labels : List Row := [(row3 508 508 508), (row3 285 508 285), (row3 243 239 239), (row3 351 123 203), (row3 216 11 293), (row3 225 201 201), (row3 349 354 356), (row3 101 451 368), (row3 364 119 174), (row3 360 374 381), (row3 95 96 83), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 287 508 287), (row3 508 508 508)]

theorem b004_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_04_rows b004_04_labels 179098454945176622068340238540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_04_rows b004_04_labels]
    decide +kernel

def b004_05_rows : List Row := [(row3 3 16 22), (row3 3 16 23), (row3 3 16 24), (row3 3 16 25), (row3 3 16 26), (row3 3 16 27), (row3 3 16 28), (row3 3 16 29), (row3 3 16 30), (row3 3 16 31), (row3 3 17 18), (row3 3 17 19), (row3 3 17 20), (row3 3 17 21), (row3 3 17 22), (row3 3 17 23)]

def b004_05_labels : List Row := [(row3 508 508 508), (row3 272 272 508), (row3 218 223 218), (row3 289 508 289), (row3 508 508 508), (row3 314 308 314), (row3 355 452 99), (row3 234 262 229), (row3 304 508 304), (row3 234 211 189), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 275 275 508)]

theorem b004_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_05_rows b004_05_labels 51533085246866739097267672992 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_05_rows b004_05_labels]
    decide +kernel

def b004_06_rows : List Row := [(row3 3 17 24), (row3 3 17 25), (row3 3 17 26), (row3 3 17 27), (row3 3 17 28), (row3 3 17 29), (row3 3 17 30), (row3 3 17 31), (row3 3 18 19), (row3 3 18 20), (row3 3 18 21), (row3 3 18 22), (row3 3 18 23), (row3 3 18 24), (row3 3 18 25), (row3 3 18 26)]

def b004_06_labels : List Row := [(row3 309 309 308), (row3 265 508 265), (row3 279 279 508), (row3 508 265 265), (row3 508 211 211), (row3 311 311 310), (row3 508 262 262), (row3 508 508 508), (row3 508 508 508), (row3 275 508 275), (row3 508 508 508), (row3 508 508 508), (row3 272 272 508), (row3 508 265 265), (row3 279 508 279), (row3 265 265 508)]

theorem b004_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_06_rows b004_06_labels 678019900285896445192695840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_06_rows b004_06_labels]
    decide +kernel

def b004_07_rows : List Row := [(row3 3 18 27), (row3 3 18 28), (row3 3 18 29), (row3 3 18 30), (row3 3 18 31), (row3 3 19 20), (row3 3 19 21), (row3 3 19 22), (row3 3 19 23), (row3 3 19 24), (row3 3 19 25), (row3 3 19 26), (row3 3 19 27), (row3 3 19 28), (row3 3 19 29), (row3 3 19 30)]

def b004_07_labels : List Row := [(row3 309 308 309), (row3 508 508 508), (row3 508 262 262), (row3 311 310 311), (row3 508 211 211), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 287 287 508), (row3 314 314 308), (row3 508 508 508), (row3 289 289 508), (row3 218 218 223), (row3 234 189 211), (row3 304 304 508), (row3 234 229 262)]

theorem b004_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_07_rows b004_07_labels 4218265201470889474841467272 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_07_rows b004_07_labels]
    decide +kernel

def b004_08_rows : List Row := [(row3 3 19 31), (row3 3 20 21), (row3 3 20 22), (row3 3 20 23), (row3 3 20 24), (row3 3 20 25), (row3 3 20 26), (row3 3 20 27), (row3 3 20 28), (row3 3 20 29), (row3 3 20 30), (row3 3 20 31), (row3 3 21 22), (row3 3 21 23), (row3 3 21 24), (row3 3 21 25)]

def b004_08_labels : List Row := [(row3 355 99 452), (row3 291 291 508), (row3 272 272 508), (row3 227 288 10), (row3 392 406 400), (row3 222 200 198), (row3 217 294 11), (row3 350 171 122), (row3 84 42 477), (row3 361 384 375), (row3 364 173 118), (row3 102 69 467), (row3 508 508 508), (row3 272 272 508), (row3 185 188 186), (row3 330 508 330)]

theorem b004_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_08_rows b004_08_labels 2795401887365984301556543469070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_08_rows b004_08_labels]
    decide +kernel

def b004_09_rows : List Row := [(row3 3 21 26), (row3 3 21 27), (row3 3 21 28), (row3 3 21 29), (row3 3 21 30), (row3 3 21 31), (row3 3 22 23), (row3 3 22 24), (row3 3 22 25), (row3 3 22 26), (row3 3 22 27), (row3 3 22 28), (row3 3 22 29), (row3 3 22 30), (row3 3 22 31), (row3 3 23 24)]

def b004_09_labels : List Row := [(row3 258 258 508), (row3 329 321 329), (row3 391 462 68), (row3 154 161 153), (row3 339 335 339), (row3 210 163 148), (row3 291 291 508), (row3 329 329 321), (row3 258 508 258), (row3 330 330 508), (row3 185 186 188), (row3 210 148 163), (row3 339 339 335), (row3 154 153 161), (row3 391 68 462), (row3 350 122 171)]

theorem b004_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_09_rows b004_09_labels 376938996709594169881272897384 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_09_rows b004_09_labels]
    decide +kernel

def b004_10_rows : List Row := [(row3 3 23 25), (row3 3 23 26), (row3 3 23 27), (row3 3 23 28), (row3 3 23 29), (row3 3 23 30), (row3 3 23 31), (row3 3 24 25), (row3 3 24 26), (row3 3 24 27), (row3 3 24 28), (row3 3 24 29), (row3 3 24 30), (row3 3 24 31), (row3 3 25 26), (row3 3 25 27)]

def b004_10_labels : List Row := [(row3 217 11 294), (row3 222 198 200), (row3 392 400 406), (row3 102 467 69), (row3 364 118 173), (row3 361 375 384), (row3 84 477 42), (row3 395 414 419), (row3 376 146 115), (row3 90 429 457), (row3 487 502 29), (row3 92 75 74), (row3 91 430 458), (row3 474 488 35), (row3 142 333 14), (row3 376 146 115)]

theorem b004_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_10_rows b004_10_labels 453723814250583123702088366260222 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_10_rows b004_10_labels]
    decide +kernel

def b004_11_rows : List Row := [(row3 3 25 28), (row3 3 25 29), (row3 3 25 30), (row3 3 25 31), (row3 3 26 27), (row3 3 26 28), (row3 3 26 29), (row3 3 26 30), (row3 3 26 31), (row3 3 27 28), (row3 3 27 29), (row3 3 27 30), (row3 3 27 31), (row3 3 28 29), (row3 3 28 30), (row3 3 28 31)]

def b004_11_labels : List Row := [(row3 51 38 489), (row3 433 444 440), (row3 401 127 109), (row3 72 50 472), (row3 395 414 419), (row3 72 472 50), (row3 401 109 127), (row3 433 440 444), (row3 51 489 38), (row3 474 35 488), (row3 91 458 430), (row3 92 74 75), (row3 487 29 502), (row3 496 30 505), (row3 482 484 34), (row3 27 25 506)]

theorem b004_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_11_rows b004_11_labels 5104085239097967717755212391054184 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_11_rows b004_11_labels]
    decide +kernel

def b004_12_rows : List Row := [(row3 3 29 30), (row3 3 29 31), (row3 3 30 31), (row3 4 5 6), (row3 4 5 7), (row3 4 5 8), (row3 4 5 9), (row3 4 5 10), (row3 4 5 11), (row3 4 5 12), (row3 4 5 13), (row3 4 5 14), (row3 4 5 15), (row3 4 5 16), (row3 4 5 17), (row3 4 5 18)]

def b004_12_labels : List Row := [(row3 46 448 470), (row3 482 484 34), (row3 496 30 505), (row3 497 504 31), (row3 22 21 21), (row3 24 24 23), (row3 498 503 32), (row3 44 36 485), (row3 495 499 494), (row3 481 491 479), (row3 57 41 475), (row3 411 461 70), (row3 59 48 58), (row3 96 83 95), (row3 368 451 101), (row3 508 210 210)]

theorem b004_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_12_rows b004_12_labels 2601852689844089741005674531414780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_12_rows b004_12_labels]
    decide +kernel

def b004_13_rows : List Row := [(row3 4 5 19), (row3 4 5 20), (row3 4 5 21), (row3 4 5 22), (row3 4 5 23), (row3 4 5 24), (row3 4 5 25), (row3 4 5 26), (row3 4 5 27), (row3 4 5 28), (row3 4 5 29), (row3 4 5 30), (row3 4 5 31), (row3 4 6 7), (row3 4 6 8), (row3 4 6 9)]

def b004_13_labels : List Row := [(row3 367 508 367), (row3 99 452 355), (row3 211 189 234), (row3 508 508 508), (row3 211 211 508), (row3 477 42 84), (row3 69 467 102), (row3 163 148 210), (row3 68 462 391), (row3 29 502 487), (row3 488 35 474), (row3 50 472 72), (row3 489 38 51), (row3 497 31 504), (row3 493 493 500), (row3 64 54 53)]

theorem b004_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_13_rows b004_13_labels 945835123796095254075946695505044 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_13_rows b004_13_labels]
    decide +kernel

def b004_14_rows : List Row := [(row3 4 6 10), (row3 4 6 11), (row3 4 6 12), (row3 4 6 13), (row3 4 6 14), (row3 4 6 15), (row3 4 6 16), (row3 4 6 17), (row3 4 6 18), (row3 4 6 19), (row3 4 6 20), (row3 4 6 21), (row3 4 6 22), (row3 4 6 23), (row3 4 6 24), (row3 4 6 25)]

def b004_14_labels : List Row := [(row3 439 446 445), (row3 64 54 53), (row3 87 81 78), (row3 396 421 416), (row3 139 159 139), (row3 396 421 416), (row3 359 380 373), (row3 211 262 207), (row3 312 312 310), (row3 211 262 207), (row3 365 120 183), (row3 316 316 508), (row3 508 268 268), (row3 316 316 508), (row3 88 455 410), (row3 403 111 145)]

theorem b004_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_14_rows b004_14_labels 4949997331990697885448263083692 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_14_rows b004_14_labels]
    decide +kernel

def b004_15_rows : List Row := [(row3 4 6 26), (row3 4 6 27), (row3 4 6 28), (row3 4 6 29), (row3 4 6 30), (row3 4 6 31), (row3 4 7 8), (row3 4 7 9), (row3 4 7 10), (row3 4 7 11), (row3 4 7 12), (row3 4 7 13), (row3 4 7 14), (row3 4 7 15), (row3 4 7 16), (row3 4 7 17)]

def b004_15_labels : List Row := [(row3 340 340 310), (row3 403 111 145), (row3 486 37 45), (row3 63 465 435), (row3 427 107 126), (row3 63 465 435), (row3 24 24 23), (row3 495 499 494), (row3 44 36 485), (row3 498 503 32), (row3 481 491 479), (row3 59 48 58), (row3 411 461 70), (row3 57 41 475), (row3 96 83 95), (row3 367 508 367)]

theorem b004_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b004_15_rows b004_15_labels 1012663893601938924444491293888692 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b004_15_rows b004_15_labels]
    decide +kernel

theorem checked004 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_004 QuarticIntegerComputationalData.ids32_004 10132410957884978355896810161512180 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b004_00_rows ++ b004_01_rows) ++ (b004_02_rows ++ b004_03_rows)) ++ ((b004_04_rows ++ b004_05_rows) ++ (b004_06_rows ++ b004_07_rows))) ++ (((b004_08_rows ++ b004_09_rows) ++ (b004_10_rows ++ b004_11_rows)) ++ ((b004_12_rows ++ b004_13_rows) ++ (b004_14_rows ++ b004_15_rows))))
    ((((b004_00_labels ++ b004_01_labels) ++ (b004_02_labels ++ b004_03_labels)) ++ ((b004_04_labels ++ b004_05_labels) ++ (b004_06_labels ++ b004_07_labels))) ++ (((b004_08_labels ++ b004_09_labels) ++ (b004_10_labels ++ b004_11_labels)) ++ ((b004_12_labels ++ b004_13_labels) ++ (b004_14_labels ++ b004_15_labels)))) 10132410957884978355896810161512180
  exact ((((b004_00_checked.append (c := 5875770623768716336032624799068) b004_01_checked (by decide +kernel)).append (c := 5892331252943518409425161864468) (b004_02_checked.append (c := 16560629174802073392537065400) b004_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6127859078237318556510803939112) ((b004_04_checked.append (c := 230631540192043361165607911532) b004_05_checked (by decide +kernel)).append (c := 235527825293800147085642074644) (b004_06_checked.append (c := 4896285101756785920034163112) b004_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 10132410957884978355896810161512180) (((b004_08_checked.append (c := 3172340884075578471437816366454) b004_09_checked (by decide +kernel)).append (c := 5560981394232626419928738573680860) (b004_10_checked.append (c := 5557809053348550841457300757314406) b004_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 10126283098806741037340299357573068) ((b004_12_checked.append (c := 3547687813640184995081621226919824) b004_13_checked (by decide +kernel)).append (c := 4565301704574114617411560783892208) (b004_14_checked.append (c := 1017613890933929622329939556972384) b004_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b005_00_rows : List Row := [(row3 4 7 18), (row3 4 7 19), (row3 4 7 20), (row3 4 7 21), (row3 4 7 22), (row3 4 7 23), (row3 4 7 24), (row3 4 7 25), (row3 4 7 26), (row3 4 7 27), (row3 4 7 28), (row3 4 7 29), (row3 4 7 30), (row3 4 7 31), (row3 4 8 9), (row3 4 8 10)]

def b005_00_labels : List Row := [(row3 508 210 210), (row3 368 451 101), (row3 99 452 355), (row3 211 211 508), (row3 508 508 508), (row3 211 189 234), (row3 477 42 84), (row3 68 462 391), (row3 163 148 210), (row3 69 467 102), (row3 29 502 487), (row3 489 38 51), (row3 50 472 72), (row3 488 35 474), (row3 487 502 29), (row3 45 37 486)]

theorem b005_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_00_rows b005_00_labels 894572269375431591396173269644684 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_00_rows b005_00_labels]
    decide +kernel

def b005_01_rows : List Row := [(row3 4 8 11), (row3 4 8 12), (row3 4 8 13), (row3 4 8 14), (row3 4 8 15), (row3 4 8 16), (row3 4 8 17), (row3 4 8 18), (row3 4 8 19), (row3 4 8 20), (row3 4 8 21), (row3 4 8 22), (row3 4 8 23), (row3 4 8 24), (row3 4 8 25), (row3 4 8 26)]

def b005_01_labels : List Row := [(row3 487 502 29), (row3 473 501 28), (row3 73 39 490), (row3 191 468 49), (row3 73 39 490), (row3 106 43 478), (row3 124 460 67), (row3 508 190 190), (row3 124 460 67), (row3 98 459 98), (row3 235 211 235), (row3 508 508 508), (row3 235 211 235), (row3 478 43 106), (row3 67 460 124), (row3 190 190 508)]

theorem b005_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_01_rows b005_01_labels 834133301245302962382858004962990 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_01_rows b005_01_labels]
    decide +kernel

def b005_02_rows : List Row := [(row3 4 8 27), (row3 4 8 28), (row3 4 8 29), (row3 4 8 30), (row3 4 8 31), (row3 4 9 10), (row3 4 9 11), (row3 4 9 12), (row3 4 9 13), (row3 4 9 14), (row3 4 9 15), (row3 4 9 16), (row3 4 9 17), (row3 4 9 18), (row3 4 9 19), (row3 4 9 20)]

def b005_02_labels : List Row := [(row3 67 460 124), (row3 28 501 473), (row3 490 39 73), (row3 49 468 191), (row3 490 39 73), (row3 433 444 440), (row3 60 55 55), (row3 85 80 79), (row3 426 436 434), (row3 140 162 140), (row3 398 423 413), (row3 362 383 372), (row3 177 188 176), (row3 323 323 321), (row3 211 258 206), (row3 366 121 228)]

theorem b005_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_02_rows b005_02_labels 403478975058894591510425961759246 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_02_rows b005_02_labels]
    decide +kernel

def b005_03_rows : List Row := [(row3 4 9 21), (row3 4 9 22), (row3 4 9 23), (row3 4 9 24), (row3 4 9 25), (row3 4 9 26), (row3 4 9 27), (row3 4 9 28), (row3 4 9 29), (row3 4 9 30), (row3 4 9 31), (row3 4 10 11), (row3 4 10 12), (row3 4 10 13), (row3 4 10 14), (row3 4 10 15)]

def b005_03_labels : List Row := [(row3 315 315 297), (row3 508 268 268), (row3 303 303 508), (row3 86 454 379), (row3 404 112 204), (row3 326 326 508), (row3 404 113 205), (row3 490 39 73), (row3 62 464 418), (row3 428 108 157), (row3 61 463 417), (row3 433 440 444), (row3 399 412 420), (row3 147 132 131), (row3 345 508 345), (row3 147 132 131)]

theorem b005_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_03_rows b005_03_labels 8729605601856937444950363786660 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_03_rows b005_03_labels]
    decide +kernel

def b005_04_rows : List Row := [(row3 4 10 16), (row3 4 10 17), (row3 4 10 18), (row3 4 10 19), (row3 4 10 20), (row3 4 10 21), (row3 4 10 22), (row3 4 10 23), (row3 4 10 24), (row3 4 10 25), (row3 4 10 26), (row3 4 10 27), (row3 4 10 28), (row3 4 10 29), (row3 4 10 30), (row3 4 10 31)]

def b005_04_labels : List Row := [(row3 190 170 170), (row3 318 508 318), (row3 258 508 258), (row3 318 508 318), (row3 184 12 248), (row3 508 508 508), (row3 278 508 278), (row3 508 508 508), (row3 405 114 240), (row3 141 14 245), (row3 508 508 508), (row3 141 14 245), (row3 49 468 191), (row3 428 108 157), (row3 129 15 244), (row3 428 108 157)]

theorem b005_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_04_rows b005_04_labels 416083729099632143550645209040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_04_rows b005_04_labels]
    decide +kernel

def b005_05_rows : List Row := [(row3 4 11 12), (row3 4 11 13), (row3 4 11 14), (row3 4 11 15), (row3 4 11 16), (row3 4 11 17), (row3 4 11 18), (row3 4 11 19), (row3 4 11 20), (row3 4 11 21), (row3 4 11 22), (row3 4 11 23), (row3 4 11 24), (row3 4 11 25), (row3 4 11 26), (row3 4 11 27)]

def b005_05_labels : List Row := [(row3 85 80 79), (row3 398 423 413), (row3 140 162 140), (row3 426 436 434), (row3 362 383 372), (row3 211 258 206), (row3 323 323 321), (row3 177 188 176), (row3 366 121 228), (row3 303 303 508), (row3 508 268 268), (row3 315 315 297), (row3 86 454 379), (row3 404 113 205), (row3 326 326 508), (row3 404 112 204)]

theorem b005_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_05_rows b005_05_labels 2548960791639314893310238417756 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_05_rows b005_05_labels]
    decide +kernel

def b005_06_rows : List Row := [(row3 4 11 28), (row3 4 11 29), (row3 4 11 30), (row3 4 11 31), (row3 4 12 13), (row3 4 12 14), (row3 4 12 15), (row3 4 12 16), (row3 4 12 17), (row3 4 12 18), (row3 4 12 19), (row3 4 12 20), (row3 4 12 21), (row3 4 12 22), (row3 4 12 23), (row3 4 12 24)]

def b005_06_labels : List Row := [(row3 490 39 73), (row3 61 463 417), (row3 428 108 157), (row3 62 464 418), (row3 392 406 400), (row3 182 231 182), (row3 392 406 400), (row3 363 382 371), (row3 213 232 214), (row3 299 299 297), (row3 213 232 214), (row3 352 125 242), (row3 296 296 286), (row3 508 271 271), (row3 296 296 286), (row3 103 449 348)]

theorem b005_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_06_rows b005_06_labels 7436615088376414854311607339576 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_06_rows b005_06_labels]
    decide +kernel

def b005_07_rows : List Row := [(row3 4 12 25), (row3 4 12 26), (row3 4 12 27), (row3 4 12 28), (row3 4 12 29), (row3 4 12 30), (row3 4 12 31), (row3 4 13 14), (row3 4 13 15), (row3 4 13 16), (row3 4 13 17), (row3 4 13 18), (row3 4 13 19), (row3 4 13 20), (row3 4 13 21), (row3 4 13 22)]

def b005_07_labels : List Row := [(row3 378 117 347), (row3 303 303 508), (row3 378 117 347), (row3 478 43 106), (row3 86 454 379), (row3 405 114 240), (row3 86 454 379), (row3 330 508 330), (row3 179 149 149), (row3 224 202 199), (row3 316 508 316), (row3 268 508 268), (row3 306 508 306), (row3 215 11 249), (row3 271 508 271), (row3 276 508 276)]

theorem b005_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_07_rows b005_07_labels 1842609239921648773016639530350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_07_rows b005_07_labels]
    decide +kernel

def b005_08_rows : List Row := [(row3 4 13 23), (row3 4 13 24), (row3 4 13 25), (row3 4 13 26), (row3 4 13 27), (row3 4 13 28), (row3 4 13 29), (row3 4 13 30), (row3 4 13 31), (row3 4 14 15), (row3 4 14 16), (row3 4 14 17), (row3 4 14 18), (row3 4 14 19), (row3 4 14 20), (row3 4 14 21)]

def b005_08_labels : List Row := [(row3 508 508 508), (row3 378 117 347), (row3 165 13 247), (row3 508 508 508), (row3 164 13 246), (row3 67 460 124), (row3 404 112 204), (row3 141 14 245), (row3 404 113 205), (row3 330 330 508), (row3 304 304 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b005_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_08_rows b005_08_labels 190977881625313187874735581070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_08_rows b005_08_labels]
    decide +kernel

def b005_09_rows : List Row := [(row3 4 14 22), (row3 4 14 23), (row3 4 14 24), (row3 4 14 25), (row3 4 14 26), (row3 4 14 27), (row3 4 14 28), (row3 4 14 29), (row3 4 14 30), (row3 4 14 31), (row3 4 15 16), (row3 4 15 17), (row3 4 15 18), (row3 4 15 19), (row3 4 15 20), (row3 4 15 21)]

def b005_09_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 303 303 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 190 190 508), (row3 326 326 508), (row3 508 508 508), (row3 326 326 508), (row3 224 202 199), (row3 306 508 306), (row3 268 508 268), (row3 316 508 316), (row3 215 11 249), (row3 508 508 508)]

theorem b005_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_09_rows b005_09_labels 8171906868833720926731271350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_09_rows b005_09_labels]
    decide +kernel

def b005_10_rows : List Row := [(row3 4 15 22), (row3 4 15 23), (row3 4 15 24), (row3 4 15 25), (row3 4 15 26), (row3 4 15 27), (row3 4 15 28), (row3 4 15 29), (row3 4 15 30), (row3 4 15 31), (row3 4 16 17), (row3 4 16 18), (row3 4 16 19), (row3 4 16 20), (row3 4 16 21), (row3 4 16 22)]

def b005_10_labels : List Row := [(row3 276 508 276), (row3 271 508 271), (row3 378 117 347), (row3 164 13 246), (row3 508 508 508), (row3 165 13 247), (row3 67 460 124), (row3 404 113 205), (row3 141 14 245), (row3 404 112 204), (row3 287 508 287), (row3 273 508 273), (row3 287 508 287), (row3 226 10 250), (row3 273 508 273), (row3 274 508 274)]

theorem b005_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_10_rows b005_10_labels 196760817330022815161718332970 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_10_rows b005_10_labels]
    decide +kernel

def b005_11_rows : List Row := [(row3 4 16 23), (row3 4 16 24), (row3 4 16 25), (row3 4 16 26), (row3 4 16 27), (row3 4 16 28), (row3 4 16 29), (row3 4 16 30), (row3 4 16 31), (row3 4 17 18), (row3 4 17 19), (row3 4 17 20), (row3 4 17 21), (row3 4 17 22), (row3 4 17 23), (row3 4 17 24)]

def b005_11_labels : List Row := [(row3 273 508 273), (row3 352 125 242), (row3 215 11 249), (row3 508 508 508), (row3 215 11 249), (row3 98 459 98), (row3 366 121 228), (row3 184 12 248), (row3 366 121 228), (row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 296 296 286)]

theorem b005_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_11_rows b005_11_labels 118959567876789270451538036820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_11_rows b005_11_labels]
    decide +kernel

def b005_12_rows : List Row := [(row3 4 17 25), (row3 4 17 26), (row3 4 17 27), (row3 4 17 28), (row3 4 17 29), (row3 4 17 30), (row3 4 17 31), (row3 4 18 19), (row3 4 18 20), (row3 4 18 21), (row3 4 18 22), (row3 4 18 23), (row3 4 18 24), (row3 4 18 25), (row3 4 18 26), (row3 4 18 27)]

def b005_12_labels : List Row := [(row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 235 211 235), (row3 315 315 297), (row3 508 508 508), (row3 303 303 508), (row3 508 508 508), (row3 274 508 274), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 271 271), (row3 276 508 276), (row3 508 508 508), (row3 276 508 276)]

theorem b005_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_12_rows b005_12_labels 560456201102084235216416160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_12_rows b005_12_labels]
    decide +kernel

def b005_13_rows : List Row := [(row3 4 18 28), (row3 4 18 29), (row3 4 18 30), (row3 4 18 31), (row3 4 19 20), (row3 4 19 21), (row3 4 19 22), (row3 4 19 23), (row3 4 19 24), (row3 4 19 25), (row3 4 19 26), (row3 4 19 27), (row3 4 19 28), (row3 4 19 29), (row3 4 19 30), (row3 4 19 31)]

def b005_13_labels : List Row := [(row3 508 508 508), (row3 508 268 268), (row3 278 508 278), (row3 508 268 268), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 296 296 286), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 235 211 235), (row3 303 303 508), (row3 508 508 508), (row3 315 315 297)]

theorem b005_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_13_rows b005_13_labels 606521377782189049931644800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_13_rows b005_13_labels]
    decide +kernel

def b005_14_rows : List Row := [(row3 4 20 21), (row3 4 20 22), (row3 4 20 23), (row3 4 20 24), (row3 4 20 25), (row3 4 20 26), (row3 4 20 27), (row3 4 20 28), (row3 4 20 29), (row3 4 20 30), (row3 4 20 31), (row3 4 21 22), (row3 4 21 23), (row3 4 21 24), (row3 4 21 25), (row3 4 21 26)]

def b005_14_labels : List Row := [(row3 287 287 508), (row3 273 273 508), (row3 287 287 508), (row3 363 382 371), (row3 224 202 199), (row3 304 304 508), (row3 224 202 199), (row3 106 43 478), (row3 362 383 372), (row3 190 170 170), (row3 362 383 372), (row3 508 508 508), (row3 508 508 508), (row3 213 232 214), (row3 316 508 316), (row3 508 508 508)]

theorem b005_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_14_rows b005_14_labels 2010220638366461795228812101672 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_14_rows b005_14_labels]
    decide +kernel

def b005_15_rows : List Row := [(row3 4 21 27), (row3 4 21 28), (row3 4 21 29), (row3 4 21 30), (row3 4 21 31), (row3 4 22 23), (row3 4 22 24), (row3 4 22 25), (row3 4 22 26), (row3 4 22 27), (row3 4 22 28), (row3 4 22 29), (row3 4 22 30), (row3 4 22 31), (row3 4 23 24), (row3 4 23 25)]

def b005_15_labels : List Row := [(row3 306 508 306), (row3 124 460 67), (row3 177 188 176), (row3 318 508 318), (row3 211 258 206), (row3 508 508 508), (row3 299 299 297), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 508 190 190), (row3 323 323 321), (row3 258 508 258), (row3 323 323 321), (row3 213 232 214), (row3 306 508 306)]

theorem b005_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b005_15_rows b005_15_labels 165805911260110642565582143998 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b005_15_rows b005_15_labels]
    decide +kernel

theorem checked005 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_005 QuarticIntegerComputationalData.ids32_005 2155850483831429509104090996179142 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b005_00_rows ++ b005_01_rows) ++ (b005_02_rows ++ b005_03_rows)) ++ ((b005_04_rows ++ b005_05_rows) ++ (b005_06_rows ++ b005_07_rows))) ++ (((b005_08_rows ++ b005_09_rows) ++ (b005_10_rows ++ b005_11_rows)) ++ ((b005_12_rows ++ b005_13_rows) ++ (b005_14_rows ++ b005_15_rows))))
    ((((b005_00_labels ++ b005_01_labels) ++ (b005_02_labels ++ b005_03_labels)) ++ ((b005_04_labels ++ b005_05_labels) ++ (b005_06_labels ++ b005_07_labels))) ++ (((b005_08_labels ++ b005_09_labels) ++ (b005_10_labels ++ b005_11_labels)) ++ ((b005_12_labels ++ b005_13_labels) ++ (b005_14_labels ++ b005_15_labels)))) 2155850483831429509104090996179142
  exact ((((b005_00_checked.append (c := 1728705570620734553779031274607674) b005_01_checked (by decide +kernel)).append (c := 2140914151281486082734407600153580) (b005_02_checked.append (c := 412208580660751528955376325545906) b005_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2153158420130523093398596730650302) ((b005_04_checked.append (c := 2965044520738947036860883626796) b005_05_checked (by decide +kernel)).append (c := 12244268849037010664189130496722) (b005_06_checked.append (c := 9279224328298063627328246869926) b005_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2155850483831429509104090996179142) (((b005_08_checked.append (c := 199149788494146908801466852420) b005_09_checked (by decide +kernel)).append (c := 514870173700958994414723222210) (b005_10_checked.append (c := 315720385206812085613256369790) b005_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2692063700906415705494265528840) ((b005_12_checked.append (c := 1166977578884273285148060960) b005_13_checked (by decide +kernel)).append (c := 2177193527205456711079542306630) (b005_14_checked.append (c := 2176026549626572437794394245670) b005_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32
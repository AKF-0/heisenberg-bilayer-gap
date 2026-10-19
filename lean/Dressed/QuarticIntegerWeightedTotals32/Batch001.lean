import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerData32
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData32.Block006
import Dressed.QuarticIntegerComputationalData32.Block007
import Dressed.QuarticIntegerComputationalData32.Block008
import Dressed.QuarticIntegerComputationalData32.Block009
import Dressed.QuarticIntegerComputationalData32.Block010
import Dressed.QuarticIntegerComputationalData32.Block011


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b006_00_rows : List Row := [(row3 4 23 26), (row3 4 23 27), (row3 4 23 28), (row3 4 23 29), (row3 4 23 30), (row3 4 23 31), (row3 4 24 25), (row3 4 24 26), (row3 4 24 27), (row3 4 24 28), (row3 4 24 29), (row3 4 24 30), (row3 4 24 31), (row3 4 25 26), (row3 4 25 27), (row3 4 25 28)]

def b006_00_labels : List Row := [(row3 508 508 508), (row3 316 508 316), (row3 124 460 67), (row3 211 258 206), (row3 318 508 318), (row3 177 188 176), (row3 392 400 406), (row3 182 182 231), (row3 392 400 406), (row3 473 501 28), (row3 85 80 79), (row3 399 412 420), (row3 85 80 79), (row3 330 330 508), (row3 179 149 149), (row3 73 39 490)]

theorem b006_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_00_rows b006_00_labels 393682256859905998926697951102146 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_00_rows b006_00_labels]
    decide +kernel

def b006_01_rows : List Row := [(row3 4 25 29), (row3 4 25 30), (row3 4 25 31), (row3 4 26 27), (row3 4 26 28), (row3 4 26 29), (row3 4 26 30), (row3 4 26 31), (row3 4 27 28), (row3 4 27 29), (row3 4 27 30), (row3 4 27 31), (row3 4 28 29), (row3 4 28 30), (row3 4 28 31), (row3 4 29 30)]

def b006_01_labels : List Row := [(row3 426 436 434), (row3 147 132 131), (row3 398 423 413), (row3 330 508 330), (row3 191 468 49), (row3 140 162 140), (row3 345 508 345), (row3 140 162 140), (row3 73 39 490), (row3 398 423 413), (row3 147 132 131), (row3 426 436 434), (row3 487 29 502), (row3 45 486 37), (row3 487 29 502), (row3 433 440 444)]

theorem b006_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_01_rows b006_01_labels 885293695064775319795769692617852 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_01_rows b006_01_labels]
    decide +kernel

def b006_02_rows : List Row := [(row3 4 29 31), (row3 4 30 31), (row3 5 6 7), (row3 5 6 8), (row3 5 6 9), (row3 5 6 10), (row3 5 6 11), (row3 5 6 12), (row3 5 6 13), (row3 5 6 14), (row3 5 6 15), (row3 5 6 16), (row3 5 6 17), (row3 5 6 18), (row3 5 6 19), (row3 5 6 20)]

def b006_02_labels : List Row := [(row3 60 55 55), (row3 433 444 440), (row3 483 33 483), (row3 52 52 66), (row3 499 495 494), (row3 44 36 485), (row3 441 466 65), (row3 415 422 397), (row3 76 77 93), (row3 429 456 89), (row3 133 110 402), (row3 209 268 210), (row3 374 381 360), (row3 174 119 364), (row3 508 317 317), (row3 310 311 311)]

theorem b006_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_02_rows b006_02_labels 42723160287663517382687552261712 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_02_rows b006_02_labels]
    decide +kernel

def b006_03_rows : List Row := [(row3 5 6 21), (row3 5 6 22), (row3 5 6 23), (row3 5 6 24), (row3 5 6 25), (row3 5 6 26), (row3 5 6 27), (row3 5 6 28), (row3 5 6 29), (row3 5 6 30), (row3 5 6 31), (row3 5 7 8), (row3 5 7 9), (row3 5 7 10), (row3 5 7 11), (row3 5 7 12)]

def b006_03_labels : List Row := [(row3 229 262 234), (row3 508 304 304), (row3 262 262 508), (row3 153 161 154), (row3 375 384 361), (row3 173 118 364), (row3 335 339 339), (row3 440 444 433), (row3 74 75 92), (row3 430 458 91), (row3 127 109 401), (row3 438 438 437), (row3 54 64 53), (row3 432 432 431), (row3 64 54 53), (row3 134 134 135)]

theorem b006_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_03_rows b006_03_labels 6116938149728176650368200942452 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_03_rows b006_03_labels]
    decide +kernel

def b006_04_rows : List Row := [(row3 5 7 13), (row3 5 7 14), (row3 5 7 15), (row3 5 7 16), (row3 5 7 17), (row3 5 7 18), (row3 5 7 19), (row3 5 7 20), (row3 5 7 21), (row3 5 7 22), (row3 5 7 23), (row3 5 7 24), (row3 5 7 25), (row3 5 7 26), (row3 5 7 27), (row3 5 7 28)]

def b006_04_labels : List Row := [(row3 387 390 388), (row3 136 136 144), (row3 390 387 388), (row3 310 310 319), (row3 220 207 221), (row3 307 307 319), (row3 207 220 221), (row3 221 221 208), (row3 310 307 290), (row3 508 508 508), (row3 307 310 290), (row3 386 386 387), (row3 155 152 151), (row3 332 332 319), (row3 152 155 151), (row3 55 55 60)]

theorem b006_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_04_rows b006_04_labels 1256386768062723416530267461720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_04_rows b006_04_labels]
    decide +kernel

def b006_05_rows : List Row := [(row3 5 7 29), (row3 5 7 30), (row3 5 7 31), (row3 5 8 9), (row3 5 8 10), (row3 5 8 11), (row3 5 8 12), (row3 5 8 13), (row3 5 8 14), (row3 5 8 15), (row3 5 8 16), (row3 5 8 17), (row3 5 8 18), (row3 5 8 19), (row3 5 8 20), (row3 5 8 21)]

def b006_05_labels : List Row := [(row3 424 425 425), (row3 130 130 128), (row3 425 424 425), (row3 474 488 35), (row3 425 425 424), (row3 92 75 74), (row3 85 80 79), (row3 409 408 408), (row3 137 138 143), (row3 389 385 388), (row3 358 357 358), (row3 172 175 178), (row3 307 310 322), (row3 188 197 196), (row3 212 221 212), (row3 307 307 307)]

theorem b006_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_05_rows b006_05_labels 13701118902806137788831517985376 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_05_rows b006_05_labels]
    decide +kernel

def b006_06_rows : List Row := [(row3 5 8 22), (row3 5 8 23), (row3 5 8 24), (row3 5 8 25), (row3 5 8 26), (row3 5 8 27), (row3 5 8 28), (row3 5 8 29), (row3 5 8 30), (row3 5 8 31), (row3 5 9 10), (row3 5 9 11), (row3 5 9 12), (row3 5 9 13), (row3 5 9 14), (row3 5 9 15)]

def b006_06_labels : List Row := [(row3 508 508 508), (row3 290 307 290), (row3 358 357 358), (row3 178 175 172), (row3 322 310 307), (row3 196 197 188), (row3 79 80 85), (row3 408 408 409), (row3 143 138 137), (row3 388 385 389), (row3 51 38 489), (row3 435 465 63), (row3 418 464 62), (row3 73 39 490), (row3 417 463 61), (row3 157 108 428)]

theorem b006_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_06_rows b006_06_labels 12919565746939312647252987152220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_06_rows b006_06_labels]
    decide +kernel

def b006_07_rows : List Row := [(row3 5 9 16), (row3 5 9 17), (row3 5 9 18), (row3 5 9 19), (row3 5 9 20), (row3 5 9 21), (row3 5 9 22), (row3 5 9 23), (row3 5 9 24), (row3 5 9 25), (row3 5 9 26), (row3 5 9 27), (row3 5 9 28), (row3 5 9 29), (row3 5 9 30), (row3 5 9 31)]

def b006_07_labels : List Row := [(row3 204 112 404), (row3 379 454 86), (row3 205 113 404), (row3 508 326 326), (row3 297 315 315), (row3 228 121 366), (row3 508 303 303), (row3 268 268 508), (row3 176 188 177), (row3 372 383 362), (row3 206 258 211), (row3 321 323 323), (row3 434 436 426), (row3 79 80 85), (row3 413 423 398), (row3 140 162 140)]

theorem b006_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_07_rows b006_07_labels 2548960791639314893310238417756 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_07_rows b006_07_labels]
    decide +kernel

def b006_08_rows : List Row := [(row3 5 10 11), (row3 5 10 12), (row3 5 10 13), (row3 5 10 14), (row3 5 10 15), (row3 5 10 16), (row3 5 10 17), (row3 5 10 18), (row3 5 10 19), (row3 5 10 20), (row3 5 10 21), (row3 5 10 22), (row3 5 10 23), (row3 5 10 24), (row3 5 10 25), (row3 5 10 26)]

def b006_08_labels : List Row := [(row3 401 109 127), (row3 169 160 169), (row3 389 385 388), (row3 140 162 140), (row3 338 508 338), (row3 307 508 307), (row3 219 208 219), (row3 322 508 322), (row3 258 508 258), (row3 268 508 268), (row3 290 508 290), (row3 268 508 268), (row3 508 508 508), (row3 322 508 322), (row3 219 208 219), (row3 307 508 307)]

theorem b006_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_08_rows b006_08_labels 88514868426602023003365394416 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_08_rows b006_08_labels]
    decide +kernel

def b006_09_rows : List Row := [(row3 5 10 27), (row3 5 10 28), (row3 5 10 29), (row3 5 10 30), (row3 5 10 31), (row3 5 11 12), (row3 5 11 13), (row3 5 11 14), (row3 5 11 15), (row3 5 11 16), (row3 5 11 17), (row3 5 11 18), (row3 5 11 19), (row3 5 11 20), (row3 5 11 21), (row3 5 11 22)]

def b006_09_labels : List Row := [(row3 258 508 258), (row3 140 162 140), (row3 388 385 389), (row3 169 160 169), (row3 338 508 338), (row3 344 346 346), (row3 167 168 158), (row3 341 342 342), (row3 147 132 131), (row3 251 255 252), (row3 310 313 313), (row3 252 256 252), (row3 321 324 324), (row3 297 302 302), (row3 262 268 268), (row3 508 278 278)]

theorem b006_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_09_rows b006_09_labels 42568204647142891704725583624 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_09_rows b006_09_labels]
    decide +kernel

def b006_10_rows : List Row := [(row3 5 11 23), (row3 5 11 24), (row3 5 11 25), (row3 5 11 26), (row3 5 11 27), (row3 5 11 28), (row3 5 11 29), (row3 5 11 30), (row3 5 11 31), (row3 5 12 13), (row3 5 12 14), (row3 5 12 15), (row3 5 12 16), (row3 5 12 17), (row3 5 12 18), (row3 5 12 19)]

def b006_10_labels : List Row := [(row3 260 260 265), (row3 193 188 194), (row3 331 334 334), (row3 255 258 262), (row3 321 324 324), (row3 413 423 398), (row3 143 138 137), (row3 341 343 343), (row3 169 160 169), (row3 350 171 122), (row3 327 328 328), (row3 222 200 198), (row3 224 202 199), (row3 310 311 311), (row3 260 265 260), (row3 297 298 298)]

theorem b006_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_10_rows b006_10_labels 48220466466889202018843821950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_10_rows b006_10_labels]
    decide +kernel

def b006_11_rows : List Row := [(row3 5 12 20), (row3 5 12 21), (row3 5 12 22), (row3 5 12 23), (row3 5 12 24), (row3 5 12 25), (row3 5 12 26), (row3 5 12 27), (row3 5 12 28), (row3 5 12 29), (row3 5 12 30), (row3 5 12 31), (row3 5 13 14), (row3 5 13 15), (row3 5 13 16), (row3 5 13 17)]

def b006_11_labels : List Row := [(row3 292 295 295), (row3 264 267 266), (row3 508 276 276), (row3 267 267 270), (row3 236 230 237), (row3 310 312 312), (row3 262 268 268), (row3 297 299 299), (row3 372 383 362), (row3 178 175 172), (row3 331 334 334), (row3 219 208 219), (row3 185 188 186), (row3 319 508 319), (row3 307 508 307), (row3 213 232 214)]

theorem b006_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_11_rows b006_11_labels 16324139721322694746248434226 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_11_rows b006_11_labels]
    decide +kernel

def b006_12_rows : List Row := [(row3 5 13 18), (row3 5 13 19), (row3 5 13 20), (row3 5 13 21), (row3 5 13 22), (row3 5 13 23), (row3 5 13 24), (row3 5 13 25), (row3 5 13 26), (row3 5 13 27), (row3 5 13 28), (row3 5 13 29), (row3 5 13 30), (row3 5 13 31), (row3 5 14 15), (row3 5 14 16)]

def b006_12_labels : List Row := [(row3 307 508 307), (row3 268 508 268), (row3 269 508 269), (row3 290 508 290), (row3 271 508 271), (row3 508 508 508), (row3 307 508 307), (row3 236 230 237), (row3 290 508 290), (row3 268 508 268), (row3 176 188 177), (row3 358 357 358), (row3 193 188 194), (row3 322 508 322), (row3 258 508 258), (row3 268 508 268)]

theorem b006_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_12_rows b006_12_labels 6434432012085183000589409064 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_12_rows b006_12_labels]
    decide +kernel

def b006_13_rows : List Row := [(row3 5 14 17), (row3 5 14 18), (row3 5 14 19), (row3 5 14 20), (row3 5 14 21), (row3 5 14 22), (row3 5 14 23), (row3 5 14 24), (row3 5 14 25), (row3 5 14 26), (row3 5 14 27), (row3 5 14 28), (row3 5 14 29), (row3 5 14 30), (row3 5 14 31), (row3 5 15 16)]

def b006_13_labels : List Row := [(row3 297 298 298), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 297 299 299), (row3 268 508 268), (row3 508 508 508), (row3 321 323 323), (row3 196 197 188), (row3 321 324 324), (row3 258 508 258), (row3 508 508 508)]

theorem b006_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_13_rows b006_13_labels 419442683248819165566048768 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_13_rows b006_13_labels]
    decide +kernel

def b006_14_rows : List Row := [(row3 5 15 17), (row3 5 15 18), (row3 5 15 19), (row3 5 15 20), (row3 5 15 21), (row3 5 15 22), (row3 5 15 23), (row3 5 15 24), (row3 5 15 25), (row3 5 15 26), (row3 5 15 27), (row3 5 15 28), (row3 5 15 29), (row3 5 15 30), (row3 5 15 31), (row3 5 16 17)]

def b006_14_labels : List Row := [(row3 268 268 508), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 262 268 268), (row3 508 508 508), (row3 268 508 268), (row3 206 258 211), (row3 322 310 307), (row3 255 258 262), (row3 307 508 307), (row3 272 272 508)]

theorem b006_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_14_rows b006_14_labels 367213128227232412748696640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_14_rows b006_14_labels]
    decide +kernel

def b006_15_rows : List Row := [(row3 5 16 18), (row3 5 16 19), (row3 5 16 20), (row3 5 16 21), (row3 5 16 22), (row3 5 16 23), (row3 5 16 24), (row3 5 16 25), (row3 5 16 26), (row3 5 16 27), (row3 5 16 28), (row3 5 16 29), (row3 5 16 30), (row3 5 16 31), (row3 5 17 18), (row3 5 17 19)]

def b006_15_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 264 267 266), (row3 508 508 508), (row3 271 508 271), (row3 228 121 366), (row3 307 307 307), (row3 262 268 268), (row3 290 508 290), (row3 272 508 272), (row3 508 508 508)]

theorem b006_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b006_15_rows b006_15_labels 2957506595487717492419201520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b006_15_rows b006_15_labels]
    decide +kernel

theorem checked006 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_006 QuarticIntegerComputationalData.ids32_006 1358447888845201507264992914531442 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b006_00_rows ++ b006_01_rows) ++ (b006_02_rows ++ b006_03_rows)) ++ ((b006_04_rows ++ b006_05_rows) ++ (b006_06_rows ++ b006_07_rows))) ++ (((b006_08_rows ++ b006_09_rows) ++ (b006_10_rows ++ b006_11_rows)) ++ ((b006_12_rows ++ b006_13_rows) ++ (b006_14_rows ++ b006_15_rows))))
    ((((b006_00_labels ++ b006_01_labels) ++ (b006_02_labels ++ b006_03_labels)) ++ ((b006_04_labels ++ b006_05_labels) ++ (b006_06_labels ++ b006_07_labels))) ++ (((b006_08_labels ++ b006_09_labels) ++ (b006_10_labels ++ b006_11_labels)) ++ ((b006_12_labels ++ b006_13_labels) ++ (b006_14_labels ++ b006_15_labels)))) 1358447888845201507264992914531442
  exact ((((b006_00_checked.append (c := 1278975951924681318722467643719998) b006_01_checked (by decide +kernel)).append (c := 1327816050362073012755523396924162) (b006_02_checked.append (c := 48840098437391694033055753204164) b006_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1358242082571520501501448407941234) ((b006_04_checked.append (c := 14957505670868861205361785447096) b006_05_checked (by decide +kernel)).append (c := 30426032209447488745925011017072) (b006_06_checked.append (c := 15468526538578627540563225569976) b006_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1358447888845201507264992914531442) (((b006_08_checked.append (c := 131083073073744914708090978040) b006_09_checked (by decide +kernel)).append (c := 195627679261956811473183234216) (b006_10_checked.append (c := 64544606188211896765092256176) b006_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 205806273681005763544506590208) ((b006_12_checked.append (c := 6853874695334002166155457832) b006_13_checked (by decide +kernel)).append (c := 10178594419048952071323355992) (b006_14_checked.append (c := 3324719723714949905167898160) b006_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b007_00_rows : List Row := [(row3 5 17 20), (row3 5 17 21), (row3 5 17 22), (row3 5 17 23), (row3 5 17 24), (row3 5 17 25), (row3 5 17 26), (row3 5 17 27), (row3 5 17 28), (row3 5 17 29), (row3 5 17 30), (row3 5 17 31), (row3 5 18 19), (row3 5 18 20), (row3 5 18 21), (row3 5 18 22)]

def b007_00_labels : List Row := [(row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 269 508 269), (row3 292 295 295), (row3 272 508 272), (row3 508 508 508), (row3 297 315 315), (row3 212 221 212), (row3 297 302 302), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b007_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_00_rows b007_00_labels 212835340673281950091949952 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_00_rows b007_00_labels]
    decide +kernel

def b007_01_rows : List Row := [(row3 5 18 23), (row3 5 18 24), (row3 5 18 25), (row3 5 18 26), (row3 5 18 27), (row3 5 18 28), (row3 5 18 29), (row3 5 18 30), (row3 5 18 31), (row3 5 19 20), (row3 5 19 21), (row3 5 19 22), (row3 5 19 23), (row3 5 19 24), (row3 5 19 25), (row3 5 19 26)]

def b007_01_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 267 267 270), (row3 508 508 508), (row3 508 508 508), (row3 268 268 508), (row3 290 307 290), (row3 260 260 265), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 276 276), (row3 508 508 508)]

theorem b007_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_01_rows b007_01_labels 10687465480205571568774560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_01_rows b007_01_labels]
    decide +kernel

def b007_02_rows : List Row := [(row3 5 19 27), (row3 5 19 28), (row3 5 19 29), (row3 5 19 30), (row3 5 19 31), (row3 5 20 21), (row3 5 20 22), (row3 5 20 23), (row3 5 20 24), (row3 5 20 25), (row3 5 20 26), (row3 5 20 27), (row3 5 20 28), (row3 5 20 29), (row3 5 20 30), (row3 5 20 31)]

def b007_02_labels : List Row := [(row3 508 508 508), (row3 508 303 303), (row3 508 508 508), (row3 508 278 278), (row3 268 508 268), (row3 272 272 508), (row3 508 508 508), (row3 272 272 508), (row3 213 232 214), (row3 310 311 311), (row3 268 268 508), (row3 297 298 298), (row3 379 454 86), (row3 172 175 178), (row3 310 313 313), (row3 219 208 219)]

theorem b007_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_02_rows b007_02_labels 65017828470145070977967653488 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_02_rows b007_02_labels]
    decide +kernel

def b007_03_rows : List Row := [(row3 5 21 22), (row3 5 21 23), (row3 5 21 24), (row3 5 21 25), (row3 5 21 26), (row3 5 21 27), (row3 5 21 28), (row3 5 21 29), (row3 5 21 30), (row3 5 21 31), (row3 5 22 23), (row3 5 22 24), (row3 5 22 25), (row3 5 22 26), (row3 5 22 27), (row3 5 22 28)]

def b007_03_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 307 508 307), (row3 224 202 199), (row3 508 508 508), (row3 268 508 268), (row3 204 112 404), (row3 358 357 358), (row3 251 255 252), (row3 307 508 307), (row3 508 508 508), (row3 268 508 268), (row3 297 298 298), (row3 508 508 508), (row3 508 508 508), (row3 508 326 326)]

theorem b007_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_03_rows b007_03_labels 14299088148162196752128412240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_03_rows b007_03_labels]
    decide +kernel

def b007_04_rows : List Row := [(row3 5 22 29), (row3 5 22 30), (row3 5 22 31), (row3 5 23 24), (row3 5 23 25), (row3 5 23 26), (row3 5 23 27), (row3 5 23 28), (row3 5 23 29), (row3 5 23 30), (row3 5 23 31), (row3 5 24 25), (row3 5 24 26), (row3 5 24 27), (row3 5 24 28), (row3 5 24 29)]

def b007_04_labels : List Row := [(row3 188 197 196), (row3 321 324 324), (row3 258 508 258), (row3 307 508 307), (row3 260 265 260), (row3 508 508 508), (row3 268 508 268), (row3 205 113 404), (row3 307 310 322), (row3 252 256 252), (row3 322 508 322), (row3 350 171 122), (row3 319 319 508), (row3 185 186 188), (row3 73 39 490), (row3 409 408 408)]

theorem b007_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_04_rows b007_04_labels 5582801700526243952111031958968 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_04_rows b007_04_labels]
    decide +kernel

def b007_05_rows : List Row := [(row3 5 24 30), (row3 5 24 31), (row3 5 25 26), (row3 5 25 27), (row3 5 25 28), (row3 5 25 29), (row3 5 25 30), (row3 5 25 31), (row3 5 26 27), (row3 5 26 28), (row3 5 26 29), (row3 5 26 30), (row3 5 26 31), (row3 5 27 28), (row3 5 27 29), (row3 5 27 30)]

def b007_05_labels : List Row := [(row3 167 168 158), (row3 389 385 388), (row3 222 198 200), (row3 327 328 328), (row3 418 464 62), (row3 85 80 79), (row3 344 346 346), (row3 169 160 169), (row3 258 508 258), (row3 157 108 428), (row3 389 385 388), (row3 147 132 131), (row3 338 508 338), (row3 417 463 61), (row3 137 138 143), (row3 341 342 342)]

theorem b007_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_05_rows b007_05_labels 994878353971744366798944258516 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_05_rows b007_05_labels]
    decide +kernel

def b007_06_rows : List Row := [(row3 5 27 31), (row3 5 28 29), (row3 5 28 30), (row3 5 28 31), (row3 5 29 30), (row3 5 29 31), (row3 5 30 31), (row3 6 7 8), (row3 6 7 9), (row3 6 7 10), (row3 6 7 11), (row3 6 7 12), (row3 6 7 13), (row3 6 7 14), (row3 6 7 15), (row3 6 7 16)]

def b007_06_labels : List Row := [(row3 140 162 140), (row3 474 488 35), (row3 435 63 465), (row3 51 489 38), (row3 92 74 75), (row3 425 424 425), (row3 401 109 127), (row3 52 52 66), (row3 466 441 65), (row3 36 44 485), (row3 495 499 494), (row3 422 415 397), (row3 110 133 402), (row3 456 429 89), (row3 77 76 93), (row3 268 209 210)]

theorem b007_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_06_rows b007_06_labels 37243151206917414095433697785972 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_06_rows b007_06_labels]
    decide +kernel

def b007_07_rows : List Row := [(row3 6 7 17), (row3 6 7 18), (row3 6 7 19), (row3 6 7 20), (row3 6 7 21), (row3 6 7 22), (row3 6 7 23), (row3 6 7 24), (row3 6 7 25), (row3 6 7 26), (row3 6 7 27), (row3 6 7 28), (row3 6 7 29), (row3 6 7 30), (row3 6 7 31), (row3 6 8 9)]

def b007_07_labels : List Row := [(row3 317 508 317), (row3 119 174 364), (row3 381 374 360), (row3 311 310 311), (row3 262 262 508), (row3 304 508 304), (row3 262 229 234), (row3 161 153 154), (row3 339 335 339), (row3 118 173 364), (row3 384 375 361), (row3 444 440 433), (row3 109 127 401), (row3 458 430 91), (row3 75 74 92), (row3 91 430 458)]

theorem b007_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_07_rows b007_07_labels 3648603368176824293489726506692 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_07_rows b007_07_labels]
    decide +kernel

def b007_08_rows : List Row := [(row3 6 8 10), (row3 6 8 11), (row3 6 8 12), (row3 6 8 13), (row3 6 8 14), (row3 6 8 15), (row3 6 8 16), (row3 6 8 17), (row3 6 8 18), (row3 6 8 19), (row3 6 8 20), (row3 6 8 21), (row3 6 8 22), (row3 6 8 23), (row3 6 8 24), (row3 6 8 25)]

def b007_08_labels : List Row := [(row3 126 427 107), (row3 91 430 458), (row3 399 412 420), (row3 167 168 158), (row3 343 341 343), (row3 167 168 158), (row3 195 195 187), (row3 325 321 325), (row3 258 253 253), (row3 325 321 325), (row3 312 310 312), (row3 268 262 268), (row3 278 508 278), (row3 268 262 268), (row3 187 195 195), (row3 325 321 325)]

theorem b007_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_08_rows b007_08_labels 243710364807607507236998591724 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_08_rows b007_08_labels]
    decide +kernel

def b007_09_rows : List Row := [(row3 6 8 26), (row3 6 8 27), (row3 6 8 28), (row3 6 8 29), (row3 6 8 30), (row3 6 8 31), (row3 6 9 10), (row3 6 9 11), (row3 6 9 12), (row3 6 9 13), (row3 6 9 14), (row3 6 9 15), (row3 6 9 16), (row3 6 9 17), (row3 6 9 18), (row3 6 9 19)]

def b007_09_labels : List Row := [(row3 253 253 258), (row3 325 321 325), (row3 420 412 399), (row3 158 168 167), (row3 343 341 343), (row3 158 168 167), (row3 72 50 472), (row3 128 130 130), (row3 169 160 169), (row3 398 423 413), (row3 137 138 143), (row3 343 343 341), (row3 324 324 321), (row3 194 188 193), (row3 334 334 331), (row3 262 258 255)]

theorem b007_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_09_rows b007_09_labels 780721330282349670725895380790 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_09_rows b007_09_labels]
    decide +kernel

def b007_10_rows : List Row := [(row3 6 9 20), (row3 6 9 21), (row3 6 9 22), (row3 6 9 23), (row3 6 9 24), (row3 6 9 25), (row3 6 9 26), (row3 6 9 27), (row3 6 9 28), (row3 6 9 29), (row3 6 9 30), (row3 6 9 31), (row3 6 10 11), (row3 6 10 12), (row3 6 10 13), (row3 6 10 14)]

def b007_10_labels : List Row := [(row3 265 260 260), (row3 302 302 297), (row3 268 268 262), (row3 278 278 508), (row3 324 324 321), (row3 252 255 251), (row3 313 313 310), (row3 252 256 252), (row3 131 132 147), (row3 346 346 344), (row3 158 168 167), (row3 342 342 341), (row3 72 472 50), (row3 244 15 129), (row3 157 108 428), (row3 191 468 49)]

theorem b007_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_10_rows b007_10_labels 1119020657917589887627419063912 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_10_rows b007_10_labels]
    decide +kernel

def b007_11_rows : List Row := [(row3 6 10 15), (row3 6 10 16), (row3 6 10 17), (row3 6 10 18), (row3 6 10 19), (row3 6 10 20), (row3 6 10 21), (row3 6 10 22), (row3 6 10 23), (row3 6 10 24), (row3 6 10 25), (row3 6 10 26), (row3 6 10 27), (row3 6 10 28), (row3 6 10 29), (row3 6 10 30)]

def b007_11_labels : List Row := [(row3 157 108 428), (row3 508 508 508), (row3 245 14 141), (row3 240 114 405), (row3 245 14 141), (row3 278 508 278), (row3 508 508 508), (row3 248 12 184), (row3 508 508 508), (row3 258 508 258), (row3 318 508 318), (row3 170 170 190), (row3 318 508 318), (row3 345 508 345), (row3 131 132 147), (row3 420 412 399)]

theorem b007_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_11_rows b007_11_labels 102052641701160566934276303360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_11_rows b007_11_labels]
    decide +kernel

def b007_12_rows : List Row := [(row3 6 10 31), (row3 6 11 12), (row3 6 11 13), (row3 6 11 14), (row3 6 11 15), (row3 6 11 16), (row3 6 11 17), (row3 6 11 18), (row3 6 11 19), (row3 6 11 20), (row3 6 11 21), (row3 6 11 22), (row3 6 11 23), (row3 6 11 24), (row3 6 11 25), (row3 6 11 26)]

def b007_12_labels : List Row := [(row3 131 132 147), (row3 169 160 169), (row3 343 343 341), (row3 137 138 143), (row3 398 423 413), (row3 324 324 321), (row3 262 258 255), (row3 334 334 331), (row3 194 188 193), (row3 265 260 260), (row3 278 278 508), (row3 268 268 262), (row3 302 302 297), (row3 324 324 321), (row3 252 256 252), (row3 313 313 310)]

theorem b007_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_12_rows b007_12_labels 49377547852318022564896395246 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_12_rows b007_12_labels]
    decide +kernel

def b007_13_rows : List Row := [(row3 6 11 27), (row3 6 11 28), (row3 6 11 29), (row3 6 11 30), (row3 6 11 31), (row3 6 12 13), (row3 6 12 14), (row3 6 12 15), (row3 6 12 16), (row3 6 12 17), (row3 6 12 18), (row3 6 12 19), (row3 6 12 20), (row3 6 12 21), (row3 6 12 22), (row3 6 12 23)]

def b007_13_labels : List Row := [(row3 252 255 251), (row3 131 132 147), (row3 342 342 341), (row3 158 168 167), (row3 346 346 344), (row3 217 294 11), (row3 257 257 508), (row3 217 294 11), (row3 304 304 508), (row3 268 268 508), (row3 280 280 508), (row3 268 268 508), (row3 268 268 271), (row3 277 277 508), (row3 508 508 508), (row3 277 277 508)]

theorem b007_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_13_rows b007_13_labels 19760413742702195066438076432 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_13_rows b007_13_labels]
    decide +kernel

def b007_14_rows : List Row := [(row3 6 12 24), (row3 6 12 25), (row3 6 12 26), (row3 6 12 27), (row3 6 12 28), (row3 6 12 29), (row3 6 12 30), (row3 6 12 31), (row3 6 13 14), (row3 6 13 15), (row3 6 13 16), (row3 6 13 17), (row3 6 13 18), (row3 6 13 19), (row3 6 13 20), (row3 6 13 21)]

def b007_14_labels : List Row := [(row3 300 300 297), (row3 265 265 265), (row3 280 280 508), (row3 265 265 265), (row3 170 170 190), (row3 313 313 310), (row3 253 253 258), (row3 313 313 310), (row3 329 321 329), (row3 252 254 254), (row3 268 508 268), (row3 306 508 306), (row3 260 265 260), (row3 280 508 280), (row3 277 508 277), (row3 271 508 271)]

theorem b007_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_14_rows b007_14_labels 1090837677643346052229377960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_14_rows b007_14_labels]
    decide +kernel

def b007_15_rows : List Row := [(row3 6 13 22), (row3 6 13 23), (row3 6 13 24), (row3 6 13 25), (row3 6 13 26), (row3 6 13 27), (row3 6 13 28), (row3 6 13 29), (row3 6 13 30), (row3 6 13 31), (row3 6 14 15), (row3 6 14 16), (row3 6 14 17), (row3 6 14 18), (row3 6 14 19), (row3 6 14 20)]

def b007_15_labels : List Row := [(row3 278 508 278), (row3 508 508 508), (row3 268 508 268), (row3 281 508 281), (row3 265 265 265), (row3 280 508 280), (row3 318 508 318), (row3 252 255 251), (row3 325 321 325), (row3 252 256 252), (row3 329 329 321), (row3 508 508 508), (row3 268 508 268), (row3 299 299 297), (row3 268 508 268), (row3 508 508 508)]

theorem b007_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b007_15_rows b007_15_labels 460532542169252939556807360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b007_15_rows b007_15_labels]
    decide +kernel

theorem checked007 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_007 QuarticIntegerComputationalData.ids32_007 49865169395540227912232867297172 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b007_00_rows ++ b007_01_rows) ++ (b007_02_rows ++ b007_03_rows)) ++ ((b007_04_rows ++ b007_05_rows) ++ (b007_06_rows ++ b007_07_rows))) ++ (((b007_08_rows ++ b007_09_rows) ++ (b007_10_rows ++ b007_11_rows)) ++ ((b007_12_rows ++ b007_13_rows) ++ (b007_14_rows ++ b007_15_rows))))
    ((((b007_00_labels ++ b007_01_labels) ++ (b007_02_labels ++ b007_03_labels)) ++ ((b007_04_labels ++ b007_05_labels) ++ (b007_06_labels ++ b007_07_labels))) ++ (((b007_08_labels ++ b007_09_labels) ++ (b007_10_labels ++ b007_11_labels)) ++ ((b007_12_labels ++ b007_13_labels) ++ (b007_14_labels ++ b007_15_labels)))) 49865169395540227912232867297172
  exact ((((b007_00_checked.append (c := 223522806153487521660724512) b007_01_checked (by decide +kernel)).append (c := 79540439424460755251756790240) (b007_02_checked.append (c := 79316916618307267730096065728) b007_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 47548975069016687463085157300388) ((b007_04_checked.append (c := 6577680054497988318909976217484) b007_05_checked (by decide +kernel)).append (c := 47469434629592226707833400510148) (b007_06_checked.append (c := 40891754575094238388923424292664) b007_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 49865169395540227912232867297172) (((b007_08_checked.append (c := 1024431695089957177962893972514) b007_09_checked (by decide +kernel)).append (c := 2245504994708707632524589339786) (b007_10_checked.append (c := 1221073299618750454561695367272) b007_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2316194326523540449147709996784) ((b007_12_checked.append (c := 69137961595020217631334471678) b007_13_checked (by decide +kernel)).append (c := 70689331814832816623120656998) (b007_14_checked.append (c := 1551370219812598991786185320) b007_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b008_00_rows : List Row := [(row3 6 14 21), (row3 6 14 22), (row3 6 14 23), (row3 6 14 24), (row3 6 14 25), (row3 6 14 26), (row3 6 14 27), (row3 6 14 28), (row3 6 14 29), (row3 6 14 30), (row3 6 14 31), (row3 6 15 16), (row3 6 15 17), (row3 6 15 18), (row3 6 15 19), (row3 6 15 20)]

def b008_00_labels : List Row := [(row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 300 300 297), (row3 268 508 268), (row3 258 508 258), (row3 324 324 321), (row3 187 195 195), (row3 324 324 321), (row3 268 508 268), (row3 280 508 280), (row3 260 265 260), (row3 306 508 306), (row3 277 508 277)]

theorem b008_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_00_rows b008_00_labels 327921450614218584216664344 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_00_rows b008_00_labels]
    decide +kernel

def b008_01_rows : List Row := [(row3 6 15 21), (row3 6 15 22), (row3 6 15 23), (row3 6 15 24), (row3 6 15 25), (row3 6 15 26), (row3 6 15 27), (row3 6 15 28), (row3 6 15 29), (row3 6 15 30), (row3 6 15 31), (row3 6 16 17), (row3 6 16 18), (row3 6 16 19), (row3 6 16 20), (row3 6 16 21)]

def b008_01_labels : List Row := [(row3 508 508 508), (row3 278 508 278), (row3 271 508 271), (row3 268 508 268), (row3 280 508 280), (row3 265 265 265), (row3 281 508 281), (row3 318 508 318), (row3 252 256 252), (row3 325 321 325), (row3 252 255 251), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 274 508 274), (row3 508 508 508)]

theorem b008_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_01_rows b008_01_labels 113638976835156037329465240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_01_rows b008_01_labels]
    decide +kernel

def b008_02_rows : List Row := [(row3 6 16 22), (row3 6 16 23), (row3 6 16 24), (row3 6 16 25), (row3 6 16 26), (row3 6 16 27), (row3 6 16 28), (row3 6 16 29), (row3 6 16 30), (row3 6 16 31), (row3 6 17 18), (row3 6 17 19), (row3 6 17 20), (row3 6 17 21), (row3 6 17 22), (row3 6 17 23)]

def b008_02_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 278 508 278), (row3 248 12 184), (row3 268 268 262), (row3 278 508 278), (row3 268 268 262), (row3 275 275 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b008_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_02_rows b008_02_labels 482323047753508630659006300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_02_rows b008_02_labels]
    decide +kernel

def b008_03_rows : List Row := [(row3 6 17 24), (row3 6 17 25), (row3 6 17 26), (row3 6 17 27), (row3 6 17 28), (row3 6 17 29), (row3 6 17 30), (row3 6 17 31), (row3 6 18 19), (row3 6 18 20), (row3 6 18 21), (row3 6 18 22), (row3 6 18 23), (row3 6 18 24), (row3 6 18 25), (row3 6 18 26)]

def b008_03_labels : List Row := [(row3 508 508 508), (row3 271 508 271), (row3 277 277 508), (row3 508 508 508), (row3 508 508 508), (row3 302 302 297), (row3 268 262 268), (row3 278 278 508), (row3 275 508 275), (row3 508 508 508), (row3 508 508 508), (row3 274 508 274), (row3 508 508 508), (row3 508 508 508), (row3 277 508 277), (row3 268 268 271)]

theorem b008_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_03_rows b008_03_labels 6883199151768730516768560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_03_rows b008_03_labels]
    decide +kernel

def b008_04_rows : List Row := [(row3 6 18 27), (row3 6 18 28), (row3 6 18 29), (row3 6 18 30), (row3 6 18 31), (row3 6 19 20), (row3 6 19 21), (row3 6 19 22), (row3 6 19 23), (row3 6 19 24), (row3 6 19 25), (row3 6 19 26), (row3 6 19 27), (row3 6 19 28), (row3 6 19 29), (row3 6 19 30)]

def b008_04_labels : List Row := [(row3 277 508 277), (row3 278 508 278), (row3 265 260 260), (row3 312 310 312), (row3 265 260 260), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 277 277 508), (row3 271 508 271), (row3 508 508 508), (row3 278 278 508), (row3 268 262 268)]

theorem b008_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_04_rows b008_04_labels 12133925146869114472454160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_04_rows b008_04_labels]
    decide +kernel

def b008_05_rows : List Row := [(row3 6 19 31), (row3 6 20 21), (row3 6 20 22), (row3 6 20 23), (row3 6 20 24), (row3 6 20 25), (row3 6 20 26), (row3 6 20 27), (row3 6 20 28), (row3 6 20 29), (row3 6 20 30), (row3 6 20 31), (row3 6 21 22), (row3 6 21 23), (row3 6 21 24), (row3 6 21 25)]

def b008_05_labels : List Row := [(row3 302 302 297), (row3 275 275 508), (row3 508 508 508), (row3 275 275 508), (row3 299 299 297), (row3 260 265 260), (row3 280 280 508), (row3 260 265 260), (row3 240 114 405), (row3 334 334 331), (row3 258 253 253), (row3 334 334 331), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 306 508 306)]

theorem b008_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_05_rows b008_05_labels 8886727517782223890996187040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_05_rows b008_05_labels]
    decide +kernel

def b008_06_rows : List Row := [(row3 6 21 26), (row3 6 21 27), (row3 6 21 28), (row3 6 21 29), (row3 6 21 30), (row3 6 21 31), (row3 6 22 23), (row3 6 22 24), (row3 6 22 25), (row3 6 22 26), (row3 6 22 27), (row3 6 22 28), (row3 6 22 29), (row3 6 22 30), (row3 6 22 31), (row3 6 23 24)]

def b008_06_labels : List Row := [(row3 268 268 508), (row3 280 508 280), (row3 245 14 141), (row3 194 188 193), (row3 325 321 325), (row3 262 258 255), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 304 304 508), (row3 268 508 268), (row3 508 508 508), (row3 324 324 321), (row3 195 195 187), (row3 324 324 321), (row3 268 508 268)]

theorem b008_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_06_rows b008_06_labels 1855967734751041083461794380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_06_rows b008_06_labels]
    decide +kernel

def b008_07_rows : List Row := [(row3 6 23 25), (row3 6 23 26), (row3 6 23 27), (row3 6 23 28), (row3 6 23 29), (row3 6 23 30), (row3 6 23 31), (row3 6 24 25), (row3 6 24 26), (row3 6 24 27), (row3 6 24 28), (row3 6 24 29), (row3 6 24 30), (row3 6 24 31), (row3 6 25 26), (row3 6 25 27)]

def b008_07_labels : List Row := [(row3 280 508 280), (row3 268 268 508), (row3 306 508 306), (row3 245 14 141), (row3 262 258 255), (row3 325 321 325), (row3 194 188 193), (row3 329 321 329), (row3 257 257 508), (row3 329 321 329), (row3 191 468 49), (row3 137 138 143), (row3 343 341 343), (row3 137 138 143), (row3 217 294 11), (row3 252 254 254)]

theorem b008_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_07_rows b008_07_labels 367094460822939857462649243984 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_07_rows b008_07_labels]
    decide +kernel

def b008_08_rows : List Row := [(row3 6 25 28), (row3 6 25 29), (row3 6 25 30), (row3 6 25 31), (row3 6 26 27), (row3 6 26 28), (row3 6 26 29), (row3 6 26 30), (row3 6 26 31), (row3 6 27 28), (row3 6 27 29), (row3 6 27 30), (row3 6 27 31), (row3 6 28 29), (row3 6 28 30), (row3 6 28 31)]

def b008_08_labels : List Row := [(row3 157 108 428), (row3 398 423 413), (row3 167 168 158), (row3 343 343 341), (row3 217 11 294), (row3 244 15 129), (row3 169 160 169), (row3 399 412 420), (row3 169 160 169), (row3 157 108 428), (row3 343 343 341), (row3 167 168 158), (row3 398 423 413), (row3 72 50 472), (row3 126 427 107), (row3 72 50 472)]

theorem b008_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_08_rows b008_08_labels 1642808159306704921495208808528 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_08_rows b008_08_labels]
    decide +kernel

def b008_09_rows : List Row := [(row3 6 29 30), (row3 6 29 31), (row3 6 30 31), (row3 7 8 9), (row3 7 8 10), (row3 7 8 11), (row3 7 8 12), (row3 7 8 13), (row3 7 8 14), (row3 7 8 15), (row3 7 8 16), (row3 7 8 17), (row3 7 8 18), (row3 7 8 19), (row3 7 8 20), (row3 7 8 21)]

def b008_09_labels : List Row := [(row3 91 430 458), (row3 128 130 130), (row3 91 458 430), (row3 92 75 74), (row3 425 425 424), (row3 474 488 35), (row3 85 80 79), (row3 389 385 388), (row3 137 138 143), (row3 409 408 408), (row3 358 357 358), (row3 188 197 196), (row3 307 310 322), (row3 172 175 178), (row3 212 221 212), (row3 290 307 290)]

theorem b008_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_09_rows b008_09_labels 13911822574298354422330889488416 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_09_rows b008_09_labels]
    decide +kernel

def b008_10_rows : List Row := [(row3 7 8 22), (row3 7 8 23), (row3 7 8 24), (row3 7 8 25), (row3 7 8 26), (row3 7 8 27), (row3 7 8 28), (row3 7 8 29), (row3 7 8 30), (row3 7 8 31), (row3 7 9 10), (row3 7 9 11), (row3 7 9 12), (row3 7 9 13), (row3 7 9 14), (row3 7 9 15)]

def b008_10_labels : List Row := [(row3 508 508 508), (row3 307 307 307), (row3 358 357 358), (row3 196 197 188), (row3 322 310 307), (row3 178 175 172), (row3 79 80 85), (row3 388 385 389), (row3 143 138 137), (row3 408 408 409), (row3 401 127 109), (row3 435 63 465), (row3 344 346 346), (row3 147 132 131), (row3 341 342 342), (row3 167 168 158)]

theorem b008_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_10_rows b008_10_labels 952558668876914501409167733072 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_10_rows b008_10_labels]
    decide +kernel

def b008_11_rows : List Row := [(row3 7 9 16), (row3 7 9 17), (row3 7 9 18), (row3 7 9 19), (row3 7 9 20), (row3 7 9 21), (row3 7 9 22), (row3 7 9 23), (row3 7 9 24), (row3 7 9 25), (row3 7 9 26), (row3 7 9 27), (row3 7 9 28), (row3 7 9 29), (row3 7 9 30), (row3 7 9 31)]

def b008_11_labels : List Row := [(row3 251 255 252), (row3 321 324 324), (row3 252 256 252), (row3 310 313 313), (row3 297 302 302), (row3 260 260 265), (row3 508 278 278), (row3 262 268 268), (row3 193 188 194), (row3 321 324 324), (row3 255 258 262), (row3 331 334 334), (row3 413 423 398), (row3 169 160 169), (row3 341 343 343), (row3 143 138 137)]

theorem b008_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_11_rows b008_11_labels 31874882624809517896847403246 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_11_rows b008_11_labels]
    decide +kernel

def b008_12_rows : List Row := [(row3 7 10 11), (row3 7 10 12), (row3 7 10 13), (row3 7 10 14), (row3 7 10 15), (row3 7 10 16), (row3 7 10 17), (row3 7 10 18), (row3 7 10 19), (row3 7 10 20), (row3 7 10 21), (row3 7 10 22), (row3 7 10 23), (row3 7 10 24), (row3 7 10 25), (row3 7 10 26)]

def b008_12_labels : List Row := [(row3 51 489 38), (row3 169 160 169), (row3 338 508 338), (row3 140 162 140), (row3 389 385 388), (row3 307 508 307), (row3 258 508 258), (row3 322 508 322), (row3 219 208 219), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 290 508 290), (row3 322 508 322), (row3 258 508 258), (row3 307 508 307)]

theorem b008_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_12_rows b008_12_labels 6191965745961351347794818321504 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_12_rows b008_12_labels]
    decide +kernel

def b008_13_rows : List Row := [(row3 7 10 27), (row3 7 10 28), (row3 7 10 29), (row3 7 10 30), (row3 7 10 31), (row3 7 11 12), (row3 7 11 13), (row3 7 11 14), (row3 7 11 15), (row3 7 11 16), (row3 7 11 17), (row3 7 11 18), (row3 7 11 19), (row3 7 11 20), (row3 7 11 21), (row3 7 11 22)]

def b008_13_labels : List Row := [(row3 219 208 219), (row3 140 162 140), (row3 338 508 338), (row3 169 160 169), (row3 388 385 389), (row3 418 464 62), (row3 157 108 428), (row3 417 463 61), (row3 73 39 490), (row3 204 112 404), (row3 508 326 326), (row3 205 113 404), (row3 379 454 86), (row3 297 315 315), (row3 268 268 508), (row3 508 303 303)]

theorem b008_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_13_rows b008_13_labels 5986086400726670561953050609804 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_13_rows b008_13_labels]
    decide +kernel

def b008_14_rows : List Row := [(row3 7 11 23), (row3 7 11 24), (row3 7 11 25), (row3 7 11 26), (row3 7 11 27), (row3 7 11 28), (row3 7 11 29), (row3 7 11 30), (row3 7 11 31), (row3 7 12 13), (row3 7 12 14), (row3 7 12 15), (row3 7 12 16), (row3 7 12 17), (row3 7 12 18), (row3 7 12 19)]

def b008_14_labels : List Row := [(row3 228 121 366), (row3 176 188 177), (row3 321 323 323), (row3 206 258 211), (row3 372 383 362), (row3 434 436 426), (row3 140 162 140), (row3 413 423 398), (row3 79 80 85), (row3 222 200 198), (row3 327 328 328), (row3 350 171 122), (row3 224 202 199), (row3 297 298 298), (row3 260 265 260), (row3 310 311 311)]

theorem b008_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_14_rows b008_14_labels 2485348046792898223729400427780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_14_rows b008_14_labels]
    decide +kernel

def b008_15_rows : List Row := [(row3 7 12 20), (row3 7 12 21), (row3 7 12 22), (row3 7 12 23), (row3 7 12 24), (row3 7 12 25), (row3 7 12 26), (row3 7 12 27), (row3 7 12 28), (row3 7 12 29), (row3 7 12 30), (row3 7 12 31), (row3 7 13 14), (row3 7 13 15), (row3 7 13 16), (row3 7 13 17)]

def b008_15_labels : List Row := [(row3 292 295 295), (row3 267 267 270), (row3 508 276 276), (row3 264 267 266), (row3 236 230 237), (row3 297 299 299), (row3 262 268 268), (row3 310 312 312), (row3 372 383 362), (row3 219 208 219), (row3 331 334 334), (row3 178 175 172), (row3 258 258 508), (row3 319 319 508), (row3 508 508 508), (row3 508 508 508)]

theorem b008_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b008_15_rows b008_15_labels 8051118672035469450006705618 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b008_15_rows b008_15_labels]
    decide +kernel

theorem checked008 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_008 QuarticIntegerComputationalData.ids32_008 31589295653934713609593691081976 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b008_00_rows ++ b008_01_rows) ++ (b008_02_rows ++ b008_03_rows)) ++ ((b008_04_rows ++ b008_05_rows) ++ (b008_06_rows ++ b008_07_rows))) ++ (((b008_08_rows ++ b008_09_rows) ++ (b008_10_rows ++ b008_11_rows)) ++ ((b008_12_rows ++ b008_13_rows) ++ (b008_14_rows ++ b008_15_rows))))
    ((((b008_00_labels ++ b008_01_labels) ++ (b008_02_labels ++ b008_03_labels)) ++ ((b008_04_labels ++ b008_05_labels) ++ (b008_06_labels ++ b008_07_labels))) ++ (((b008_08_labels ++ b008_09_labels) ++ (b008_10_labels ++ b008_11_labels)) ++ ((b008_12_labels ++ b008_13_labels) ++ (b008_14_labels ++ b008_15_labels)))) 31589295653934713609593691081976
  exact ((((b008_00_checked.append (c := 441560427449374621546129584) b008_01_checked (by decide +kernel)).append (c := 930766674354651982721904444) (b008_02_checked.append (c := 489206246905277361175774860) b008_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 378780056674974643534301584008) ((b008_04_checked.append (c := 8898861442929093005468641200) b008_05_checked (by decide +kernel)).append (c := 377849290000619991551579679564) (b008_06_checked.append (c := 368950428557690898546111038364) b008_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 31589295653934713609593691081976) (((b008_08_checked.append (c := 15554630733605059343826098296944) b008_09_checked (by decide +kernel)).append (c := 16539064285106783363132113433262) (b008_10_checked.append (c := 984433551501724019306015136318) b008_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 31210515597259738966059389497968) ((b008_12_checked.append (c := 12178052146688021909747868931308) b008_13_checked (by decide +kernel)).append (c := 14671451312152955602927276064706) (b008_14_checked.append (c := 2493399165464933693179407133398) b008_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b009_00_rows : List Row := [(row3 7 13 18), (row3 7 13 19), (row3 7 13 20), (row3 7 13 21), (row3 7 13 22), (row3 7 13 23), (row3 7 13 24), (row3 7 13 25), (row3 7 13 26), (row3 7 13 27), (row3 7 13 28), (row3 7 13 29), (row3 7 13 30), (row3 7 13 31), (row3 7 14 15), (row3 7 14 16)]

def b009_00_labels : List Row := [(row3 508 508 508), (row3 268 268 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 268 508 268), (row3 508 508 508), (row3 262 268 268), (row3 206 258 211), (row3 307 508 307), (row3 255 258 262), (row3 322 310 307), (row3 185 186 188), (row3 268 508 268)]

theorem b009_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_00_rows b009_00_labels 5983588159081151731687010016 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_00_rows b009_00_labels]
    decide +kernel

def b009_01_rows : List Row := [(row3 7 14 17), (row3 7 14 18), (row3 7 14 19), (row3 7 14 20), (row3 7 14 21), (row3 7 14 22), (row3 7 14 23), (row3 7 14 24), (row3 7 14 25), (row3 7 14 26), (row3 7 14 27), (row3 7 14 28), (row3 7 14 29), (row3 7 14 30), (row3 7 14 31), (row3 7 15 16)]

def b009_01_labels : List Row := [(row3 508 508 508), (row3 268 508 268), (row3 297 298 298), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 297 299 299), (row3 321 323 323), (row3 258 508 258), (row3 321 324 324), (row3 196 197 188), (row3 307 508 307)]

theorem b009_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_01_rows b009_01_labels 448581868119908705354231808 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_01_rows b009_01_labels]
    decide +kernel

def b009_02_rows : List Row := [(row3 7 15 17), (row3 7 15 18), (row3 7 15 19), (row3 7 15 20), (row3 7 15 21), (row3 7 15 22), (row3 7 15 23), (row3 7 15 24), (row3 7 15 25), (row3 7 15 26), (row3 7 15 27), (row3 7 15 28), (row3 7 15 29), (row3 7 15 30), (row3 7 15 31), (row3 7 16 17)]

def b009_02_labels : List Row := [(row3 268 508 268), (row3 307 508 307), (row3 213 232 214), (row3 269 508 269), (row3 508 508 508), (row3 271 508 271), (row3 290 508 290), (row3 307 508 307), (row3 268 508 268), (row3 290 508 290), (row3 236 230 237), (row3 176 188 177), (row3 322 508 322), (row3 193 188 194), (row3 358 357 358), (row3 508 508 508)]

theorem b009_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_02_rows b009_02_labels 9054658445708418621521052456 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_02_rows b009_02_labels]
    decide +kernel

def b009_03_rows : List Row := [(row3 7 16 18), (row3 7 16 19), (row3 7 16 20), (row3 7 16 21), (row3 7 16 22), (row3 7 16 23), (row3 7 16 24), (row3 7 16 25), (row3 7 16 26), (row3 7 16 27), (row3 7 16 28), (row3 7 16 29), (row3 7 16 30), (row3 7 16 31), (row3 7 17 18), (row3 7 17 19)]

def b009_03_labels : List Row := [(row3 508 508 508), (row3 272 272 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 271 508 271), (row3 508 508 508), (row3 264 267 266), (row3 228 121 366), (row3 290 508 290), (row3 262 268 268), (row3 307 307 307), (row3 508 508 508), (row3 508 508 508)]

theorem b009_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_03_rows b009_03_labels 2957506595487717492419201520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_03_rows b009_03_labels]
    decide +kernel

def b009_04_rows : List Row := [(row3 7 17 20), (row3 7 17 21), (row3 7 17 22), (row3 7 17 23), (row3 7 17 24), (row3 7 17 25), (row3 7 17 26), (row3 7 17 27), (row3 7 17 28), (row3 7 17 29), (row3 7 17 30), (row3 7 17 31), (row3 7 18 19), (row3 7 18 20), (row3 7 18 21), (row3 7 18 22)]

def b009_04_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 276 276), (row3 508 303 303), (row3 268 508 268), (row3 508 278 278), (row3 508 508 508), (row3 272 272 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b009_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_04_rows b009_04_labels 36156013345078879930340400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_04_rows b009_04_labels]
    decide +kernel

def b009_05_rows : List Row := [(row3 7 18 23), (row3 7 18 24), (row3 7 18 25), (row3 7 18 26), (row3 7 18 27), (row3 7 18 28), (row3 7 18 29), (row3 7 18 30), (row3 7 18 31), (row3 7 19 20), (row3 7 19 21), (row3 7 19 22), (row3 7 19 23), (row3 7 19 24), (row3 7 19 25), (row3 7 19 26)]

def b009_05_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 267 267 270), (row3 268 268 508), (row3 508 508 508), (row3 260 260 265), (row3 290 307 290), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 269 508 269), (row3 508 508 508), (row3 272 508 272)]

theorem b009_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_05_rows b009_05_labels 14722544914866674230521960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_05_rows b009_05_labels]
    decide +kernel

def b009_06_rows : List Row := [(row3 7 19 27), (row3 7 19 28), (row3 7 19 29), (row3 7 19 30), (row3 7 19 31), (row3 7 20 21), (row3 7 20 22), (row3 7 20 23), (row3 7 20 24), (row3 7 20 25), (row3 7 20 26), (row3 7 20 27), (row3 7 20 28), (row3 7 20 29), (row3 7 20 30), (row3 7 20 31)]

def b009_06_labels : List Row := [(row3 292 295 295), (row3 297 315 315), (row3 268 508 268), (row3 297 302 302), (row3 212 221 212), (row3 272 272 508), (row3 508 508 508), (row3 272 272 508), (row3 213 232 214), (row3 297 298 298), (row3 268 268 508), (row3 310 311 311), (row3 379 454 86), (row3 219 208 219), (row3 310 313 313), (row3 172 175 178)]

theorem b009_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_06_rows b009_06_labels 65197753117977593762051104440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_06_rows b009_06_labels]
    decide +kernel

def b009_07_rows : List Row := [(row3 7 21 22), (row3 7 21 23), (row3 7 21 24), (row3 7 21 25), (row3 7 21 26), (row3 7 21 27), (row3 7 21 28), (row3 7 21 29), (row3 7 21 30), (row3 7 21 31), (row3 7 22 23), (row3 7 22 24), (row3 7 22 25), (row3 7 22 26), (row3 7 22 27), (row3 7 22 28)]

def b009_07_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 307 508 307), (row3 268 508 268), (row3 508 508 508), (row3 260 265 260), (row3 205 113 404), (row3 322 508 322), (row3 252 256 252), (row3 307 310 322), (row3 508 508 508), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 297 298 298), (row3 508 326 326)]

theorem b009_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_07_rows b009_07_labels 9275602438563107302382087160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_07_rows b009_07_labels]
    decide +kernel

def b009_08_rows : List Row := [(row3 7 22 29), (row3 7 22 30), (row3 7 22 31), (row3 7 23 24), (row3 7 23 25), (row3 7 23 26), (row3 7 23 27), (row3 7 23 28), (row3 7 23 29), (row3 7 23 30), (row3 7 23 31), (row3 7 24 25), (row3 7 24 26), (row3 7 24 27), (row3 7 24 28), (row3 7 24 29)]

def b009_08_labels : List Row := [(row3 258 508 258), (row3 321 324 324), (row3 188 197 196), (row3 307 508 307), (row3 268 508 268), (row3 508 508 508), (row3 224 202 199), (row3 204 112 404), (row3 307 508 307), (row3 251 255 252), (row3 358 357 358), (row3 185 186 188), (row3 319 319 508), (row3 350 171 122), (row3 73 39 490), (row3 389 385 388)]

theorem b009_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_08_rows b009_08_labels 5578141770779663446891321486608 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_08_rows b009_08_labels]
    decide +kernel

def b009_09_rows : List Row := [(row3 7 24 30), (row3 7 24 31), (row3 7 25 26), (row3 7 25 27), (row3 7 25 28), (row3 7 25 29), (row3 7 25 30), (row3 7 25 31), (row3 7 26 27), (row3 7 26 28), (row3 7 26 29), (row3 7 26 30), (row3 7 26 31), (row3 7 27 28), (row3 7 27 29), (row3 7 27 30)]

def b009_09_labels : List Row := [(row3 167 168 158), (row3 409 408 408), (row3 258 258 508), (row3 327 328 328), (row3 417 463 61), (row3 140 162 140), (row3 341 342 342), (row3 137 138 143), (row3 222 200 198), (row3 157 108 428), (row3 338 508 338), (row3 147 132 131), (row3 389 385 388), (row3 418 464 62), (row3 169 160 169), (row3 344 346 346)]

theorem b009_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_09_rows b009_09_labels 404741023446689880659437144068 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_09_rows b009_09_labels]
    decide +kernel

def b009_10_rows : List Row := [(row3 7 27 31), (row3 7 28 29), (row3 7 28 30), (row3 7 28 31), (row3 7 29 30), (row3 7 29 31), (row3 7 30 31), (row3 8 9 10), (row3 8 9 11), (row3 8 9 12), (row3 8 9 13), (row3 8 9 14), (row3 8 9 15), (row3 8 9 16), (row3 8 9 17), (row3 8 9 18)]

def b009_10_labels : List Row := [(row3 85 80 79), (row3 51 489 38), (row3 435 63 465), (row3 474 488 35), (row3 401 127 109), (row3 425 425 424), (row3 92 75 74), (row3 56 40 476), (row3 492 480 480), (row3 491 481 479), (row3 57 41 475), (row3 429 456 89), (row3 77 76 93), (row3 97 97 105), (row3 407 450 104), (row3 156 116 377)]

theorem b009_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_10_rows b009_10_labels 31684959647791483213049914683888 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_10_rows b009_10_labels]
    decide +kernel

def b009_11_rows : List Row := [(row3 8 9 19), (row3 8 9 20), (row3 8 9 21), (row3 8 9 22), (row3 8 9 23), (row3 8 9 24), (row3 8 9 25), (row3 8 9 26), (row3 8 9 27), (row3 8 9 28), (row3 8 9 29), (row3 8 9 30), (row3 8 9 31), (row3 8 10 11), (row3 8 10 12), (row3 8 10 13)]

def b009_11_labels : List Row := [(row3 393 394 370), (row3 354 356 349), (row3 203 123 351), (row3 508 304 304), (row3 233 271 234), (row3 218 223 218), (row3 308 314 314), (row3 265 265 508), (row3 308 309 309), (row3 400 406 392), (row3 171 122 350), (row3 321 329 329), (row3 186 188 185), (row3 56 476 40), (row3 81 87 78), (row3 390 387 388)]

theorem b009_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_11_rows b009_11_labels 2941158214268618847345183066294 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_11_rows b009_11_labels]
    decide +kernel

def b009_12_rows : List Row := [(row3 8 10 14), (row3 8 10 15), (row3 8 10 16), (row3 8 10 17), (row3 8 10 18), (row3 8 10 19), (row3 8 10 20), (row3 8 10 21), (row3 8 10 22), (row3 8 10 23), (row3 8 10 24), (row3 8 10 25), (row3 8 10 26), (row3 8 10 27), (row3 8 10 28), (row3 8 10 29)]

def b009_12_labels : List Row := [(row3 139 159 139), (row3 390 387 388), (row3 357 357 357), (row3 192 187 192), (row3 327 508 327), (row3 192 187 192), (row3 238 231 238), (row3 290 508 290), (row3 268 508 268), (row3 290 508 290), (row3 307 508 307), (row3 265 508 265), (row3 508 508 508), (row3 265 508 265), (row3 182 231 182), (row3 319 508 319)]

theorem b009_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_12_rows b009_12_labels 20202051666777701643464266368 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_12_rows b009_12_labels]
    decide +kernel

def b009_13_rows : List Row := [(row3 8 10 30), (row3 8 10 31), (row3 8 11 12), (row3 8 11 13), (row3 8 11 14), (row3 8 11 15), (row3 8 11 16), (row3 8 11 17), (row3 8 11 18), (row3 8 11 19), (row3 8 11 20), (row3 8 11 21), (row3 8 11 22), (row3 8 11 23), (row3 8 11 24), (row3 8 11 25)]

def b009_13_labels : List Row := [(row3 257 508 257), (row3 319 508 319), (row3 491 481 479), (row3 77 76 93), (row3 429 456 89), (row3 57 41 475), (row3 97 97 105), (row3 393 394 370), (row3 156 116 377), (row3 407 450 104), (row3 354 356 349), (row3 233 271 234), (row3 508 304 304), (row3 203 123 351), (row3 218 223 218), (row3 308 309 309)]

theorem b009_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_13_rows b009_13_labels 5731842294841693263315938218200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_13_rows b009_13_labels]
    decide +kernel

def b009_14_rows : List Row := [(row3 8 11 26), (row3 8 11 27), (row3 8 11 28), (row3 8 11 29), (row3 8 11 30), (row3 8 11 31), (row3 8 12 13), (row3 8 12 14), (row3 8 12 15), (row3 8 12 16), (row3 8 12 17), (row3 8 12 18), (row3 8 12 19), (row3 8 12 20), (row3 8 12 21), (row3 8 12 22)]

def b009_14_labels : List Row := [(row3 265 265 508), (row3 308 314 314), (row3 400 406 392), (row3 186 188 185), (row3 321 329 329), (row3 171 122 350), (row3 84 42 477), (row3 410 455 88), (row3 84 42 477), (row3 106 43 478), (row3 379 454 86), (row3 240 114 405), (row3 379 454 86), (row3 348 449 103), (row3 347 117 378), (row3 508 303 303)]

theorem b009_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_14_rows b009_14_labels 6250299302833980974850976208010 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_14_rows b009_14_labels]
    decide +kernel

def b009_15_rows : List Row := [(row3 8 12 23), (row3 8 12 24), (row3 8 12 25), (row3 8 12 26), (row3 8 12 27), (row3 8 12 28), (row3 8 12 29), (row3 8 12 30), (row3 8 12 31), (row3 8 13 14), (row3 8 13 15), (row3 8 13 16), (row3 8 13 17), (row3 8 13 18), (row3 8 13 19), (row3 8 13 20)]

def b009_15_labels : List Row := [(row3 347 117 378), (row3 242 125 352), (row3 286 296 296), (row3 271 271 508), (row3 286 296 296), (row3 371 382 363), (row3 214 232 213), (row3 297 299 299), (row3 214 232 213), (row3 154 161 153), (row3 387 386 386), (row3 358 357 358), (row3 177 188 176), (row3 322 508 322), (row3 194 188 193), (row3 237 230 236)]

theorem b009_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b009_15_rows b009_15_labels 335881444718317425555555605580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b009_15_rows b009_15_labels]
    decide +kernel

theorem checked009 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_009 QuarticIntegerComputationalData.ids32_009 53040194319530422596481366228776 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b009_00_rows ++ b009_01_rows) ++ (b009_02_rows ++ b009_03_rows)) ++ ((b009_04_rows ++ b009_05_rows) ++ (b009_06_rows ++ b009_07_rows))) ++ (((b009_08_rows ++ b009_09_rows) ++ (b009_10_rows ++ b009_11_rows)) ++ ((b009_12_rows ++ b009_13_rows) ++ (b009_14_rows ++ b009_15_rows))))
    ((((b009_00_labels ++ b009_01_labels) ++ (b009_02_labels ++ b009_03_labels)) ++ ((b009_04_labels ++ b009_05_labels) ++ (b009_06_labels ++ b009_07_labels))) ++ (((b009_08_labels ++ b009_09_labels) ++ (b009_10_labels ++ b009_11_labels)) ++ ((b009_12_labels ++ b009_13_labels) ++ (b009_14_labels ++ b009_15_labels)))) 53040194319530422596481366228776
  exact ((((b009_00_checked.append (c := 6432170027201060437041241824) b009_01_checked (by decide +kernel)).append (c := 18444335068397196550981495800) (b009_02_checked.append (c := 12012165041196136113940253976) b009_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 92968569183197843169575549760) ((b009_04_checked.append (c := 50878558259945554160862360) b009_05_checked (by decide +kernel)).append (c := 74524234114800646618594053960) (b009_06_checked.append (c := 74473355556540701064433191600) b009_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 53040194319530422596481366228776) (((b009_08_checked.append (c := 5982882794226353327550758630676) b009_09_checked (by decide +kernel)).append (c := 40609000656286455387945856380858) (b009_10_checked.append (c := 34626117862060102060395097750182) b009_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 52947225750347224753311790679016) ((b009_12_checked.append (c := 5752044346508470964959402484568) b009_13_checked (by decide +kernel)).append (c := 12338225094060769365365934298158) (b009_14_checked.append (c := 6586180747552298400406531813590) b009_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b010_00_rows : List Row := [(row3 8 13 21), (row3 8 13 22), (row3 8 13 23), (row3 8 13 24), (row3 8 13 25), (row3 8 13 26), (row3 8 13 27), (row3 8 13 28), (row3 8 13 29), (row3 8 13 30), (row3 8 13 31), (row3 8 14 15), (row3 8 14 16), (row3 8 14 17), (row3 8 14 18), (row3 8 14 19)]

def b010_00_labels : List Row := [(row3 307 508 307), (row3 268 508 268), (row3 290 508 290), (row3 290 508 290), (row3 269 508 269), (row3 508 508 508), (row3 271 508 271), (row3 214 232 213), (row3 307 508 307), (row3 268 508 268), (row3 307 508 307), (row3 154 153 161), (row3 195 195 187), (row3 321 324 324), (row3 258 508 258), (row3 321 324 324)]

theorem b010_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_00_rows b010_00_labels 9435260805211000869865548768 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_00_rows b010_00_labels]
    decide +kernel

def b010_01_rows : List Row := [(row3 8 14 20), (row3 8 14 21), (row3 8 14 22), (row3 8 14 23), (row3 8 14 24), (row3 8 14 25), (row3 8 14 26), (row3 8 14 27), (row3 8 14 28), (row3 8 14 29), (row3 8 14 30), (row3 8 14 31), (row3 8 15 16), (row3 8 15 17), (row3 8 15 18), (row3 8 15 19)]

def b010_01_labels : List Row := [(row3 297 300 300), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 297 299 299), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 358 357 358), (row3 194 188 193), (row3 322 508 322), (row3 177 188 176)]

theorem b010_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_01_rows b010_01_labels 6345412925733593886978205992 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_01_rows b010_01_labels]
    decide +kernel

def b010_02_rows : List Row := [(row3 8 15 20), (row3 8 15 21), (row3 8 15 22), (row3 8 15 23), (row3 8 15 24), (row3 8 15 25), (row3 8 15 26), (row3 8 15 27), (row3 8 15 28), (row3 8 15 29), (row3 8 15 30), (row3 8 15 31), (row3 8 16 17), (row3 8 16 18), (row3 8 16 19), (row3 8 16 20)]

def b010_02_labels : List Row := [(row3 237 230 236), (row3 290 508 290), (row3 268 508 268), (row3 307 508 307), (row3 290 508 290), (row3 271 508 271), (row3 508 508 508), (row3 269 508 269), (row3 214 232 213), (row3 307 508 307), (row3 268 508 268), (row3 307 508 307), (row3 218 223 218), (row3 307 508 307), (row3 218 223 218), (row3 352 125 242)]

theorem b010_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_02_rows b010_02_labels 12258904369520798273579165568 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_02_rows b010_02_labels]
    decide +kernel

def b010_03_rows : List Row := [(row3 8 16 21), (row3 8 16 22), (row3 8 16 23), (row3 8 16 24), (row3 8 16 25), (row3 8 16 26), (row3 8 16 27), (row3 8 16 28), (row3 8 16 29), (row3 8 16 30), (row3 8 16 31), (row3 8 17 18), (row3 8 17 19), (row3 8 17 20), (row3 8 17 21), (row3 8 17 22)]

def b010_03_labels : List Row := [(row3 290 508 290), (row3 271 508 271), (row3 290 508 290), (row3 290 508 290), (row3 271 508 271), (row3 508 508 508), (row3 271 508 271), (row3 242 125 352), (row3 290 508 290), (row3 271 508 271), (row3 290 508 290), (row3 265 508 265), (row3 308 309 309), (row3 292 295 295), (row3 271 508 271), (row3 508 508 508)]

theorem b010_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_03_rows b010_03_labels 6361120771595772442050208320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_03_rows b010_03_labels]
    decide +kernel

def b010_04_rows : List Row := [(row3 8 17 23), (row3 8 17 24), (row3 8 17 25), (row3 8 17 26), (row3 8 17 27), (row3 8 17 28), (row3 8 17 29), (row3 8 17 30), (row3 8 17 31), (row3 8 18 19), (row3 8 18 20), (row3 8 18 21), (row3 8 18 22), (row3 8 18 23), (row3 8 18 24), (row3 8 18 25)]

def b010_04_labels : List Row := [(row3 271 508 271), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 286 296 296), (row3 269 508 269), (row3 508 508 508), (row3 271 508 271), (row3 265 265 508), (row3 268 268 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b010_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_04_rows b010_04_labels 60589074981024246739598040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_04_rows b010_04_labels]
    decide +kernel

def b010_05_rows : List Row := [(row3 8 18 26), (row3 8 18 27), (row3 8 18 28), (row3 8 18 29), (row3 8 18 30), (row3 8 18 31), (row3 8 19 20), (row3 8 19 21), (row3 8 19 22), (row3 8 19 23), (row3 8 19 24), (row3 8 19 25), (row3 8 19 26), (row3 8 19 27), (row3 8 19 28), (row3 8 19 29)]

def b010_05_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 271 271 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 292 295 295), (row3 271 508 271), (row3 508 508 508), (row3 271 508 271), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 286 296 296), (row3 271 508 271)]

theorem b010_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_05_rows b010_05_labels 61407467295960006310326240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_05_rows b010_05_labels]
    decide +kernel

def b010_06_rows : List Row := [(row3 8 19 30), (row3 8 19 31), (row3 8 20 21), (row3 8 20 22), (row3 8 20 23), (row3 8 20 24), (row3 8 20 25), (row3 8 20 26), (row3 8 20 27), (row3 8 20 28), (row3 8 20 29), (row3 8 20 30), (row3 8 20 31), (row3 8 21 22), (row3 8 21 23), (row3 8 21 24)]

def b010_06_labels : List Row := [(row3 508 508 508), (row3 269 508 269), (row3 243 239 239), (row3 283 284 284), (row3 243 239 239), (row3 352 125 242), (row3 292 295 295), (row3 268 268 271), (row3 292 295 295), (row3 348 449 103), (row3 237 230 236), (row3 297 300 300), (row3 237 230 236), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290)]

theorem b010_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_06_rows b010_06_labels 39716149322445136575417151044 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_06_rows b010_06_labels]
    decide +kernel

def b010_07_rows : List Row := [(row3 8 21 25), (row3 8 21 26), (row3 8 21 27), (row3 8 21 28), (row3 8 21 29), (row3 8 21 30), (row3 8 21 31), (row3 8 22 23), (row3 8 22 24), (row3 8 22 25), (row3 8 22 26), (row3 8 22 27), (row3 8 22 28), (row3 8 22 29), (row3 8 22 30), (row3 8 22 31)]

def b010_07_labels : List Row := [(row3 271 508 271), (row3 508 508 508), (row3 271 508 271), (row3 347 117 378), (row3 307 508 307), (row3 268 508 268), (row3 290 508 290), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 303 303), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268)]

theorem b010_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_07_rows b010_07_labels 4367188865444470137234409680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_07_rows b010_07_labels]
    decide +kernel

def b010_08_rows : List Row := [(row3 8 23 24), (row3 8 23 25), (row3 8 23 26), (row3 8 23 27), (row3 8 23 28), (row3 8 23 29), (row3 8 23 30), (row3 8 23 31), (row3 8 24 25), (row3 8 24 26), (row3 8 24 27), (row3 8 24 28), (row3 8 24 29), (row3 8 24 30), (row3 8 24 31), (row3 8 25 26)]

def b010_08_labels : List Row := [(row3 290 508 290), (row3 271 508 271), (row3 508 508 508), (row3 271 508 271), (row3 347 117 378), (row3 290 508 290), (row3 268 508 268), (row3 307 508 307), (row3 218 218 223), (row3 307 307 508), (row3 218 218 223), (row3 106 43 478), (row3 358 357 358), (row3 195 195 187), (row3 358 357 358), (row3 265 265 508)]

theorem b010_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_08_rows b010_08_labels 1689941388955137125442253951608 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_08_rows b010_08_labels]
    decide +kernel

def b010_09_rows : List Row := [(row3 8 25 27), (row3 8 25 28), (row3 8 25 29), (row3 8 25 30), (row3 8 25 31), (row3 8 26 27), (row3 8 26 28), (row3 8 26 29), (row3 8 26 30), (row3 8 26 31), (row3 8 27 28), (row3 8 27 29), (row3 8 27 30), (row3 8 27 31), (row3 8 28 29), (row3 8 28 30)]

def b010_09_labels : List Row := [(row3 308 309 309), (row3 379 454 86), (row3 177 188 176), (row3 321 324 324), (row3 194 188 193), (row3 265 508 265), (row3 240 114 405), (row3 322 508 322), (row3 258 508 258), (row3 322 508 322), (row3 379 454 86), (row3 194 188 193), (row3 321 324 324), (row3 177 188 176), (row3 84 477 42), (row3 410 88 455)]

theorem b010_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_09_rows b010_09_labels 2066265753040456240761384545784 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_09_rows b010_09_labels]
    decide +kernel

def b010_10_rows : List Row := [(row3 8 28 31), (row3 8 29 30), (row3 8 29 31), (row3 8 30 31), (row3 9 10 11), (row3 9 10 12), (row3 9 10 13), (row3 9 10 14), (row3 9 10 15), (row3 9 10 16), (row3 9 10 17), (row3 9 10 18), (row3 9 10 19), (row3 9 10 20), (row3 9 10 21), (row3 9 10 22)]

def b010_10_labels : List Row := [(row3 84 477 42), (row3 154 153 161), (row3 387 386 386), (row3 154 161 153), (row3 71 469 71), (row3 422 415 397), (row3 48 59 58), (row3 411 461 70), (row3 133 110 402), (row3 150 150 180), (row3 394 393 370), (row3 156 116 377), (row3 320 13 166), (row3 305 508 305), (row3 201 201 225), (row3 293 11 216)]

theorem b010_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_10_rows b010_10_labels 2842506113472344989473809803284 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_10_rows b010_10_labels]
    decide +kernel

def b010_11_rows : List Row := [(row3 9 10 23), (row3 9 10 24), (row3 9 10 25), (row3 9 10 26), (row3 9 10 27), (row3 9 10 28), (row3 9 10 29), (row3 9 10 30), (row3 9 10 31), (row3 9 11 12), (row3 9 11 13), (row3 9 11 14), (row3 9 11 15), (row3 9 11 16), (row3 9 11 17), (row3 9 11 18)]

def b010_11_labels : List Row := [(row3 508 508 508), (row3 265 508 265), (row3 289 508 289), (row3 508 508 508), (row3 279 508 279), (row3 330 508 330), (row3 198 200 222), (row3 294 11 217), (row3 258 508 258), (row3 134 134 135), (row3 421 396 416), (row3 136 136 144), (row3 396 421 416), (row3 337 337 335), (row3 187 192 192), (row3 336 336 335)]

theorem b010_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_11_rows b010_11_labels 57459994396335314830269716976 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_11_rows b010_11_labels]
    decide +kernel

def b010_12_rows : List Row := [(row3 9 11 19), (row3 9 11 20), (row3 9 11 21), (row3 9 11 22), (row3 9 11 23), (row3 9 11 24), (row3 9 11 25), (row3 9 11 26), (row3 9 11 27), (row3 9 11 28), (row3 9 11 29), (row3 9 11 30), (row3 9 11 31), (row3 9 12 13), (row3 9 12 14), (row3 9 12 15)]

def b010_12_labels : List Row := [(row3 192 187 192), (row3 263 263 259), (row3 301 301 297), (row3 268 268 262), (row3 301 301 297), (row3 309 309 308), (row3 259 261 259), (row3 279 279 508), (row3 261 259 259), (row3 149 149 179), (row3 328 328 327), (row3 254 254 252), (row3 328 328 327), (row3 102 69 467), (row3 151 152 155), (row3 361 384 375)]

theorem b010_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_12_rows b010_12_labels 252089953510447228546091748456 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_12_rows b010_12_labels]
    decide +kernel

def b010_13_rows : List Row := [(row3 9 12 16), (row3 9 12 17), (row3 9 12 18), (row3 9 12 19), (row3 9 12 20), (row3 9 12 21), (row3 9 12 22), (row3 9 12 23), (row3 9 12 24), (row3 9 12 25), (row3 9 12 26), (row3 9 12 27), (row3 9 12 28), (row3 9 12 29), (row3 9 12 30), (row3 9 12 31)]

def b010_13_labels : List Row := [(row3 362 383 372), (row3 172 175 178), (row3 334 334 331), (row3 219 208 219), (row3 237 230 236), (row3 312 312 310), (row3 268 268 262), (row3 299 299 297), (row3 295 295 292), (row3 266 267 264), (row3 276 276 508), (row3 270 267 267), (row3 199 202 224), (row3 311 311 310), (row3 260 265 260), (row3 298 298 297)]

theorem b010_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_13_rows b010_13_labels 10924514797190354233162701138 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_13_rows b010_13_labels]
    decide +kernel

def b010_14_rows : List Row := [(row3 9 13 14), (row3 9 13 15), (row3 9 13 16), (row3 9 13 17), (row3 9 13 18), (row3 9 13 19), (row3 9 13 20), (row3 9 13 21), (row3 9 13 22), (row3 9 13 23), (row3 9 13 24), (row3 9 13 25), (row3 9 13 26), (row3 9 13 27), (row3 9 13 28), (row3 9 13 29)]

def b010_14_labels : List Row := [(row3 391 462 68), (row3 145 111 403), (row3 204 112 404), (row3 124 460 67), (row3 205 113 404), (row3 245 14 141), (row3 247 13 165), (row3 347 117 378), (row3 246 13 164), (row3 508 508 508), (row3 271 508 271), (row3 249 11 215), (row3 508 508 508), (row3 276 508 276), (row3 316 508 316), (row3 199 202 224)]

theorem b010_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_14_rows b010_14_labels 366557214573541593521898783900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_14_rows b010_14_labels]
    decide +kernel

def b010_15_rows : List Row := [(row3 9 13 30), (row3 9 13 31), (row3 9 14 15), (row3 9 14 16), (row3 9 14 17), (row3 9 14 18), (row3 9 14 19), (row3 9 14 20), (row3 9 14 21), (row3 9 14 22), (row3 9 14 23), (row3 9 14 24), (row3 9 14 25), (row3 9 14 26), (row3 9 14 27), (row3 9 14 28)]

def b010_15_labels : List Row := [(row3 306 508 306), (row3 268 508 268), (row3 339 339 335), (row3 324 324 321), (row3 188 197 196), (row3 323 323 321), (row3 258 508 258), (row3 268 508 268), (row3 299 299 297), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268)]

theorem b010_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b010_15_rows b010_15_labels 884234939885236478101109328 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b010_15_rows b010_15_labels]
    decide +kernel

theorem checked010 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_010 QuarticIntegerComputationalData.ids32_010 7365235201287565839725146974126 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b010_00_rows ++ b010_01_rows) ++ (b010_02_rows ++ b010_03_rows)) ++ ((b010_04_rows ++ b010_05_rows) ++ (b010_06_rows ++ b010_07_rows))) ++ (((b010_08_rows ++ b010_09_rows) ++ (b010_10_rows ++ b010_11_rows)) ++ ((b010_12_rows ++ b010_13_rows) ++ (b010_14_rows ++ b010_15_rows))))
    ((((b010_00_labels ++ b010_01_labels) ++ (b010_02_labels ++ b010_03_labels)) ++ ((b010_04_labels ++ b010_05_labels) ++ (b010_06_labels ++ b010_07_labels))) ++ (((b010_08_labels ++ b010_09_labels) ++ (b010_10_labels ++ b010_11_labels)) ++ ((b010_12_labels ++ b010_13_labels) ++ (b010_14_labels ++ b010_15_labels)))) 7365235201287565839725146974126
  exact ((((b010_00_checked.append (c := 15780673730944594756843754760) b010_01_checked (by decide +kernel)).append (c := 34400698872061165472473128648) (b010_02_checked.append (c := 18620025141116570715629373888) b010_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 78606033602227756438174613652) ((b010_04_checked.append (c := 121996542276984253049924280) b010_05_checked (by decide +kernel)).append (c := 44205334730166590965701485004) (b010_06_checked.append (c := 44083338187889606712651560724) b010_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7365235201287565839725146974126) (((b010_08_checked.append (c := 3756207141995593366203638497392) b010_09_checked (by decide +kernel)).append (c := 6656173249864273670507718017652) (b010_10_checked.append (c := 2899966107868680304304079520260) b010_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 7286629167685338083286972360474) ((b010_12_checked.append (c := 263014468307637582779254449594) b010_13_checked (by decide +kernel)).append (c := 630455917821064412779254342822) (b010_14_checked.append (c := 367441449513426829999999893228) b010_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b011_00_rows : List Row := [(row3 9 14 29), (row3 9 14 30), (row3 9 14 31), (row3 9 15 16), (row3 9 15 17), (row3 9 15 18), (row3 9 15 19), (row3 9 15 20), (row3 9 15 21), (row3 9 15 22), (row3 9 15 23), (row3 9 15 24), (row3 9 15 25), (row3 9 15 26), (row3 9 15 27), (row3 9 15 28)]

def b011_00_labels : List Row := [(row3 298 298 297), (row3 268 508 268), (row3 508 508 508), (row3 251 255 252), (row3 325 321 325), (row3 252 256 252), (row3 318 508 318), (row3 281 508 281), (row3 265 265 265), (row3 280 508 280), (row3 268 508 268), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 277 508 277), (row3 306 508 306)]

theorem b011_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_00_rows b011_00_labels 203807480314990578368345640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_00_rows b011_00_labels]
    decide +kernel

def b011_01_rows : List Row := [(row3 9 15 29), (row3 9 15 30), (row3 9 15 31), (row3 9 16 17), (row3 9 16 18), (row3 9 16 19), (row3 9 16 20), (row3 9 16 21), (row3 9 16 22), (row3 9 16 23), (row3 9 16 24), (row3 9 16 25), (row3 9 16 26), (row3 9 16 27), (row3 9 16 28), (row3 9 16 29)]

def b011_01_labels : List Row := [(row3 260 265 260), (row3 280 508 280), (row3 268 508 268), (row3 314 308 314), (row3 259 261 259), (row3 289 508 289), (row3 215 11 249), (row3 264 267 266), (row3 278 508 278), (row3 271 508 271), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 276 508 276), (row3 249 11 215), (row3 266 267 264)]

theorem b011_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_01_rows b011_01_labels 929774843109825471442896420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_01_rows b011_01_labels]
    decide +kernel

def b011_02_rows : List Row := [(row3 9 16 30), (row3 9 16 31), (row3 9 17 18), (row3 9 17 19), (row3 9 17 20), (row3 9 17 21), (row3 9 17 22), (row3 9 17 23), (row3 9 17 24), (row3 9 17 25), (row3 9 17 26), (row3 9 17 27), (row3 9 17 28), (row3 9 17 29), (row3 9 17 30), (row3 9 17 31)]

def b011_02_labels : List Row := [(row3 278 508 278), (row3 271 508 271), (row3 309 309 308), (row3 265 508 265), (row3 269 508 269), (row3 296 296 286), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 295 295 292), (row3 271 508 271), (row3 508 508 508)]

theorem b011_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_02_rows b011_02_labels 139722738938034986986577760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_02_rows b011_02_labels]
    decide +kernel

def b011_03_rows : List Row := [(row3 9 18 19), (row3 9 18 20), (row3 9 18 21), (row3 9 18 22), (row3 9 18 23), (row3 9 18 24), (row3 9 18 25), (row3 9 18 26), (row3 9 18 27), (row3 9 18 28), (row3 9 18 29), (row3 9 18 30), (row3 9 18 31), (row3 9 19 20), (row3 9 19 21), (row3 9 19 22)]

def b011_03_labels : List Row := [(row3 279 508 279), (row3 277 508 277), (row3 267 267 270), (row3 276 508 276), (row3 508 508 508), (row3 508 508 508), (row3 276 508 276), (row3 508 508 508), (row3 508 508 508), (row3 276 508 276), (row3 270 267 267), (row3 277 508 277), (row3 508 508 508), (row3 272 508 272), (row3 277 277 508), (row3 508 508 508)]

theorem b011_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_03_rows b011_03_labels 3684516851579968694489400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_03_rows b011_03_labels]
    decide +kernel

def b011_04_rows : List Row := [(row3 9 19 23), (row3 9 19 24), (row3 9 19 25), (row3 9 19 26), (row3 9 19 27), (row3 9 19 28), (row3 9 19 29), (row3 9 19 30), (row3 9 19 31), (row3 9 20 21), (row3 9 20 22), (row3 9 20 23), (row3 9 20 24), (row3 9 20 25), (row3 9 20 26), (row3 9 20 27)]

def b011_04_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 276 276 508), (row3 508 508 508), (row3 508 508 508), (row3 241 282 9), (row3 272 272 508), (row3 285 285 508), (row3 296 296 286), (row3 264 267 266), (row3 277 277 508), (row3 267 267 270)]

theorem b011_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_04_rows b011_04_labels 178895765804898520577288640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_04_rows b011_04_labels]
    decide +kernel

def b011_05_rows : List Row := [(row3 9 20 28), (row3 9 20 29), (row3 9 20 30), (row3 9 20 31), (row3 9 21 22), (row3 9 21 23), (row3 9 21 24), (row3 9 21 25), (row3 9 21 26), (row3 9 21 27), (row3 9 21 28), (row3 9 21 29), (row3 9 21 30), (row3 9 21 31), (row3 9 22 23), (row3 9 22 24)]

def b011_05_labels : List Row := [(row3 347 117 378), (row3 312 312 310), (row3 265 265 265), (row3 299 299 297), (row3 285 508 285), (row3 272 508 272), (row3 269 508 269), (row3 215 11 249), (row3 272 508 272), (row3 277 508 277), (row3 247 13 165), (row3 237 230 236), (row3 281 508 281), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508)]

theorem b011_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_05_rows b011_05_labels 5699352642112168726411725552 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_05_rows b011_05_labels]
    decide +kernel

def b011_06_rows : List Row := [(row3 9 22 25), (row3 9 22 26), (row3 9 22 27), (row3 9 22 28), (row3 9 22 29), (row3 9 22 30), (row3 9 22 31), (row3 9 23 24), (row3 9 23 25), (row3 9 23 26), (row3 9 23 27), (row3 9 23 28), (row3 9 23 29), (row3 9 23 30), (row3 9 23 31), (row3 9 24 25)]

def b011_06_labels : List Row := [(row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 299 299 297), (row3 268 508 268), (row3 508 508 508), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 276 508 276), (row3 246 13 164), (row3 268 268 262), (row3 280 508 280), (row3 268 508 268), (row3 314 308 314)]

theorem b011_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_06_rows b011_06_labels 853522920353060125034111730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_06_rows b011_06_labels]
    decide +kernel

def b011_07_rows : List Row := [(row3 9 24 26), (row3 9 24 27), (row3 9 24 28), (row3 9 24 29), (row3 9 24 30), (row3 9 24 31), (row3 9 25 26), (row3 9 25 27), (row3 9 25 28), (row3 9 25 29), (row3 9 25 30), (row3 9 25 31), (row3 9 26 27), (row3 9 26 28), (row3 9 26 29), (row3 9 26 30)]

def b011_07_labels : List Row := [(row3 265 265 508), (row3 309 308 309), (row3 124 460 67), (row3 172 175 178), (row3 325 321 325), (row3 188 197 196), (row3 289 289 508), (row3 259 259 261), (row3 204 112 404), (row3 362 383 372), (row3 251 255 252), (row3 324 324 321), (row3 279 508 279), (row3 245 14 141), (row3 219 208 219), (row3 318 508 318)]

theorem b011_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_07_rows b011_07_labels 176306870187978420671400013044 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_07_rows b011_07_labels]
    decide +kernel

def b011_08_rows : List Row := [(row3 9 26 31), (row3 9 27 28), (row3 9 27 29), (row3 9 27 30), (row3 9 27 31), (row3 9 28 29), (row3 9 28 30), (row3 9 28 31), (row3 9 29 30), (row3 9 29 31), (row3 9 30 31), (row3 10 11 12), (row3 10 11 13), (row3 10 11 14), (row3 10 11 15), (row3 10 11 16)]

def b011_08_labels : List Row := [(row3 258 508 258), (row3 205 113 404), (row3 334 334 331), (row3 252 256 252), (row3 323 323 321), (row3 102 69 467), (row3 145 403 111), (row3 391 68 462), (row3 361 375 384), (row3 151 155 152), (row3 339 339 335), (row3 415 422 397), (row3 110 133 402), (row3 461 411 70), (row3 59 48 58), (row3 150 150 180)]

theorem b011_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_08_rows b011_08_labels 982345250315431499993732903880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_08_rows b011_08_labels]
    decide +kernel

def b011_09_rows : List Row := [(row3 10 11 17), (row3 10 11 18), (row3 10 11 19), (row3 10 11 20), (row3 10 11 21), (row3 10 11 22), (row3 10 11 23), (row3 10 11 24), (row3 10 11 25), (row3 10 11 26), (row3 10 11 27), (row3 10 11 28), (row3 10 11 29), (row3 10 11 30), (row3 10 11 31), (row3 10 12 13)]

def b011_09_labels : List Row := [(row3 13 320 166), (row3 116 156 377), (row3 393 394 370), (row3 508 305 305), (row3 508 508 508), (row3 11 293 216), (row3 201 201 225), (row3 508 265 265), (row3 508 279 279), (row3 508 508 508), (row3 508 289 289), (row3 508 330 330), (row3 508 258 258), (row3 11 294 217), (row3 200 198 222), (row3 364 173 118)]

theorem b011_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_09_rows b011_09_labels 26534331576735095579992806780 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_09_rows b011_09_labels]
    decide +kernel

def b011_10_rows : List Row := [(row3 10 12 14), (row3 10 12 15), (row3 10 12 16), (row3 10 12 17), (row3 10 12 18), (row3 10 12 19), (row3 10 12 20), (row3 10 12 21), (row3 10 12 22), (row3 10 12 23), (row3 10 12 24), (row3 10 12 25), (row3 10 12 26), (row3 10 12 27), (row3 10 12 28), (row3 10 12 29)]

def b011_10_labels : List Row := [(row3 310 340 340), (row3 364 173 118), (row3 190 170 170), (row3 310 313 313), (row3 258 253 253), (row3 310 313 313), (row3 297 300 300), (row3 265 265 265), (row3 508 280 280), (row3 265 265 265), (row3 271 268 268), (row3 508 277 277), (row3 508 508 508), (row3 508 277 277), (row3 508 304 304), (row3 508 268 268)]

theorem b011_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_10_rows b011_10_labels 4056180566330381909785192440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_10_rows b011_10_labels]
    decide +kernel

def b011_11_rows : List Row := [(row3 10 12 30), (row3 10 12 31), (row3 10 13 14), (row3 10 13 15), (row3 10 13 16), (row3 10 13 17), (row3 10 13 18), (row3 10 13 19), (row3 10 13 20), (row3 10 13 21), (row3 10 13 22), (row3 10 13 23), (row3 10 13 24), (row3 10 13 25), (row3 10 13 26), (row3 10 13 27)]

def b011_11_labels : List Row := [(row3 508 280 280), (row3 508 268 268), (row3 210 163 148), (row3 319 332 332), (row3 307 508 307), (row3 211 258 206), (row3 307 310 322), (row3 262 258 255), (row3 268 508 268), (row3 290 508 290), (row3 268 268 262), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508)]

theorem b011_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_11_rows b011_11_labels 2267409171760121786664155040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_11_rows b011_11_labels]
    decide +kernel

def b011_12_rows : List Row := [(row3 10 13 28), (row3 10 13 29), (row3 10 13 30), (row3 10 13 31), (row3 10 14 15), (row3 10 14 16), (row3 10 14 17), (row3 10 14 18), (row3 10 14 19), (row3 10 14 20), (row3 10 14 21), (row3 10 14 22), (row3 10 14 23), (row3 10 14 24), (row3 10 14 25), (row3 10 14 26)]

def b011_12_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 268 268), (row3 508 508 508), (row3 210 148 163), (row3 508 508 508), (row3 508 326 326), (row3 508 190 190), (row3 508 326 326), (row3 508 508 508), (row3 508 508 508), (row3 508 303 303), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b011_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_12_rows b011_12_labels 2739406916212961554391995800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_12_rows b011_12_labels]
    decide +kernel

def b011_13_rows : List Row := [(row3 10 14 27), (row3 10 14 28), (row3 10 14 29), (row3 10 14 30), (row3 10 14 31), (row3 10 15 16), (row3 10 15 17), (row3 10 15 18), (row3 10 15 19), (row3 10 15 20), (row3 10 15 21), (row3 10 15 22), (row3 10 15 23), (row3 10 15 24), (row3 10 15 25), (row3 10 15 26)]

def b011_13_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 304 304), (row3 508 508 508), (row3 307 508 307), (row3 262 258 255), (row3 307 310 322), (row3 211 258 206), (row3 268 508 268), (row3 508 508 508), (row3 268 268 262), (row3 290 508 290), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b011_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_13_rows b011_13_labels 419896762260690359220794640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_13_rows b011_13_labels]
    decide +kernel

def b011_14_rows : List Row := [(row3 10 15 27), (row3 10 15 28), (row3 10 15 29), (row3 10 15 30), (row3 10 15 31), (row3 10 16 17), (row3 10 16 18), (row3 10 16 19), (row3 10 16 20), (row3 10 16 21), (row3 10 16 22), (row3 10 16 23), (row3 10 16 24), (row3 10 16 25), (row3 10 16 26), (row3 10 16 27)]

def b011_14_labels : List Row := [(row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 268 268), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b011_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_14_rows b011_14_labels 906276442920910236403200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_14_rows b011_14_labels]
    decide +kernel

def b011_15_rows : List Row := [(row3 10 16 28), (row3 10 16 29), (row3 10 16 30), (row3 10 16 31), (row3 10 17 18), (row3 10 17 19), (row3 10 17 20), (row3 10 17 21), (row3 10 17 22), (row3 10 17 23), (row3 10 17 24), (row3 10 17 25), (row3 10 17 26), (row3 10 17 27), (row3 10 17 28), (row3 10 17 29)]

def b011_15_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 265 265), (row3 508 279 279), (row3 508 508 508), (row3 508 508 508), (row3 508 276 276), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272)]

theorem b011_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b011_15_rows b011_15_labels 2531052291158622385329600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b011_15_rows b011_15_labels]
    decide +kernel

theorem checked011 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_011 QuarticIntegerComputationalData.ids32_011 1202681543732927809765325029566 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b011_00_rows ++ b011_01_rows) ++ (b011_02_rows ++ b011_03_rows)) ++ ((b011_04_rows ++ b011_05_rows) ++ (b011_06_rows ++ b011_07_rows))) ++ (((b011_08_rows ++ b011_09_rows) ++ (b011_10_rows ++ b011_11_rows)) ++ ((b011_12_rows ++ b011_13_rows) ++ (b011_14_rows ++ b011_15_rows))))
    ((((b011_00_labels ++ b011_01_labels) ++ (b011_02_labels ++ b011_03_labels)) ++ ((b011_04_labels ++ b011_05_labels) ++ (b011_06_labels ++ b011_07_labels))) ++ (((b011_08_labels ++ b011_09_labels) ++ (b011_10_labels ++ b011_11_labels)) ++ ((b011_12_labels ++ b011_13_labels) ++ (b011_14_labels ++ b011_15_labels)))) 1202681543732927809765325029566
  exact ((((b011_00_checked.append (c := 1133582323424816049811242060) b011_01_checked (by decide +kernel)).append (c := 1276989579214431005492309220) (b011_02_checked.append (c := 143407255789614955681067160) b011_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 184315631095462979048915448186) ((b011_04_checked.append (c := 5878248407917067246989014192) b011_05_checked (by decide +kernel)).append (c := 183038641516248548043423138966) (b011_06_checked.append (c := 177160393108331480796434124774) b011_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1202681543732927809765325029566) (((b011_08_checked.append (c := 1008879581892166595573725710660) b011_09_checked (by decide +kernel)).append (c := 1015203171630257099270175058140) (b011_10_checked.append (c := 6323589738090503696449347480) b011_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1018365912637464830716409581380) ((b011_12_checked.append (c := 3159303678473651913612790440) b011_13_checked (by decide +kernel)).append (c := 3162741007207731446234523240) (b011_14_checked.append (c := 3437328734079532621732800) b011_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32
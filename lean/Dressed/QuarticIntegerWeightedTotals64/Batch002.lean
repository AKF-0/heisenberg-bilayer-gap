import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch001
import Dressed.QuarticIntegerComputationalData64.Batch002


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b017_00_rows : List Row := [(row3 3 15 53), (row3 3 15 54), (row3 3 15 55), (row3 3 15 56), (row3 3 15 57), (row3 3 15 58), (row3 3 15 59), (row3 3 15 60), (row3 3 15 61), (row3 3 15 62), (row3 3 15 63), (row3 3 16 17), (row3 3 16 18), (row3 3 16 19), (row3 3 16 20), (row3 3 16 21)]

def b017_00_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 279 278 279), (row3 373 365 352), (row3 161 175 175), (row3 279 278 279), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 282 278 282), (row3 161 176 176), (row3 302 265 302), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_00_rows b017_00_labels 11071667512417716616305677070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_00_rows b017_00_labels]
    decide +kernel

def b017_01_rows : List Row := [(row3 3 16 22), (row3 3 16 23), (row3 3 16 24), (row3 3 16 25), (row3 3 16 26), (row3 3 16 27), (row3 3 16 28), (row3 3 16 29), (row3 3 16 30), (row3 3 16 31), (row3 3 16 32), (row3 3 16 33), (row3 3 16 34), (row3 3 16 35), (row3 3 16 36), (row3 3 16 37)]

def b017_01_labels : List Row := [(row3 237 237 462), (row3 266 265 266), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_01_rows b017_01_labels 57853403727605545876795200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_01_rows b017_01_labels]
    decide +kernel

def b017_02_rows : List Row := [(row3 3 16 38), (row3 3 16 39), (row3 3 16 40), (row3 3 16 41), (row3 3 16 42), (row3 3 16 43), (row3 3 16 44), (row3 3 16 45), (row3 3 16 46), (row3 3 16 47), (row3 3 16 48), (row3 3 16 49), (row3 3 16 50), (row3 3 16 51), (row3 3 16 52), (row3 3 16 53)]

def b017_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 256 255 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 206 210 210), (row3 266 265 266), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_02_rows b017_02_labels 31745131181244484066586640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_02_rows b017_02_labels]
    decide +kernel

def b017_03_rows : List Row := [(row3 3 16 54), (row3 3 16 55), (row3 3 16 56), (row3 3 16 57), (row3 3 16 58), (row3 3 16 59), (row3 3 16 60), (row3 3 16 61), (row3 3 16 62), (row3 3 16 63), (row3 3 17 18), (row3 3 17 19), (row3 3 17 20), (row3 3 17 21), (row3 3 17 22), (row3 3 17 23)]

def b017_03_labels : List Row := [(row3 237 237 462), (row3 266 265 266), (row3 343 338 330), (row3 190 197 196), (row3 266 265 266), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 266 265 266), (row3 190 199 198), (row3 119 216 11), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 228 228 234)]

theorem b017_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_03_rows b017_03_labels 7078955182718077427842192320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_03_rows b017_03_labels]
    decide +kernel

def b017_04_rows : List Row := [(row3 3 17 24), (row3 3 17 25), (row3 3 17 26), (row3 3 17 27), (row3 3 17 28), (row3 3 17 29), (row3 3 17 30), (row3 3 17 31), (row3 3 17 32), (row3 3 17 33), (row3 3 17 34), (row3 3 17 35), (row3 3 17 36), (row3 3 17 37), (row3 3 17 38), (row3 3 17 39)]

def b017_04_labels : List Row := [(row3 226 226 237), (row3 294 294 462), (row3 228 228 462), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 250 462), (row3 249 249 462), (row3 234 234 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_04_rows b017_04_labels 112549279513375568996536500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_04_rows b017_04_labels]
    decide +kernel

def b017_05_rows : List Row := [(row3 3 17 40), (row3 3 17 41), (row3 3 17 42), (row3 3 17 43), (row3 3 17 44), (row3 3 17 45), (row3 3 17 46), (row3 3 17 47), (row3 3 17 48), (row3 3 17 49), (row3 3 17 50), (row3 3 17 51), (row3 3 17 52), (row3 3 17 53), (row3 3 17 54), (row3 3 17 55)]

def b017_05_labels : List Row := [(row3 237 237 237), (row3 245 245 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 246 246 462), (row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 234)]

theorem b017_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_05_rows b017_05_labels 4241936616988866773414400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_05_rows b017_05_labels]
    decide +kernel

def b017_06_rows : List Row := [(row3 3 17 56), (row3 3 17 57), (row3 3 17 58), (row3 3 17 59), (row3 3 17 60), (row3 3 17 61), (row3 3 17 62), (row3 3 17 63), (row3 3 18 19), (row3 3 18 20), (row3 3 18 21), (row3 3 18 22), (row3 3 18 23), (row3 3 18 24), (row3 3 18 25), (row3 3 18 26)]

def b017_06_labels : List Row := [(row3 154 154 180), (row3 298 298 295), (row3 229 224 226), (row3 271 271 462), (row3 235 235 462), (row3 245 245 462), (row3 234 234 234), (row3 279 279 278), (row3 302 265 302), (row3 228 234 228), (row3 246 462 246), (row3 462 462 462), (row3 246 462 246), (row3 249 462 249), (row3 228 462 228), (row3 294 462 294)]

theorem b017_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_06_rows b017_06_labels 1146173563988193944652037200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_06_rows b017_06_labels]
    decide +kernel

def b017_07_rows : List Row := [(row3 3 18 27), (row3 3 18 28), (row3 3 18 29), (row3 3 18 30), (row3 3 18 31), (row3 3 18 32), (row3 3 18 33), (row3 3 18 34), (row3 3 18 35), (row3 3 18 36), (row3 3 18 37), (row3 3 18 38), (row3 3 18 39), (row3 3 18 40), (row3 3 18 41), (row3 3 18 42)]

def b017_07_labels : List Row := [(row3 226 237 226), (row3 250 462 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 462 234), (row3 249 462 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 245 462 245)]

theorem b017_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_07_rows b017_07_labels 2373710846575800166200000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_07_rows b017_07_labels]
    decide +kernel

def b017_08_rows : List Row := [(row3 3 18 43), (row3 3 18 44), (row3 3 18 45), (row3 3 18 46), (row3 3 18 47), (row3 3 18 48), (row3 3 18 49), (row3 3 18 50), (row3 3 18 51), (row3 3 18 52), (row3 3 18 53), (row3 3 18 54), (row3 3 18 55), (row3 3 18 56), (row3 3 18 57), (row3 3 18 58)]

def b017_08_labels : List Row := [(row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 246 462 246), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234), (row3 244 462 244), (row3 462 462 462), (row3 244 462 244), (row3 271 462 271), (row3 229 226 224), (row3 298 295 298)]

theorem b017_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_08_rows b017_08_labels 77926081252380868273517100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_08_rows b017_08_labels]
    decide +kernel

def b017_09_rows : List Row := [(row3 3 18 59), (row3 3 18 60), (row3 3 18 61), (row3 3 18 62), (row3 3 18 63), (row3 3 19 20), (row3 3 19 21), (row3 3 19 22), (row3 3 19 23), (row3 3 19 24), (row3 3 19 25), (row3 3 19 26), (row3 3 19 27), (row3 3 19 28), (row3 3 19 29), (row3 3 19 30)]

def b017_09_labels : List Row := [(row3 154 180 154), (row3 279 278 279), (row3 234 234 234), (row3 245 462 245), (row3 235 462 235), (row3 266 266 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b017_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_09_rows b017_09_labels 865294287426801849935457300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_09_rows b017_09_labels]
    decide +kernel

def b017_10_rows : List Row := [(row3 3 19 31), (row3 3 19 32), (row3 3 19 33), (row3 3 19 34), (row3 3 19 35), (row3 3 19 36), (row3 3 19 37), (row3 3 19 38), (row3 3 19 39), (row3 3 19 40), (row3 3 19 41), (row3 3 19 42), (row3 3 19 43), (row3 3 19 44), (row3 3 19 45), (row3 3 19 46)]

def b017_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b017_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_10_rows b017_10_labels 1282626235839183742912800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_10_rows b017_10_labels]
    decide +kernel

def b017_11_rows : List Row := [(row3 3 19 47), (row3 3 19 48), (row3 3 19 49), (row3 3 19 50), (row3 3 19 51), (row3 3 19 52), (row3 3 19 53), (row3 3 19 54), (row3 3 19 55), (row3 3 19 56), (row3 3 19 57), (row3 3 19 58), (row3 3 19 59), (row3 3 19 60), (row3 3 19 61), (row3 3 19 62)]

def b017_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 266 266 265), (row3 206 210 210), (row3 266 266 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 266 266 265), (row3 190 196 197), (row3 343 330 338), (row3 190 198 199), (row3 266 266 265), (row3 238 462 238)]

theorem b017_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_11_rows b017_11_labels 5148689997732211724281145910 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_11_rows b017_11_labels]
    decide +kernel

def b017_12_rows : List Row := [(row3 3 19 63), (row3 3 20 21), (row3 3 20 22), (row3 3 20 23), (row3 3 20 24), (row3 3 20 25), (row3 3 20 26), (row3 3 20 27), (row3 3 20 28), (row3 3 20 29), (row3 3 20 30), (row3 3 20 31), (row3 3 20 32), (row3 3 20 33), (row3 3 20 34), (row3 3 20 35)]

def b017_12_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242)]

theorem b017_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_12_rows b017_12_labels 865162616655715358130000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_12_rows b017_12_labels]
    decide +kernel

def b017_13_rows : List Row := [(row3 3 20 36), (row3 3 20 37), (row3 3 20 38), (row3 3 20 39), (row3 3 20 40), (row3 3 20 41), (row3 3 20 42), (row3 3 20 43), (row3 3 20 44), (row3 3 20 45), (row3 3 20 46), (row3 3 20 47), (row3 3 20 48), (row3 3 20 49), (row3 3 20 50), (row3 3 20 51)]

def b017_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 234 234 234), (row3 266 265 266)]

theorem b017_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_13_rows b017_13_labels 3676333273541756435421900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_13_rows b017_13_labels]
    decide +kernel

def b017_14_rows : List Row := [(row3 3 20 52), (row3 3 20 53), (row3 3 20 54), (row3 3 20 55), (row3 3 20 56), (row3 3 20 57), (row3 3 20 58), (row3 3 20 59), (row3 3 20 60), (row3 3 20 61), (row3 3 20 62), (row3 3 20 63), (row3 3 21 22), (row3 3 21 23), (row3 3 21 24), (row3 3 21 25)]

def b017_14_labels : List Row := [(row3 234 234 234), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 234 234 234), (row3 279 278 279), (row3 154 180 154), (row3 279 278 279), (row3 234 234 234), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_14_rows b017_14_labels 819447117858411769599014700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_14_rows b017_14_labels]
    decide +kernel

def b017_15_rows : List Row := [(row3 3 21 26), (row3 3 21 27), (row3 3 21 28), (row3 3 21 29), (row3 3 21 30), (row3 3 21 31), (row3 3 21 32), (row3 3 21 33), (row3 3 21 34), (row3 3 21 35), (row3 3 21 36), (row3 3 21 37), (row3 3 21 38), (row3 3 21 39), (row3 3 21 40), (row3 3 21 41)]

def b017_15_labels : List Row := [(row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b017_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b017_15_rows b017_15_labels 4248890416128681112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b017_15_rows b017_15_labels]
    decide +kernel

theorem checked017 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_017 QuarticIntegerComputationalData.ids64_017 26422745576296037250986151540 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b017_00_rows ++ b017_01_rows) ++ (b017_02_rows ++ b017_03_rows)) ++ ((b017_04_rows ++ b017_05_rows) ++ (b017_06_rows ++ b017_07_rows))) ++ (((b017_08_rows ++ b017_09_rows) ++ (b017_10_rows ++ b017_11_rows)) ++ ((b017_12_rows ++ b017_13_rows) ++ (b017_14_rows ++ b017_15_rows))))
    ((((b017_00_labels ++ b017_01_labels) ++ (b017_02_labels ++ b017_03_labels)) ++ ((b017_04_labels ++ b017_05_labels) ++ (b017_06_labels ++ b017_07_labels))) ++ (((b017_08_labels ++ b017_09_labels) ++ (b017_10_labels ++ b017_11_labels)) ++ ((b017_12_labels ++ b017_13_labels) ++ (b017_14_labels ++ b017_15_labels)))) 26422745576296037250986151540
  exact ((((b017_00_checked.append (c := 11129520916145322162182472270) b017_01_checked (by decide +kernel)).append (c := 18240221230044644074091251230) (b017_02_checked.append (c := 7110700313899321911908778960) b017_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 19505559721009778254679439330) ((b017_04_checked.append (c := 116791216130364435769950900) b017_05_checked (by decide +kernel)).append (c := 1265338490965134180588188100) (b017_06_checked.append (c := 1148547274834769744818237200) b017_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 26422745576296037250986151540) (((b017_08_checked.append (c := 943220368679182718208974400) b017_09_checked (by decide +kernel)).append (c := 6093192992647233626233033110) (b017_10_checked.append (c := 5149972623968050908024058710) b017_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 6917185855286258996306712210) ((b017_12_checked.append (c := 4541495890197471793551900) b017_13_checked (by decide +kernel)).append (c := 823992862639025370073679100) (b017_14_checked.append (c := 819451366748827898280127200) b017_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b018_00_rows : List Row := [(row3 3 21 42), (row3 3 21 43), (row3 3 21 44), (row3 3 21 45), (row3 3 21 46), (row3 3 21 47), (row3 3 21 48), (row3 3 21 49), (row3 3 21 50), (row3 3 21 51), (row3 3 21 52), (row3 3 21 53), (row3 3 21 54), (row3 3 21 55), (row3 3 21 56), (row3 3 21 57)]

def b018_00_labels : List Row := [(row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 237 237 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462)]

theorem b018_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_00_rows b018_00_labels 173055706975043264493000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_00_rows b018_00_labels]
    decide +kernel

def b018_01_rows : List Row := [(row3 3 21 58), (row3 3 21 59), (row3 3 21 60), (row3 3 21 61), (row3 3 21 62), (row3 3 21 63), (row3 3 22 23), (row3 3 22 24), (row3 3 22 25), (row3 3 22 26), (row3 3 22 27), (row3 3 22 28), (row3 3 22 29), (row3 3 22 30), (row3 3 22 31), (row3 3 22 32)]

def b018_01_labels : List Row := [(row3 235 235 462), (row3 269 269 462), (row3 235 235 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_01_rows b018_01_labels 30704559298533407354769000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_01_rows b018_01_labels]
    decide +kernel

def b018_02_rows : List Row := [(row3 3 22 33), (row3 3 22 34), (row3 3 22 35), (row3 3 22 36), (row3 3 22 37), (row3 3 22 38), (row3 3 22 39), (row3 3 22 40), (row3 3 22 41), (row3 3 22 42), (row3 3 22 43), (row3 3 22 44), (row3 3 22 45), (row3 3 22 46), (row3 3 22 47), (row3 3 22 48)]

def b018_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237)]

theorem b018_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_02_rows b018_02_labels 125922244183908719350500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_02_rows b018_02_labels]
    decide +kernel

def b018_03_rows : List Row := [(row3 3 22 49), (row3 3 22 50), (row3 3 22 51), (row3 3 22 52), (row3 3 22 53), (row3 3 22 54), (row3 3 22 55), (row3 3 22 56), (row3 3 22 57), (row3 3 22 58), (row3 3 22 59), (row3 3 22 60), (row3 3 22 61), (row3 3 22 62), (row3 3 22 63), (row3 3 23 24)]

def b018_03_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 269 462 269), (row3 235 462 235), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 462 245), (row3 235 462 235), (row3 237 237 237)]

theorem b018_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_03_rows b018_03_labels 30739733754422471500441500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_03_rows b018_03_labels]
    decide +kernel

def b018_04_rows : List Row := [(row3 3 23 25), (row3 3 23 26), (row3 3 23 27), (row3 3 23 28), (row3 3 23 29), (row3 3 23 30), (row3 3 23 31), (row3 3 23 32), (row3 3 23 33), (row3 3 23 34), (row3 3 23 35), (row3 3 23 36), (row3 3 23 37), (row3 3 23 38), (row3 3 23 39), (row3 3 23 40)]

def b018_04_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237)]

theorem b018_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_04_rows b018_04_labels 326481328149440723662500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_04_rows b018_04_labels]
    decide +kernel

def b018_05_rows : List Row := [(row3 3 23 41), (row3 3 23 42), (row3 3 23 43), (row3 3 23 44), (row3 3 23 45), (row3 3 23 46), (row3 3 23 47), (row3 3 23 48), (row3 3 23 49), (row3 3 23 50), (row3 3 23 51), (row3 3 23 52), (row3 3 23 53), (row3 3 23 54), (row3 3 23 55), (row3 3 23 56)]

def b018_05_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 266 266 265), (row3 234 234 234), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 234), (row3 154 154 180)]

theorem b018_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_05_rows b018_05_labels 800951052637645647813509400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_05_rows b018_05_labels]
    decide +kernel

def b018_06_rows : List Row := [(row3 3 23 57), (row3 3 23 58), (row3 3 23 59), (row3 3 23 60), (row3 3 23 61), (row3 3 23 62), (row3 3 23 63), (row3 3 24 25), (row3 3 24 26), (row3 3 24 27), (row3 3 24 28), (row3 3 24 29), (row3 3 24 30), (row3 3 24 31), (row3 3 24 32), (row3 3 24 33)]

def b018_06_labels : List Row := [(row3 279 279 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 279 279 278), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 240 240 462), (row3 462 462 462)]

theorem b018_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_06_rows b018_06_labels 22252867344922745598164700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_06_rows b018_06_labels]
    decide +kernel

def b018_07_rows : List Row := [(row3 3 24 34), (row3 3 24 35), (row3 3 24 36), (row3 3 24 37), (row3 3 24 38), (row3 3 24 39), (row3 3 24 40), (row3 3 24 41), (row3 3 24 42), (row3 3 24 43), (row3 3 24 44), (row3 3 24 45), (row3 3 24 46), (row3 3 24 47), (row3 3 24 48), (row3 3 24 49)]

def b018_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 239), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 256 256 255), (row3 237 237 237)]

theorem b018_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_07_rows b018_07_labels 1217769427386823958818800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_07_rows b018_07_labels]
    decide +kernel

def b018_08_rows : List Row := [(row3 3 24 50), (row3 3 24 51), (row3 3 24 52), (row3 3 24 53), (row3 3 24 54), (row3 3 24 55), (row3 3 24 56), (row3 3 24 57), (row3 3 24 58), (row3 3 24 59), (row3 3 24 60), (row3 3 24 61), (row3 3 24 62), (row3 3 24 63), (row3 3 25 26), (row3 3 25 27)]

def b018_08_labels : List Row := [(row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 237 237 237), (row3 201 201 208), (row3 262 262 261), (row3 237 237 237), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 237 237 237), (row3 262 262 261), (row3 462 462 462), (row3 462 462 462)]

theorem b018_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_08_rows b018_08_labels 270806864437982941988003400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_08_rows b018_08_labels]
    decide +kernel

def b018_09_rows : List Row := [(row3 3 25 28), (row3 3 25 29), (row3 3 25 30), (row3 3 25 31), (row3 3 25 32), (row3 3 25 33), (row3 3 25 34), (row3 3 25 35), (row3 3 25 36), (row3 3 25 37), (row3 3 25 38), (row3 3 25 39), (row3 3 25 40), (row3 3 25 41), (row3 3 25 42), (row3 3 25 43)]

def b018_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_09_rows b018_09_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_09_rows b018_09_labels]
    decide +kernel

def b018_10_rows : List Row := [(row3 3 25 44), (row3 3 25 45), (row3 3 25 46), (row3 3 25 47), (row3 3 25 48), (row3 3 25 49), (row3 3 25 50), (row3 3 25 51), (row3 3 25 52), (row3 3 25 53), (row3 3 25 54), (row3 3 25 55), (row3 3 25 56), (row3 3 25 57), (row3 3 25 58), (row3 3 25 59)]

def b018_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 245 462 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 263 462 263), (row3 236 235 233), (row3 243 462 243), (row3 462 462 462)]

theorem b018_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_10_rows b018_10_labels 20514716299338335616889500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_10_rows b018_10_labels]
    decide +kernel

def b018_11_rows : List Row := [(row3 3 25 60), (row3 3 25 61), (row3 3 25 62), (row3 3 25 63), (row3 3 26 27), (row3 3 26 28), (row3 3 26 29), (row3 3 26 30), (row3 3 26 31), (row3 3 26 32), (row3 3 26 33), (row3 3 26 34), (row3 3 26 35), (row3 3 26 36), (row3 3 26 37), (row3 3 26 38)]

def b018_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_11_rows b018_11_labels 336886722888746100288000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_11_rows b018_11_labels]
    decide +kernel

def b018_12_rows : List Row := [(row3 3 26 39), (row3 3 26 40), (row3 3 26 41), (row3 3 26 42), (row3 3 26 43), (row3 3 26 44), (row3 3 26 45), (row3 3 26 46), (row3 3 26 47), (row3 3 26 48), (row3 3 26 49), (row3 3 26 50), (row3 3 26 51), (row3 3 26 52), (row3 3 26 53), (row3 3 26 54)]

def b018_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_12_rows b018_12_labels 112908308962001584204500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_12_rows b018_12_labels]
    decide +kernel

def b018_13_rows : List Row := [(row3 3 26 55), (row3 3 26 56), (row3 3 26 57), (row3 3 26 58), (row3 3 26 59), (row3 3 26 60), (row3 3 26 61), (row3 3 26 62), (row3 3 26 63), (row3 3 27 28), (row3 3 27 29), (row3 3 27 30), (row3 3 27 31), (row3 3 27 32), (row3 3 27 33), (row3 3 27 34)]

def b018_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 233 235), (row3 263 263 462), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_13_rows b018_13_labels 20741527306875832587048000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_13_rows b018_13_labels]
    decide +kernel

def b018_14_rows : List Row := [(row3 3 27 35), (row3 3 27 36), (row3 3 27 37), (row3 3 27 38), (row3 3 27 39), (row3 3 27 40), (row3 3 27 41), (row3 3 27 42), (row3 3 27 43), (row3 3 27 44), (row3 3 27 45), (row3 3 27 46), (row3 3 27 47), (row3 3 27 48), (row3 3 27 49), (row3 3 27 50)]

def b018_14_labels : List Row := [(row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 239 239 239), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 237 237 237)]

theorem b018_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_14_rows b018_14_labels 208218089694155700930000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_14_rows b018_14_labels]
    decide +kernel

def b018_15_rows : List Row := [(row3 3 27 51), (row3 3 27 52), (row3 3 27 53), (row3 3 27 54), (row3 3 27 55), (row3 3 27 56), (row3 3 27 57), (row3 3 27 58), (row3 3 27 59), (row3 3 27 60), (row3 3 27 61), (row3 3 27 62), (row3 3 27 63), (row3 3 28 29), (row3 3 28 30), (row3 3 28 31)]

def b018_15_labels : List Row := [(row3 256 255 256), (row3 237 237 237), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 201 208 201), (row3 262 261 262), (row3 237 237 237), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b018_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b018_15_rows b018_15_labels 271852024048884397713329700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b018_15_rows b018_15_labels]
    decide +kernel

theorem checked018 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_018 QuarticIntegerComputationalData.ids64_018 1471067419550456652677977500 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b018_00_rows ++ b018_01_rows) ++ (b018_02_rows ++ b018_03_rows)) ++ ((b018_04_rows ++ b018_05_rows) ++ (b018_06_rows ++ b018_07_rows))) ++ (((b018_08_rows ++ b018_09_rows) ++ (b018_10_rows ++ b018_11_rows)) ++ ((b018_12_rows ++ b018_13_rows) ++ (b018_14_rows ++ b018_15_rows))))
    ((((b018_00_labels ++ b018_01_labels) ++ (b018_02_labels ++ b018_03_labels)) ++ ((b018_04_labels ++ b018_05_labels) ++ (b018_06_labels ++ b018_07_labels))) ++ (((b018_08_labels ++ b018_09_labels) ++ (b018_10_labels ++ b018_11_labels)) ++ ((b018_12_labels ++ b018_13_labels) ++ (b018_14_labels ++ b018_15_labels)))) 1471067419550456652677977500
  exact ((((b018_00_checked.append (c := 30877615005508450619262000) b018_01_checked (by decide +kernel)).append (c := 61743271004114830839054000) (b018_02_checked.append (c := 30865655998606380219792000) b018_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 886491441742219488933209400) ((b018_04_checked.append (c := 801277533965795088537171900) b018_05_checked (by decide +kernel)).append (c := 824748170738104658094155400) (b018_06_checked.append (c := 23470636772309569556983500) b018_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1471067419550456652677977500) (((b018_08_checked.append (c := 270809697031593694442078400) b018_09_checked (by decide +kernel)).append (c := 291661300053820776159255900) (b018_10_checked.append (c := 20851603022227081717177500) b018_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 584575977808237163744768100) ((b018_12_checked.append (c := 20854435615837834171252500) b018_13_checked (by decide +kernel)).append (c := 292914677754416387585512200) (b018_14_checked.append (c := 272060242138578553414259700) b018_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b019_00_rows : List Row := [(row3 3 28 32), (row3 3 28 33), (row3 3 28 34), (row3 3 28 35), (row3 3 28 36), (row3 3 28 37), (row3 3 28 38), (row3 3 28 39), (row3 3 28 40), (row3 3 28 41), (row3 3 28 42), (row3 3 28 43), (row3 3 28 44), (row3 3 28 45), (row3 3 28 46), (row3 3 28 47)]

def b019_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_00_rows b019_00_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_00_rows b019_00_labels]
    decide +kernel

def b019_01_rows : List Row := [(row3 3 28 48), (row3 3 28 49), (row3 3 28 50), (row3 3 28 51), (row3 3 28 52), (row3 3 28 53), (row3 3 28 54), (row3 3 28 55), (row3 3 28 56), (row3 3 28 57), (row3 3 28 58), (row3 3 28 59), (row3 3 28 60), (row3 3 28 61), (row3 3 28 62), (row3 3 28 63)]

def b019_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 263 263 462), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_01_rows b019_01_labels 20359854851779437696483000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_01_rows b019_01_labels]
    decide +kernel

def b019_02_rows : List Row := [(row3 3 29 30), (row3 3 29 31), (row3 3 29 32), (row3 3 29 33), (row3 3 29 34), (row3 3 29 35), (row3 3 29 36), (row3 3 29 37), (row3 3 29 38), (row3 3 29 39), (row3 3 29 40), (row3 3 29 41), (row3 3 29 42), (row3 3 29 43), (row3 3 29 44), (row3 3 29 45)]

def b019_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_02_rows b019_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_02_rows b019_02_labels]
    decide +kernel

def b019_03_rows : List Row := [(row3 3 29 46), (row3 3 29 47), (row3 3 29 48), (row3 3 29 49), (row3 3 29 50), (row3 3 29 51), (row3 3 29 52), (row3 3 29 53), (row3 3 29 54), (row3 3 29 55), (row3 3 29 56), (row3 3 29 57), (row3 3 29 58), (row3 3 29 59), (row3 3 29 60), (row3 3 29 61)]

def b019_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_03_rows b019_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_03_rows b019_03_labels]
    decide +kernel

def b019_04_rows : List Row := [(row3 3 29 62), (row3 3 29 63), (row3 3 30 31), (row3 3 30 32), (row3 3 30 33), (row3 3 30 34), (row3 3 30 35), (row3 3 30 36), (row3 3 30 37), (row3 3 30 38), (row3 3 30 39), (row3 3 30 40), (row3 3 30 41), (row3 3 30 42), (row3 3 30 43), (row3 3 30 44)]

def b019_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_04_rows b019_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_04_rows b019_04_labels]
    decide +kernel

def b019_05_rows : List Row := [(row3 3 30 45), (row3 3 30 46), (row3 3 30 47), (row3 3 30 48), (row3 3 30 49), (row3 3 30 50), (row3 3 30 51), (row3 3 30 52), (row3 3 30 53), (row3 3 30 54), (row3 3 30 55), (row3 3 30 56), (row3 3 30 57), (row3 3 30 58), (row3 3 30 59), (row3 3 30 60)]

def b019_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_05_rows b019_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_05_rows b019_05_labels]
    decide +kernel

def b019_06_rows : List Row := [(row3 3 30 61), (row3 3 30 62), (row3 3 30 63), (row3 3 31 32), (row3 3 31 33), (row3 3 31 34), (row3 3 31 35), (row3 3 31 36), (row3 3 31 37), (row3 3 31 38), (row3 3 31 39), (row3 3 31 40), (row3 3 31 41), (row3 3 31 42), (row3 3 31 43), (row3 3 31 44)]

def b019_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_06_rows b019_06_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_06_rows b019_06_labels]
    decide +kernel

def b019_07_rows : List Row := [(row3 3 31 45), (row3 3 31 46), (row3 3 31 47), (row3 3 31 48), (row3 3 31 49), (row3 3 31 50), (row3 3 31 51), (row3 3 31 52), (row3 3 31 53), (row3 3 31 54), (row3 3 31 55), (row3 3 31 56), (row3 3 31 57), (row3 3 31 58), (row3 3 31 59), (row3 3 31 60)]

def b019_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 263 462 263), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462)]

theorem b019_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_07_rows b019_07_labels 20094184675308266531070000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_07_rows b019_07_labels]
    decide +kernel

def b019_08_rows : List Row := [(row3 3 31 61), (row3 3 31 62), (row3 3 31 63), (row3 3 32 33), (row3 3 32 34), (row3 3 32 35), (row3 3 32 36), (row3 3 32 37), (row3 3 32 38), (row3 3 32 39), (row3 3 32 40), (row3 3 32 41), (row3 3 32 42), (row3 3 32 43), (row3 3 32 44), (row3 3 32 45)]

def b019_08_labels : List Row := [(row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_08_rows b019_08_labels 301278449679958632850500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_08_rows b019_08_labels]
    decide +kernel

def b019_09_rows : List Row := [(row3 3 32 46), (row3 3 32 47), (row3 3 32 48), (row3 3 32 49), (row3 3 32 50), (row3 3 32 51), (row3 3 32 52), (row3 3 32 53), (row3 3 32 54), (row3 3 32 55), (row3 3 32 56), (row3 3 32 57), (row3 3 32 58), (row3 3 32 59), (row3 3 32 60), (row3 3 32 61)]

def b019_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 249 462 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 254 8 203), (row3 238 232 230), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_09_rows b019_09_labels 171356061022886962364980500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_09_rows b019_09_labels]
    decide +kernel

def b019_10_rows : List Row := [(row3 3 32 62), (row3 3 32 63), (row3 3 33 34), (row3 3 33 35), (row3 3 33 36), (row3 3 33 37), (row3 3 33 38), (row3 3 33 39), (row3 3 33 40), (row3 3 33 41), (row3 3 33 42), (row3 3 33 43), (row3 3 33 44), (row3 3 33 45), (row3 3 33 46), (row3 3 33 47)]

def b019_10_labels : List Row := [(row3 242 462 242), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_10_rows b019_10_labels 132835088235585582706500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_10_rows b019_10_labels]
    decide +kernel

def b019_11_rows : List Row := [(row3 3 33 48), (row3 3 33 49), (row3 3 33 50), (row3 3 33 51), (row3 3 33 52), (row3 3 33 53), (row3 3 33 54), (row3 3 33 55), (row3 3 33 56), (row3 3 33 57), (row3 3 33 58), (row3 3 33 59), (row3 3 33 60), (row3 3 33 61), (row3 3 33 62), (row3 3 33 63)]

def b019_11_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 279 278), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_11_rows b019_11_labels 11069378410805519925140100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_11_rows b019_11_labels]
    decide +kernel

def b019_12_rows : List Row := [(row3 3 34 35), (row3 3 34 36), (row3 3 34 37), (row3 3 34 38), (row3 3 34 39), (row3 3 34 40), (row3 3 34 41), (row3 3 34 42), (row3 3 34 43), (row3 3 34 44), (row3 3 34 45), (row3 3 34 46), (row3 3 34 47), (row3 3 34 48), (row3 3 34 49), (row3 3 34 50)]

def b019_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 234 234 462)]

theorem b019_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_12_rows b019_12_labels 495836240688545342728500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_12_rows b019_12_labels]
    decide +kernel

def b019_13_rows : List Row := [(row3 3 34 51), (row3 3 34 52), (row3 3 34 53), (row3 3 34 54), (row3 3 34 55), (row3 3 34 56), (row3 3 34 57), (row3 3 34 58), (row3 3 34 59), (row3 3 34 60), (row3 3 34 61), (row3 3 34 62), (row3 3 34 63), (row3 3 35 36), (row3 3 35 37), (row3 3 35 38)]

def b019_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 279 278 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_13_rows b019_13_labels 10573542170116974582411600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_13_rows b019_13_labels]
    decide +kernel

def b019_14_rows : List Row := [(row3 3 35 39), (row3 3 35 40), (row3 3 35 41), (row3 3 35 42), (row3 3 35 43), (row3 3 35 44), (row3 3 35 45), (row3 3 35 46), (row3 3 35 47), (row3 3 35 48), (row3 3 35 49), (row3 3 35 50), (row3 3 35 51), (row3 3 35 52), (row3 3 35 53), (row3 3 35 54)]

def b019_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 240 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 249 462), (row3 239 239 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_14_rows b019_14_labels 157631714591095332615000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_14_rows b019_14_labels]
    decide +kernel

def b019_15_rows : List Row := [(row3 3 35 55), (row3 3 35 56), (row3 3 35 57), (row3 3 35 58), (row3 3 35 59), (row3 3 35 60), (row3 3 35 61), (row3 3 35 62), (row3 3 35 63), (row3 3 36 37), (row3 3 36 38), (row3 3 36 39), (row3 3 36 40), (row3 3 36 41), (row3 3 36 42), (row3 3 36 43)]

def b019_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 238 230 232), (row3 254 203 8), (row3 238 238 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b019_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b019_15_rows b019_15_labels 171366872669740240082509500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b019_15_rows b019_15_labels]
    decide +kernel

theorem checked019 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_019 QuarticIntegerComputationalData.ids64_019 405913140481054090981645200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b019_00_rows ++ b019_01_rows) ++ (b019_02_rows ++ b019_03_rows)) ++ ((b019_04_rows ++ b019_05_rows) ++ (b019_06_rows ++ b019_07_rows))) ++ (((b019_08_rows ++ b019_09_rows) ++ (b019_10_rows ++ b019_11_rows)) ++ ((b019_12_rows ++ b019_13_rows) ++ (b019_14_rows ++ b019_15_rows))))
    ((((b019_00_labels ++ b019_01_labels) ++ (b019_02_labels ++ b019_03_labels)) ++ ((b019_04_labels ++ b019_05_labels) ++ (b019_06_labels ++ b019_07_labels))) ++ (((b019_08_labels ++ b019_09_labels) ++ (b019_10_labels ++ b019_11_labels)) ++ ((b019_12_labels ++ b019_13_labels) ++ (b019_14_labels ++ b019_15_labels)))) 405913140481054090981645200
  exact ((((b019_00_checked.append (c := 20362687445390190150558000) b019_01_checked (by decide +kernel)).append (c := 20362687445390190150558000) (b019_02_checked.append (c := 0) b019_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 40459704714309209135703000) ((b019_04_checked.append (c := 0) b019_05_checked (by decide +kernel)).append (c := 20097017268919018985145000) (b019_06_checked.append (c := 20097017268919018985145000) b019_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 405913140481054090981645200) (((b019_08_checked.append (c := 171657339472566920997831000) b019_09_checked (by decide +kernel)).append (c := 182859552971608026505677600) (b019_10_checked.append (c := 11202213499041105507846600) b019_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 365453435766744881845942200) ((b019_12_checked.append (c := 11069378410805519925140100) b019_13_checked (by decide +kernel)).append (c := 182593882795136855340264600) (b019_14_checked.append (c := 171524504384331335415124500) b019_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b020_00_rows : List Row := [(row3 3 36 44), (row3 3 36 45), (row3 3 36 46), (row3 3 36 47), (row3 3 36 48), (row3 3 36 49), (row3 3 36 50), (row3 3 36 51), (row3 3 36 52), (row3 3 36 53), (row3 3 36 54), (row3 3 36 55), (row3 3 36 56), (row3 3 36 57), (row3 3 36 58), (row3 3 36 59)]

def b020_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_00_rows b020_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_00_rows b020_00_labels]
    decide +kernel

def b020_01_rows : List Row := [(row3 3 36 60), (row3 3 36 61), (row3 3 36 62), (row3 3 36 63), (row3 3 37 38), (row3 3 37 39), (row3 3 37 40), (row3 3 37 41), (row3 3 37 42), (row3 3 37 43), (row3 3 37 44), (row3 3 37 45), (row3 3 37 46), (row3 3 37 47), (row3 3 37 48), (row3 3 37 49)]

def b020_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_01_rows b020_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_01_rows b020_01_labels]
    decide +kernel

def b020_02_rows : List Row := [(row3 3 37 50), (row3 3 37 51), (row3 3 37 52), (row3 3 37 53), (row3 3 37 54), (row3 3 37 55), (row3 3 37 56), (row3 3 37 57), (row3 3 37 58), (row3 3 37 59), (row3 3 37 60), (row3 3 37 61), (row3 3 37 62), (row3 3 37 63), (row3 3 38 39), (row3 3 38 40)]

def b020_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_02_rows b020_02_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_02_rows b020_02_labels]
    decide +kernel

def b020_03_rows : List Row := [(row3 3 38 41), (row3 3 38 42), (row3 3 38 43), (row3 3 38 44), (row3 3 38 45), (row3 3 38 46), (row3 3 38 47), (row3 3 38 48), (row3 3 38 49), (row3 3 38 50), (row3 3 38 51), (row3 3 38 52), (row3 3 38 53), (row3 3 38 54), (row3 3 38 55), (row3 3 38 56)]

def b020_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_03_rows b020_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_03_rows b020_03_labels]
    decide +kernel

def b020_04_rows : List Row := [(row3 3 38 57), (row3 3 38 58), (row3 3 38 59), (row3 3 38 60), (row3 3 38 61), (row3 3 38 62), (row3 3 38 63), (row3 3 39 40), (row3 3 39 41), (row3 3 39 42), (row3 3 39 43), (row3 3 39 44), (row3 3 39 45), (row3 3 39 46), (row3 3 39 47), (row3 3 39 48)]

def b020_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_04_rows b020_04_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_04_rows b020_04_labels]
    decide +kernel

def b020_05_rows : List Row := [(row3 3 39 49), (row3 3 39 50), (row3 3 39 51), (row3 3 39 52), (row3 3 39 53), (row3 3 39 54), (row3 3 39 55), (row3 3 39 56), (row3 3 39 57), (row3 3 39 58), (row3 3 39 59), (row3 3 39 60), (row3 3 39 61), (row3 3 39 62), (row3 3 39 63), (row3 3 40 41)]

def b020_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462)]

theorem b020_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_05_rows b020_05_labels 71216546417574934875000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_05_rows b020_05_labels]
    decide +kernel

def b020_06_rows : List Row := [(row3 3 40 42), (row3 3 40 43), (row3 3 40 44), (row3 3 40 45), (row3 3 40 46), (row3 3 40 47), (row3 3 40 48), (row3 3 40 49), (row3 3 40 50), (row3 3 40 51), (row3 3 40 52), (row3 3 40 53), (row3 3 40 54), (row3 3 40 55), (row3 3 40 56), (row3 3 40 57)]

def b020_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 256 256 255), (row3 226 237 226), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 237 237 237), (row3 202 97 334), (row3 317 317 308)]

theorem b020_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_06_rows b020_06_labels 3112372234097578993783791300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_06_rows b020_06_labels]
    decide +kernel

def b020_07_rows : List Row := [(row3 3 40 58), (row3 3 40 59), (row3 3 40 60), (row3 3 40 61), (row3 3 40 62), (row3 3 40 63), (row3 3 41 42), (row3 3 41 43), (row3 3 41 44), (row3 3 41 45), (row3 3 41 46), (row3 3 41 47), (row3 3 41 48), (row3 3 41 49), (row3 3 41 50), (row3 3 41 51)]

def b020_07_labels : List Row := [(row3 237 226 226), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 237 237 237), (row3 262 262 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 294 462 294), (row3 228 228 462), (row3 462 462 462)]

theorem b020_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_07_rows b020_07_labels 115551749374089824550491700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_07_rows b020_07_labels]
    decide +kernel

def b020_08_rows : List Row := [(row3 3 41 52), (row3 3 41 53), (row3 3 41 54), (row3 3 41 55), (row3 3 41 56), (row3 3 41 57), (row3 3 41 58), (row3 3 41 59), (row3 3 41 60), (row3 3 41 61), (row3 3 41 62), (row3 3 41 63), (row3 3 42 43), (row3 3 42 44), (row3 3 42 45), (row3 3 42 46)]

def b020_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 254 10 171), (row3 148 137 145), (row3 310 306 310), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_08_rows b020_08_labels 790289448289409652669459420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_08_rows b020_08_labels]
    decide +kernel

def b020_09_rows : List Row := [(row3 3 42 47), (row3 3 42 48), (row3 3 42 49), (row3 3 42 50), (row3 3 42 51), (row3 3 42 52), (row3 3 42 53), (row3 3 42 54), (row3 3 42 55), (row3 3 42 56), (row3 3 42 57), (row3 3 42 58), (row3 3 42 59), (row3 3 42 60), (row3 3 42 61), (row3 3 42 62)]

def b020_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 294 294 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 310 310 306), (row3 148 145 137), (row3 254 171 10), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462)]

theorem b020_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_09_rows b020_09_labels 900564335579316747328288920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_09_rows b020_09_labels]
    decide +kernel

def b020_10_rows : List Row := [(row3 3 42 63), (row3 3 43 44), (row3 3 43 45), (row3 3 43 46), (row3 3 43 47), (row3 3 43 48), (row3 3 43 49), (row3 3 43 50), (row3 3 43 51), (row3 3 43 52), (row3 3 43 53), (row3 3 43 54), (row3 3 43 55), (row3 3 43 56), (row3 3 43 57), (row3 3 43 58)]

def b020_10_labels : List Row := [(row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 462 249), (row3 226 226 237), (row3 256 255 256), (row3 237 237 237), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 237 226 226), (row3 317 308 317)]

theorem b020_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_10_rows b020_10_labels 53418733088512347070224300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_10_rows b020_10_labels]
    decide +kernel

def b020_11_rows : List Row := [(row3 3 43 59), (row3 3 43 60), (row3 3 43 61), (row3 3 43 62), (row3 3 43 63), (row3 3 44 45), (row3 3 44 46), (row3 3 44 47), (row3 3 44 48), (row3 3 44 49), (row3 3 44 50), (row3 3 44 51), (row3 3 44 52), (row3 3 44 53), (row3 3 44 54), (row3 3 44 55)]

def b020_11_labels : List Row := [(row3 202 334 97), (row3 262 261 262), (row3 237 237 237), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 250 462), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_11_rows b020_11_labels 3064623369257822560592234700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_11_rows b020_11_labels]
    decide +kernel

def b020_12_rows : List Row := [(row3 3 44 56), (row3 3 44 57), (row3 3 44 58), (row3 3 44 59), (row3 3 44 60), (row3 3 44 61), (row3 3 44 62), (row3 3 44 63), (row3 3 45 46), (row3 3 45 47), (row3 3 45 48), (row3 3 45 49), (row3 3 45 50), (row3 3 45 51), (row3 3 45 52), (row3 3 45 53)]

def b020_12_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 236 225 228), (row3 254 171 10), (row3 236 236 462), (row3 247 247 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_12_rows b020_12_labels 519351693134024739501850500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_12_rows b020_12_labels]
    decide +kernel

def b020_13_rows : List Row := [(row3 3 45 54), (row3 3 45 55), (row3 3 45 56), (row3 3 45 57), (row3 3 45 58), (row3 3 45 59), (row3 3 45 60), (row3 3 45 61), (row3 3 45 62), (row3 3 45 63), (row3 3 46 47), (row3 3 46 48), (row3 3 46 49), (row3 3 46 50), (row3 3 46 51), (row3 3 46 52)]

def b020_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_13_rows b020_13_labels 330557493792363561819000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_13_rows b020_13_labels]
    decide +kernel

def b020_14_rows : List Row := [(row3 3 46 53), (row3 3 46 54), (row3 3 46 55), (row3 3 46 56), (row3 3 46 57), (row3 3 46 58), (row3 3 46 59), (row3 3 46 60), (row3 3 46 61), (row3 3 46 62), (row3 3 46 63), (row3 3 47 48), (row3 3 47 49), (row3 3 47 50), (row3 3 47 51), (row3 3 47 52)]

def b020_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 462 235), (row3 462 462 462), (row3 238 462 238), (row3 250 462 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_14_rows b020_14_labels 580125564642693712774500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_14_rows b020_14_labels]
    decide +kernel

def b020_15_rows : List Row := [(row3 3 47 53), (row3 3 47 54), (row3 3 47 55), (row3 3 47 56), (row3 3 47 57), (row3 3 47 58), (row3 3 47 59), (row3 3 47 60), (row3 3 47 61), (row3 3 47 62), (row3 3 47 63), (row3 3 48 49), (row3 3 48 50), (row3 3 48 51), (row3 3 48 52), (row3 3 48 53)]

def b020_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 254 10 171), (row3 236 228 225), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 236 462 236), (row3 302 265 302), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b020_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b020_15_rows b020_15_labels 674217961977254123867513400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b020_15_rows b020_15_labels]
    decide +kernel

theorem checked020 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_020 QuarticIntegerComputationalData.ids64_020 9231387973057817466775972740 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b020_00_rows ++ b020_01_rows) ++ (b020_02_rows ++ b020_03_rows)) ++ ((b020_04_rows ++ b020_05_rows) ++ (b020_06_rows ++ b020_07_rows))) ++ (((b020_08_rows ++ b020_09_rows) ++ (b020_10_rows ++ b020_11_rows)) ++ ((b020_12_rows ++ b020_13_rows) ++ (b020_14_rows ++ b020_15_rows))))
    ((((b020_00_labels ++ b020_01_labels) ++ (b020_02_labels ++ b020_03_labels)) ++ ((b020_04_labels ++ b020_05_labels) ++ (b020_06_labels ++ b020_07_labels))) ++ (((b020_08_labels ++ b020_09_labels) ++ (b020_10_labels ++ b020_11_labels)) ++ ((b020_12_labels ++ b020_13_labels) ++ (b020_14_labels ++ b020_15_labels)))) 9231387973057817466775972740
  exact ((((b020_00_checked.append (c := 0) b020_01_checked (by decide +kernel)).append (c := 8274327477922601325000) (b020_02_checked.append (c := 8274327477922601325000) b020_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3228011748673042238471808000) ((b020_04_checked.append (c := 79490873895497536200000) b020_05_checked (by decide +kernel)).append (c := 3228003474345564315870483000) (b020_06_checked.append (c := 3227923983471668818334283000) b020_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 9231387973057817466775972740) (((b020_08_checked.append (c := 1690853783868726399997748340) b020_09_checked (by decide +kernel)).append (c := 4808895886215061307660207340) (b020_10_checked.append (c := 3118042102346334907662459000) b020_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 6003376224384775228304164740) ((b020_12_checked.append (c := 519682250627817103063669500) b020_13_checked (by decide +kernel)).append (c := 1194480338169713920643957400) (b020_14_checked.append (c := 674798087541896817580287900) b020_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b021_00_rows : List Row := [(row3 3 48 54), (row3 3 48 55), (row3 3 48 56), (row3 3 48 57), (row3 3 48 58), (row3 3 48 59), (row3 3 48 60), (row3 3 48 61), (row3 3 48 62), (row3 3 48 63), (row3 3 49 50), (row3 3 49 51), (row3 3 49 52), (row3 3 49 53), (row3 3 49 54), (row3 3 49 55)]

def b021_00_labels : List Row := [(row3 237 237 462), (row3 266 265 266), (row3 336 428 72), (row3 110 109 111), (row3 318 315 318), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 268 265 268), (row3 190 199 198), (row3 119 216 11), (row3 232 232 462), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 228 228 234)]

theorem b021_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_00_rows b021_00_labels 104373805900235322228896170710 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_00_rows b021_00_labels]
    decide +kernel

def b021_01_rows : List Row := [(row3 3 49 56), (row3 3 49 57), (row3 3 49 58), (row3 3 49 59), (row3 3 49 60), (row3 3 49 61), (row3 3 49 62), (row3 3 49 63), (row3 3 50 51), (row3 3 50 52), (row3 3 50 53), (row3 3 50 54), (row3 3 50 55), (row3 3 50 56), (row3 3 50 57), (row3 3 50 58)]

def b021_01_labels : List Row := [(row3 158 89 356), (row3 395 415 407), (row3 120 120 112), (row3 260 173 10), (row3 235 235 462), (row3 245 245 462), (row3 234 234 234), (row3 283 283 278), (row3 302 265 302), (row3 228 234 228), (row3 246 462 246), (row3 462 462 462), (row3 246 462 246), (row3 260 10 173), (row3 120 112 120), (row3 395 407 415)]

theorem b021_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_01_rows b021_01_labels 84315624441356770450656616440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_01_rows b021_01_labels]
    decide +kernel

def b021_02_rows : List Row := [(row3 3 50 59), (row3 3 50 60), (row3 3 50 61), (row3 3 50 62), (row3 3 50 63), (row3 3 51 52), (row3 3 51 53), (row3 3 51 54), (row3 3 51 55), (row3 3 51 56), (row3 3 51 57), (row3 3 51 58), (row3 3 51 59), (row3 3 51 60), (row3 3 51 61), (row3 3 51 62)]

def b021_02_labels : List Row := [(row3 158 356 89), (row3 283 278 283), (row3 234 234 234), (row3 245 462 245), (row3 235 462 235), (row3 266 266 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 318 318 315), (row3 110 111 109), (row3 336 72 428), (row3 190 198 199), (row3 268 268 265), (row3 238 462 238)]

theorem b021_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_02_rows b021_02_labels 108833295746771915325211731060 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_02_rows b021_02_labels]
    decide +kernel

def b021_03_rows : List Row := [(row3 3 51 63), (row3 3 52 53), (row3 3 52 54), (row3 3 52 55), (row3 3 52 56), (row3 3 52 57), (row3 3 52 58), (row3 3 52 59), (row3 3 52 60), (row3 3 52 61), (row3 3 52 62), (row3 3 52 63), (row3 3 53 54), (row3 3 53 55), (row3 3 53 56), (row3 3 53 57)]

def b021_03_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 234 226 226), (row3 320 319 320), (row3 159 356 91), (row3 279 278 279), (row3 226 226 234), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462)]

theorem b021_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_03_rows b021_03_labels 6541696362559381914840084000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_03_rows b021_03_labels]
    decide +kernel

def b021_04_rows : List Row := [(row3 3 53 58), (row3 3 53 59), (row3 3 53 60), (row3 3 53 61), (row3 3 53 62), (row3 3 53 63), (row3 3 54 55), (row3 3 54 56), (row3 3 54 57), (row3 3 54 58), (row3 3 54 59), (row3 3 54 60), (row3 3 54 61), (row3 3 54 62), (row3 3 54 63), (row3 3 55 56)]

def b021_04_labels : List Row := [(row3 235 228 232), (row3 258 172 10), (row3 235 235 462), (row3 285 285 462), (row3 232 462 232), (row3 462 462 462), (row3 244 462 244), (row3 258 10 172), (row3 235 232 228), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 285 462 285), (row3 235 462 235), (row3 159 91 356)]

theorem b021_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_04_rows b021_04_labels 7580290296074972803414497000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_04_rows b021_04_labels]
    decide +kernel

def b021_05_rows : List Row := [(row3 3 55 57), (row3 3 55 58), (row3 3 55 59), (row3 3 55 60), (row3 3 55 61), (row3 3 55 62), (row3 3 55 63), (row3 3 56 57), (row3 3 56 58), (row3 3 56 59), (row3 3 56 60), (row3 3 56 61), (row3 3 56 62), (row3 3 56 63), (row3 3 57 58), (row3 3 57 59)]

def b021_05_labels : List Row := [(row3 320 320 319), (row3 234 226 226), (row3 243 243 462), (row3 462 462 462), (row3 247 247 462), (row3 226 234 226), (row3 279 279 278), (row3 44 74 439), (row3 123 331 92), (row3 269 186 9), (row3 236 236 462), (row3 259 204 8), (row3 155 332 93), (row3 359 73 429), (row3 40 413 438), (row3 123 331 92)]

theorem b021_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_05_rows b021_05_labels 1094147881562132645714990383980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_05_rows b021_05_labels]
    decide +kernel

def b021_06_rows : List Row := [(row3 3 57 60), (row3 3 57 61), (row3 3 57 62), (row3 3 57 63), (row3 3 58 59), (row3 3 58 60), (row3 3 58 61), (row3 3 58 62), (row3 3 58 63), (row3 3 59 60), (row3 3 59 61), (row3 3 59 62), (row3 3 59 63), (row3 3 60 61), (row3 3 60 62), (row3 3 60 63)]

def b021_06_labels : List Row := [(row3 296 295 296), (row3 231 227 229), (row3 297 295 297), (row3 126 128 125), (row3 44 74 439), (row3 126 125 128), (row3 297 297 295), (row3 231 229 227), (row3 296 296 295), (row3 359 429 73), (row3 155 93 332), (row3 259 8 204), (row3 236 462 236), (row3 301 301 278), (row3 233 462 233), (row3 462 462 462)]

theorem b021_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_06_rows b021_06_labels 639981909023493324902946925800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_06_rows b021_06_labels]
    decide +kernel

def b021_07_rows : List Row := [(row3 3 61 62), (row3 3 61 63), (row3 3 62 63), (row3 4 5 6), (row3 4 5 7), (row3 4 5 8), (row3 4 5 9), (row3 4 5 10), (row3 4 5 11), (row3 4 5 12), (row3 4 5 13), (row3 4 5 14), (row3 4 5 15), (row3 4 5 16), (row3 4 5 17), (row3 4 5 18)]

def b021_07_labels : List Row := [(row3 116 11 213), (row3 233 462 233), (row3 301 301 278), (row3 446 30 80), (row3 364 374 355), (row3 462 269 269), (row3 462 238 238), (row3 10 217 169), (row3 90 187 357), (row3 429 341 71), (row3 64 55 66), (row3 366 375 353), (row3 151 153 179), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462)]

theorem b021_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_07_rows b021_07_labels 4852350374615510778379421755650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_07_rows b021_07_labels]
    decide +kernel

def b021_08_rows : List Row := [(row3 4 5 19), (row3 4 5 20), (row3 4 5 21), (row3 4 5 22), (row3 4 5 23), (row3 4 5 24), (row3 4 5 25), (row3 4 5 26), (row3 4 5 27), (row3 4 5 28), (row3 4 5 29), (row3 4 5 30), (row3 4 5 31), (row3 4 5 32), (row3 4 5 33), (row3 4 5 34)]

def b021_08_labels : List Row := [(row3 10 218 170), (row3 94 168 333), (row3 339 342 328), (row3 154 154 180), (row3 462 270 270), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 8 254 203), (row3 201 201 208), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b021_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_08_rows b021_08_labels 9837853750058768422899717300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_08_rows b021_08_labels]
    decide +kernel

def b021_09_rows : List Row := [(row3 4 5 35), (row3 4 5 36), (row3 4 5 37), (row3 4 5 38), (row3 4 5 39), (row3 4 5 40), (row3 4 5 41), (row3 4 5 42), (row3 4 5 43), (row3 4 5 44), (row3 4 5 45), (row3 4 5 46), (row3 4 5 47), (row3 4 5 48), (row3 4 5 49), (row3 4 5 50)]

def b021_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 8 254 203), (row3 201 201 208), (row3 462 263 263), (row3 462 462 462), (row3 462 239 239), (row3 462 242 242), (row3 462 462 462)]

theorem b021_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_09_rows b021_09_labels 466202760129174857569917000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_09_rows b021_09_labels]
    decide +kernel

def b021_10_rows : List Row := [(row3 4 5 51), (row3 4 5 52), (row3 4 5 53), (row3 4 5 54), (row3 4 5 55), (row3 4 5 56), (row3 4 5 57), (row3 4 5 58), (row3 4 5 59), (row3 4 5 60), (row3 4 5 61), (row3 4 5 62), (row3 4 5 63), (row3 4 6 7), (row3 4 6 8), (row3 4 6 9)]

def b021_10_labels : List Row := [(row3 10 218 170), (row3 94 168 333), (row3 339 342 328), (row3 154 154 180), (row3 462 270 270), (row3 462 269 269), (row3 462 238 238), (row3 10 217 169), (row3 90 187 357), (row3 429 341 71), (row3 64 55 66), (row3 366 375 353), (row3 151 153 179), (row3 446 30 80), (row3 178 174 174), (row3 462 273 273)]

theorem b021_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_10_rows b021_10_labels 4182795616330784438513101179540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_10_rows b021_10_labels]
    decide +kernel

def b021_11_rows : List Row := [(row3 4 6 10), (row3 4 6 11), (row3 4 6 12), (row3 4 6 13), (row3 4 6 14), (row3 4 6 15), (row3 4 6 16), (row3 4 6 17), (row3 4 6 18), (row3 4 6 19), (row3 4 6 20), (row3 4 6 21), (row3 4 6 22), (row3 4 6 23), (row3 4 6 24), (row3 4 6 25)]

def b021_11_labels : List Row := [(row3 462 235 235), (row3 462 273 273), (row3 178 174 174), (row3 350 349 346), (row3 79 67 67), (row3 350 346 349), (row3 462 273 273), (row3 462 237 237), (row3 462 462 462), (row3 462 237 237), (row3 462 273 273), (row3 178 183 183), (row3 327 327 327), (row3 178 183 183), (row3 462 239 239), (row3 462 462 462)]

theorem b021_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_11_rows b021_11_labels 108825257719710425150287246800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_11_rows b021_11_labels]
    decide +kernel

def b021_12_rows : List Row := [(row3 4 6 26), (row3 4 6 27), (row3 4 6 28), (row3 4 6 29), (row3 4 6 30), (row3 4 6 31), (row3 4 6 32), (row3 4 6 33), (row3 4 6 34), (row3 4 6 35), (row3 4 6 36), (row3 4 6 37), (row3 4 6 38), (row3 4 6 39), (row3 4 6 40), (row3 4 6 41)]

def b021_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 261 261), (row3 206 210 210), (row3 462 261 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 255 255), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462)]

theorem b021_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_12_rows b021_12_labels 32566053010145013395497440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_12_rows b021_12_labels]
    decide +kernel

def b021_13_rows : List Row := [(row3 4 6 42), (row3 4 6 43), (row3 4 6 44), (row3 4 6 45), (row3 4 6 46), (row3 4 6 47), (row3 4 6 48), (row3 4 6 49), (row3 4 6 50), (row3 4 6 51), (row3 4 6 52), (row3 4 6 53), (row3 4 6 54), (row3 4 6 55), (row3 4 6 56), (row3 4 6 57)]

def b021_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 261 261), (row3 206 210 210), (row3 462 261 261), (row3 462 273 273), (row3 462 237 237), (row3 462 462 462), (row3 462 237 237), (row3 462 273 273), (row3 178 183 183), (row3 327 327 327), (row3 178 183 183), (row3 178 174 174), (row3 462 273 273)]

theorem b021_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_13_rows b021_13_labels 4494253402753967367789467760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_13_rows b021_13_labels]
    decide +kernel

def b021_14_rows : List Row := [(row3 4 6 58), (row3 4 6 59), (row3 4 6 60), (row3 4 6 61), (row3 4 6 62), (row3 4 6 63), (row3 4 7 8), (row3 4 7 9), (row3 4 7 10), (row3 4 7 11), (row3 4 7 12), (row3 4 7 13), (row3 4 7 14), (row3 4 7 15), (row3 4 7 16), (row3 4 7 17)]

def b021_14_labels : List Row := [(row3 462 235 235), (row3 462 273 273), (row3 178 174 174), (row3 350 349 346), (row3 79 67 67), (row3 350 346 349), (row3 429 71 341), (row3 90 357 187), (row3 10 169 217), (row3 462 238 238), (row3 462 269 269), (row3 151 179 153), (row3 366 353 375), (row3 64 66 55), (row3 94 333 168), (row3 10 170 218)]

theorem b021_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_14_rows b021_14_labels 513545285326805643144189486270 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_14_rows b021_14_labels]
    decide +kernel

def b021_15_rows : List Row := [(row3 4 7 18), (row3 4 7 19), (row3 4 7 20), (row3 4 7 21), (row3 4 7 22), (row3 4 7 23), (row3 4 7 24), (row3 4 7 25), (row3 4 7 26), (row3 4 7 27), (row3 4 7 28), (row3 4 7 29), (row3 4 7 30), (row3 4 7 31), (row3 4 7 32), (row3 4 7 33)]

def b021_15_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 462 239 239), (row3 462 270 270), (row3 154 180 154), (row3 339 328 342), (row3 8 203 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 263 263), (row3 201 208 201), (row3 462 462 462), (row3 462 462 462)]

theorem b021_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b021_15_rows b021_15_labels 6084696530139748068452842050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b021_15_rows b021_15_labels]
    decide +kernel

theorem checked021 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_021 QuarticIntegerComputationalData.ids64_021 11724206609821527422258063518800 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b021_00_rows ++ b021_01_rows) ++ (b021_02_rows ++ b021_03_rows)) ++ ((b021_04_rows ++ b021_05_rows) ++ (b021_06_rows ++ b021_07_rows))) ++ (((b021_08_rows ++ b021_09_rows) ++ (b021_10_rows ++ b021_11_rows)) ++ ((b021_12_rows ++ b021_13_rows) ++ (b021_14_rows ++ b021_15_rows))))
    ((((b021_00_labels ++ b021_01_labels) ++ (b021_02_labels ++ b021_03_labels)) ++ ((b021_04_labels ++ b021_05_labels) ++ (b021_06_labels ++ b021_07_labels))) ++ (((b021_08_labels ++ b021_09_labels) ++ (b021_10_labels ++ b021_11_labels)) ++ ((b021_12_labels ++ b021_13_labels) ++ (b021_14_labels ++ b021_15_labels)))) 11724206609821527422258063518800
  exact ((((b021_00_checked.append (c := 188689430341592092679552787150) b021_01_checked (by decide +kernel)).append (c := 304064422450923389919604602210) (b021_02_checked.append (c := 115374992109331297240051815060) b021_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 6898124877948135111720378164640) ((b021_04_checked.append (c := 1101728171858207618518404880980) b021_05_checked (by decide +kernel)).append (c := 6594060455497211721800773562430) (b021_06_checked.append (c := 5492332283639004103282368681450) b021_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11724206609821527422258063518800) (((b021_08_checked.append (c := 10304056510187943280469634300) b021_09_checked (by decide +kernel)).append (c := 4301924930560682806943858060640) (b021_10_checked.append (c := 4291620874050494863663388426340) b021_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4826081731873392310537685354160) ((b021_12_checked.append (c := 4526819455764112381184965200) b021_13_checked (by decide +kernel)).append (c := 524156801312709503593827293520) (b021_14_checked.append (c := 519629981856945391212642328320) b021_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b022_00_rows : List Row := [(row3 4 7 34), (row3 4 7 35), (row3 4 7 36), (row3 4 7 37), (row3 4 7 38), (row3 4 7 39), (row3 4 7 40), (row3 4 7 41), (row3 4 7 42), (row3 4 7 43), (row3 4 7 44), (row3 4 7 45), (row3 4 7 46), (row3 4 7 47), (row3 4 7 48), (row3 4 7 49)]

def b022_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 8 203 254), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 240 240), (row3 462 462 462), (row3 462 263 263), (row3 201 208 201), (row3 94 333 168), (row3 10 170 218)]

theorem b022_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_00_rows b022_00_labels 4219359980048195212016792250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_00_rows b022_00_labels]
    decide +kernel

def b022_01_rows : List Row := [(row3 4 7 50), (row3 4 7 51), (row3 4 7 52), (row3 4 7 53), (row3 4 7 54), (row3 4 7 55), (row3 4 7 56), (row3 4 7 57), (row3 4 7 58), (row3 4 7 59), (row3 4 7 60), (row3 4 7 61), (row3 4 7 62), (row3 4 7 63), (row3 4 8 9), (row3 4 8 10)]

def b022_01_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 462 239 239), (row3 462 270 270), (row3 154 180 154), (row3 339 328 342), (row3 429 71 341), (row3 90 357 187), (row3 10 169 217), (row3 462 238 238), (row3 462 269 269), (row3 151 179 153), (row3 366 353 375), (row3 64 66 55), (row3 163 193 139), (row3 289 299 299)]

theorem b022_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_01_rows b022_01_labels 409275025006846224330879433350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_01_rows b022_01_labels]
    decide +kernel

def b022_02_rows : List Row := [(row3 4 8 11), (row3 4 8 12), (row3 4 8 13), (row3 4 8 14), (row3 4 8 15), (row3 4 8 16), (row3 4 8 17), (row3 4 8 18), (row3 4 8 19), (row3 4 8 20), (row3 4 8 21), (row3 4 8 22), (row3 4 8 23), (row3 4 8 24), (row3 4 8 25), (row3 4 8 26)]

def b022_02_labels : List Row := [(row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 289 299 299), (row3 163 193 139), (row3 462 208 208), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462)]

theorem b022_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_02_rows b022_02_labels 2146211646908190228204202200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_02_rows b022_02_labels]
    decide +kernel

def b022_03_rows : List Row := [(row3 4 8 27), (row3 4 8 28), (row3 4 8 29), (row3 4 8 30), (row3 4 8 31), (row3 4 8 32), (row3 4 8 33), (row3 4 8 34), (row3 4 8 35), (row3 4 8 36), (row3 4 8 37), (row3 4 8 38), (row3 4 8 39), (row3 4 8 40), (row3 4 8 41), (row3 4 8 42)]

def b022_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462)]

theorem b022_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_03_rows b022_03_labels 9856983129894651751837500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_03_rows b022_03_labels]
    decide +kernel

def b022_04_rows : List Row := [(row3 4 8 43), (row3 4 8 44), (row3 4 8 45), (row3 4 8 46), (row3 4 8 47), (row3 4 8 48), (row3 4 8 49), (row3 4 8 50), (row3 4 8 51), (row3 4 8 52), (row3 4 8 53), (row3 4 8 54), (row3 4 8 55), (row3 4 8 56), (row3 4 8 57), (row3 4 8 58)]

def b022_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 208 208), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 337 337), (row3 232 193 189), (row3 462 272 272)]

theorem b022_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_04_rows b022_04_labels 7247862091079120122717201500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_04_rows b022_04_labels]
    decide +kernel

def b022_05_rows : List Row := [(row3 4 8 59), (row3 4 8 60), (row3 4 8 61), (row3 4 8 62), (row3 4 8 63), (row3 4 9 10), (row3 4 9 11), (row3 4 9 12), (row3 4 9 13), (row3 4 9 14), (row3 4 9 15), (row3 4 9 16), (row3 4 9 17), (row3 4 9 18), (row3 4 9 19), (row3 4 9 20)]

def b022_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 272 272), (row3 232 193 189), (row3 399 156 82), (row3 288 288 462), (row3 236 236 462), (row3 462 462 462), (row3 231 227 229), (row3 288 288 288), (row3 288 290 261), (row3 163 162 235), (row3 288 288 462), (row3 232 232 462), (row3 462 462 462)]

theorem b022_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_05_rows b022_05_labels 21550841395519110940332428040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_05_rows b022_05_labels]
    decide +kernel

def b022_06_rows : List Row := [(row3 4 9 21), (row3 4 9 22), (row3 4 9 23), (row3 4 9 24), (row3 4 9 25), (row3 4 9 26), (row3 4 9 27), (row3 4 9 28), (row3 4 9 29), (row3 4 9 30), (row3 4 9 31), (row3 4 9 32), (row3 4 9 33), (row3 4 9 34), (row3 4 9 35), (row3 4 9 36)]

def b022_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 228 235), (row3 232 230 238), (row3 273 273 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_06_rows b022_06_labels 9093427980765171217977600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_06_rows b022_06_labels]
    decide +kernel

def b022_07_rows : List Row := [(row3 4 9 37), (row3 4 9 38), (row3 4 9 39), (row3 4 9 40), (row3 4 9 41), (row3 4 9 42), (row3 4 9 43), (row3 4 9 44), (row3 4 9 45), (row3 4 9 46), (row3 4 9 47), (row3 4 9 48), (row3 4 9 49), (row3 4 9 50), (row3 4 9 51), (row3 4 9 52)]

def b022_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 236 233 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_07_rows b022_07_labels 3717810713571145265944800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_07_rows b022_07_labels]
    decide +kernel

def b022_08_rows : List Row := [(row3 4 9 53), (row3 4 9 54), (row3 4 9 55), (row3 4 9 56), (row3 4 9 57), (row3 4 9 58), (row3 4 9 59), (row3 4 9 60), (row3 4 9 61), (row3 4 9 62), (row3 4 9 63), (row3 4 10 11), (row3 4 10 12), (row3 4 10 13), (row3 4 10 14), (row3 4 10 15)]

def b022_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 232 189 193), (row3 288 288 288), (row3 221 220 222), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 273 273), (row3 399 156 82), (row3 289 299 299), (row3 231 227 229), (row3 462 251 251), (row3 231 229 227)]

theorem b022_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_08_rows b022_08_labels 20892451211427124488185374500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_08_rows b022_08_labels]
    decide +kernel

def b022_09_rows : List Row := [(row3 4 10 16), (row3 4 10 17), (row3 4 10 18), (row3 4 10 19), (row3 4 10 20), (row3 4 10 21), (row3 4 10 22), (row3 4 10 23), (row3 4 10 24), (row3 4 10 25), (row3 4 10 26), (row3 4 10 27), (row3 4 10 28), (row3 4 10 29), (row3 4 10 30), (row3 4 10 31)]

def b022_09_labels : List Row := [(row3 224 223 223), (row3 306 311 311), (row3 131 105 105), (row3 306 311 311), (row3 224 223 223), (row3 462 248 248), (row3 462 462 462), (row3 462 248 248), (row3 462 249 249), (row3 224 224 224), (row3 289 291 291), (row3 224 224 224), (row3 462 249 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_09_rows b022_09_labels 2490244858433652393795940800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_09_rows b022_09_labels]
    decide +kernel

def b022_10_rows : List Row := [(row3 4 10 32), (row3 4 10 33), (row3 4 10 34), (row3 4 10 35), (row3 4 10 36), (row3 4 10 37), (row3 4 10 38), (row3 4 10 39), (row3 4 10 40), (row3 4 10 41), (row3 4 10 42), (row3 4 10 43), (row3 4 10 44), (row3 4 10 45), (row3 4 10 46), (row3 4 10 47)]

def b022_10_labels : List Row := [(row3 462 462 462), (row3 462 246 246), (row3 234 234 234), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_10_rows b022_10_labels 398866115304400177012500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_10_rows b022_10_labels]
    decide +kernel

def b022_11_rows : List Row := [(row3 4 10 48), (row3 4 10 49), (row3 4 10 50), (row3 4 10 51), (row3 4 10 52), (row3 4 10 53), (row3 4 10 54), (row3 4 10 55), (row3 4 10 56), (row3 4 10 57), (row3 4 10 58), (row3 4 10 59), (row3 4 10 60), (row3 4 10 61), (row3 4 10 62), (row3 4 10 63)]

def b022_11_labels : List Row := [(row3 462 237 237), (row3 462 248 248), (row3 234 234 234), (row3 462 248 248), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 244 244), (row3 462 272 272), (row3 221 222 220), (row3 306 314 314), (row3 221 220 222), (row3 462 272 272), (row3 462 235 235), (row3 462 246 246), (row3 462 235 235)]

theorem b022_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_11_rows b022_11_labels 140369035622399043083438400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_11_rows b022_11_labels]
    decide +kernel

def b022_12_rows : List Row := [(row3 4 11 12), (row3 4 11 13), (row3 4 11 14), (row3 4 11 15), (row3 4 11 16), (row3 4 11 17), (row3 4 11 18), (row3 4 11 19), (row3 4 11 20), (row3 4 11 21), (row3 4 11 22), (row3 4 11 23), (row3 4 11 24), (row3 4 11 25), (row3 4 11 26), (row3 4 11 27)]

def b022_12_labels : List Row := [(row3 163 193 139), (row3 288 288 288), (row3 231 229 227), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 163 235 162), (row3 288 261 290), (row3 232 235 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 273 462 273)]

theorem b022_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_12_rows b022_12_labels 2363971080141026200136930400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_12_rows b022_12_labels]
    decide +kernel

def b022_13_rows : List Row := [(row3 4 11 28), (row3 4 11 29), (row3 4 11 30), (row3 4 11 31), (row3 4 11 32), (row3 4 11 33), (row3 4 11 34), (row3 4 11 35), (row3 4 11 36), (row3 4 11 37), (row3 4 11 38), (row3 4 11 39), (row3 4 11 40), (row3 4 11 41), (row3 4 11 42), (row3 4 11 43)]

def b022_13_labels : List Row := [(row3 232 238 230), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_13_rows b022_13_labels 1207476383526128917656000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_13_rows b022_13_labels]
    decide +kernel

def b022_14_rows : List Row := [(row3 4 11 44), (row3 4 11 45), (row3 4 11 46), (row3 4 11 47), (row3 4 11 48), (row3 4 11 49), (row3 4 11 50), (row3 4 11 51), (row3 4 11 52), (row3 4 11 53), (row3 4 11 54), (row3 4 11 55), (row3 4 11 56), (row3 4 11 57), (row3 4 11 58), (row3 4 11 59)]

def b022_14_labels : List Row := [(row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 235 233), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 221 222 220), (row3 288 288 288)]

theorem b022_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_14_rows b022_14_labels 32787851640577362009046800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_14_rows b022_14_labels]
    decide +kernel

def b022_15_rows : List Row := [(row3 4 11 60), (row3 4 11 61), (row3 4 11 62), (row3 4 11 63), (row3 4 12 13), (row3 4 12 14), (row3 4 12 15), (row3 4 12 16), (row3 4 12 17), (row3 4 12 18), (row3 4 12 19), (row3 4 12 20), (row3 4 12 21), (row3 4 12 22), (row3 4 12 23), (row3 4 12 24)]

def b022_15_labels : List Row := [(row3 232 193 189), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462), (row3 163 139 193), (row3 289 299 299), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 208 208), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b022_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b022_15_rows b022_15_labels 2495014179911330158867099500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b022_15_rows b022_15_labels]
    decide +kernel

theorem checked022 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_022 QuarticIntegerComputationalData.ids64_022 472878412901900011977558316140 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b022_00_rows ++ b022_01_rows) ++ (b022_02_rows ++ b022_03_rows)) ++ ((b022_04_rows ++ b022_05_rows) ++ (b022_06_rows ++ b022_07_rows))) ++ (((b022_08_rows ++ b022_09_rows) ++ (b022_10_rows ++ b022_11_rows)) ++ ((b022_12_rows ++ b022_13_rows) ++ (b022_14_rows ++ b022_15_rows))))
    ((((b022_00_labels ++ b022_01_labels) ++ (b022_02_labels ++ b022_03_labels)) ++ ((b022_04_labels ++ b022_05_labels) ++ (b022_06_labels ++ b022_07_labels))) ++ (((b022_08_labels ++ b022_09_labels) ++ (b022_10_labels ++ b022_11_labels)) ++ ((b022_12_labels ++ b022_13_labels) ++ (b022_14_labels ++ b022_15_labels)))) 472878412901900011977558316140
  exact ((((b022_00_checked.append (c := 413494384986894419542896225600) b022_01_checked (by decide +kernel)).append (c := 415650453616932504422852265300) (b022_02_checked.append (c := 2156068630038084879956039700) b022_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 444461968342225071802385817240) ((b022_04_checked.append (c := 28798703486598231063049629540) b022_05_checked (by decide +kernel)).append (c := 28811514725292567379533551940) (b022_06_checked.append (c := 12811238694336316483922400) b022_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 472878412901900011977558316140) (((b022_08_checked.append (c := 23382696069860776881981315300) b022_09_checked (by decide +kernel)).append (c := 23523463971598480325241766200) (b022_10_checked.append (c := 140767901737703443260450900) b022_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 28416444559674940175172498900) ((b022_12_checked.append (c := 2365178556524552329054586400) b022_13_checked (by decide +kernel)).append (c := 4892980588076459849930732700) (b022_14_checked.append (c := 2527802031551907520876146300) b022_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b023_00_rows : List Row := [(row3 4 12 25), (row3 4 12 26), (row3 4 12 27), (row3 4 12 28), (row3 4 12 29), (row3 4 12 30), (row3 4 12 31), (row3 4 12 32), (row3 4 12 33), (row3 4 12 34), (row3 4 12 35), (row3 4 12 36), (row3 4 12 37), (row3 4 12 38), (row3 4 12 39), (row3 4 12 40)]

def b023_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_00_rows b023_00_labels 10094062839304017402007500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_00_rows b023_00_labels]
    decide +kernel

def b023_01_rows : List Row := [(row3 4 12 41), (row3 4 12 42), (row3 4 12 43), (row3 4 12 44), (row3 4 12 45), (row3 4 12 46), (row3 4 12 47), (row3 4 12 48), (row3 4 12 49), (row3 4 12 50), (row3 4 12 51), (row3 4 12 52), (row3 4 12 53), (row3 4 12 54), (row3 4 12 55), (row3 4 12 56)]

def b023_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 257 257), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 269 269), (row3 462 208 208), (row3 462 269 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_01_rows b023_01_labels 242663682317394268532374500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_01_rows b023_01_labels]
    decide +kernel

def b023_02_rows : List Row := [(row3 4 12 57), (row3 4 12 58), (row3 4 12 59), (row3 4 12 60), (row3 4 12 61), (row3 4 12 62), (row3 4 12 63), (row3 4 13 14), (row3 4 13 15), (row3 4 13 16), (row3 4 13 17), (row3 4 13 18), (row3 4 13 19), (row3 4 13 20), (row3 4 13 21), (row3 4 13 22)]

def b023_02_labels : List Row := [(row3 462 462 462), (row3 462 272 272), (row3 232 189 193), (row3 462 337 337), (row3 232 189 193), (row3 462 272 272), (row3 462 462 462), (row3 399 82 156), (row3 288 462 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 235 228), (row3 288 261 290), (row3 163 235 162), (row3 288 462 288)]

theorem b023_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_02_rows b023_02_labels 28524297746704636683286392540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_02_rows b023_02_labels]
    decide +kernel

def b023_03_rows : List Row := [(row3 4 13 23), (row3 4 13 24), (row3 4 13 25), (row3 4 13 26), (row3 4 13 27), (row3 4 13 28), (row3 4 13 29), (row3 4 13 30), (row3 4 13 31), (row3 4 13 32), (row3 4 13 33), (row3 4 13 34), (row3 4 13 35), (row3 4 13 36), (row3 4 13 37), (row3 4 13 38)]

def b023_03_labels : List Row := [(row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 238 230), (row3 273 462 273), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462)]

theorem b023_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_03_rows b023_03_labels 9080596711230070166481600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_03_rows b023_03_labels]
    decide +kernel

def b023_04_rows : List Row := [(row3 4 13 39), (row3 4 13 40), (row3 4 13 41), (row3 4 13 42), (row3 4 13 43), (row3 4 13 44), (row3 4 13 45), (row3 4 13 46), (row3 4 13 47), (row3 4 13 48), (row3 4 13 49), (row3 4 13 50), (row3 4 13 51), (row3 4 13 52), (row3 4 13 53), (row3 4 13 54)]

def b023_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 261 261), (row3 236 235 233), (row3 462 462 462)]

theorem b023_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_04_rows b023_04_labels 4121709842655973791316800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_04_rows b023_04_labels]
    decide +kernel

def b023_05_rows : List Row := [(row3 4 13 55), (row3 4 13 56), (row3 4 13 57), (row3 4 13 58), (row3 4 13 59), (row3 4 13 60), (row3 4 13 61), (row3 4 13 62), (row3 4 13 63), (row3 4 14 15), (row3 4 14 16), (row3 4 14 17), (row3 4 14 18), (row3 4 14 19), (row3 4 14 20), (row3 4 14 21)]

def b023_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 273 273), (row3 232 193 189), (row3 288 288 288), (row3 221 222 220), (row3 462 462 462), (row3 399 82 156), (row3 224 223 223), (row3 462 248 248), (row3 462 462 462), (row3 462 248 248), (row3 224 223 223), (row3 306 311 311)]

theorem b023_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_05_rows b023_05_labels 20702941682219310902799194100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_05_rows b023_05_labels]
    decide +kernel

def b023_06_rows : List Row := [(row3 4 14 22), (row3 4 14 23), (row3 4 14 24), (row3 4 14 25), (row3 4 14 26), (row3 4 14 27), (row3 4 14 28), (row3 4 14 29), (row3 4 14 30), (row3 4 14 31), (row3 4 14 32), (row3 4 14 33), (row3 4 14 34), (row3 4 14 35), (row3 4 14 36), (row3 4 14 37)]

def b023_06_labels : List Row := [(row3 131 105 105), (row3 306 311 311), (row3 462 249 249), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 249 249), (row3 224 224 224), (row3 289 291 291), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246)]

theorem b023_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_06_rows b023_06_labels 2452353267658306110841552500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_06_rows b023_06_labels]
    decide +kernel

def b023_07_rows : List Row := [(row3 4 14 38), (row3 4 14 39), (row3 4 14 40), (row3 4 14 41), (row3 4 14 42), (row3 4 14 43), (row3 4 14 44), (row3 4 14 45), (row3 4 14 46), (row3 4 14 47), (row3 4 14 48), (row3 4 14 49), (row3 4 14 50), (row3 4 14 51), (row3 4 14 52), (row3 4 14 53)]

def b023_07_labels : List Row := [(row3 234 234 234), (row3 462 246 246), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 244 244), (row3 462 237 237), (row3 462 248 248)]

theorem b023_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_07_rows b023_07_labels 838707519873949522875000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_07_rows b023_07_labels]
    decide +kernel

def b023_08_rows : List Row := [(row3 4 14 54), (row3 4 14 55), (row3 4 14 56), (row3 4 14 57), (row3 4 14 58), (row3 4 14 59), (row3 4 14 60), (row3 4 14 61), (row3 4 14 62), (row3 4 14 63), (row3 4 15 16), (row3 4 15 17), (row3 4 15 18), (row3 4 15 19), (row3 4 15 20), (row3 4 15 21)]

def b023_08_labels : List Row := [(row3 234 234 234), (row3 462 248 248), (row3 462 272 272), (row3 462 235 235), (row3 462 246 246), (row3 462 235 235), (row3 462 272 272), (row3 221 220 222), (row3 306 314 314), (row3 221 222 220), (row3 288 290 261), (row3 232 228 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462)]

theorem b023_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_08_rows b023_08_labels 162520476212522308437656100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_08_rows b023_08_labels]
    decide +kernel

def b023_09_rows : List Row := [(row3 4 15 22), (row3 4 15 23), (row3 4 15 24), (row3 4 15 25), (row3 4 15 26), (row3 4 15 27), (row3 4 15 28), (row3 4 15 29), (row3 4 15 30), (row3 4 15 31), (row3 4 15 32), (row3 4 15 33), (row3 4 15 34), (row3 4 15 35), (row3 4 15 36), (row3 4 15 37)]

def b023_09_labels : List Row := [(row3 288 288 462), (row3 163 162 235), (row3 232 230 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_09_rows b023_09_labels 751310550007807512222259200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_09_rows b023_09_labels]
    decide +kernel

def b023_10_rows : List Row := [(row3 4 15 38), (row3 4 15 39), (row3 4 15 40), (row3 4 15 41), (row3 4 15 42), (row3 4 15 43), (row3 4 15 44), (row3 4 15 45), (row3 4 15 46), (row3 4 15 47), (row3 4 15 48), (row3 4 15 49), (row3 4 15 50), (row3 4 15 51), (row3 4 15 52), (row3 4 15 53)]

def b023_10_labels : List Row := [(row3 462 462 462), (row3 236 236 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_10_rows b023_10_labels 3705147702386075290564800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_10_rows b023_10_labels]
    decide +kernel

def b023_11_rows : List Row := [(row3 4 15 54), (row3 4 15 55), (row3 4 15 56), (row3 4 15 57), (row3 4 15 58), (row3 4 15 59), (row3 4 15 60), (row3 4 15 61), (row3 4 15 62), (row3 4 15 63), (row3 4 16 17), (row3 4 16 18), (row3 4 16 19), (row3 4 16 20), (row3 4 16 21), (row3 4 16 22)]

def b023_11_labels : List Row := [(row3 462 462 462), (row3 236 233 235), (row3 232 189 193), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 221 220 222), (row3 288 288 288), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_11_rows b023_11_labels 405403392760371657079318800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_11_rows b023_11_labels]
    decide +kernel

def b023_12_rows : List Row := [(row3 4 16 23), (row3 4 16 24), (row3 4 16 25), (row3 4 16 26), (row3 4 16 27), (row3 4 16 28), (row3 4 16 29), (row3 4 16 30), (row3 4 16 31), (row3 4 16 32), (row3 4 16 33), (row3 4 16 34), (row3 4 16 35), (row3 4 16 36), (row3 4 16 37), (row3 4 16 38)]

def b023_12_labels : List Row := [(row3 462 237 237), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_12_rows b023_12_labels 1120220437693254695784000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_12_rows b023_12_labels]
    decide +kernel

def b023_13_rows : List Row := [(row3 4 16 39), (row3 4 16 40), (row3 4 16 41), (row3 4 16 42), (row3 4 16 43), (row3 4 16 44), (row3 4 16 45), (row3 4 16 46), (row3 4 16 47), (row3 4 16 48), (row3 4 16 49), (row3 4 16 50), (row3 4 16 51), (row3 4 16 52), (row3 4 16 53), (row3 4 16 54)]

def b023_13_labels : List Row := [(row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 255 255), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b023_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_13_rows b023_13_labels 1232609799478312880427600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_13_rows b023_13_labels]
    decide +kernel

def b023_14_rows : List Row := [(row3 4 16 55), (row3 4 16 56), (row3 4 16 57), (row3 4 16 58), (row3 4 16 59), (row3 4 16 60), (row3 4 16 61), (row3 4 16 62), (row3 4 16 63), (row3 4 17 18), (row3 4 17 19), (row3 4 17 20), (row3 4 17 21), (row3 4 17 22), (row3 4 17 23), (row3 4 17 24)]

def b023_14_labels : List Row := [(row3 462 237 237), (row3 462 208 208), (row3 462 261 261), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 261 261), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 242 242)]

theorem b023_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_14_rows b023_14_labels 179694999578780784971841600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_14_rows b023_14_labels]
    decide +kernel

def b023_15_rows : List Row := [(row3 4 17 25), (row3 4 17 26), (row3 4 17 27), (row3 4 17 28), (row3 4 17 29), (row3 4 17 30), (row3 4 17 31), (row3 4 17 32), (row3 4 17 33), (row3 4 17 34), (row3 4 17 35), (row3 4 17 36), (row3 4 17 37), (row3 4 17 38), (row3 4 17 39), (row3 4 17 40)]

def b023_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242)]

theorem b023_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b023_15_rows b023_15_labels 3830050178451618862500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b023_15_rows b023_15_labels]
    decide +kernel

theorem checked023 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_023 QuarticIntegerComputationalData.ids64_023 53451382682361930333538909140 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b023_00_rows ++ b023_01_rows) ++ (b023_02_rows ++ b023_03_rows)) ++ ((b023_04_rows ++ b023_05_rows) ++ (b023_06_rows ++ b023_07_rows))) ++ (((b023_08_rows ++ b023_09_rows) ++ (b023_10_rows ++ b023_11_rows)) ++ ((b023_12_rows ++ b023_13_rows) ++ (b023_14_rows ++ b023_15_rows))))
    ((((b023_00_labels ++ b023_01_labels) ++ (b023_02_labels ++ b023_03_labels)) ++ ((b023_04_labels ++ b023_05_labels) ++ (b023_06_labels ++ b023_07_labels))) ++ (((b023_08_labels ++ b023_09_labels) ++ (b023_10_labels ++ b023_11_labels)) ++ ((b023_12_labels ++ b023_13_labels) ++ (b023_14_labels ++ b023_15_labels)))) 53451382682361930333538909140
  exact ((((b023_00_checked.append (c := 252757745156698285934382000) b023_01_checked (by decide +kernel)).append (c := 28786136088572565039387256140) (b023_02_checked.append (c := 28533378343415866753452874140) b023_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 51946391455812711976342194540) ((b023_04_checked.append (c := 20707063392061966876590510900) b023_05_checked (by decide +kernel)).append (c := 23160255367240146936954938400) (b023_06_checked.append (c := 2453191975178180060364427500) b023_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 53451382682361930333538909140) (((b023_08_checked.append (c := 913831026220329820659915300) b023_09_checked (by decide +kernel)).append (c := 1322939566683087553029798900) (b023_10_checked.append (c := 409108540462757732369883600) b023_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1504991226549218357196714600) ((b023_12_checked.append (c := 2352830237171567576211600) b023_13_checked (by decide +kernel)).append (c := 182051659866130804166915700) (b023_14_checked.append (c := 179698829628959236590704100) b023_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b024_00_rows : List Row := [(row3 4 17 41), (row3 4 17 42), (row3 4 17 43), (row3 4 17 44), (row3 4 17 45), (row3 4 17 46), (row3 4 17 47), (row3 4 17 48), (row3 4 17 49), (row3 4 17 50), (row3 4 17 51), (row3 4 17 52), (row3 4 17 53), (row3 4 17 54), (row3 4 17 55), (row3 4 17 56)]

def b024_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 269 269)]

theorem b024_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_00_rows b024_00_labels 29897324044901917589695500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_00_rows b024_00_labels]
    decide +kernel

def b024_01_rows : List Row := [(row3 4 17 57), (row3 4 17 58), (row3 4 17 59), (row3 4 17 60), (row3 4 17 61), (row3 4 17 62), (row3 4 17 63), (row3 4 18 19), (row3 4 18 20), (row3 4 18 21), (row3 4 18 22), (row3 4 18 23), (row3 4 18 24), (row3 4 18 25), (row3 4 18 26), (row3 4 18 27)]

def b024_01_labels : List Row := [(row3 236 235 233), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_01_rows b024_01_labels 1145540201493012418962000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_01_rows b024_01_labels]
    decide +kernel

def b024_02_rows : List Row := [(row3 4 18 28), (row3 4 18 29), (row3 4 18 30), (row3 4 18 31), (row3 4 18 32), (row3 4 18 33), (row3 4 18 34), (row3 4 18 35), (row3 4 18 36), (row3 4 18 37), (row3 4 18 38), (row3 4 18 39), (row3 4 18 40), (row3 4 18 41), (row3 4 18 42), (row3 4 18 43)]

def b024_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_02_rows b024_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_02_rows b024_02_labels]
    decide +kernel

def b024_03_rows : List Row := [(row3 4 18 44), (row3 4 18 45), (row3 4 18 46), (row3 4 18 47), (row3 4 18 48), (row3 4 18 49), (row3 4 18 50), (row3 4 18 51), (row3 4 18 52), (row3 4 18 53), (row3 4 18 54), (row3 4 18 55), (row3 4 18 56), (row3 4 18 57), (row3 4 18 58), (row3 4 18 59)]

def b024_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462)]

theorem b024_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_03_rows b024_03_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_03_rows b024_03_labels]
    decide +kernel

def b024_04_rows : List Row := [(row3 4 18 60), (row3 4 18 61), (row3 4 18 62), (row3 4 18 63), (row3 4 19 20), (row3 4 19 21), (row3 4 19 22), (row3 4 19 23), (row3 4 19 24), (row3 4 19 25), (row3 4 19 26), (row3 4 19 27), (row3 4 19 28), (row3 4 19 29), (row3 4 19 30), (row3 4 19 31)]

def b024_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_04_rows b024_04_labels 869656041500373422118000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_04_rows b024_04_labels]
    decide +kernel

def b024_05_rows : List Row := [(row3 4 19 32), (row3 4 19 33), (row3 4 19 34), (row3 4 19 35), (row3 4 19 36), (row3 4 19 37), (row3 4 19 38), (row3 4 19 39), (row3 4 19 40), (row3 4 19 41), (row3 4 19 42), (row3 4 19 43), (row3 4 19 44), (row3 4 19 45), (row3 4 19 46), (row3 4 19 47)]

def b024_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_05_rows b024_05_labels 3830050178451618862500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_05_rows b024_05_labels]
    decide +kernel

def b024_06_rows : List Row := [(row3 4 19 48), (row3 4 19 49), (row3 4 19 50), (row3 4 19 51), (row3 4 19 52), (row3 4 19 53), (row3 4 19 54), (row3 4 19 55), (row3 4 19 56), (row3 4 19 57), (row3 4 19 58), (row3 4 19 59), (row3 4 19 60), (row3 4 19 61), (row3 4 19 62), (row3 4 19 63)]

def b024_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 236 233 235), (row3 462 269 269), (row3 462 235 235), (row3 462 244 244), (row3 462 462 462)]

theorem b024_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_06_rows b024_06_labels 31042864246394930008657500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_06_rows b024_06_labels]
    decide +kernel

def b024_07_rows : List Row := [(row3 4 20 21), (row3 4 20 22), (row3 4 20 23), (row3 4 20 24), (row3 4 20 25), (row3 4 20 26), (row3 4 20 27), (row3 4 20 28), (row3 4 20 29), (row3 4 20 30), (row3 4 20 31), (row3 4 20 32), (row3 4 20 33), (row3 4 20 34), (row3 4 20 35), (row3 4 20 36)]

def b024_07_labels : List Row := [(row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_07_rows b024_07_labels 1120220437693254695784000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_07_rows b024_07_labels]
    decide +kernel

def b024_08_rows : List Row := [(row3 4 20 37), (row3 4 20 38), (row3 4 20 39), (row3 4 20 40), (row3 4 20 41), (row3 4 20 42), (row3 4 20 43), (row3 4 20 44), (row3 4 20 45), (row3 4 20 46), (row3 4 20 47), (row3 4 20 48), (row3 4 20 49), (row3 4 20 50), (row3 4 20 51), (row3 4 20 52)]

def b024_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 239 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 255 255)]

theorem b024_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_08_rows b024_08_labels 1232609799478312880427600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_08_rows b024_08_labels]
    decide +kernel

def b024_09_rows : List Row := [(row3 4 20 53), (row3 4 20 54), (row3 4 20 55), (row3 4 20 56), (row3 4 20 57), (row3 4 20 58), (row3 4 20 59), (row3 4 20 60), (row3 4 20 61), (row3 4 20 62), (row3 4 20 63), (row3 4 21 22), (row3 4 21 23), (row3 4 21 24), (row3 4 21 25), (row3 4 21 26)]

def b024_09_labels : List Row := [(row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 237 237), (row3 462 261 261), (row3 462 208 208), (row3 462 261 261), (row3 462 237 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_09_rows b024_09_labels 179667619367414530900791600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_09_rows b024_09_labels]
    decide +kernel

def b024_10_rows : List Row := [(row3 4 21 27), (row3 4 21 28), (row3 4 21 29), (row3 4 21 30), (row3 4 21 31), (row3 4 21 32), (row3 4 21 33), (row3 4 21 34), (row3 4 21 35), (row3 4 21 36), (row3 4 21 37), (row3 4 21 38), (row3 4 21 39), (row3 4 21 40), (row3 4 21 41), (row3 4 21 42)]

def b024_10_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_10_rows b024_10_labels 8051053906808277322500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_10_rows b024_10_labels]
    decide +kernel

def b024_11_rows : List Row := [(row3 4 21 43), (row3 4 21 44), (row3 4 21 45), (row3 4 21 46), (row3 4 21 47), (row3 4 21 48), (row3 4 21 49), (row3 4 21 50), (row3 4 21 51), (row3 4 21 52), (row3 4 21 53), (row3 4 21 54), (row3 4 21 55), (row3 4 21 56), (row3 4 21 57), (row3 4 21 58)]

def b024_11_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 237 237), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244)]

theorem b024_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_11_rows b024_11_labels 177629269824299997783000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_11_rows b024_11_labels]
    decide +kernel

def b024_12_rows : List Row := [(row3 4 21 59), (row3 4 21 60), (row3 4 21 61), (row3 4 21 62), (row3 4 21 63), (row3 4 22 23), (row3 4 22 24), (row3 4 22 25), (row3 4 22 26), (row3 4 22 27), (row3 4 22 28), (row3 4 22 29), (row3 4 22 30), (row3 4 22 31), (row3 4 22 32), (row3 4 22 33)]

def b024_12_labels : List Row := [(row3 462 235 235), (row3 462 269 269), (row3 236 233 235), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_12_rows b024_12_labels 30869065026749081629737000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_12_rows b024_12_labels]
    decide +kernel

def b024_13_rows : List Row := [(row3 4 22 34), (row3 4 22 35), (row3 4 22 36), (row3 4 22 37), (row3 4 22 38), (row3 4 22 39), (row3 4 22 40), (row3 4 22 41), (row3 4 22 42), (row3 4 22 43), (row3 4 22 44), (row3 4 22 45), (row3 4 22 46), (row3 4 22 47), (row3 4 22 48), (row3 4 22 49)]

def b024_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b024_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_13_rows b024_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_13_rows b024_13_labels]
    decide +kernel

def b024_14_rows : List Row := [(row3 4 22 50), (row3 4 22 51), (row3 4 22 52), (row3 4 22 53), (row3 4 22 54), (row3 4 22 55), (row3 4 22 56), (row3 4 22 57), (row3 4 22 58), (row3 4 22 59), (row3 4 22 60), (row3 4 22 61), (row3 4 22 62), (row3 4 22 63), (row3 4 23 24), (row3 4 23 25)]

def b024_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462)]

theorem b024_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_14_rows b024_14_labels 332426128156693095622500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_14_rows b024_14_labels]
    decide +kernel

def b024_15_rows : List Row := [(row3 4 23 26), (row3 4 23 27), (row3 4 23 28), (row3 4 23 29), (row3 4 23 30), (row3 4 23 31), (row3 4 23 32), (row3 4 23 33), (row3 4 23 34), (row3 4 23 35), (row3 4 23 36), (row3 4 23 37), (row3 4 23 38), (row3 4 23 39), (row3 4 23 40), (row3 4 23 41)]

def b024_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 242 242), (row3 462 462 462)]

theorem b024_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b024_15_rows b024_15_labels 3830050178451618862500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b024_15_rows b024_15_labels]
    decide +kernel

theorem checked024 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_024 QuarticIntegerComputationalData.ids64_024 276695040792120002972926200 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b024_00_rows ++ b024_01_rows) ++ (b024_02_rows ++ b024_03_rows)) ++ ((b024_04_rows ++ b024_05_rows) ++ (b024_06_rows ++ b024_07_rows))) ++ (((b024_08_rows ++ b024_09_rows) ++ (b024_10_rows ++ b024_11_rows)) ++ ((b024_12_rows ++ b024_13_rows) ++ (b024_14_rows ++ b024_15_rows))))
    ((((b024_00_labels ++ b024_01_labels) ++ (b024_02_labels ++ b024_03_labels)) ++ ((b024_04_labels ++ b024_05_labels) ++ (b024_06_labels ++ b024_07_labels))) ++ (((b024_08_labels ++ b024_09_labels) ++ (b024_10_labels ++ b024_11_labels)) ++ ((b024_12_labels ++ b024_13_labels) ++ (b024_14_labels ++ b024_15_labels)))) 276695040792120002972926200
  exact ((((b024_00_checked.append (c := 31042864246394930008657500) b024_01_checked (by decide +kernel)).append (c := 31367239320644814826957500) (b024_02_checked.append (c := 324375074249884818300000) b024_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 64403810096411824572379500) ((b024_04_checked.append (c := 873486091678825040980500) b024_05_checked (by decide +kernel)).append (c := 33036570775767009745422000) (b024_06_checked.append (c := 32163084684088184704441500) b024_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 276695040792120002972926200) (((b024_08_checked.append (c := 180900229166892843781219200) b024_09_checked (by decide +kernel)).append (c := 181085909490623952056324700) (b024_10_checked.append (c := 185680323731108275105500) b024_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 212291230695708178400546700) ((b024_12_checked.append (c := 30869065026749081629737000) b024_13_checked (by decide +kernel)).append (c := 31205321205084226344222000) (b024_14_checked.append (c := 336256178335144714485000) b024_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
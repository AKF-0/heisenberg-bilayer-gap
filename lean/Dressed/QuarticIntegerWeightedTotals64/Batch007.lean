import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch006
import Dressed.QuarticIntegerComputationalData64.Batch007


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b057_00_rows : List Row := [(row3 9 38 49), (row3 9 38 50), (row3 9 38 51), (row3 9 38 52), (row3 9 38 53), (row3 9 38 54), (row3 9 38 55), (row3 9 38 56), (row3 9 38 57), (row3 9 38 58), (row3 9 38 59), (row3 9 38 60), (row3 9 38 61), (row3 9 38 62), (row3 9 38 63), (row3 9 39 40)]

def b057_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_00_rows b057_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_00_rows b057_00_labels]
    decide +kernel

def b057_01_rows : List Row := [(row3 9 39 41), (row3 9 39 42), (row3 9 39 43), (row3 9 39 44), (row3 9 39 45), (row3 9 39 46), (row3 9 39 47), (row3 9 39 48), (row3 9 39 49), (row3 9 39 50), (row3 9 39 51), (row3 9 39 52), (row3 9 39 53), (row3 9 39 54), (row3 9 39 55), (row3 9 39 56)]

def b057_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284)]

theorem b057_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_01_rows b057_01_labels 63084621031696900787008500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_01_rows b057_01_labels]
    decide +kernel

def b057_02_rows : List Row := [(row3 9 39 57), (row3 9 39 58), (row3 9 39 59), (row3 9 39 60), (row3 9 39 61), (row3 9 39 62), (row3 9 39 63), (row3 9 40 41), (row3 9 40 42), (row3 9 40 43), (row3 9 40 44), (row3 9 40 45), (row3 9 40 46), (row3 9 40 47), (row3 9 40 48), (row3 9 40 49)]

def b057_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 166 190 167), (row3 295 296 296)]

theorem b057_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_02_rows b057_02_labels 6194880671056851992076308160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_02_rows b057_02_labels]
    decide +kernel

def b057_03_rows : List Row := [(row3 9 40 50), (row3 9 40 51), (row3 9 40 52), (row3 9 40 53), (row3 9 40 54), (row3 9 40 55), (row3 9 40 56), (row3 9 40 57), (row3 9 40 58), (row3 9 40 59), (row3 9 40 60), (row3 9 40 61), (row3 9 40 62), (row3 9 40 63), (row3 9 41 42), (row3 9 41 43)]

def b057_03_labels : List Row := [(row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 278 279 279), (row3 372 430 58), (row3 125 126 128), (row3 278 283 283), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 278 279 279), (row3 175 161 175), (row3 462 462 462), (row3 462 462 462)]

theorem b057_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_03_rows b057_03_labels 139515620432546885917966488000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_03_rows b057_03_labels]
    decide +kernel

def b057_04_rows : List Row := [(row3 9 41 44), (row3 9 41 45), (row3 9 41 46), (row3 9 41 47), (row3 9 41 48), (row3 9 41 49), (row3 9 41 50), (row3 9 41 51), (row3 9 41 52), (row3 9 41 53), (row3 9 41 54), (row3 9 41 55), (row3 9 41 56), (row3 9 41 57), (row3 9 41 58), (row3 9 41 59)]

def b057_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 179 153 151), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 156 82 399), (row3 349 346 350), (row3 220 222 221), (row3 462 462 462)]

theorem b057_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_04_rows b057_04_labels 31789017993511337177545231680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_04_rows b057_04_labels]
    decide +kernel

def b057_05_rows : List Row := [(row3 9 41 60), (row3 9 41 61), (row3 9 41 62), (row3 9 41 63), (row3 9 42 43), (row3 9 42 44), (row3 9 42 45), (row3 9 42 46), (row3 9 42 47), (row3 9 42 48), (row3 9 42 49), (row3 9 42 50), (row3 9 42 51), (row3 9 42 52), (row3 9 42 53), (row3 9 42 54)]

def b057_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_05_rows b057_05_labels 78421703790898336744122480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_05_rows b057_05_labels]
    decide +kernel

def b057_06_rows : List Row := [(row3 9 42 55), (row3 9 42 56), (row3 9 42 57), (row3 9 42 58), (row3 9 42 59), (row3 9 42 60), (row3 9 42 61), (row3 9 42 62), (row3 9 42 63), (row3 9 43 44), (row3 9 43 45), (row3 9 43 46), (row3 9 43 47), (row3 9 43 48), (row3 9 43 49), (row3 9 43 50)]

def b057_06_labels : List Row := [(row3 462 462 462), (row3 462 293 293), (row3 137 149 146), (row3 289 291 291), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462)]

theorem b057_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_06_rows b057_06_labels 569746060922222943344564220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_06_rows b057_06_labels]
    decide +kernel

def b057_07_rows : List Row := [(row3 9 43 51), (row3 9 43 52), (row3 9 43 53), (row3 9 43 54), (row3 9 43 55), (row3 9 43 56), (row3 9 43 57), (row3 9 43 58), (row3 9 43 59), (row3 9 43 60), (row3 9 43 61), (row3 9 43 62), (row3 9 43 63), (row3 9 44 45), (row3 9 44 46), (row3 9 44 47)]

def b057_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 278 278), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_07_rows b057_07_labels 14853273413954396571133200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_07_rows b057_07_labels]
    decide +kernel

def b057_08_rows : List Row := [(row3 9 44 48), (row3 9 44 49), (row3 9 44 50), (row3 9 44 51), (row3 9 44 52), (row3 9 44 53), (row3 9 44 54), (row3 9 44 55), (row3 9 44 56), (row3 9 44 57), (row3 9 44 58), (row3 9 44 59), (row3 9 44 60), (row3 9 44 61), (row3 9 44 62), (row3 9 44 63)]

def b057_08_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_08_rows b057_08_labels 93084096969558898897500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_08_rows b057_08_labels]
    decide +kernel

def b057_09_rows : List Row := [(row3 9 45 46), (row3 9 45 47), (row3 9 45 48), (row3 9 45 49), (row3 9 45 50), (row3 9 45 51), (row3 9 45 52), (row3 9 45 53), (row3 9 45 54), (row3 9 45 55), (row3 9 45 56), (row3 9 45 57), (row3 9 45 58), (row3 9 45 59), (row3 9 45 60), (row3 9 45 61)]

def b057_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_09_rows b057_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_09_rows b057_09_labels]
    decide +kernel

def b057_10_rows : List Row := [(row3 9 45 62), (row3 9 45 63), (row3 9 46 47), (row3 9 46 48), (row3 9 46 49), (row3 9 46 50), (row3 9 46 51), (row3 9 46 52), (row3 9 46 53), (row3 9 46 54), (row3 9 46 55), (row3 9 46 56), (row3 9 46 57), (row3 9 46 58), (row3 9 46 59), (row3 9 46 60)]

def b057_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_10_rows b057_10_labels 94239340273508359987768500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_10_rows b057_10_labels]
    decide +kernel

def b057_11_rows : List Row := [(row3 9 46 61), (row3 9 46 62), (row3 9 46 63), (row3 9 47 48), (row3 9 47 49), (row3 9 47 50), (row3 9 47 51), (row3 9 47 52), (row3 9 47 53), (row3 9 47 54), (row3 9 47 55), (row3 9 47 56), (row3 9 47 57), (row3 9 47 58), (row3 9 47 59), (row3 9 47 60)]

def b057_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 288 462 288), (row3 226 234 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 157 83 399), (row3 288 278 300), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462)]

theorem b057_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_11_rows b057_11_labels 20407046972659908804024186240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_11_rows b057_11_labels]
    decide +kernel

def b057_12_rows : List Row := [(row3 9 47 61), (row3 9 47 62), (row3 9 47 63), (row3 9 48 49), (row3 9 48 50), (row3 9 48 51), (row3 9 48 52), (row3 9 48 53), (row3 9 48 54), (row3 9 48 55), (row3 9 48 56), (row3 9 48 57), (row3 9 48 58), (row3 9 48 59), (row3 9 48 60), (row3 9 48 61)]

def b057_12_labels : List Row := [(row3 462 462 462), (row3 232 462 232), (row3 300 462 300), (row3 331 123 92), (row3 288 288 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 288 288 462), (row3 132 133 137), (row3 47 26 453), (row3 404 402 403), (row3 141 142 136), (row3 273 273 462), (row3 462 462 462), (row3 273 273 462)]

theorem b057_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_12_rows b057_12_labels 12525220625291392027202263837440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_12_rows b057_12_labels]
    decide +kernel

def b057_13_rows : List Row := [(row3 9 48 62), (row3 9 48 63), (row3 9 49 50), (row3 9 49 51), (row3 9 49 52), (row3 9 49 53), (row3 9 49 54), (row3 9 49 55), (row3 9 49 56), (row3 9 49 57), (row3 9 49 58), (row3 9 49 59), (row3 9 49 60), (row3 9 49 61), (row3 9 49 62), (row3 9 49 63)]

def b057_13_labels : List Row := [(row3 144 147 137), (row3 382 378 381), (row3 177 150 152), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 226 226 237), (row3 315 318 318), (row3 413 438 40), (row3 57 53 51), (row3 323 324 324), (row3 224 226 229), (row3 462 243 243), (row3 232 232 462), (row3 306 310 310), (row3 120 112 120)]

theorem b057_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_13_rows b057_13_labels 1791272942780950745200291029840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_13_rows b057_13_labels]
    decide +kernel

def b057_14_rows : List Row := [(row3 9 50 51), (row3 9 50 52), (row3 9 50 53), (row3 9 50 54), (row3 9 50 55), (row3 9 50 56), (row3 9 50 57), (row3 9 50 58), (row3 9 50 59), (row3 9 50 60), (row3 9 50 61), (row3 9 50 62), (row3 9 50 63), (row3 9 51 52), (row3 9 51 53), (row3 9 51 54)]

def b057_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 134 81 398), (row3 382 378 381), (row3 129 103 102), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 295 462 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b057_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_14_rows b057_14_labels 55331648749471927530484156320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_14_rows b057_14_labels]
    decide +kernel

def b057_15_rows : List Row := [(row3 9 51 55), (row3 9 51 56), (row3 9 51 57), (row3 9 51 58), (row3 9 51 59), (row3 9 51 60), (row3 9 51 61), (row3 9 51 62), (row3 9 51 63), (row3 9 52 53), (row3 9 52 54), (row3 9 52 55), (row3 9 52 56), (row3 9 52 57), (row3 9 52 58), (row3 9 52 59)]

def b057_15_labels : List Row := [(row3 462 462 462), (row3 462 284 284), (row3 137 149 146), (row3 306 309 309), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 273 273), (row3 224 224 224), (row3 462 462 462)]

theorem b057_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b057_15_rows b057_15_labels 681393363602587835752513800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b057_15_rows b057_15_labels]
    decide +kernel

theorem checked057 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_057 QuarticIntegerComputationalData.ids64_057 14571233614338721522156737245880 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b057_00_rows ++ b057_01_rows) ++ (b057_02_rows ++ b057_03_rows)) ++ ((b057_04_rows ++ b057_05_rows) ++ (b057_06_rows ++ b057_07_rows))) ++ (((b057_08_rows ++ b057_09_rows) ++ (b057_10_rows ++ b057_11_rows)) ++ ((b057_12_rows ++ b057_13_rows) ++ (b057_14_rows ++ b057_15_rows))))
    ((((b057_00_labels ++ b057_01_labels) ++ (b057_02_labels ++ b057_03_labels)) ++ ((b057_04_labels ++ b057_05_labels) ++ (b057_06_labels ++ b057_07_labels))) ++ (((b057_08_labels ++ b057_09_labels) ++ (b057_10_labels ++ b057_11_labels)) ++ ((b057_12_labels ++ b057_13_labels) ++ (b057_14_labels ++ b057_15_labels)))) 14571233614338721522156737245880
  exact ((((b057_00_checked.append (c := 63084621031696900787008500) b057_01_checked (by decide +kernel)).append (c := 145773585724635434810829804660) (b057_02_checked.append (c := 145710501103603737910042796160) b057_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 178225624756273847665034856240) ((b057_04_checked.append (c := 31867439697302235514289354160) b057_05_checked (by decide +kernel)).append (c := 32452039031638412854205051580) (b057_06_checked.append (c := 584599334336177339915697420) b057_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 14571233614338721522156737245880) (((b057_08_checked.append (c := 93084096969558898897500) b057_09_checked (by decide +kernel)).append (c := 20501379397030386722910852240) (b057_10_checked.append (c := 20501286312933417164011954740) b057_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 14393007989582447674491702389640) ((b057_12_checked.append (c := 14316493568072342772402554867280) b057_13_checked (by decide +kernel)).append (c := 14372506610185417287768791537400) (b057_14_checked.append (c := 56013042113074515366236670120) b057_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b058_00_rows : List Row := [(row3 9 52 60), (row3 9 52 61), (row3 9 52 62), (row3 9 52 63), (row3 9 53 54), (row3 9 53 55), (row3 9 53 56), (row3 9 53 57), (row3 9 53 58), (row3 9 53 59), (row3 9 53 60), (row3 9 53 61), (row3 9 53 62), (row3 9 53 63), (row3 9 54 55), (row3 9 54 56)]

def b058_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 462 462), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 228 462 228), (row3 135 83 398)]

theorem b058_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_00_rows b058_00_labels 20265800930477126292767688000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_00_rows b058_00_labels]
    decide +kernel

def b058_01_rows : List Row := [(row3 9 54 57), (row3 9 54 58), (row3 9 54 59), (row3 9 54 60), (row3 9 54 61), (row3 9 54 62), (row3 9 54 63), (row3 9 55 56), (row3 9 55 57), (row3 9 55 58), (row3 9 55 59), (row3 9 55 60), (row3 9 55 61), (row3 9 55 62), (row3 9 55 63), (row3 9 56 57)]

def b058_01_labels : List Row := [(row3 295 273 304), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 319 462 319), (row3 412 437 39), (row3 99 98 101), (row3 306 312 312), (row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 306 309 309), (row3 100 113 100), (row3 442 451 24)]

theorem b058_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_01_rows b058_01_labels 28061162131823102795797603720260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_01_rows b058_01_labels]
    decide +kernel

def b058_02_rows : List Row := [(row3 9 56 58), (row3 9 56 59), (row3 9 56 60), (row3 9 56 61), (row3 9 56 62), (row3 9 56 63), (row3 9 57 58), (row3 9 57 59), (row3 9 57 60), (row3 9 57 61), (row3 9 57 62), (row3 9 57 63), (row3 9 58 59), (row3 9 58 60), (row3 9 58 61), (row3 9 58 62)]

def b058_02_labels : List Row := [(row3 411 60 432), (row3 158 356 89), (row3 462 269 269), (row3 159 356 91), (row3 410 59 431), (row3 32 452 25), (row3 61 50 48), (row3 351 350 348), (row3 190 198 199), (row3 288 290 261), (row3 110 111 109), (row3 406 405 406), (row3 129 103 102), (row3 289 291 291), (row3 226 226 234), (row3 306 311 311)]

theorem b058_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_02_rows b058_02_labels 15585825149461221410282347773720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_02_rows b058_02_labels]
    decide +kernel

def b058_03_rows : List Row := [(row3 9 58 63), (row3 9 59 60), (row3 9 59 61), (row3 9 59 62), (row3 9 59 63), (row3 9 60 61), (row3 9 60 62), (row3 9 60 63), (row3 9 61 62), (row3 9 61 63), (row3 9 62 63), (row3 10 11 12), (row3 10 11 13), (row3 10 11 14), (row3 10 11 15), (row3 10 11 16)]

def b058_03_labels : List Row := [(row3 120 112 120), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 232 462 232), (row3 300 462 300), (row3 100 113 100), (row3 95 435 41), (row3 325 87 371), (row3 217 10 169), (row3 151 153 179), (row3 104 104 130)]

theorem b058_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_03_rows b058_03_labels 410249445454479616996677114420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_03_rows b058_03_labels]
    decide +kernel

def b058_04_rows : List Row := [(row3 10 11 17), (row3 10 11 18), (row3 10 11 19), (row3 10 11 20), (row3 10 11 21), (row3 10 11 22), (row3 10 11 23), (row3 10 11 24), (row3 10 11 25), (row3 10 11 26), (row3 10 11 27), (row3 10 11 28), (row3 10 11 29), (row3 10 11 30), (row3 10 11 31), (row3 10 11 32)]

def b058_04_labels : List Row := [(row3 416 408 396), (row3 31 35 36), (row3 383 436 43), (row3 157 83 399), (row3 212 11 115), (row3 462 462 462), (row3 286 462 286), (row3 294 462 294), (row3 105 105 131), (row3 390 387 360), (row3 122 86 369), (row3 214 11 117), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b058_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_04_rows b058_04_labels 1270474811006443202503446893100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_04_rows b058_04_labels]
    decide +kernel

def b058_05_rows : List Row := [(row3 10 11 33), (row3 10 11 34), (row3 10 11 35), (row3 10 11 36), (row3 10 11 37), (row3 10 11 38), (row3 10 11 39), (row3 10 11 40), (row3 10 11 41), (row3 10 11 42), (row3 10 11 43), (row3 10 11 44), (row3 10 11 45), (row3 10 11 46), (row3 10 11 47), (row3 10 11 48)]

def b058_05_labels : List Row := [(row3 284 462 284), (row3 154 154 180), (row3 254 10 171), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b058_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_05_rows b058_05_labels 1417639041187088404638852000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_05_rows b058_05_labels]
    decide +kernel

def b058_06_rows : List Row := [(row3 10 11 49), (row3 10 11 50), (row3 10 11 51), (row3 10 11 52), (row3 10 11 53), (row3 10 11 54), (row3 10 11 55), (row3 10 11 56), (row3 10 11 57), (row3 10 11 58), (row3 10 11 59), (row3 10 11 60), (row3 10 11 61), (row3 10 11 62), (row3 10 11 63), (row3 10 12 13)]

def b058_06_labels : List Row := [(row3 286 462 286), (row3 154 154 180), (row3 254 10 171), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 307 462 307), (row3 103 102 129), (row3 392 388 362), (row3 121 85 369), (row3 214 11 117), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 277 277 265)]

theorem b058_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_06_rows b058_06_labels 66910340655958140545304655500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_06_rows b058_06_labels]
    decide +kernel

def b058_07_rows : List Row := [(row3 10 12 14), (row3 10 12 15), (row3 10 12 16), (row3 10 12 17), (row3 10 12 18), (row3 10 12 19), (row3 10 12 20), (row3 10 12 21), (row3 10 12 22), (row3 10 12 23), (row3 10 12 24), (row3 10 12 25), (row3 10 12 26), (row3 10 12 27), (row3 10 12 28), (row3 10 12 29)]

def b058_07_labels : List Row := [(row3 235 462 235), (row3 276 276 275), (row3 291 291 289), (row3 137 143 146), (row3 391 361 387), (row3 137 146 149), (row3 291 291 289), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 234 462 234), (row3 291 291 289), (row3 178 184 184), (row3 291 291 289), (row3 234 462 234), (row3 462 462 462)]

theorem b058_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_07_rows b058_07_labels 15545286501556178222433723450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_07_rows b058_07_labels]
    decide +kernel

def b058_08_rows : List Row := [(row3 10 12 30), (row3 10 12 31), (row3 10 12 32), (row3 10 12 33), (row3 10 12 34), (row3 10 12 35), (row3 10 12 36), (row3 10 12 37), (row3 10 12 38), (row3 10 12 39), (row3 10 12 40), (row3 10 12 41), (row3 10 12 42), (row3 10 12 43), (row3 10 12 44), (row3 10 12 45)]

def b058_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b058_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_08_rows b058_08_labels 3878375052883639404074400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_08_rows b058_08_labels]
    decide +kernel

def b058_09_rows : List Row := [(row3 10 12 46), (row3 10 12 47), (row3 10 12 48), (row3 10 12 49), (row3 10 12 50), (row3 10 12 51), (row3 10 12 52), (row3 10 12 53), (row3 10 12 54), (row3 10 12 55), (row3 10 12 56), (row3 10 12 57), (row3 10 12 58), (row3 10 12 59), (row3 10 12 60), (row3 10 12 61)]

def b058_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 291 291 289), (row3 178 182 182), (row3 292 292 289), (row3 234 462 234), (row3 462 462 462)]

theorem b058_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_09_rows b058_09_labels 200945000796087450021608520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_09_rows b058_09_labels]
    decide +kernel

def b058_10_rows : List Row := [(row3 10 12 62), (row3 10 12 63), (row3 10 13 14), (row3 10 13 15), (row3 10 13 16), (row3 10 13 17), (row3 10 13 18), (row3 10 13 19), (row3 10 13 20), (row3 10 13 21), (row3 10 13 22), (row3 10 13 23), (row3 10 13 24), (row3 10 13 25), (row3 10 13 26), (row3 10 13 27)]

def b058_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 169 10 217), (row3 195 188 194), (row3 229 229 226), (row3 282 278 282), (row3 154 180 154), (row3 280 278 280), (row3 231 234 231), (row3 264 462 264), (row3 236 462 236), (row3 252 462 252), (row3 245 462 245), (row3 234 234 234), (row3 266 265 266), (row3 234 234 234)]

theorem b058_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_10_rows b058_10_labels 1855411554677439934995763770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_10_rows b058_10_labels]
    decide +kernel

def b058_11_rows : List Row := [(row3 10 13 28), (row3 10 13 29), (row3 10 13 30), (row3 10 13 31), (row3 10 13 32), (row3 10 13 33), (row3 10 13 34), (row3 10 13 35), (row3 10 13 36), (row3 10 13 37), (row3 10 13 38), (row3 10 13 39), (row3 10 13 40), (row3 10 13 41), (row3 10 13 42), (row3 10 13 43)]

def b058_11_labels : List Row := [(row3 245 462 245), (row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462)]

theorem b058_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_11_rows b058_11_labels 285141224770356913170000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_11_rows b058_11_labels]
    decide +kernel

def b058_12_rows : List Row := [(row3 10 13 44), (row3 10 13 45), (row3 10 13 46), (row3 10 13 47), (row3 10 13 48), (row3 10 13 49), (row3 10 13 50), (row3 10 13 51), (row3 10 13 52), (row3 10 13 53), (row3 10 13 54), (row3 10 13 55), (row3 10 13 56), (row3 10 13 57), (row3 10 13 58), (row3 10 13 59)]

def b058_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 247 462 247), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 241 462 241), (row3 462 462 462), (row3 246 462 246), (row3 285 462 285), (row3 226 234 226), (row3 268 265 268), (row3 234 234 234)]

theorem b058_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_12_rows b058_12_labels 79030083788286392526108900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_12_rows b058_12_labels]
    decide +kernel

def b058_13_rows : List Row := [(row3 10 13 60), (row3 10 13 61), (row3 10 13 62), (row3 10 13 63), (row3 10 14 15), (row3 10 14 16), (row3 10 14 17), (row3 10 14 18), (row3 10 14 19), (row3 10 14 20), (row3 10 14 21), (row3 10 14 22), (row3 10 14 23), (row3 10 14 24), (row3 10 14 25), (row3 10 14 26)]

def b058_13_labels : List Row := [(row3 245 462 245), (row3 238 462 238), (row3 247 462 247), (row3 232 462 232), (row3 353 375 366), (row3 314 314 306), (row3 222 220 221), (row3 272 272 462), (row3 235 235 462), (row3 246 246 462), (row3 235 235 462), (row3 272 272 462), (row3 220 222 221), (row3 234 234 234), (row3 248 248 462), (row3 237 237 462)]

theorem b058_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_13_rows b058_13_labels 16691834615378562356546611650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_13_rows b058_13_labels]
    decide +kernel

def b058_14_rows : List Row := [(row3 10 14 27), (row3 10 14 28), (row3 10 14 29), (row3 10 14 30), (row3 10 14 31), (row3 10 14 32), (row3 10 14 33), (row3 10 14 34), (row3 10 14 35), (row3 10 14 36), (row3 10 14 37), (row3 10 14 38), (row3 10 14 39), (row3 10 14 40), (row3 10 14 41), (row3 10 14 42)]

def b058_14_labels : List Row := [(row3 244 244 462), (row3 462 462 462), (row3 244 244 462), (row3 237 237 462), (row3 248 248 462), (row3 244 244 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 462 462 462), (row3 234 234 234), (row3 246 246 462), (row3 462 462 462)]

theorem b058_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_14_rows b058_14_labels 647707200737274959625000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_14_rows b058_14_labels]
    decide +kernel

def b058_15_rows : List Row := [(row3 10 14 43), (row3 10 14 44), (row3 10 14 45), (row3 10 14 46), (row3 10 14 47), (row3 10 14 48), (row3 10 14 49), (row3 10 14 50), (row3 10 14 51), (row3 10 14 52), (row3 10 14 53), (row3 10 14 54), (row3 10 14 55), (row3 10 14 56), (row3 10 14 57), (row3 10 14 58)]

def b058_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 291 291 289), (row3 224 224 224), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 249 249 462), (row3 224 224 224), (row3 105 105 131), (row3 311 311 306), (row3 223 223 224)]

theorem b058_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b058_15_rows b058_15_labels 2454948598812345207718942500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b058_15_rows b058_15_labels]
    decide +kernel

theorem checked058 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_058 QuarticIntegerComputationalData.ids64_058 45453137585951356671658306325190 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b058_00_rows ++ b058_01_rows) ++ (b058_02_rows ++ b058_03_rows)) ++ ((b058_04_rows ++ b058_05_rows) ++ (b058_06_rows ++ b058_07_rows))) ++ (((b058_08_rows ++ b058_09_rows) ++ (b058_10_rows ++ b058_11_rows)) ++ ((b058_12_rows ++ b058_13_rows) ++ (b058_14_rows ++ b058_15_rows))))
    ((((b058_00_labels ++ b058_01_labels) ++ (b058_02_labels ++ b058_03_labels)) ++ ((b058_04_labels ++ b058_05_labels) ++ (b058_06_labels ++ b058_07_labels))) ++ (((b058_08_labels ++ b058_09_labels) ++ (b058_10_labels ++ b058_11_labels)) ++ ((b058_12_labels ++ b058_13_labels) ++ (b058_14_labels ++ b058_15_labels)))) 45453137585951356671658306325190
  exact ((((b058_00_checked.append (c := 28081427932753579922090371408260) b058_01_checked (by decide +kernel)).append (c := 44077502527669280949369396296400) (b058_02_checked.append (c := 15996074594915701027279024888140) b058_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 45431850604874425559045220420450) ((b058_04_checked.append (c := 1271892450047630290908085745100) b058_05_checked (by decide +kernel)).append (c := 1354348077205144609675824124050) (b058_06_checked.append (c := 82455627157514318767738378950) b058_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 45453137585951356671658306325190) (((b058_08_checked.append (c := 204823375848971089425682920) b058_09_checked (by decide +kernel)).append (c := 2060520071751181381334616690) (b058_10_checked.append (c := 1855696695902210291908933770) b058_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 21286981076931112613085904740) ((b058_12_checked.append (c := 16770864699166848749072720550) b058_13_checked (by decide +kernel)).append (c := 19226461005179931231751288050) (b058_14_checked.append (c := 2455596306013082482678567500) b058_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b059_00_rows : List Row := [(row3 10 14 59), (row3 10 14 60), (row3 10 14 61), (row3 10 14 62), (row3 10 14 63), (row3 10 15 16), (row3 10 15 17), (row3 10 15 18), (row3 10 15 19), (row3 10 15 20), (row3 10 15 21), (row3 10 15 22), (row3 10 15 23), (row3 10 15 24), (row3 10 15 25), (row3 10 15 26)]

def b059_00_labels : List Row := [(row3 248 248 462), (row3 462 462 462), (row3 248 248 462), (row3 223 223 224), (row3 311 311 306), (row3 106 106 107), (row3 324 323 324), (row3 150 177 152), (row3 279 278 279), (row3 234 231 231), (row3 280 278 280), (row3 175 175 161), (row3 354 366 376), (row3 298 295 298), (row3 226 224 229), (row3 266 265 266)]

theorem b059_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_00_rows b059_00_labels 25475023262113500011248457670 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_00_rows b059_00_labels]
    decide +kernel

def b059_01_rows : List Row := [(row3 10 15 27), (row3 10 15 28), (row3 10 15 29), (row3 10 15 30), (row3 10 15 31), (row3 10 15 32), (row3 10 15 33), (row3 10 15 34), (row3 10 15 35), (row3 10 15 36), (row3 10 15 37), (row3 10 15 38), (row3 10 15 39), (row3 10 15 40), (row3 10 15 41), (row3 10 15 42)]

def b059_01_labels : List Row := [(row3 234 234 234), (row3 244 462 244), (row3 462 235 235), (row3 279 278 279), (row3 197 196 190), (row3 235 233 236), (row3 243 462 243), (row3 237 237 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 262 261 262), (row3 279 278 279), (row3 232 232 462), (row3 242 462 242)]

theorem b059_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_01_rows b059_01_labels 117294578304013771800098880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_01_rows b059_01_labels]
    decide +kernel

def b059_02_rows : List Row := [(row3 10 15 43), (row3 10 15 44), (row3 10 15 45), (row3 10 15 46), (row3 10 15 47), (row3 10 15 48), (row3 10 15 49), (row3 10 15 50), (row3 10 15 51), (row3 10 15 52), (row3 10 15 53), (row3 10 15 54), (row3 10 15 55), (row3 10 15 56), (row3 10 15 57), (row3 10 15 58)]

def b059_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 230 238), (row3 137 145 148), (row3 310 306 310), (row3 226 226 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 228 225 236), (row3 317 308 317), (row3 415 407 395), (row3 112 120 120), (row3 318 315 318)]

theorem b059_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_02_rows b059_02_labels 38465424510697206170955169230 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_02_rows b059_02_labels]
    decide +kernel

def b059_03_rows : List Row := [(row3 10 15 59), (row3 10 15 60), (row3 10 15 61), (row3 10 15 62), (row3 10 15 63), (row3 10 16 17), (row3 10 16 18), (row3 10 16 19), (row3 10 16 20), (row3 10 16 21), (row3 10 16 22), (row3 10 16 23), (row3 10 16 24), (row3 10 16 25), (row3 10 16 26), (row3 10 16 27)]

def b059_03_labels : List Row := [(row3 226 226 234), (row3 244 462 244), (row3 232 228 235), (row3 320 319 320), (row3 109 111 110), (row3 60 411 432), (row3 108 367 84), (row3 318 315 318), (row3 224 223 223), (row3 268 265 268), (row3 182 182 178), (row3 362 388 392), (row3 363 386 393), (row3 141 142 136), (row3 313 306 313), (row3 224 222 222)]

theorem b059_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_03_rows b059_03_labels 311029560612392503549790142000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_03_rows b059_03_labels]
    decide +kernel

def b059_04_rows : List Row := [(row3 10 16 28), (row3 10 16 29), (row3 10 16 30), (row3 10 16 31), (row3 10 16 32), (row3 10 16 33), (row3 10 16 34), (row3 10 16 35), (row3 10 16 36), (row3 10 16 37), (row3 10 16 38), (row3 10 16 39), (row3 10 16 40), (row3 10 16 41), (row3 10 16 42), (row3 10 16 43)]

def b059_04_labels : List Row := [(row3 248 462 248), (row3 462 235 235), (row3 291 289 291), (row3 144 147 137), (row3 183 183 178), (row3 292 289 292), (row3 234 228 228), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 291 289 291), (row3 281 278 281), (row3 235 232 235), (row3 244 462 244), (row3 462 462 462)]

theorem b059_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_04_rows b059_04_labels 465856974055757901656209680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_04_rows b059_04_labels]
    decide +kernel

def b059_05_rows : List Row := [(row3 10 16 44), (row3 10 16 45), (row3 10 16 46), (row3 10 16 47), (row3 10 16 48), (row3 10 16 49), (row3 10 16 50), (row3 10 16 51), (row3 10 16 52), (row3 10 16 53), (row3 10 16 54), (row3 10 16 55), (row3 10 16 56), (row3 10 16 57), (row3 10 16 58), (row3 10 16 59)]

def b059_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 232 235), (row3 178 183 183), (row3 292 289 292), (row3 228 228 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 291 289 291), (row3 393 386 363), (row3 136 142 141), (row3 313 306 313), (row3 222 222 224)]

theorem b059_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_05_rows b059_05_labels 24447531629451878430399134370 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_05_rows b059_05_labels]
    decide +kernel

def b059_06_rows : List Row := [(row3 10 16 60), (row3 10 16 61), (row3 10 16 62), (row3 10 16 63), (row3 10 17 18), (row3 10 17 19), (row3 10 17 20), (row3 10 17 21), (row3 10 17 22), (row3 10 17 23), (row3 10 17 24), (row3 10 17 25), (row3 10 17 26), (row3 10 17 27), (row3 10 17 28), (row3 10 17 29)]

def b059_06_labels : List Row := [(row3 248 462 248), (row3 235 235 462), (row3 291 289 291), (row3 137 147 144), (row3 46 46 440), (row3 98 99 101), (row3 320 320 319), (row3 232 235 228), (row3 283 283 278), (row3 142 136 141), (row3 120 112 120), (row3 396 416 408), (row3 99 98 101), (row3 322 322 321), (row3 228 232 223), (row3 462 462 462)]

theorem b059_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_06_rows b059_06_labels 978210353495995058506517070930 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_06_rows b059_06_labels]
    decide +kernel

def b059_07_rows : List Row := [(row3 10 17 30), (row3 10 17 31), (row3 10 17 32), (row3 10 17 33), (row3 10 17 34), (row3 10 17 35), (row3 10 17 36), (row3 10 17 37), (row3 10 17 38), (row3 10 17 39), (row3 10 17 40), (row3 10 17 41), (row3 10 17 42), (row3 10 17 43), (row3 10 17 44), (row3 10 17 45)]

def b059_07_labels : List Row := [(row3 462 232 232), (row3 312 312 306), (row3 311 311 306), (row3 146 137 143), (row3 320 320 319), (row3 232 228 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 234 226 226), (row3 282 282 278), (row3 235 232 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b059_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_07_rows b059_07_labels 402157115231684900269424940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_07_rows b059_07_labels]
    decide +kernel

def b059_08_rows : List Row := [(row3 10 17 46), (row3 10 17 47), (row3 10 17 48), (row3 10 17 49), (row3 10 17 50), (row3 10 17 51), (row3 10 17 52), (row3 10 17 53), (row3 10 17 54), (row3 10 17 55), (row3 10 17 56), (row3 10 17 57), (row3 10 17 58), (row3 10 17 59), (row3 10 17 60), (row3 10 17 61)]

def b059_08_labels : List Row := [(row3 462 462 462), (row3 246 246 462), (row3 291 291 289), (row3 221 222 220), (row3 283 283 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 224 224 224), (row3 102 103 129), (row3 324 324 323), (row3 136 142 141), (row3 312 312 306), (row3 228 462 228), (row3 246 246 462)]

theorem b059_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_08_rows b059_08_labels 20595767054867552754385077600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_08_rows b059_08_labels]
    decide +kernel

def b059_09_rows : List Row := [(row3 10 17 62), (row3 10 17 63), (row3 10 18 19), (row3 10 18 20), (row3 10 18 21), (row3 10 18 22), (row3 10 18 23), (row3 10 18 24), (row3 10 18 25), (row3 10 18 26), (row3 10 18 27), (row3 10 18 28), (row3 10 18 29), (row3 10 18 30), (row3 10 18 31), (row3 10 18 32)]

def b059_09_labels : List Row := [(row3 224 224 224), (row3 309 309 306), (row3 389 436 45), (row3 114 86 368), (row3 258 10 172), (row3 462 462 462), (row3 260 10 173), (row3 216 11 119), (row3 134 81 398), (row3 181 435 42), (row3 135 83 398), (row3 215 11 118), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b059_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_09_rows b059_09_labels 773427012224345455804263901890 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_09_rows b059_09_labels]
    decide +kernel

def b059_10_rows : List Row := [(row3 10 18 33), (row3 10 18 34), (row3 10 18 35), (row3 10 18 36), (row3 10 18 37), (row3 10 18 38), (row3 10 18 39), (row3 10 18 40), (row3 10 18 41), (row3 10 18 42), (row3 10 18 43), (row3 10 18 44), (row3 10 18 45), (row3 10 18 46), (row3 10 18 47), (row3 10 18 48)]

def b059_10_labels : List Row := [(row3 214 11 117), (row3 211 88 370), (row3 214 11 117), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 218 10 170), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234)]

theorem b059_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_10_rows b059_10_labels 13376849368478238637939176750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_10_rows b059_10_labels]
    decide +kernel

def b059_11_rows : List Row := [(row3 10 18 49), (row3 10 18 50), (row3 10 18 51), (row3 10 18 52), (row3 10 18 53), (row3 10 18 54), (row3 10 18 55), (row3 10 18 56), (row3 10 18 57), (row3 10 18 58), (row3 10 18 59), (row3 10 18 60), (row3 10 18 61), (row3 10 18 62), (row3 10 18 63), (row3 10 19 20)]

def b059_11_labels : List Row := [(row3 287 462 287), (row3 154 154 180), (row3 284 462 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 316 462 316), (row3 102 103 129), (row3 393 386 363), (row3 105 105 131), (row3 293 462 293), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 309 309 306)]

theorem b059_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_11_rows b059_11_labels 60546507976369900225290776850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_11_rows b059_11_labels]
    decide +kernel

def b059_12_rows : List Row := [(row3 10 19 21), (row3 10 19 22), (row3 10 19 23), (row3 10 19 24), (row3 10 19 25), (row3 10 19 26), (row3 10 19 27), (row3 10 19 28), (row3 10 19 29), (row3 10 19 30), (row3 10 19 31), (row3 10 19 32), (row3 10 19 33), (row3 10 19 34), (row3 10 19 35), (row3 10 19 36)]

def b059_12_labels : List Row := [(row3 232 462 232), (row3 462 462 462), (row3 232 462 232), (row3 228 462 228), (row3 312 312 306), (row3 137 149 146), (row3 309 309 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 232 462 232), (row3 462 462 462)]

theorem b059_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_12_rows b059_12_labels 825399256830405016596631560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_12_rows b059_12_labels]
    decide +kernel

def b059_13_rows : List Row := [(row3 10 19 37), (row3 10 19 38), (row3 10 19 39), (row3 10 19 40), (row3 10 19 41), (row3 10 19 42), (row3 10 19 43), (row3 10 19 44), (row3 10 19 45), (row3 10 19 46), (row3 10 19 47), (row3 10 19 48), (row3 10 19 49), (row3 10 19 50), (row3 10 19 51), (row3 10 19 52)]

def b059_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 232 462 232), (row3 462 462 462)]

theorem b059_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_13_rows b059_13_labels 11971416235469013542775600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_13_rows b059_13_labels]
    decide +kernel

def b059_14_rows : List Row := [(row3 10 19 53), (row3 10 19 54), (row3 10 19 55), (row3 10 19 56), (row3 10 19 57), (row3 10 19 58), (row3 10 19 59), (row3 10 19 60), (row3 10 19 61), (row3 10 19 62), (row3 10 19 63), (row3 10 20 21), (row3 10 20 22), (row3 10 20 23), (row3 10 20 24), (row3 10 20 25)]

def b059_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 309 309 306), (row3 137 147 144), (row3 310 310 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 247 462 247), (row3 248 462 248), (row3 224 224 224)]

theorem b059_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_14_rows b059_14_labels 606445842883229208504276660 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_14_rows b059_14_labels]
    decide +kernel

def b059_15_rows : List Row := [(row3 10 20 26), (row3 10 20 27), (row3 10 20 28), (row3 10 20 29), (row3 10 20 30), (row3 10 20 31), (row3 10 20 32), (row3 10 20 33), (row3 10 20 34), (row3 10 20 35), (row3 10 20 36), (row3 10 20 37), (row3 10 20 38), (row3 10 20 39), (row3 10 20 40), (row3 10 20 41)]

def b059_15_labels : List Row := [(row3 291 289 291), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b059_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b059_15_rows b059_15_labels 17115419396932458853511700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b059_15_rows b059_15_labels]
    decide +kernel

theorem checked059 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_059 QuarticIntegerComputationalData.ids64_059 2248020270737648786362011836310 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b059_00_rows ++ b059_01_rows) ++ (b059_02_rows ++ b059_03_rows)) ++ ((b059_04_rows ++ b059_05_rows) ++ (b059_06_rows ++ b059_07_rows))) ++ (((b059_08_rows ++ b059_09_rows) ++ (b059_10_rows ++ b059_11_rows)) ++ ((b059_12_rows ++ b059_13_rows) ++ (b059_14_rows ++ b059_15_rows))))
    ((((b059_00_labels ++ b059_01_labels) ++ (b059_02_labels ++ b059_03_labels)) ++ ((b059_04_labels ++ b059_05_labels) ++ (b059_06_labels ++ b059_07_labels))) ++ (((b059_08_labels ++ b059_09_labels) ++ (b059_10_labels ++ b059_11_labels)) ++ ((b059_12_labels ++ b059_13_labels) ++ (b059_14_labels ++ b059_15_labels)))) 2248020270737648786362011836310
  exact ((((b059_00_checked.append (c := 25592317840417513783048556550) b059_01_checked (by decide +kernel)).append (c := 375087302963507223503793867780) (b059_02_checked.append (c := 349494985123089709720745311230) b059_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1378613202178241603242635707700) ((b059_04_checked.append (c := 24913388603507636332055344050) b059_05_checked (by decide +kernel)).append (c := 1003525899214734379738841839920) (b059_06_checked.append (c := 978612510611226743406786495870) b059_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2248020270737648786362011836310) (((b059_08_checked.append (c := 794022779279213008558648979490) b059_09_checked (by decide +kernel)).append (c := 867946136624061147421878933090) (b059_10_checked.append (c := 73923357344848138863229953600) b059_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 869407068559407183119376128610) ((b059_12_checked.append (c := 837370673065874030139407160) b059_13_checked (by decide +kernel)).append (c := 1460931935346035697497195520) (b059_14_checked.append (c := 623561262280161667357788360) b059_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b060_00_rows : List Row := [(row3 10 20 42), (row3 10 20 43), (row3 10 20 44), (row3 10 20 45), (row3 10 20 46), (row3 10 20 47), (row3 10 20 48), (row3 10 20 49), (row3 10 20 50), (row3 10 20 51), (row3 10 20 52), (row3 10 20 53), (row3 10 20 54), (row3 10 20 55), (row3 10 20 56), (row3 10 20 57)]

def b060_00_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224)]

theorem b060_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_00_rows b060_00_labels 5434138706319983574000000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_00_rows b060_00_labels]
    decide +kernel

def b060_01_rows : List Row := [(row3 10 20 58), (row3 10 20 59), (row3 10 20 60), (row3 10 20 61), (row3 10 20 62), (row3 10 20 63), (row3 10 21 22), (row3 10 21 23), (row3 10 21 24), (row3 10 21 25), (row3 10 21 26), (row3 10 21 27), (row3 10 21 28), (row3 10 21 29), (row3 10 21 30), (row3 10 21 31)]

def b060_01_labels : List Row := [(row3 291 289 291), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_01_rows b060_01_labels 13508742440688115606427700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_01_rows b060_01_labels]
    decide +kernel

def b060_02_rows : List Row := [(row3 10 21 32), (row3 10 21 33), (row3 10 21 34), (row3 10 21 35), (row3 10 21 36), (row3 10 21 37), (row3 10 21 38), (row3 10 21 39), (row3 10 21 40), (row3 10 21 41), (row3 10 21 42), (row3 10 21 43), (row3 10 21 44), (row3 10 21 45), (row3 10 21 46), (row3 10 21 47)]

def b060_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_02_rows b060_02_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_02_rows b060_02_labels]
    decide +kernel

def b060_03_rows : List Row := [(row3 10 21 48), (row3 10 21 49), (row3 10 21 50), (row3 10 21 51), (row3 10 21 52), (row3 10 21 53), (row3 10 21 54), (row3 10 21 55), (row3 10 21 56), (row3 10 21 57), (row3 10 21 58), (row3 10 21 59), (row3 10 21 60), (row3 10 21 61), (row3 10 21 62), (row3 10 21 63)]

def b060_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_03_rows b060_03_labels 359713145191801189131000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_03_rows b060_03_labels]
    decide +kernel

def b060_04_rows : List Row := [(row3 10 22 23), (row3 10 22 24), (row3 10 22 25), (row3 10 22 26), (row3 10 22 27), (row3 10 22 28), (row3 10 22 29), (row3 10 22 30), (row3 10 22 31), (row3 10 22 32), (row3 10 22 33), (row3 10 22 34), (row3 10 22 35), (row3 10 22 36), (row3 10 22 37), (row3 10 22 38)]

def b060_04_labels : List Row := [(row3 287 462 287), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_04_rows b060_04_labels 99394527846749352152962500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_04_rows b060_04_labels]
    decide +kernel

def b060_05_rows : List Row := [(row3 10 22 39), (row3 10 22 40), (row3 10 22 41), (row3 10 22 42), (row3 10 22 43), (row3 10 22 44), (row3 10 22 45), (row3 10 22 46), (row3 10 22 47), (row3 10 22 48), (row3 10 22 49), (row3 10 22 50), (row3 10 22 51), (row3 10 22 52), (row3 10 22 53), (row3 10 22 54)]

def b060_05_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_05_rows b060_05_labels 443593211854154476374000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_05_rows b060_05_labels]
    decide +kernel

def b060_06_rows : List Row := [(row3 10 22 55), (row3 10 22 56), (row3 10 22 57), (row3 10 22 58), (row3 10 22 59), (row3 10 22 60), (row3 10 22 61), (row3 10 22 62), (row3 10 22 63), (row3 10 23 24), (row3 10 23 25), (row3 10 23 26), (row3 10 23 27), (row3 10 23 28), (row3 10 23 29), (row3 10 23 30)]

def b060_06_labels : List Row := [(row3 248 462 248), (row3 293 462 293), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 224 226 229), (row3 253 253 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 232 232 462)]

theorem b060_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_06_rows b060_06_labels 96742701546306980565627000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_06_rows b060_06_labels]
    decide +kernel

def b060_07_rows : List Row := [(row3 10 23 31), (row3 10 23 32), (row3 10 23 33), (row3 10 23 34), (row3 10 23 35), (row3 10 23 36), (row3 10 23 37), (row3 10 23 38), (row3 10 23 39), (row3 10 23 40), (row3 10 23 41), (row3 10 23 42), (row3 10 23 43), (row3 10 23 44), (row3 10 23 45), (row3 10 23 46)]

def b060_07_labels : List Row := [(row3 286 286 462), (row3 248 248 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 234 234 234), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b060_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_07_rows b060_07_labels 99753273157249073295337500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_07_rows b060_07_labels]
    decide +kernel

def b060_08_rows : List Row := [(row3 10 23 47), (row3 10 23 48), (row3 10 23 49), (row3 10 23 50), (row3 10 23 51), (row3 10 23 52), (row3 10 23 53), (row3 10 23 54), (row3 10 23 55), (row3 10 23 56), (row3 10 23 57), (row3 10 23 58), (row3 10 23 59), (row3 10 23 60), (row3 10 23 61), (row3 10 23 62)]

def b060_08_labels : List Row := [(row3 247 247 462), (row3 291 291 289), (row3 224 224 224), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 224 224 224), (row3 105 105 131), (row3 312 312 306), (row3 222 222 224), (row3 251 251 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224)]

theorem b060_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_08_rows b060_08_labels 2456344769089667940100800000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_08_rows b060_08_labels]
    decide +kernel

def b060_09_rows : List Row := [(row3 10 23 63), (row3 10 24 25), (row3 10 24 26), (row3 10 24 27), (row3 10 24 28), (row3 10 24 29), (row3 10 24 30), (row3 10 24 31), (row3 10 24 32), (row3 10 24 33), (row3 10 24 34), (row3 10 24 35), (row3 10 24 36), (row3 10 24 37), (row3 10 24 38), (row3 10 24 39)]

def b060_09_labels : List Row := [(row3 310 310 306), (row3 173 260 10), (row3 232 232 462), (row3 249 249 462), (row3 462 462 462), (row3 242 242 462), (row3 237 237 462), (row3 271 271 462), (row3 270 270 462), (row3 235 235 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 235 235 462)]

theorem b060_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_09_rows b060_09_labels 975912720188882181471433800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_09_rows b060_09_labels]
    decide +kernel

def b060_10_rows : List Row := [(row3 10 24 40), (row3 10 24 41), (row3 10 24 42), (row3 10 24 43), (row3 10 24 44), (row3 10 24 45), (row3 10 24 46), (row3 10 24 47), (row3 10 24 48), (row3 10 24 49), (row3 10 24 50), (row3 10 24 51), (row3 10 24 52), (row3 10 24 53), (row3 10 24 54), (row3 10 24 55)]

def b060_10_labels : List Row := [(row3 235 235 237), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 267 267 265), (row3 234 234 234), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 234)]

theorem b060_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_10_rows b060_10_labels 4556188713235167106304400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_10_rows b060_10_labels]
    decide +kernel

def b060_11_rows : List Row := [(row3 10 24 56), (row3 10 24 57), (row3 10 24 58), (row3 10 24 59), (row3 10 24 60), (row3 10 24 61), (row3 10 24 62), (row3 10 24 63), (row3 10 25 26), (row3 10 25 27), (row3 10 25 28), (row3 10 25 29), (row3 10 25 30), (row3 10 25 31), (row3 10 25 32), (row3 10 25 33)]

def b060_11_labels : List Row := [(row3 154 154 180), (row3 283 283 278), (row3 228 228 234), (row3 250 250 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 279 279 278), (row3 305 289 305), (row3 222 224 222), (row3 250 462 250), (row3 462 462 462), (row3 243 462 243), (row3 235 462 235), (row3 232 462 232), (row3 286 462 286)]

theorem b060_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_11_rows b060_11_labels 1193966316402378789292920900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_11_rows b060_11_labels]
    decide +kernel

def b060_12_rows : List Row := [(row3 10 25 34), (row3 10 25 35), (row3 10 25 36), (row3 10 25 37), (row3 10 25 38), (row3 10 25 39), (row3 10 25 40), (row3 10 25 41), (row3 10 25 42), (row3 10 25 43), (row3 10 25 44), (row3 10 25 45), (row3 10 25 46), (row3 10 25 47), (row3 10 25 48), (row3 10 25 49)]

def b060_12_labels : List Row := [(row3 226 234 226), (row3 251 462 251), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 247 462 247), (row3 235 462 235), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 252 462 252)]

theorem b060_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_12_rows b060_12_labels 3515369328449019930667500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_12_rows b060_12_labels]
    decide +kernel

def b060_13_rows : List Row := [(row3 10 25 50), (row3 10 25 51), (row3 10 25 52), (row3 10 25 53), (row3 10 25 54), (row3 10 25 55), (row3 10 25 56), (row3 10 25 57), (row3 10 25 58), (row3 10 25 59), (row3 10 25 60), (row3 10 25 61), (row3 10 25 62), (row3 10 25 63), (row3 10 26 27), (row3 10 26 28)]

def b060_13_labels : List Row := [(row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 287 462 287), (row3 221 222 220), (row3 292 289 292), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 291 291 289), (row3 234 462 234)]

theorem b060_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_13_rows b060_13_labels 292951094454009337136072400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_13_rows b060_13_labels]
    decide +kernel

def b060_14_rows : List Row := [(row3 10 26 29), (row3 10 26 30), (row3 10 26 31), (row3 10 26 32), (row3 10 26 33), (row3 10 26 34), (row3 10 26 35), (row3 10 26 36), (row3 10 26 37), (row3 10 26 38), (row3 10 26 39), (row3 10 26 40), (row3 10 26 41), (row3 10 26 42), (row3 10 26 43), (row3 10 26 44)]

def b060_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 266 266 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b060_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_14_rows b060_14_labels 59098406017103583103994400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_14_rows b060_14_labels]
    decide +kernel

def b060_15_rows : List Row := [(row3 10 26 45), (row3 10 26 46), (row3 10 26 47), (row3 10 26 48), (row3 10 26 49), (row3 10 26 50), (row3 10 26 51), (row3 10 26 52), (row3 10 26 53), (row3 10 26 54), (row3 10 26 55), (row3 10 26 56), (row3 10 26 57), (row3 10 26 58), (row3 10 26 59), (row3 10 26 60)]

def b060_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 267 267 265), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 291 291 289), (row3 178 183 183), (row3 291 291 289), (row3 234 462 234)]

theorem b060_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b060_15_rows b060_15_labels 198753754011628211347660020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b060_15_rows b060_15_labels]
    decide +kernel

theorem checked060 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_060 QuarticIntegerComputationalData.ids64_060 5500742968360070593587438120 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b060_00_rows ++ b060_01_rows) ++ (b060_02_rows ++ b060_03_rows)) ++ ((b060_04_rows ++ b060_05_rows) ++ (b060_06_rows ++ b060_07_rows))) ++ (((b060_08_rows ++ b060_09_rows) ++ (b060_10_rows ++ b060_11_rows)) ++ ((b060_12_rows ++ b060_13_rows) ++ (b060_14_rows ++ b060_15_rows))))
    ((((b060_00_labels ++ b060_01_labels) ++ (b060_02_labels ++ b060_03_labels)) ++ ((b060_04_labels ++ b060_05_labels) ++ (b060_06_labels ++ b060_07_labels))) ++ (((b060_08_labels ++ b060_09_labels) ++ (b060_10_labels ++ b060_11_labels)) ++ ((b060_12_labels ++ b060_13_labels) ++ (b060_14_labels ++ b060_15_labels)))) 5500742968360070593587438120
  exact ((((b060_00_checked.append (c := 18942881147008099180427700) b060_01_checked (by decide +kernel)).append (c := 19310254392556803607283700) (b060_02_checked.append (c := 367373245548704426856000) b060_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 315644350154716364097584700) ((b060_04_checked.append (c := 99838121058603506629336500) b060_05_checked (by decide +kernel)).append (c := 296334095762159560490301000) (b060_06_checked.append (c := 196495974703556053860964500) b060_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 5500742968360070593587438120) (((b060_08_checked.append (c := 3432257489278550121572233800) b060_09_checked (by decide +kernel)).append (c := 4630779994394164077971459100) (b060_10_checked.append (c := 1198522505115613956399225300) b060_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 5185098618205354229489853420) ((b060_12_checked.append (c := 296466463782458357066739900) b060_13_checked (by decide +kernel)).append (c := 554318623811190151518394320) (b060_14_checked.append (c := 257852160028731794451654420) b060_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b061_00_rows : List Row := [(row3 10 26 61), (row3 10 26 62), (row3 10 26 63), (row3 10 27 28), (row3 10 27 29), (row3 10 27 30), (row3 10 27 31), (row3 10 27 32), (row3 10 27 33), (row3 10 27 34), (row3 10 27 35), (row3 10 27 36), (row3 10 27 37), (row3 10 27 38), (row3 10 27 39), (row3 10 27 40)]

def b061_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_00_rows b061_00_labels 3426736178168802625612500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_00_rows b061_00_labels]
    decide +kernel

def b061_01_rows : List Row := [(row3 10 27 41), (row3 10 27 42), (row3 10 27 43), (row3 10 27 44), (row3 10 27 45), (row3 10 27 46), (row3 10 27 47), (row3 10 27 48), (row3 10 27 49), (row3 10 27 50), (row3 10 27 51), (row3 10 27 52), (row3 10 27 53), (row3 10 27 54), (row3 10 27 55), (row3 10 27 56)]

def b061_01_labels : List Row := [(row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248)]

theorem b061_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_01_rows b061_01_labels 1712520457903044125100000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_01_rows b061_01_labels]
    decide +kernel

def b061_02_rows : List Row := [(row3 10 27 57), (row3 10 27 58), (row3 10 27 59), (row3 10 27 60), (row3 10 27 61), (row3 10 27 62), (row3 10 27 63), (row3 10 28 29), (row3 10 28 30), (row3 10 28 31), (row3 10 28 32), (row3 10 28 33), (row3 10 28 34), (row3 10 28 35), (row3 10 28 36), (row3 10 28 37)]

def b061_02_labels : List Row := [(row3 224 224 224), (row3 291 289 291), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_02_rows b061_02_labels 16544529669374341573399200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_02_rows b061_02_labels]
    decide +kernel

def b061_03_rows : List Row := [(row3 10 28 38), (row3 10 28 39), (row3 10 28 40), (row3 10 28 41), (row3 10 28 42), (row3 10 28 43), (row3 10 28 44), (row3 10 28 45), (row3 10 28 46), (row3 10 28 47), (row3 10 28 48), (row3 10 28 49), (row3 10 28 50), (row3 10 28 51), (row3 10 28 52), (row3 10 28 53)]

def b061_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_03_rows b061_03_labels 11490150535354856587500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_03_rows b061_03_labels]
    decide +kernel

def b061_04_rows : List Row := [(row3 10 28 54), (row3 10 28 55), (row3 10 28 56), (row3 10 28 57), (row3 10 28 58), (row3 10 28 59), (row3 10 28 60), (row3 10 28 61), (row3 10 28 62), (row3 10 28 63), (row3 10 29 30), (row3 10 29 31), (row3 10 29 32), (row3 10 29 33), (row3 10 29 34), (row3 10 29 35)]

def b061_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_04_rows b061_04_labels 528079567252346927109000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_04_rows b061_04_labels]
    decide +kernel

def b061_05_rows : List Row := [(row3 10 29 36), (row3 10 29 37), (row3 10 29 38), (row3 10 29 39), (row3 10 29 40), (row3 10 29 41), (row3 10 29 42), (row3 10 29 43), (row3 10 29 44), (row3 10 29 45), (row3 10 29 46), (row3 10 29 47), (row3 10 29 48), (row3 10 29 49), (row3 10 29 50), (row3 10 29 51)]

def b061_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_05_rows b061_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_05_rows b061_05_labels]
    decide +kernel

def b061_06_rows : List Row := [(row3 10 29 52), (row3 10 29 53), (row3 10 29 54), (row3 10 29 55), (row3 10 29 56), (row3 10 29 57), (row3 10 29 58), (row3 10 29 59), (row3 10 29 60), (row3 10 29 61), (row3 10 29 62), (row3 10 29 63), (row3 10 30 31), (row3 10 30 32), (row3 10 30 33), (row3 10 30 34)]

def b061_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_06_rows b061_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_06_rows b061_06_labels]
    decide +kernel

def b061_07_rows : List Row := [(row3 10 30 35), (row3 10 30 36), (row3 10 30 37), (row3 10 30 38), (row3 10 30 39), (row3 10 30 40), (row3 10 30 41), (row3 10 30 42), (row3 10 30 43), (row3 10 30 44), (row3 10 30 45), (row3 10 30 46), (row3 10 30 47), (row3 10 30 48), (row3 10 30 49), (row3 10 30 50)]

def b061_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_07_rows b061_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_07_rows b061_07_labels]
    decide +kernel

def b061_08_rows : List Row := [(row3 10 30 51), (row3 10 30 52), (row3 10 30 53), (row3 10 30 54), (row3 10 30 55), (row3 10 30 56), (row3 10 30 57), (row3 10 30 58), (row3 10 30 59), (row3 10 30 60), (row3 10 30 61), (row3 10 30 62), (row3 10 30 63), (row3 10 31 32), (row3 10 31 33), (row3 10 31 34)]

def b061_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_08_rows b061_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_08_rows b061_08_labels]
    decide +kernel

def b061_09_rows : List Row := [(row3 10 31 35), (row3 10 31 36), (row3 10 31 37), (row3 10 31 38), (row3 10 31 39), (row3 10 31 40), (row3 10 31 41), (row3 10 31 42), (row3 10 31 43), (row3 10 31 44), (row3 10 31 45), (row3 10 31 46), (row3 10 31 47), (row3 10 31 48), (row3 10 31 49), (row3 10 31 50)]

def b061_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462)]

theorem b061_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_09_rows b061_09_labels 298241849328832024416000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_09_rows b061_09_labels]
    decide +kernel

def b061_10_rows : List Row := [(row3 10 31 51), (row3 10 31 52), (row3 10 31 53), (row3 10 31 54), (row3 10 31 55), (row3 10 31 56), (row3 10 31 57), (row3 10 31 58), (row3 10 31 59), (row3 10 31 60), (row3 10 31 61), (row3 10 31 62), (row3 10 31 63), (row3 10 32 33), (row3 10 32 34), (row3 10 32 35)]

def b061_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 284 462 284), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_10_rows b061_10_labels 61214668581046198391478000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_10_rows b061_10_labels]
    decide +kernel

def b061_11_rows : List Row := [(row3 10 32 36), (row3 10 32 37), (row3 10 32 38), (row3 10 32 39), (row3 10 32 40), (row3 10 32 41), (row3 10 32 42), (row3 10 32 43), (row3 10 32 44), (row3 10 32 45), (row3 10 32 46), (row3 10 32 47), (row3 10 32 48), (row3 10 32 49), (row3 10 32 50), (row3 10 32 51)]

def b061_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462)]

theorem b061_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_11_rows b061_11_labels 444531022881631145973000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_11_rows b061_11_labels]
    decide +kernel

def b061_12_rows : List Row := [(row3 10 32 52), (row3 10 32 53), (row3 10 32 54), (row3 10 32 55), (row3 10 32 56), (row3 10 32 57), (row3 10 32 58), (row3 10 32 59), (row3 10 32 60), (row3 10 32 61), (row3 10 32 62), (row3 10 32 63), (row3 10 33 34), (row3 10 33 35), (row3 10 33 36), (row3 10 33 37)]

def b061_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 218 10 170), (row3 235 232 228), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_12_rows b061_12_labels 536711465736193935229949250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_12_rows b061_12_labels]
    decide +kernel

def b061_13_rows : List Row := [(row3 10 33 38), (row3 10 33 39), (row3 10 33 40), (row3 10 33 41), (row3 10 33 42), (row3 10 33 43), (row3 10 33 44), (row3 10 33 45), (row3 10 33 46), (row3 10 33 47), (row3 10 33 48), (row3 10 33 49), (row3 10 33 50), (row3 10 33 51), (row3 10 33 52), (row3 10 33 53)]

def b061_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_13_rows b061_13_labels 407433492730763154562500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_13_rows b061_13_labels]
    decide +kernel

def b061_14_rows : List Row := [(row3 10 33 54), (row3 10 33 55), (row3 10 33 56), (row3 10 33 57), (row3 10 33 58), (row3 10 33 59), (row3 10 33 60), (row3 10 33 61), (row3 10 33 62), (row3 10 33 63), (row3 10 34 35), (row3 10 34 36), (row3 10 34 37), (row3 10 34 38), (row3 10 34 39), (row3 10 34 40)]

def b061_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 282 282 278), (row3 235 232 235), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b061_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_14_rows b061_14_labels 11145439241401263908070600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_14_rows b061_14_labels]
    decide +kernel

def b061_15_rows : List Row := [(row3 10 34 41), (row3 10 34 42), (row3 10 34 43), (row3 10 34 44), (row3 10 34 45), (row3 10 34 46), (row3 10 34 47), (row3 10 34 48), (row3 10 34 49), (row3 10 34 50), (row3 10 34 51), (row3 10 34 52), (row3 10 34 53), (row3 10 34 54), (row3 10 34 55), (row3 10 34 56)]

def b061_15_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 235 235 237), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244)]

theorem b061_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b061_15_rows b061_15_labels 955205769679002270135000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b061_15_rows b061_15_labels]
    decide +kernel

theorem checked061 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_061 QuarticIntegerComputationalData.ids64_061 633400341716495516232392550 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b061_00_rows ++ b061_01_rows) ++ (b061_02_rows ++ b061_03_rows)) ++ ((b061_04_rows ++ b061_05_rows) ++ (b061_06_rows ++ b061_07_rows))) ++ (((b061_08_rows ++ b061_09_rows) ++ (b061_10_rows ++ b061_11_rows)) ++ ((b061_12_rows ++ b061_13_rows) ++ (b061_14_rows ++ b061_15_rows))))
    ((((b061_00_labels ++ b061_01_labels) ++ (b061_02_labels ++ b061_03_labels)) ++ ((b061_04_labels ++ b061_05_labels) ++ (b061_06_labels ++ b061_07_labels))) ++ (((b061_08_labels ++ b061_09_labels) ++ (b061_10_labels ++ b061_11_labels)) ++ ((b061_12_labels ++ b061_13_labels) ++ (b061_14_labels ++ b061_15_labels)))) 633400341716495516232392550
  exact ((((b061_00_checked.append (c := 5139256636071846750712500) b061_01_checked (by decide +kernel)).append (c := 21695276455981543180699200) (b061_02_checked.append (c := 16556019819909696429986700) b061_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 22223356023233890107808200) ((b061_04_checked.append (c := 528079567252346927109000) b061_05_checked (by decide +kernel)).append (c := 528079567252346927109000) (b061_06_checked.append (c := 0) b061_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 633400341716495516232392550) (((b061_08_checked.append (c := 298241849328832024416000) b061_09_checked (by decide +kernel)).append (c := 61957441453256661561867000) (b061_10_checked.append (c := 61659199603927829537451000) b061_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 611176985693261626124584350) ((b061_12_checked.append (c := 537118899228924698384511750) b061_13_checked (by decide +kernel)).append (c := 549219544240004964562717350) (b061_14_checked.append (c := 12100645011080266178205600) b061_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b062_00_rows : List Row := [(row3 10 34 57), (row3 10 34 58), (row3 10 34 59), (row3 10 34 60), (row3 10 34 61), (row3 10 34 62), (row3 10 34 63), (row3 10 35 36), (row3 10 35 37), (row3 10 35 38), (row3 10 35 39), (row3 10 35 40), (row3 10 35 41), (row3 10 35 42), (row3 10 35 43), (row3 10 35 44)]

def b062_00_labels : List Row := [(row3 234 226 226), (row3 281 278 281), (row3 234 234 234), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_00_rows b062_00_labels 9761265845699181964476300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_00_rows b062_00_labels]
    decide +kernel

def b062_01_rows : List Row := [(row3 10 35 45), (row3 10 35 46), (row3 10 35 47), (row3 10 35 48), (row3 10 35 49), (row3 10 35 50), (row3 10 35 51), (row3 10 35 52), (row3 10 35 53), (row3 10 35 54), (row3 10 35 55), (row3 10 35 56), (row3 10 35 57), (row3 10 35 58), (row3 10 35 59), (row3 10 35 60)]

def b062_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 232 235), (row3 247 247 462), (row3 462 462 462)]

theorem b062_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_01_rows b062_01_labels 664238137435450457989500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_01_rows b062_01_labels]
    decide +kernel

def b062_02_rows : List Row := [(row3 10 35 61), (row3 10 35 62), (row3 10 35 63), (row3 10 36 37), (row3 10 36 38), (row3 10 36 39), (row3 10 36 40), (row3 10 36 41), (row3 10 36 42), (row3 10 36 43), (row3 10 36 44), (row3 10 36 45), (row3 10 36 46), (row3 10 36 47), (row3 10 36 48), (row3 10 36 49)]

def b062_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_02_rows b062_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_02_rows b062_02_labels]
    decide +kernel

def b062_03_rows : List Row := [(row3 10 36 50), (row3 10 36 51), (row3 10 36 52), (row3 10 36 53), (row3 10 36 54), (row3 10 36 55), (row3 10 36 56), (row3 10 36 57), (row3 10 36 58), (row3 10 36 59), (row3 10 36 60), (row3 10 36 61), (row3 10 36 62), (row3 10 36 63), (row3 10 37 38), (row3 10 37 39)]

def b062_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_03_rows b062_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_03_rows b062_03_labels]
    decide +kernel

def b062_04_rows : List Row := [(row3 10 37 40), (row3 10 37 41), (row3 10 37 42), (row3 10 37 43), (row3 10 37 44), (row3 10 37 45), (row3 10 37 46), (row3 10 37 47), (row3 10 37 48), (row3 10 37 49), (row3 10 37 50), (row3 10 37 51), (row3 10 37 52), (row3 10 37 53), (row3 10 37 54), (row3 10 37 55)]

def b062_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_04_rows b062_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_04_rows b062_04_labels]
    decide +kernel

def b062_05_rows : List Row := [(row3 10 37 56), (row3 10 37 57), (row3 10 37 58), (row3 10 37 59), (row3 10 37 60), (row3 10 37 61), (row3 10 37 62), (row3 10 37 63), (row3 10 38 39), (row3 10 38 40), (row3 10 38 41), (row3 10 38 42), (row3 10 38 43), (row3 10 38 44), (row3 10 38 45), (row3 10 38 46)]

def b062_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_05_rows b062_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_05_rows b062_05_labels]
    decide +kernel

def b062_06_rows : List Row := [(row3 10 38 47), (row3 10 38 48), (row3 10 38 49), (row3 10 38 50), (row3 10 38 51), (row3 10 38 52), (row3 10 38 53), (row3 10 38 54), (row3 10 38 55), (row3 10 38 56), (row3 10 38 57), (row3 10 38 58), (row3 10 38 59), (row3 10 38 60), (row3 10 38 61), (row3 10 38 62)]

def b062_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_06_rows b062_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_06_rows b062_06_labels]
    decide +kernel

def b062_07_rows : List Row := [(row3 10 38 63), (row3 10 39 40), (row3 10 39 41), (row3 10 39 42), (row3 10 39 43), (row3 10 39 44), (row3 10 39 45), (row3 10 39 46), (row3 10 39 47), (row3 10 39 48), (row3 10 39 49), (row3 10 39 50), (row3 10 39 51), (row3 10 39 52), (row3 10 39 53), (row3 10 39 54)]

def b062_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_07_rows b062_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_07_rows b062_07_labels]
    decide +kernel

def b062_08_rows : List Row := [(row3 10 39 55), (row3 10 39 56), (row3 10 39 57), (row3 10 39 58), (row3 10 39 59), (row3 10 39 60), (row3 10 39 61), (row3 10 39 62), (row3 10 39 63), (row3 10 40 41), (row3 10 40 42), (row3 10 40 43), (row3 10 40 44), (row3 10 40 45), (row3 10 40 46), (row3 10 40 47)]

def b062_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462)]

theorem b062_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_08_rows b062_08_labels 579916841102486388450000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_08_rows b062_08_labels]
    decide +kernel

def b062_09_rows : List Row := [(row3 10 40 48), (row3 10 40 49), (row3 10 40 50), (row3 10 40 51), (row3 10 40 52), (row3 10 40 53), (row3 10 40 54), (row3 10 40 55), (row3 10 40 56), (row3 10 40 57), (row3 10 40 58), (row3 10 40 59), (row3 10 40 60), (row3 10 40 61), (row3 10 40 62), (row3 10 40 63)]

def b062_09_labels : List Row := [(row3 266 266 265), (row3 226 234 226), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 234), (row3 211 88 370), (row3 320 320 319), (row3 234 228 228), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 279 279 278)]

theorem b062_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_09_rows b062_09_labels 9654264466984597493479896900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_09_rows b062_09_labels]
    decide +kernel

def b062_10_rows : List Row := [(row3 10 41 42), (row3 10 41 43), (row3 10 41 44), (row3 10 41 45), (row3 10 41 46), (row3 10 41 47), (row3 10 41 48), (row3 10 41 49), (row3 10 41 50), (row3 10 41 51), (row3 10 41 52), (row3 10 41 53), (row3 10 41 54), (row3 10 41 55), (row3 10 41 56), (row3 10 41 57)]

def b062_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 286 462 286), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 214 11 117), (row3 146 137 143)]

theorem b062_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_10_rows b062_10_labels 2017147207200239243340310590 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_10_rows b062_10_labels]
    decide +kernel

def b062_11_rows : List Row := [(row3 10 41 58), (row3 10 41 59), (row3 10 41 60), (row3 10 41 61), (row3 10 41 62), (row3 10 41 63), (row3 10 42 43), (row3 10 42 44), (row3 10 42 45), (row3 10 42 46), (row3 10 42 47), (row3 10 42 48), (row3 10 42 49), (row3 10 42 50), (row3 10 42 51), (row3 10 42 52)]

def b062_11_labels : List Row := [(row3 292 289 292), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 270 270 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_11_rows b062_11_labels 62814097568014637731108200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_11_rows b062_11_labels]
    decide +kernel

def b062_12_rows : List Row := [(row3 10 42 53), (row3 10 42 54), (row3 10 42 55), (row3 10 42 56), (row3 10 42 57), (row3 10 42 58), (row3 10 42 59), (row3 10 42 60), (row3 10 42 61), (row3 10 42 62), (row3 10 42 63), (row3 10 43 44), (row3 10 43 45), (row3 10 43 46), (row3 10 43 47), (row3 10 43 48)]

def b062_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 311 311 306), (row3 183 183 178), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_12_rows b062_12_labels 141744141022400389689543360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_12_rows b062_12_labels]
    decide +kernel

def b062_13_rows : List Row := [(row3 10 43 49), (row3 10 43 50), (row3 10 43 51), (row3 10 43 52), (row3 10 43 53), (row3 10 43 54), (row3 10 43 55), (row3 10 43 56), (row3 10 43 57), (row3 10 43 58), (row3 10 43 59), (row3 10 43 60), (row3 10 43 61), (row3 10 43 62), (row3 10 43 63), (row3 10 44 45)]

def b062_13_labels : List Row := [(row3 246 462 246), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 228 228), (row3 291 289 291), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_13_rows b062_13_labels 13961043390298310038420200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_13_rows b062_13_labels]
    decide +kernel

def b062_14_rows : List Row := [(row3 10 44 46), (row3 10 44 47), (row3 10 44 48), (row3 10 44 49), (row3 10 44 50), (row3 10 44 51), (row3 10 44 52), (row3 10 44 53), (row3 10 44 54), (row3 10 44 55), (row3 10 44 56), (row3 10 44 57), (row3 10 44 58), (row3 10 44 59), (row3 10 44 60), (row3 10 44 61)]

def b062_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_14_rows b062_14_labels 460898763182129314156500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_14_rows b062_14_labels]
    decide +kernel

def b062_15_rows : List Row := [(row3 10 44 62), (row3 10 44 63), (row3 10 45 46), (row3 10 45 47), (row3 10 45 48), (row3 10 45 49), (row3 10 45 50), (row3 10 45 51), (row3 10 45 52), (row3 10 45 53), (row3 10 45 54), (row3 10 45 55), (row3 10 45 56), (row3 10 45 57), (row3 10 45 58), (row3 10 45 59)]

def b062_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b062_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b062_15_rows b062_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b062_15_rows b062_15_labels]
    decide +kernel

theorem checked062 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_062 QuarticIntegerComputationalData.ids64_062 11901397275752969322404351550 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b062_00_rows ++ b062_01_rows) ++ (b062_02_rows ++ b062_03_rows)) ++ ((b062_04_rows ++ b062_05_rows) ++ (b062_06_rows ++ b062_07_rows))) ++ (((b062_08_rows ++ b062_09_rows) ++ (b062_10_rows ++ b062_11_rows)) ++ ((b062_12_rows ++ b062_13_rows) ++ (b062_14_rows ++ b062_15_rows))))
    ((((b062_00_labels ++ b062_01_labels) ++ (b062_02_labels ++ b062_03_labels)) ++ ((b062_04_labels ++ b062_05_labels) ++ (b062_06_labels ++ b062_07_labels))) ++ (((b062_08_labels ++ b062_09_labels) ++ (b062_10_labels ++ b062_11_labels)) ++ ((b062_12_labels ++ b062_13_labels) ++ (b062_14_labels ++ b062_15_labels)))) 11901397275752969322404351550
  exact ((((b062_00_checked.append (c := 10425503983134632422465800) b062_01_checked (by decide +kernel)).append (c := 10425503983134632422465800) (b062_02_checked.append (c := 0) b062_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 10425503983134632422465800) ((b062_04_checked.append (c := 0) b062_05_checked (by decide +kernel)).append (c := 0) (b062_06_checked.append (c := 0) b062_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11901397275752969322404351550) (((b062_08_checked.append (c := 9654844383825699979868346900) b062_09_checked (by decide +kernel)).append (c := 11734805688593953860939765690) (b062_10_checked.append (c := 2079961304768253881071418790) b062_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 11890971771769834689981885750) ((b062_12_checked.append (c := 155705184412698699727963560) b062_13_checked (by decide +kernel)).append (c := 156166083175880829042120060) (b062_14_checked.append (c := 460898763182129314156500) b062_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b063_00_rows : List Row := [(row3 10 45 60), (row3 10 45 61), (row3 10 45 62), (row3 10 45 63), (row3 10 46 47), (row3 10 46 48), (row3 10 46 49), (row3 10 46 50), (row3 10 46 51), (row3 10 46 52), (row3 10 46 53), (row3 10 46 54), (row3 10 46 55), (row3 10 46 56), (row3 10 46 57), (row3 10 46 58)]

def b063_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_00_rows b063_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_00_rows b063_00_labels]
    decide +kernel

def b063_01_rows : List Row := [(row3 10 46 59), (row3 10 46 60), (row3 10 46 61), (row3 10 46 62), (row3 10 46 63), (row3 10 47 48), (row3 10 47 49), (row3 10 47 50), (row3 10 47 51), (row3 10 47 52), (row3 10 47 53), (row3 10 47 54), (row3 10 47 55), (row3 10 47 56), (row3 10 47 57), (row3 10 47 58)]

def b063_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 251 462 251), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 214 11 117), (row3 232 228 223), (row3 246 462 246)]

theorem b063_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_01_rows b063_01_labels 1646158310725349783874759750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_01_rows b063_01_labels]
    decide +kernel

def b063_02_rows : List Row := [(row3 10 47 59), (row3 10 47 60), (row3 10 47 61), (row3 10 47 62), (row3 10 47 63), (row3 10 48 49), (row3 10 48 50), (row3 10 48 51), (row3 10 48 52), (row3 10 48 53), (row3 10 48 54), (row3 10 48 55), (row3 10 48 56), (row3 10 48 57), (row3 10 48 58), (row3 10 48 59)]

def b063_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 305 289 305), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 291 289 291), (row3 181 435 42), (row3 99 98 101), (row3 313 306 313), (row3 235 235 462)]

theorem b063_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_02_rows b063_02_labels 346367491044277428965122149330 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_02_rows b063_02_labels]
    decide +kernel

def b063_03_rows : List Row := [(row3 10 48 60), (row3 10 48 61), (row3 10 48 62), (row3 10 48 63), (row3 10 49 50), (row3 10 49 51), (row3 10 49 52), (row3 10 49 53), (row3 10 49 54), (row3 10 49 55), (row3 10 49 56), (row3 10 49 57), (row3 10 49 58), (row3 10 49 59), (row3 10 49 60), (row3 10 49 61)]

def b063_03_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 291 289 291), (row3 137 149 146), (row3 173 260 10), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 250 250 462), (row3 222 222 224), (row3 134 81 398), (row3 396 416 408), (row3 141 142 136), (row3 253 253 462), (row3 462 462 462), (row3 246 246 462)]

theorem b063_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_03_rows b063_03_labels 70989867261841067512711230510 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_03_rows b063_03_labels]
    decide +kernel

def b063_04_rows : List Row := [(row3 10 49 62), (row3 10 49 63), (row3 10 50 51), (row3 10 50 52), (row3 10 50 53), (row3 10 50 54), (row3 10 50 55), (row3 10 50 56), (row3 10 50 57), (row3 10 50 58), (row3 10 50 59), (row3 10 50 60), (row3 10 50 61), (row3 10 50 62), (row3 10 50 63), (row3 10 51 52)]

def b063_04_labels : List Row := [(row3 224 224 224), (row3 312 312 306), (row3 271 462 271), (row3 237 462 237), (row3 242 462 242), (row3 462 462 462), (row3 249 462 249), (row3 216 11 119), (row3 120 112 120), (row3 363 386 393), (row3 224 226 229), (row3 246 462 246), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 462 462 462)]

theorem b063_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_04_rows b063_04_labels 26716425028036091868470802120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_04_rows b063_04_labels]
    decide +kernel

def b063_05_rows : List Row := [(row3 10 51 53), (row3 10 51 54), (row3 10 51 55), (row3 10 51 56), (row3 10 51 57), (row3 10 51 58), (row3 10 51 59), (row3 10 51 60), (row3 10 51 61), (row3 10 51 62), (row3 10 51 63), (row3 10 52 53), (row3 10 52 54), (row3 10 52 55), (row3 10 52 56), (row3 10 52 57)]

def b063_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 312 312 306), (row3 144 147 137), (row3 286 286 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232)]

theorem b063_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_05_rows b063_05_labels 444128295542112562062188520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_05_rows b063_05_labels]
    decide +kernel

def b063_06_rows : List Row := [(row3 10 52 58), (row3 10 52 59), (row3 10 52 60), (row3 10 52 61), (row3 10 52 62), (row3 10 52 63), (row3 10 53 54), (row3 10 53 55), (row3 10 53 56), (row3 10 53 57), (row3 10 53 58), (row3 10 53 59), (row3 10 53 60), (row3 10 53 61), (row3 10 53 62), (row3 10 53 63)]

def b063_06_labels : List Row := [(row3 291 289 291), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_06_rows b063_06_labels 13239404336763104045380200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_06_rows b063_06_labels]
    decide +kernel

def b063_07_rows : List Row := [(row3 10 54 55), (row3 10 54 56), (row3 10 54 57), (row3 10 54 58), (row3 10 54 59), (row3 10 54 60), (row3 10 54 61), (row3 10 54 62), (row3 10 54 63), (row3 10 55 56), (row3 10 55 57), (row3 10 55 58), (row3 10 55 59), (row3 10 55 60), (row3 10 55 61), (row3 10 55 62)]

def b063_07_labels : List Row := [(row3 248 462 248), (row3 215 11 118), (row3 228 232 223), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 462 228), (row3 135 83 398), (row3 322 322 321), (row3 224 222 222), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224)]

theorem b063_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_07_rows b063_07_labels 21824410448560795689551266350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_07_rows b063_07_labels]
    decide +kernel

def b063_08_rows : List Row := [(row3 10 55 63), (row3 10 56 57), (row3 10 56 58), (row3 10 56 59), (row3 10 56 60), (row3 10 56 61), (row3 10 56 62), (row3 10 56 63), (row3 10 57 58), (row3 10 57 59), (row3 10 57 60), (row3 10 57 61), (row3 10 57 62), (row3 10 57 63), (row3 10 58 59), (row3 10 58 60)]

def b063_08_labels : List Row := [(row3 309 309 306), (row3 46 46 440), (row3 108 367 84), (row3 260 173 10), (row3 462 462 462), (row3 258 172 10), (row3 114 368 86), (row3 389 45 436), (row3 60 411 432), (row3 142 141 136), (row3 283 278 283), (row3 232 228 235), (row3 320 319 320), (row3 98 101 99), (row3 362 392 388), (row3 182 178 182)]

theorem b063_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_08_rows b063_08_labels 1597301483171897887571411892630 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_08_rows b063_08_labels]
    decide +kernel

def b063_09_rows : List Row := [(row3 10 58 61), (row3 10 58 62), (row3 10 58 63), (row3 10 59 60), (row3 10 59 61), (row3 10 59 62), (row3 10 59 63), (row3 10 60 61), (row3 10 60 62), (row3 10 60 63), (row3 10 61 62), (row3 10 61 63), (row3 10 62 63), (row3 11 12 13), (row3 11 12 14), (row3 11 12 15)]

def b063_09_labels : List Row := [(row3 268 268 265), (row3 224 223 223), (row3 318 318 315), (row3 287 462 287), (row3 235 462 235), (row3 247 462 247), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 309 309 306), (row3 193 163 193), (row3 265 277 277), (row3 238 462 238)]

theorem b063_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_09_rows b063_09_labels 1700646161324878258036373940 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_09_rows b063_09_labels]
    decide +kernel

def b063_10_rows : List Row := [(row3 11 12 16), (row3 11 12 17), (row3 11 12 18), (row3 11 12 19), (row3 11 12 20), (row3 11 12 21), (row3 11 12 22), (row3 11 12 23), (row3 11 12 24), (row3 11 12 25), (row3 11 12 26), (row3 11 12 27), (row3 11 12 28), (row3 11 12 29), (row3 11 12 30), (row3 11 12 31)]

def b063_10_labels : List Row := [(row3 462 462 462), (row3 462 286 286), (row3 228 160 163), (row3 462 358 358), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 193 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_10_rows b063_10_labels 15760443188898216235434282000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_10_rows b063_10_labels]
    decide +kernel

def b063_11_rows : List Row := [(row3 11 12 32), (row3 11 12 33), (row3 11 12 34), (row3 11 12 35), (row3 11 12 36), (row3 11 12 37), (row3 11 12 38), (row3 11 12 39), (row3 11 12 40), (row3 11 12 41), (row3 11 12 42), (row3 11 12 43), (row3 11 12 44), (row3 11 12 45), (row3 11 12 46), (row3 11 12 47)]

def b063_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_11_rows b063_11_labels 19713966259789303503675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_11_rows b063_11_labels]
    decide +kernel

def b063_12_rows : List Row := [(row3 11 12 48), (row3 11 12 49), (row3 11 12 50), (row3 11 12 51), (row3 11 12 52), (row3 11 12 53), (row3 11 12 54), (row3 11 12 55), (row3 11 12 56), (row3 11 12 57), (row3 11 12 58), (row3 11 12 59), (row3 11 12 60), (row3 11 12 61), (row3 11 12 62), (row3 11 12 63)]

def b063_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 287 287), (row3 235 191 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_12_rows b063_12_labels 529266137732026740433747500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_12_rows b063_12_labels]
    decide +kernel

def b063_13_rows : List Row := [(row3 11 13 14), (row3 11 13 15), (row3 11 13 16), (row3 11 13 17), (row3 11 13 18), (row3 11 13 19), (row3 11 13 20), (row3 11 13 21), (row3 11 13 22), (row3 11 13 23), (row3 11 13 24), (row3 11 13 25), (row3 11 13 26), (row3 11 13 27), (row3 11 13 28), (row3 11 13 29)]

def b063_13_labels : List Row := [(row3 371 87 325), (row3 273 462 273), (row3 462 462 462), (row3 462 235 235), (row3 462 273 273), (row3 235 193 191), (row3 273 273 288), (row3 193 235 191), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 261 261), (row3 235 235 232), (row3 261 462 261)]

theorem b063_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_13_rows b063_13_labels 10422985499869703026625326560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_13_rows b063_13_labels]
    decide +kernel

def b063_14_rows : List Row := [(row3 11 13 30), (row3 11 13 31), (row3 11 13 32), (row3 11 13 33), (row3 11 13 34), (row3 11 13 35), (row3 11 13 36), (row3 11 13 37), (row3 11 13 38), (row3 11 13 39), (row3 11 13 40), (row3 11 13 41), (row3 11 13 42), (row3 11 13 43), (row3 11 13 44), (row3 11 13 45)]

def b063_14_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b063_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_14_rows b063_14_labels 425532996411123579300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_14_rows b063_14_labels]
    decide +kernel

def b063_15_rows : List Row := [(row3 11 13 46), (row3 11 13 47), (row3 11 13 48), (row3 11 13 49), (row3 11 13 50), (row3 11 13 51), (row3 11 13 52), (row3 11 13 53), (row3 11 13 54), (row3 11 13 55), (row3 11 13 56), (row3 11 13 57), (row3 11 13 58), (row3 11 13 59), (row3 11 13 60), (row3 11 13 61)]

def b063_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 261 261), (row3 235 235 232), (row3 261 462 261)]

theorem b063_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b063_15_rows b063_15_labels 5334951856071169493330400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b063_15_rows b063_15_labels]
    decide +kernel

theorem checked063 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_063 QuarticIntegerComputationalData.ids64_063 2093742018404154592914355704810 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b063_00_rows ++ b063_01_rows) ++ (b063_02_rows ++ b063_03_rows)) ++ ((b063_04_rows ++ b063_05_rows) ++ (b063_06_rows ++ b063_07_rows))) ++ (((b063_08_rows ++ b063_09_rows) ++ (b063_10_rows ++ b063_11_rows)) ++ ((b063_12_rows ++ b063_13_rows) ++ (b063_14_rows ++ b063_15_rows))))
    ((((b063_00_labels ++ b063_01_labels) ++ (b063_02_labels ++ b063_03_labels)) ++ ((b063_04_labels ++ b063_05_labels) ++ (b063_06_labels ++ b063_07_labels))) ++ (((b063_08_labels ++ b063_09_labels) ++ (b063_10_labels ++ b063_11_labels)) ++ ((b063_12_labels ++ b063_13_labels) ++ (b063_14_labels ++ b063_15_labels)))) 2093742018404154592914355704810
  exact ((((b063_00_checked.append (c := 1646158310725349783874759750) b063_01_checked (by decide +kernel)).append (c := 419003516616843846261708139590) (b063_02_checked.append (c := 417357358306118496477833379840) b063_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 468001719793319609485837776780) ((b063_04_checked.append (c := 27160553323578204430532990640) b063_05_checked (by decide +kernel)).append (c := 48998203176475763224129637190) (b063_06_checked.append (c := 21837649852897558793596646550) b063_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2093742018404154592914355704810) (((b063_08_checked.append (c := 1599002129333222765829448266570) b063_09_checked (by decide +kernel)).append (c := 1614782286488380771368386223570) (b063_10_checked.append (c := 15780157155158005538937957000) b063_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 1625740298610834983428517928030) ((b063_12_checked.append (c := 10952251637601729767059074060) b063_13_checked (by decide +kernel)).append (c := 10958012122454212060131704460) (b063_14_checked.append (c := 5760484852482293072630400) b063_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b064_00_rows : List Row := [(row3 11 13 62), (row3 11 13 63), (row3 11 14 15), (row3 11 14 16), (row3 11 14 17), (row3 11 14 18), (row3 11 14 19), (row3 11 14 20), (row3 11 14 21), (row3 11 14 22), (row3 11 14 23), (row3 11 14 24), (row3 11 14 25), (row3 11 14 26), (row3 11 14 27), (row3 11 14 28)]

def b064_00_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 357 90 187), (row3 229 229 226), (row3 462 252 252), (row3 462 236 236), (row3 462 264 264), (row3 234 231 231), (row3 278 280 280), (row3 180 154 154), (row3 278 282 282), (row3 462 245 245), (row3 462 462 462), (row3 462 243 243), (row3 462 238 238), (row3 462 245 245)]

theorem b064_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_00_rows b064_00_labels 7401610144114304306096659200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_00_rows b064_00_labels]
    decide +kernel

def b064_01_rows : List Row := [(row3 11 14 29), (row3 11 14 30), (row3 11 14 31), (row3 11 14 32), (row3 11 14 33), (row3 11 14 34), (row3 11 14 35), (row3 11 14 36), (row3 11 14 37), (row3 11 14 38), (row3 11 14 39), (row3 11 14 40), (row3 11 14 41), (row3 11 14 42), (row3 11 14 43), (row3 11 14 44)]

def b064_01_labels : List Row := [(row3 234 234 234), (row3 265 266 266), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 243 243), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_01_rows b064_01_labels 3995941329084848528684400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_01_rows b064_01_labels]
    decide +kernel

def b064_02_rows : List Row := [(row3 11 14 45), (row3 11 14 46), (row3 11 14 47), (row3 11 14 48), (row3 11 14 49), (row3 11 14 50), (row3 11 14 51), (row3 11 14 52), (row3 11 14 53), (row3 11 14 54), (row3 11 14 55), (row3 11 14 56), (row3 11 14 57), (row3 11 14 58), (row3 11 14 59), (row3 11 14 60)]

def b064_02_labels : List Row := [(row3 462 462 462), (row3 462 242 242), (row3 462 462 462), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 243 243), (row3 237 237 237), (row3 462 247 247), (row3 462 285 285), (row3 462 232 232), (row3 462 247 247), (row3 462 238 238), (row3 462 245 245)]

theorem b064_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_02_rows b064_02_labels 74287078478481977622442500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_02_rows b064_02_labels]
    decide +kernel

def b064_03_rows : List Row := [(row3 11 14 61), (row3 11 14 62), (row3 11 14 63), (row3 11 15 16), (row3 11 15 17), (row3 11 15 18), (row3 11 15 19), (row3 11 15 20), (row3 11 15 21), (row3 11 15 22), (row3 11 15 23), (row3 11 15 24), (row3 11 15 25), (row3 11 15 26), (row3 11 15 27), (row3 11 15 28)]

def b064_03_labels : List Row := [(row3 234 234 234), (row3 265 268 268), (row3 234 226 226), (row3 288 288 288), (row3 222 220 221), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 273 273 462), (row3 193 189 232), (row3 235 233 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_03_rows b064_03_labels 410453971200919856768578200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_03_rows b064_03_labels]
    decide +kernel

def b064_04_rows : List Row := [(row3 11 15 29), (row3 11 15 30), (row3 11 15 31), (row3 11 15 32), (row3 11 15 33), (row3 11 15 34), (row3 11 15 35), (row3 11 15 36), (row3 11 15 37), (row3 11 15 38), (row3 11 15 39), (row3 11 15 40), (row3 11 15 41), (row3 11 15 42), (row3 11 15 43), (row3 11 15 44)]

def b064_04_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_04_rows b064_04_labels 3705147702386075290564800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_04_rows b064_04_labels]
    decide +kernel

def b064_05_rows : List Row := [(row3 11 15 45), (row3 11 15 46), (row3 11 15 47), (row3 11 15 48), (row3 11 15 49), (row3 11 15 50), (row3 11 15 51), (row3 11 15 52), (row3 11 15 53), (row3 11 15 54), (row3 11 15 55), (row3 11 15 56), (row3 11 15 57), (row3 11 15 58), (row3 11 15 59), (row3 11 15 60)]

def b064_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 273 273), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 230 232), (row3 235 162 163), (row3 462 288 288), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462)]

theorem b064_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_05_rows b064_05_labels 752547405159082106673019200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_05_rows b064_05_labels]
    decide +kernel

def b064_06_rows : List Row := [(row3 11 15 61), (row3 11 15 62), (row3 11 15 63), (row3 11 16 17), (row3 11 16 18), (row3 11 16 19), (row3 11 16 20), (row3 11 16 21), (row3 11 16 22), (row3 11 16 23), (row3 11 16 24), (row3 11 16 25), (row3 11 16 26), (row3 11 16 27), (row3 11 16 28), (row3 11 16 29)]

def b064_06_labels : List Row := [(row3 462 462 462), (row3 235 228 232), (row3 261 290 288), (row3 369 121 85), (row3 288 288 462), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 261 261 462), (row3 193 191 235), (row3 193 192 238), (row3 273 273 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_06_rows b064_06_labels 10673596466650045393252560720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_06_rows b064_06_labels]
    decide +kernel

def b064_07_rows : List Row := [(row3 11 16 30), (row3 11 16 31), (row3 11 16 32), (row3 11 16 33), (row3 11 16 34), (row3 11 16 35), (row3 11 16 36), (row3 11 16 37), (row3 11 16 38), (row3 11 16 39), (row3 11 16 40), (row3 11 16 41), (row3 11 16 42), (row3 11 16 43), (row3 11 16 44), (row3 11 16 45)]

def b064_07_labels : List Row := [(row3 235 235 462), (row3 273 273 462), (row3 261 261 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 238 236 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_07_rows b064_07_labels 8900970122382730052320800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_07_rows b064_07_labels]
    decide +kernel

def b064_08_rows : List Row := [(row3 11 16 46), (row3 11 16 47), (row3 11 16 48), (row3 11 16 49), (row3 11 16 50), (row3 11 16 51), (row3 11 16 52), (row3 11 16 53), (row3 11 16 54), (row3 11 16 55), (row3 11 16 56), (row3 11 16 57), (row3 11 16 58), (row3 11 16 59), (row3 11 16 60), (row3 11 16 61)]

def b064_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 238 192 193), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_08_rows b064_08_labels 356062743194828594436136800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_08_rows b064_08_labels]
    decide +kernel

def b064_09_rows : List Row := [(row3 11 16 62), (row3 11 16 63), (row3 11 17 18), (row3 11 17 19), (row3 11 17 20), (row3 11 17 21), (row3 11 17 22), (row3 11 17 23), (row3 11 17 24), (row3 11 17 25), (row3 11 17 26), (row3 11 17 27), (row3 11 17 28), (row3 11 17 29), (row3 11 17 30), (row3 11 17 31)]

def b064_09_labels : List Row := [(row3 462 235 235), (row3 462 273 273), (row3 398 134 81), (row3 289 305 305), (row3 234 226 226), (row3 462 248 248), (row3 234 234 234), (row3 289 292 292), (row3 306 310 310), (row3 131 105 105), (row3 306 312 312), (row3 224 222 222), (row3 462 251 251), (row3 462 462 462), (row3 462 246 246), (row3 224 224 224)]

theorem b064_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_09_rows b064_09_labels 22898751067767042908835965100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_09_rows b064_09_labels]
    decide +kernel

def b064_10_rows : List Row := [(row3 11 17 32), (row3 11 17 33), (row3 11 17 34), (row3 11 17 35), (row3 11 17 36), (row3 11 17 37), (row3 11 17 38), (row3 11 17 39), (row3 11 17 40), (row3 11 17 41), (row3 11 17 42), (row3 11 17 43), (row3 11 17 44), (row3 11 17 45), (row3 11 17 46), (row3 11 17 47)]

def b064_10_labels : List Row := [(row3 224 224 224), (row3 289 291 291), (row3 224 224 224), (row3 462 250 250), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 247 247), (row3 234 234 234), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_10_rows b064_10_labels 12863808114151398898804200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_10_rows b064_10_labels]
    decide +kernel

def b064_11_rows : List Row := [(row3 11 17 48), (row3 11 17 49), (row3 11 17 50), (row3 11 17 51), (row3 11 17 52), (row3 11 17 53), (row3 11 17 54), (row3 11 17 55), (row3 11 17 56), (row3 11 17 57), (row3 11 17 58), (row3 11 17 59), (row3 11 17 60), (row3 11 17 61), (row3 11 17 62), (row3 11 17 63)]

def b064_11_labels : List Row := [(row3 462 235 235), (row3 462 248 248), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 286 286), (row3 229 226 224), (row3 462 253 253), (row3 462 235 235), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 462 232 232)]

theorem b064_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_11_rows b064_11_labels 104323601454003049843372500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_11_rows b064_11_labels]
    decide +kernel

def b064_12_rows : List Row := [(row3 11 18 19), (row3 11 18 20), (row3 11 18 21), (row3 11 18 22), (row3 11 18 23), (row3 11 18 24), (row3 11 18 25), (row3 11 18 26), (row3 11 18 27), (row3 11 18 28), (row3 11 18 29), (row3 11 18 30), (row3 11 18 31), (row3 11 18 32), (row3 11 18 33), (row3 11 18 34)]

def b064_12_labels : List Row := [(row3 139 163 124), (row3 278 288 300), (row3 235 232 228), (row3 462 462 462), (row3 235 462 235), (row3 228 462 228), (row3 295 462 295), (row3 139 232 138), (row3 295 273 304), (row3 228 232 223), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 278 462 278)]

theorem b064_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_12_rows b064_12_labels 3800887052914496737181656800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_12_rows b064_12_labels]
    decide +kernel

def b064_13_rows : List Row := [(row3 11 18 35), (row3 11 18 36), (row3 11 18 37), (row3 11 18 38), (row3 11 18 39), (row3 11 18 40), (row3 11 18 41), (row3 11 18 42), (row3 11 18 43), (row3 11 18 44), (row3 11 18 45), (row3 11 18 46), (row3 11 18 47), (row3 11 18 48), (row3 11 18 49), (row3 11 18 50)]

def b064_13_labels : List Row := [(row3 228 236 225), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_13_rows b064_13_labels 1877827596181938687636000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_13_rows b064_13_labels]
    decide +kernel

def b064_14_rows : List Row := [(row3 11 18 51), (row3 11 18 52), (row3 11 18 53), (row3 11 18 54), (row3 11 18 55), (row3 11 18 56), (row3 11 18 57), (row3 11 18 58), (row3 11 18 59), (row3 11 18 60), (row3 11 18 61), (row3 11 18 62), (row3 11 18 63), (row3 11 19 20), (row3 11 19 21), (row3 11 19 22)]

def b064_14_labels : List Row := [(row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 229 226 224), (row3 462 273 273), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462)]

theorem b064_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_14_rows b064_14_labels 1114670920234236950021574600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_14_rows b064_14_labels]
    decide +kernel

def b064_15_rows : List Row := [(row3 11 19 23), (row3 11 19 24), (row3 11 19 25), (row3 11 19 26), (row3 11 19 27), (row3 11 19 28), (row3 11 19 29), (row3 11 19 30), (row3 11 19 31), (row3 11 19 32), (row3 11 19 33), (row3 11 19 34), (row3 11 19 35), (row3 11 19 36), (row3 11 19 37), (row3 11 19 38)]

def b064_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 193 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b064_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b064_15_rows b064_15_labels 650809001802525760883409000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b064_15_rows b064_15_labels]
    decide +kernel

theorem checked064 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_064 QuarticIntegerComputationalData.ids64_064 48269343147834154633073384820 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b064_00_rows ++ b064_01_rows) ++ (b064_02_rows ++ b064_03_rows)) ++ ((b064_04_rows ++ b064_05_rows) ++ (b064_06_rows ++ b064_07_rows))) ++ (((b064_08_rows ++ b064_09_rows) ++ (b064_10_rows ++ b064_11_rows)) ++ ((b064_12_rows ++ b064_13_rows) ++ (b064_14_rows ++ b064_15_rows))))
    ((((b064_00_labels ++ b064_01_labels) ++ (b064_02_labels ++ b064_03_labels)) ++ ((b064_04_labels ++ b064_05_labels) ++ (b064_06_labels ++ b064_07_labels))) ++ (((b064_08_labels ++ b064_09_labels) ++ (b064_10_labels ++ b064_11_labels)) ++ ((b064_12_labels ++ b064_13_labels) ++ (b064_14_labels ++ b064_15_labels)))) 48269343147834154633073384820
  exact ((((b064_00_checked.append (c := 7405606085443389154625343600) b064_01_checked (by decide +kernel)).append (c := 7890347135122790989016364300) (b064_02_checked.append (c := 484741049679401834391020700) b064_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 19329097124756687294284829820) ((b064_04_checked.append (c := 756252552861468181963584000) b064_05_checked (by decide +kernel)).append (c := 11438749989633896305268465520) (b064_06_checked.append (c := 10682497436772428123304881520) b064_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 48269343147834154633073384820) (((b064_08_checked.append (c := 23254813810961871503272101900) b064_09_checked (by decide +kernel)).append (c := 23372001220530025952014278600) (b064_10_checked.append (c := 117187409568154448742176700) b064_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 28940246023077467338788555000) ((b064_12_checked.append (c := 3802764880510678675869292800) b064_13_checked (by decide +kernel)).append (c := 5568244802547441386774276400) (b064_14_checked.append (c := 1765479922036762710904983600) b064_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
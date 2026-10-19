import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch016
import Dressed.QuarticIntegerComputationalData64.Batch017


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b137_00_rows : List Row := [(row3 32 46 56), (row3 32 46 57), (row3 32 46 58), (row3 32 46 59), (row3 32 46 60), (row3 32 46 61), (row3 32 46 62), (row3 32 46 63), (row3 32 47 48), (row3 32 47 49), (row3 32 47 50), (row3 32 47 51), (row3 32 47 52), (row3 32 47 53), (row3 32 47 54), (row3 32 47 55)]

def b137_00_labels : List Row := [(row3 462 270 270), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 350 346 349), (row3 221 222 220), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 399 82 156)]

theorem b137_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_00_rows b137_00_labels 25240277383562082816246938040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_00_rows b137_00_labels]
    decide +kernel

def b137_01_rows : List Row := [(row3 32 47 56), (row3 32 47 57), (row3 32 47 58), (row3 32 47 59), (row3 32 47 60), (row3 32 47 61), (row3 32 47 62), (row3 32 47 63), (row3 32 48 49), (row3 32 48 50), (row3 32 48 51), (row3 32 48 52), (row3 32 48 53), (row3 32 48 54), (row3 32 48 55), (row3 32 48 56)]

def b137_01_labels : List Row := [(row3 151 153 179), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 79 67 67), (row3 327 327 327), (row3 206 210 210), (row3 462 255 255), (row3 206 210 210), (row3 327 327 327), (row3 79 67 67), (row3 446 30 80)]

theorem b137_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_01_rows b137_01_labels 3965046076885521594637810510320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_01_rows b137_01_labels]
    decide +kernel

def b137_02_rows : List Row := [(row3 32 48 57), (row3 32 48 58), (row3 32 48 59), (row3 32 48 60), (row3 32 48 61), (row3 32 48 62), (row3 32 48 63), (row3 32 49 50), (row3 32 49 51), (row3 32 49 52), (row3 32 49 53), (row3 32 49 54), (row3 32 49 55), (row3 32 49 56), (row3 32 49 57), (row3 32 49 58)]

def b137_02_labels : List Row := [(row3 350 346 349), (row3 178 183 183), (row3 462 261 261), (row3 462 462 462), (row3 462 261 261), (row3 178 183 183), (row3 350 346 349), (row3 131 105 105), (row3 289 291 291), (row3 234 234 234), (row3 462 244 244), (row3 234 234 234), (row3 306 314 314), (row3 366 375 353), (row3 399 82 156), (row3 306 311 311)]

theorem b137_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_02_rows b137_02_labels 49326474112335042562672603050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_02_rows b137_02_labels]
    decide +kernel

def b137_03_rows : List Row := [(row3 32 49 59), (row3 32 49 60), (row3 32 49 61), (row3 32 49 62), (row3 32 49 63), (row3 32 50 51), (row3 32 50 52), (row3 32 50 53), (row3 32 50 54), (row3 32 50 55), (row3 32 50 56), (row3 32 50 57), (row3 32 50 58), (row3 32 50 59), (row3 32 50 60), (row3 32 50 61)]

def b137_03_labels : List Row := [(row3 224 224 224), (row3 462 246 246), (row3 462 462 462), (row3 462 248 248), (row3 221 222 220), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 154 154 180), (row3 288 462 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_03_rows b137_03_labels 818960199176466052365545100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_03_rows b137_03_labels]
    decide +kernel

def b137_04_rows : List Row := [(row3 32 50 62), (row3 32 50 63), (row3 32 51 52), (row3 32 51 53), (row3 32 51 54), (row3 32 51 55), (row3 32 51 56), (row3 32 51 57), (row3 32 51 58), (row3 32 51 59), (row3 32 51 60), (row3 32 51 61), (row3 32 51 62), (row3 32 51 63), (row3 32 52 53), (row3 32 52 54)]

def b137_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 263 263), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_04_rows b137_04_labels 20534762169825871360456500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_04_rows b137_04_labels]
    decide +kernel

def b137_05_rows : List Row := [(row3 32 52 55), (row3 32 52 56), (row3 32 52 57), (row3 32 52 58), (row3 32 52 59), (row3 32 52 60), (row3 32 52 61), (row3 32 52 62), (row3 32 52 63), (row3 32 53 54), (row3 32 53 55), (row3 32 53 56), (row3 32 53 57), (row3 32 53 58), (row3 32 53 59), (row3 32 53 60)]

def b137_05_labels : List Row := [(row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 289 291 291), (row3 462 263 263), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_05_rows b137_05_labels 30286314074991157210804200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_05_rows b137_05_labels]
    decide +kernel

def b137_06_rows : List Row := [(row3 32 53 61), (row3 32 53 62), (row3 32 53 63), (row3 32 54 55), (row3 32 54 56), (row3 32 54 57), (row3 32 54 58), (row3 32 54 59), (row3 32 54 60), (row3 32 54 61), (row3 32 54 62), (row3 32 54 63), (row3 32 55 56), (row3 32 55 57), (row3 32 55 58), (row3 32 55 59)]

def b137_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 131 105 105), (row3 154 154 180), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 366 375 353), (row3 221 222 220), (row3 462 248 248), (row3 462 462 462)]

theorem b137_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_06_rows b137_06_labels 19776165682180824344956666350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_06_rows b137_06_labels]
    decide +kernel

def b137_07_rows : List Row := [(row3 32 55 60), (row3 32 55 61), (row3 32 55 62), (row3 32 55 63), (row3 32 56 57), (row3 32 56 58), (row3 32 56 59), (row3 32 56 60), (row3 32 56 61), (row3 32 56 62), (row3 32 56 63), (row3 32 57 58), (row3 32 57 59), (row3 32 57 60), (row3 32 57 61), (row3 32 57 62)]

def b137_07_labels : List Row := [(row3 462 246 246), (row3 224 224 224), (row3 306 311 311), (row3 399 82 156), (row3 64 66 55), (row3 339 328 342), (row3 201 208 201), (row3 462 257 257), (row3 201 208 201), (row3 339 328 342), (row3 64 66 55), (row3 163 162 235), (row3 273 273 462), (row3 236 236 462), (row3 462 462 462), (row3 236 233 235)]

theorem b137_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_07_rows b137_07_labels 550958981632836392592911785500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_07_rows b137_07_labels]
    decide +kernel

def b137_08_rows : List Row := [(row3 32 57 63), (row3 32 58 59), (row3 32 58 60), (row3 32 58 61), (row3 32 58 62), (row3 32 58 63), (row3 32 59 60), (row3 32 59 61), (row3 32 59 62), (row3 32 59 63), (row3 32 60 61), (row3 32 60 62), (row3 32 60 63), (row3 32 61 62), (row3 32 61 63), (row3 32 62 63)]

def b137_08_labels : List Row := [(row3 288 288 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 236 235 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 273 462 273), (row3 163 235 162)]

theorem b137_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_08_rows b137_08_labels 758710004489433795658535100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_08_rows b137_08_labels]
    decide +kernel

def b137_09_rows : List Row := [(row3 33 34 35), (row3 33 34 36), (row3 33 34 37), (row3 33 34 38), (row3 33 34 39), (row3 33 34 40), (row3 33 34 41), (row3 33 34 42), (row3 33 34 43), (row3 33 34 44), (row3 33 34 45), (row3 33 34 46), (row3 33 34 47), (row3 33 34 48), (row3 33 34 49), (row3 33 34 50)]

def b137_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279), (row3 163 163 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 291 289 291), (row3 234 234 462)]

theorem b137_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_09_rows b137_09_labels 1328175621050272719480442800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_09_rows b137_09_labels]
    decide +kernel

def b137_10_rows : List Row := [(row3 33 34 51), (row3 33 34 52), (row3 33 34 53), (row3 33 34 54), (row3 33 34 55), (row3 33 34 56), (row3 33 34 57), (row3 33 34 58), (row3 33 34 59), (row3 33 34 60), (row3 33 34 61), (row3 33 34 62), (row3 33 34 63), (row3 33 35 36), (row3 33 35 37), (row3 33 35 38)]

def b137_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_10_rows b137_10_labels 16613765494039278211401000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_10_rows b137_10_labels]
    decide +kernel

def b137_11_rows : List Row := [(row3 33 35 39), (row3 33 35 40), (row3 33 35 41), (row3 33 35 42), (row3 33 35 43), (row3 33 35 44), (row3 33 35 45), (row3 33 35 46), (row3 33 35 47), (row3 33 35 48), (row3 33 35 49), (row3 33 35 50), (row3 33 35 51), (row3 33 35 52), (row3 33 35 53), (row3 33 35 54)]

def b137_11_labels : List Row := [(row3 462 462 462), (row3 462 236 236), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_11_rows b137_11_labels 62082383370327939168985500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_11_rows b137_11_labels]
    decide +kernel

def b137_12_rows : List Row := [(row3 33 35 55), (row3 33 35 56), (row3 33 35 57), (row3 33 35 58), (row3 33 35 59), (row3 33 35 60), (row3 33 35 61), (row3 33 35 62), (row3 33 35 63), (row3 33 36 37), (row3 33 36 38), (row3 33 36 39), (row3 33 36 40), (row3 33 36 41), (row3 33 36 42), (row3 33 36 43)]

def b137_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_12_rows b137_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_12_rows b137_12_labels]
    decide +kernel

def b137_13_rows : List Row := [(row3 33 36 44), (row3 33 36 45), (row3 33 36 46), (row3 33 36 47), (row3 33 36 48), (row3 33 36 49), (row3 33 36 50), (row3 33 36 51), (row3 33 36 52), (row3 33 36 53), (row3 33 36 54), (row3 33 36 55), (row3 33 36 56), (row3 33 36 57), (row3 33 36 58), (row3 33 36 59)]

def b137_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_13_rows b137_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_13_rows b137_13_labels]
    decide +kernel

def b137_14_rows : List Row := [(row3 33 36 60), (row3 33 36 61), (row3 33 36 62), (row3 33 36 63), (row3 33 37 38), (row3 33 37 39), (row3 33 37 40), (row3 33 37 41), (row3 33 37 42), (row3 33 37 43), (row3 33 37 44), (row3 33 37 45), (row3 33 37 46), (row3 33 37 47), (row3 33 37 48), (row3 33 37 49)]

def b137_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462)]

theorem b137_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_14_rows b137_14_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_14_rows b137_14_labels]
    decide +kernel

def b137_15_rows : List Row := [(row3 33 37 50), (row3 33 37 51), (row3 33 37 52), (row3 33 37 53), (row3 33 37 54), (row3 33 37 55), (row3 33 37 56), (row3 33 37 57), (row3 33 37 58), (row3 33 37 59), (row3 33 37 60), (row3 33 37 61), (row3 33 37 62), (row3 33 37 63), (row3 33 38 39), (row3 33 38 40)]

def b137_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279)]

theorem b137_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b137_15_rows b137_15_labels 9757301904490604214747600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b137_15_rows b137_15_labels]
    decide +kernel

theorem checked137 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_137 QuarticIntegerComputationalData.ids64_137 4613393380053545632461809184060 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b137_00_rows ++ b137_01_rows) ++ (b137_02_rows ++ b137_03_rows)) ++ ((b137_04_rows ++ b137_05_rows) ++ (b137_06_rows ++ b137_07_rows))) ++ (((b137_08_rows ++ b137_09_rows) ++ (b137_10_rows ++ b137_11_rows)) ++ ((b137_12_rows ++ b137_13_rows) ++ (b137_14_rows ++ b137_15_rows))))
    ((((b137_00_labels ++ b137_01_labels) ++ (b137_02_labels ++ b137_03_labels)) ++ ((b137_04_labels ++ b137_05_labels) ++ (b137_06_labels ++ b137_07_labels))) ++ (((b137_08_labels ++ b137_09_labels) ++ (b137_10_labels ++ b137_11_labels)) ++ ((b137_12_labels ++ b137_13_labels) ++ (b137_14_labels ++ b137_15_labels)))) 4613393380053545632461809184060
  exact ((((b137_00_checked.append (c := 3990286354269083677454057448360) b137_01_checked (by decide +kernel)).append (c := 4040431788580595186069095596510) (b137_02_checked.append (c := 50145434311511508615038148150) b137_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4611217756971857220035535309060) ((b137_04_checked.append (c := 50821076244817028571260700) b137_05_checked (by decide +kernel)).append (c := 570785968391262033966439712550) (b137_06_checked.append (c := 570735147315017216937868451850) b137_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4613393380053545632461809184060) (((b137_08_checked.append (c := 2086885625539706515138977900) b137_09_checked (by decide +kernel)).append (c := 2165581774404073732519364400) (b137_10_checked.append (c := 78696148864367217380386500) b137_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 2175623081688412426273875000) ((b137_12_checked.append (c := 0) b137_13_checked (by decide +kernel)).append (c := 10041307284338693754510600) (b137_14_checked.append (c := 10041307284338693754510600) b137_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b138_00_rows : List Row := [(row3 33 38 41), (row3 33 38 42), (row3 33 38 43), (row3 33 38 44), (row3 33 38 45), (row3 33 38 46), (row3 33 38 47), (row3 33 38 48), (row3 33 38 49), (row3 33 38 50), (row3 33 38 51), (row3 33 38 52), (row3 33 38 53), (row3 33 38 54), (row3 33 38 55), (row3 33 38 56)]

def b138_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462)]

theorem b138_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_00_rows b138_00_labels 1312076506314915710392500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_00_rows b138_00_labels]
    decide +kernel

def b138_01_rows : List Row := [(row3 33 38 57), (row3 33 38 58), (row3 33 38 59), (row3 33 38 60), (row3 33 38 61), (row3 33 38 62), (row3 33 38 63), (row3 33 39 40), (row3 33 39 41), (row3 33 39 42), (row3 33 39 43), (row3 33 39 44), (row3 33 39 45), (row3 33 39 46), (row3 33 39 47), (row3 33 39 48)]

def b138_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 176 176 161), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 291 291 289)]

theorem b138_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_01_rows b138_01_labels 384154529125114469192470560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_01_rows b138_01_labels]
    decide +kernel

def b138_02_rows : List Row := [(row3 33 39 49), (row3 33 39 50), (row3 33 39 51), (row3 33 39 52), (row3 33 39 53), (row3 33 39 54), (row3 33 39 55), (row3 33 39 56), (row3 33 39 57), (row3 33 39 58), (row3 33 39 59), (row3 33 39 60), (row3 33 39 61), (row3 33 39 62), (row3 33 39 63), (row3 33 40 41)]

def b138_02_labels : List Row := [(row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 73 359 429)]

theorem b138_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_02_rows b138_02_labels 109558698574253653873533878100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_02_rows b138_02_labels]
    decide +kernel

def b138_03_rows : List Row := [(row3 33 40 42), (row3 33 40 43), (row3 33 40 44), (row3 33 40 45), (row3 33 40 46), (row3 33 40 47), (row3 33 40 48), (row3 33 40 49), (row3 33 40 50), (row3 33 40 51), (row3 33 40 52), (row3 33 40 53), (row3 33 40 54), (row3 33 40 55), (row3 33 40 56), (row3 33 40 57)]

def b138_03_labels : List Row := [(row3 199 190 198), (row3 262 262 261), (row3 462 238 238), (row3 262 262 261), (row3 199 190 198), (row3 352 373 365), (row3 58 430 372), (row3 128 126 125), (row3 283 283 278), (row3 462 236 236), (row3 462 462 462), (row3 462 236 236), (row3 279 279 278), (row3 175 161 175), (row3 167 190 166), (row3 296 296 295)]

theorem b138_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_03_rows b138_03_labels 156159672393781179016003617930 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_03_rows b138_03_labels]
    decide +kernel

def b138_04_rows : List Row := [(row3 33 40 58), (row3 33 40 59), (row3 33 40 60), (row3 33 40 61), (row3 33 40 62), (row3 33 40 63), (row3 33 41 42), (row3 33 41 43), (row3 33 41 44), (row3 33 41 45), (row3 33 41 46), (row3 33 41 47), (row3 33 41 48), (row3 33 41 49), (row3 33 41 50), (row3 33 41 51)]

def b138_04_labels : List Row := [(row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 279 279 278), (row3 358 462 358), (row3 193 462 193), (row3 263 462 263), (row3 462 462 462), (row3 263 462 263), (row3 191 235 193), (row3 126 137 127), (row3 41 435 95), (row3 160 228 163), (row3 284 462 284)]

theorem b138_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_04_rows b138_04_labels 376890057524725117807669868910 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_04_rows b138_04_labels]
    decide +kernel

def b138_05_rows : List Row := [(row3 33 41 52), (row3 33 41 53), (row3 33 41 54), (row3 33 41 55), (row3 33 41 56), (row3 33 41 57), (row3 33 41 58), (row3 33 41 59), (row3 33 41 60), (row3 33 41 61), (row3 33 41 62), (row3 33 41 63), (row3 33 42 43), (row3 33 42 44), (row3 33 42 45), (row3 33 42 46)]

def b138_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 287 462 287), (row3 303 462 303), (row3 167 190 166), (row3 286 462 286), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_05_rows b138_05_labels 15020504873271337933523187900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_05_rows b138_05_labels]
    decide +kernel

def b138_06_rows : List Row := [(row3 33 42 47), (row3 33 42 48), (row3 33 42 49), (row3 33 42 50), (row3 33 42 51), (row3 33 42 52), (row3 33 42 53), (row3 33 42 54), (row3 33 42 55), (row3 33 42 56), (row3 33 42 57), (row3 33 42 58), (row3 33 42 59), (row3 33 42 60), (row3 33 42 61), (row3 33 42 62)]

def b138_06_labels : List Row := [(row3 243 243 462), (row3 291 291 289), (row3 146 149 137), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 279 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_06_rows b138_06_labels 631331262390770814485510100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_06_rows b138_06_labels]
    decide +kernel

def b138_07_rows : List Row := [(row3 33 42 63), (row3 33 43 44), (row3 33 43 45), (row3 33 43 46), (row3 33 43 47), (row3 33 43 48), (row3 33 43 49), (row3 33 43 50), (row3 33 43 51), (row3 33 43 52), (row3 33 43 53), (row3 33 43 54), (row3 33 43 55), (row3 33 43 56), (row3 33 43 57), (row3 33 43 58)]

def b138_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 291 289 291), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 246 462 246)]

theorem b138_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_07_rows b138_07_labels 13961043390298310038420200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_07_rows b138_07_labels]
    decide +kernel

def b138_08_rows : List Row := [(row3 33 43 59), (row3 33 43 60), (row3 33 43 61), (row3 33 43 62), (row3 33 43 63), (row3 33 44 45), (row3 33 44 46), (row3 33 44 47), (row3 33 44 48), (row3 33 44 49), (row3 33 44 50), (row3 33 44 51), (row3 33 44 52), (row3 33 44 53), (row3 33 44 54), (row3 33 44 55)]

def b138_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 235 235), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_08_rows b138_08_labels 308726459769680456953500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_08_rows b138_08_labels]
    decide +kernel

def b138_09_rows : List Row := [(row3 33 44 56), (row3 33 44 57), (row3 33 44 58), (row3 33 44 59), (row3 33 44 60), (row3 33 44 61), (row3 33 44 62), (row3 33 44 63), (row3 33 45 46), (row3 33 45 47), (row3 33 45 48), (row3 33 45 49), (row3 33 45 50), (row3 33 45 51), (row3 33 45 52), (row3 33 45 53)]

def b138_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_09_rows b138_09_labels 524146807624089602232000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_09_rows b138_09_labels]
    decide +kernel

def b138_10_rows : List Row := [(row3 33 45 54), (row3 33 45 55), (row3 33 45 56), (row3 33 45 57), (row3 33 45 58), (row3 33 45 59), (row3 33 45 60), (row3 33 45 61), (row3 33 45 62), (row3 33 45 63), (row3 33 46 47), (row3 33 46 48), (row3 33 46 49), (row3 33 46 50), (row3 33 46 51), (row3 33 46 52)]

def b138_10_labels : List Row := [(row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_10_rows b138_10_labels 70029623178888893262182700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_10_rows b138_10_labels]
    decide +kernel

def b138_11_rows : List Row := [(row3 33 46 53), (row3 33 46 54), (row3 33 46 55), (row3 33 46 56), (row3 33 46 57), (row3 33 46 58), (row3 33 46 59), (row3 33 46 60), (row3 33 46 61), (row3 33 46 62), (row3 33 46 63), (row3 33 47 48), (row3 33 47 49), (row3 33 47 50), (row3 33 47 51), (row3 33 47 52)]

def b138_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 143 137 146), (row3 292 289 292), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_11_rows b138_11_labels 287439856502451738970496040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_11_rows b138_11_labels]
    decide +kernel

def b138_12_rows : List Row := [(row3 33 47 53), (row3 33 47 54), (row3 33 47 55), (row3 33 47 56), (row3 33 47 57), (row3 33 47 58), (row3 33 47 59), (row3 33 47 60), (row3 33 47 61), (row3 33 47 62), (row3 33 47 63), (row3 33 48 49), (row3 33 48 50), (row3 33 48 51), (row3 33 48 52), (row3 33 48 53)]

def b138_12_labels : List Row := [(row3 246 462 246), (row3 232 462 232), (row3 117 11 214), (row3 286 462 286), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 462 235), (row3 78 401 427), (row3 182 182 178), (row3 266 265 266), (row3 462 237 237), (row3 266 265 266)]

theorem b138_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_12_rows b138_12_labels 70812583458956835066168577650 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_12_rows b138_12_labels]
    decide +kernel

def b138_13_rows : List Row := [(row3 33 48 54), (row3 33 48 55), (row3 33 48 56), (row3 33 48 57), (row3 33 48 58), (row3 33 48 59), (row3 33 48 60), (row3 33 48 61), (row3 33 48 62), (row3 33 48 63), (row3 33 49 50), (row3 33 49 51), (row3 33 49 52), (row3 33 49 53), (row3 33 49 54), (row3 33 49 55)]

def b138_13_labels : List Row := [(row3 184 184 178), (row3 361 387 391), (row3 41 435 95), (row3 128 126 125), (row3 292 289 292), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 289 291), (row3 146 149 137), (row3 361 391 387), (row3 184 178 184), (row3 266 266 265), (row3 462 237 237), (row3 266 266 265), (row3 182 178 182)]

theorem b138_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_13_rows b138_13_labels 383685827339199675766978303050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_13_rows b138_13_labels]
    decide +kernel

def b138_14_rows : List Row := [(row3 33 49 56), (row3 33 49 57), (row3 33 49 58), (row3 33 49 59), (row3 33 49 60), (row3 33 49 61), (row3 33 49 62), (row3 33 49 63), (row3 33 50 51), (row3 33 50 52), (row3 33 50 53), (row3 33 50 54), (row3 33 50 55), (row3 33 50 56), (row3 33 50 57), (row3 33 50 58)]

def b138_14_labels : List Row := [(row3 126 137 127), (row3 58 430 372), (row3 143 137 146), (row3 291 291 289), (row3 462 235 235), (row3 462 462 462), (row3 462 235 235), (row3 291 291 289), (row3 293 462 293), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 246 462 246), (row3 287 462 287), (row3 175 161 175), (row3 117 11 214)]

theorem b138_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_14_rows b138_14_labels 149601933199604515489164552510 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_14_rows b138_14_labels]
    decide +kernel

def b138_15_rows : List Row := [(row3 33 50 59), (row3 33 50 60), (row3 33 50 61), (row3 33 50 62), (row3 33 50 63), (row3 33 51 52), (row3 33 51 53), (row3 33 51 54), (row3 33 51 55), (row3 33 51 56), (row3 33 51 57), (row3 33 51 58), (row3 33 51 59), (row3 33 51 60), (row3 33 51 61), (row3 33 51 62)]

def b138_15_labels : List Row := [(row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 279 278), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b138_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b138_15_rows b138_15_labels 11581352297964808560872100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b138_15_rows b138_15_labels]
    decide +kernel

theorem checked138 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_138 QuarticIntegerComputationalData.ids64_138 1263129919980451512673321515750 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b138_00_rows ++ b138_01_rows) ++ (b138_02_rows ++ b138_03_rows)) ++ ((b138_04_rows ++ b138_05_rows) ++ (b138_06_rows ++ b138_07_rows))) ++ (((b138_08_rows ++ b138_09_rows) ++ (b138_10_rows ++ b138_11_rows)) ++ ((b138_12_rows ++ b138_13_rows) ++ (b138_14_rows ++ b138_15_rows))))
    ((((b138_00_labels ++ b138_01_labels) ++ (b138_02_labels ++ b138_03_labels)) ++ ((b138_04_labels ++ b138_05_labels) ++ (b138_06_labels ++ b138_07_labels))) ++ (((b138_08_labels ++ b138_09_labels) ++ (b138_10_labels ++ b138_11_labels)) ++ ((b138_12_labels ++ b138_13_labels) ++ (b138_14_labels ++ b138_15_labels)))) 1263129919980451512673321515750
  exact ((((b138_00_checked.append (c := 385466605631429384902863060) b138_01_checked (by decide +kernel)).append (c := 266103837573666262274440359090) (b138_02_checked.append (c := 265718370968034832889537496030) b138_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 658659692277443787140157346200) ((b138_04_checked.append (c := 391910562397996455741193056810) b138_05_checked (by decide +kernel)).append (c := 392555854703777524865716987110) (b138_06_checked.append (c := 645292305781069124523930300) b138_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1263129919980451512673321515750) (((b138_08_checked.append (c := 832873267393770059185500) b138_09_checked (by decide +kernel)).append (c := 358302352948734402291864240) (b138_10_checked.append (c := 357469479681340632232678740) b138_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 604470227703007725533164169550) ((b138_12_checked.append (c := 454498410798156510833146880700) b138_13_checked (by decide +kernel)).append (c := 604111925350058991130872305310) (b138_14_checked.append (c := 149613514551902480297725424610) b138_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b139_00_rows : List Row := [(row3 33 51 63), (row3 33 52 53), (row3 33 52 54), (row3 33 52 55), (row3 33 52 56), (row3 33 52 57), (row3 33 52 58), (row3 33 52 59), (row3 33 52 60), (row3 33 52 61), (row3 33 52 62), (row3 33 52 63), (row3 33 53 54), (row3 33 53 55), (row3 33 53 56), (row3 33 53 57)]

def b139_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 236 236), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462)]

theorem b139_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_00_rows b139_00_labels 688605636101511598024500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_00_rows b139_00_labels]
    decide +kernel

def b139_01_rows : List Row := [(row3 33 53 58), (row3 33 53 59), (row3 33 53 60), (row3 33 53 61), (row3 33 53 62), (row3 33 53 63), (row3 33 54 55), (row3 33 54 56), (row3 33 54 57), (row3 33 54 58), (row3 33 54 59), (row3 33 54 60), (row3 33 54 61), (row3 33 54 62), (row3 33 54 63), (row3 33 55 56)]

def b139_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 284 462 284), (row3 462 236 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 160 228 163)]

theorem b139_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_01_rows b139_01_labels 881503213484843250182032500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_01_rows b139_01_labels]
    decide +kernel

def b139_02_rows : List Row := [(row3 33 55 57), (row3 33 55 58), (row3 33 55 59), (row3 33 55 60), (row3 33 55 61), (row3 33 55 62), (row3 33 55 63), (row3 33 56 57), (row3 33 56 58), (row3 33 56 59), (row3 33 56 60), (row3 33 56 61), (row3 33 56 62), (row3 33 56 63), (row3 33 57 58), (row3 33 57 59)]

def b139_02_labels : List Row := [(row3 283 283 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 228 228 462), (row3 293 293 462), (row3 73 359 429), (row3 191 193 235), (row3 263 263 462), (row3 462 462 462), (row3 263 263 462), (row3 193 193 462), (row3 358 358 462), (row3 352 365 373), (row3 199 198 190)]

theorem b139_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_02_rows b139_02_labels 134172259902121789739381389770 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_02_rows b139_02_labels]
    decide +kernel

def b139_03_rows : List Row := [(row3 33 57 60), (row3 33 57 61), (row3 33 57 62), (row3 33 57 63), (row3 33 58 59), (row3 33 58 60), (row3 33 58 61), (row3 33 58 62), (row3 33 58 63), (row3 33 59 60), (row3 33 59 61), (row3 33 59 62), (row3 33 59 63), (row3 33 60 61), (row3 33 60 62), (row3 33 60 63)]

def b139_03_labels : List Row := [(row3 262 261 262), (row3 462 238 238), (row3 262 261 262), (row3 199 198 190), (row3 284 284 462), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_03_rows b139_03_labels 186767010390505167450241080 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_03_rows b139_03_labels]
    decide +kernel

def b139_04_rows : List Row := [(row3 33 61 62), (row3 33 61 63), (row3 33 62 63), (row3 34 35 36), (row3 34 35 37), (row3 34 35 38), (row3 34 35 39), (row3 34 35 40), (row3 34 35 41), (row3 34 35 42), (row3 34 35 43), (row3 34 35 44), (row3 34 35 45), (row3 34 35 46), (row3 34 35 47), (row3 34 35 48)]

def b139_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_04_rows b139_04_labels 3867409411222473623709000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_04_rows b139_04_labels]
    decide +kernel

def b139_05_rows : List Row := [(row3 34 35 49), (row3 34 35 50), (row3 34 35 51), (row3 34 35 52), (row3 34 35 53), (row3 34 35 54), (row3 34 35 55), (row3 34 35 56), (row3 34 35 57), (row3 34 35 58), (row3 34 35 59), (row3 34 35 60), (row3 34 35 61), (row3 34 35 62), (row3 34 35 63), (row3 34 36 37)]

def b139_05_labels : List Row := [(row3 462 248 248), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_05_rows b139_05_labels 4126121307428863469791500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_05_rows b139_05_labels]
    decide +kernel

def b139_06_rows : List Row := [(row3 34 36 38), (row3 34 36 39), (row3 34 36 40), (row3 34 36 41), (row3 34 36 42), (row3 34 36 43), (row3 34 36 44), (row3 34 36 45), (row3 34 36 46), (row3 34 36 47), (row3 34 36 48), (row3 34 36 49), (row3 34 36 50), (row3 34 36 51), (row3 34 36 52), (row3 34 36 53)]

def b139_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_06_rows b139_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_06_rows b139_06_labels]
    decide +kernel

def b139_07_rows : List Row := [(row3 34 36 54), (row3 34 36 55), (row3 34 36 56), (row3 34 36 57), (row3 34 36 58), (row3 34 36 59), (row3 34 36 60), (row3 34 36 61), (row3 34 36 62), (row3 34 36 63), (row3 34 37 38), (row3 34 37 39), (row3 34 37 40), (row3 34 37 41), (row3 34 37 42), (row3 34 37 43)]

def b139_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_07_rows b139_07_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_07_rows b139_07_labels]
    decide +kernel

def b139_08_rows : List Row := [(row3 34 37 44), (row3 34 37 45), (row3 34 37 46), (row3 34 37 47), (row3 34 37 48), (row3 34 37 49), (row3 34 37 50), (row3 34 37 51), (row3 34 37 52), (row3 34 37 53), (row3 34 37 54), (row3 34 37 55), (row3 34 37 56), (row3 34 37 57), (row3 34 37 58), (row3 34 37 59)]

def b139_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_08_rows b139_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_08_rows b139_08_labels]
    decide +kernel

def b139_09_rows : List Row := [(row3 34 37 60), (row3 34 37 61), (row3 34 37 62), (row3 34 37 63), (row3 34 38 39), (row3 34 38 40), (row3 34 38 41), (row3 34 38 42), (row3 34 38 43), (row3 34 38 44), (row3 34 38 45), (row3 34 38 46), (row3 34 38 47), (row3 34 38 48), (row3 34 38 49), (row3 34 38 50)]

def b139_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_09_rows b139_09_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_09_rows b139_09_labels]
    decide +kernel

def b139_10_rows : List Row := [(row3 34 38 51), (row3 34 38 52), (row3 34 38 53), (row3 34 38 54), (row3 34 38 55), (row3 34 38 56), (row3 34 38 57), (row3 34 38 58), (row3 34 38 59), (row3 34 38 60), (row3 34 38 61), (row3 34 38 62), (row3 34 38 63), (row3 34 39 40), (row3 34 39 41), (row3 34 39 42)]

def b139_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 279 279), (row3 232 232 462), (row3 462 462 462)]

theorem b139_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_10_rows b139_10_labels 10573542170116974582411600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_10_rows b139_10_labels]
    decide +kernel

def b139_11_rows : List Row := [(row3 34 39 43), (row3 34 39 44), (row3 34 39 45), (row3 34 39 46), (row3 34 39 47), (row3 34 39 48), (row3 34 39 49), (row3 34 39 50), (row3 34 39 51), (row3 34 39 52), (row3 34 39 53), (row3 34 39 54), (row3 34 39 55), (row3 34 39 56), (row3 34 39 57), (row3 34 39 58)]

def b139_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_11_rows b139_11_labels 495836240688545342728500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_11_rows b139_11_labels]
    decide +kernel

def b139_12_rows : List Row := [(row3 34 39 59), (row3 34 39 60), (row3 34 39 61), (row3 34 39 62), (row3 34 39 63), (row3 34 40 41), (row3 34 40 42), (row3 34 40 43), (row3 34 40 44), (row3 34 40 45), (row3 34 40 46), (row3 34 40 47), (row3 34 40 48), (row3 34 40 49), (row3 34 40 50), (row3 34 40 51)]

def b139_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 356 159 91), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237), (row3 265 266 266), (row3 180 154 154), (row3 370 88 211), (row3 319 320 320), (row3 228 228 234), (row3 462 243 243)]

theorem b139_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_12_rows b139_12_labels 16829300808665101489688642700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_12_rows b139_12_labels]
    decide +kernel

def b139_13_rows : List Row := [(row3 34 40 52), (row3 34 40 53), (row3 34 40 54), (row3 34 40 55), (row3 34 40 56), (row3 34 40 57), (row3 34 40 58), (row3 34 40 59), (row3 34 40 60), (row3 34 40 61), (row3 34 40 62), (row3 34 40 63), (row3 34 41 42), (row3 34 41 43), (row3 34 41 44), (row3 34 41 45)]

def b139_13_labels : List Row := [(row3 462 462 462), (row3 462 243 243), (row3 234 234 234), (row3 278 279 279), (row3 265 266 266), (row3 226 234 226), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 234 234 234), (row3 163 462 163), (row3 273 462 273), (row3 236 462 236), (row3 462 462 462)]

theorem b139_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_13_rows b139_13_labels 1123394718920922908853414300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_13_rows b139_13_labels]
    decide +kernel

def b139_14_rows : List Row := [(row3 34 41 46), (row3 34 41 47), (row3 34 41 48), (row3 34 41 49), (row3 34 41 50), (row3 34 41 51), (row3 34 41 52), (row3 34 41 53), (row3 34 41 54), (row3 34 41 55), (row3 34 41 56), (row3 34 41 57), (row3 34 41 58), (row3 34 41 59), (row3 34 41 60), (row3 34 41 61)]

def b139_14_labels : List Row := [(row3 236 462 236), (row3 273 462 273), (row3 300 462 300), (row3 399 83 157), (row3 300 278 288), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 232 462 232), (row3 288 462 288), (row3 226 234 226), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_14_rows b139_14_labels 20484792533025919147112776800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_14_rows b139_14_labels]
    decide +kernel

def b139_15_rows : List Row := [(row3 34 41 62), (row3 34 41 63), (row3 34 42 43), (row3 34 42 44), (row3 34 42 45), (row3 34 42 46), (row3 34 42 47), (row3 34 42 48), (row3 34 42 49), (row3 34 42 50), (row3 34 42 51), (row3 34 42 52), (row3 34 42 53), (row3 34 42 54), (row3 34 42 55), (row3 34 42 56)]

def b139_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 306 309 309), (row3 180 180 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b139_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b139_15_rows b139_15_labels 1132517767386618204190084800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b139_15_rows b139_15_labels]
    decide +kernel

theorem checked139 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_139 QuarticIntegerComputationalData.ids64_139 174830620118162986082894872050 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b139_00_rows ++ b139_01_rows) ++ (b139_02_rows ++ b139_03_rows)) ++ ((b139_04_rows ++ b139_05_rows) ++ (b139_06_rows ++ b139_07_rows))) ++ (((b139_08_rows ++ b139_09_rows) ++ (b139_10_rows ++ b139_11_rows)) ++ ((b139_12_rows ++ b139_13_rows) ++ (b139_14_rows ++ b139_15_rows))))
    ((((b139_00_labels ++ b139_01_labels) ++ (b139_02_labels ++ b139_03_labels)) ++ ((b139_04_labels ++ b139_05_labels) ++ (b139_06_labels ++ b139_07_labels))) ++ (((b139_08_labels ++ b139_09_labels) ++ (b139_10_labels ++ b139_11_labels)) ++ ((b139_12_labels ++ b139_13_labels) ++ (b139_14_labels ++ b139_15_labels)))) 174830620118162986082894872050
  exact ((((b139_00_checked.append (c := 882191819120944761780057000) b139_01_checked (by decide +kernel)).append (c := 135241218731633239668611687850) (b139_02_checked.append (c := 134359026912512294906831630850) b139_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 135249220536679368928306513350) ((b139_04_checked.append (c := 7993530718651337093500500) b139_05_checked (by decide +kernel)).append (c := 8001805046129259694825500) (b139_06_checked.append (c := 8274327477922601325000) b139_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 174830620118162986082894872050) (((b139_08_checked.append (c := 324375074249884818300000) b139_09_checked (by decide +kernel)).append (c := 11393753485055404743440100) (b139_10_checked.append (c := 11069378410805519925140100) b139_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 39581399581483617154588358700) ((b139_12_checked.append (c := 17952695527586024398542057000) b139_13_checked (by decide +kernel)).append (c := 39570005827998561749844918600) (b139_14_checked.append (c := 21617310300412537351302861600) b139_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b140_00_rows : List Row := [(row3 34 42 57), (row3 34 42 58), (row3 34 42 59), (row3 34 42 60), (row3 34 42 61), (row3 34 42 62), (row3 34 42 63), (row3 34 43 44), (row3 34 43 45), (row3 34 43 46), (row3 34 43 47), (row3 34 43 48), (row3 34 43 49), (row3 34 43 50), (row3 34 43 51), (row3 34 43 52)]

def b140_00_labels : List Row := [(row3 232 462 232), (row3 265 266 266), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 224 224 224), (row3 278 278 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_00_rows b140_00_labels 121237763953681059546585600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_00_rows b140_00_labels]
    decide +kernel

def b140_01_rows : List Row := [(row3 34 43 53), (row3 34 43 54), (row3 34 43 55), (row3 34 43 56), (row3 34 43 57), (row3 34 43 58), (row3 34 43 59), (row3 34 43 60), (row3 34 43 61), (row3 34 43 62), (row3 34 43 63), (row3 34 44 45), (row3 34 44 46), (row3 34 44 47), (row3 34 44 48), (row3 34 44 49)]

def b140_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246)]

theorem b140_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_01_rows b140_01_labels 1244510517376698921675000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_01_rows b140_01_labels]
    decide +kernel

def b140_02_rows : List Row := [(row3 34 44 50), (row3 34 44 51), (row3 34 44 52), (row3 34 44 53), (row3 34 44 54), (row3 34 44 55), (row3 34 44 56), (row3 34 44 57), (row3 34 44 58), (row3 34 44 59), (row3 34 44 60), (row3 34 44 61), (row3 34 44 62), (row3 34 44 63), (row3 34 45 46), (row3 34 45 47)]

def b140_02_labels : List Row := [(row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_02_rows b140_02_labels 427364335170120581581500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_02_rows b140_02_labels]
    decide +kernel

def b140_03_rows : List Row := [(row3 34 45 48), (row3 34 45 49), (row3 34 45 50), (row3 34 45 51), (row3 34 45 52), (row3 34 45 53), (row3 34 45 54), (row3 34 45 55), (row3 34 45 56), (row3 34 45 57), (row3 34 45 58), (row3 34 45 59), (row3 34 45 60), (row3 34 45 61), (row3 34 45 62), (row3 34 45 63)]

def b140_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_03_rows b140_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_03_rows b140_03_labels]
    decide +kernel

def b140_04_rows : List Row := [(row3 34 46 47), (row3 34 46 48), (row3 34 46 49), (row3 34 46 50), (row3 34 46 51), (row3 34 46 52), (row3 34 46 53), (row3 34 46 54), (row3 34 46 55), (row3 34 46 56), (row3 34 46 57), (row3 34 46 58), (row3 34 46 59), (row3 34 46 60), (row3 34 46 61), (row3 34 46 62)]

def b140_04_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_04_rows b140_04_labels 419105409451888813749000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_04_rows b140_04_labels]
    decide +kernel

def b140_05_rows : List Row := [(row3 34 46 63), (row3 34 47 48), (row3 34 47 49), (row3 34 47 50), (row3 34 47 51), (row3 34 47 52), (row3 34 47 53), (row3 34 47 54), (row3 34 47 55), (row3 34 47 56), (row3 34 47 57), (row3 34 47 58), (row3 34 47 59), (row3 34 47 60), (row3 34 47 61), (row3 34 47 62)]

def b140_05_labels : List Row := [(row3 462 462 462), (row3 278 462 278), (row3 224 224 224), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_05_rows b140_05_labels 9810798184027213891232400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_05_rows b140_05_labels]
    decide +kernel

def b140_06_rows : List Row := [(row3 34 47 63), (row3 34 48 49), (row3 34 48 50), (row3 34 48 51), (row3 34 48 52), (row3 34 48 53), (row3 34 48 54), (row3 34 48 55), (row3 34 48 56), (row3 34 48 57), (row3 34 48 58), (row3 34 48 59), (row3 34 48 60), (row3 34 48 61), (row3 34 48 62), (row3 34 48 63)]

def b140_06_labels : List Row := [(row3 462 462 462), (row3 368 114 86), (row3 278 278 462), (row3 237 237 462), (row3 462 462 462), (row3 237 237 462), (row3 265 265 462), (row3 180 180 462), (row3 180 180 462), (row3 300 278 288), (row3 228 228 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 278 278 462)]

theorem b140_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_06_rows b140_06_labels 11171471561642656035651910320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_06_rows b140_06_labels]
    decide +kernel

def b140_07_rows : List Row := [(row3 34 49 50), (row3 34 49 51), (row3 34 49 52), (row3 34 49 53), (row3 34 49 54), (row3 34 49 55), (row3 34 49 56), (row3 34 49 57), (row3 34 49 58), (row3 34 49 59), (row3 34 49 60), (row3 34 49 61), (row3 34 49 62), (row3 34 49 63), (row3 34 50 51), (row3 34 50 52)]

def b140_07_labels : List Row := [(row3 368 114 86), (row3 289 291 291), (row3 234 234 234), (row3 462 244 244), (row3 234 234 234), (row3 289 291 291), (row3 306 309 309), (row3 399 83 157), (row3 319 320 320), (row3 224 224 224), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 224 224 224), (row3 180 462 180), (row3 265 462 265)]

theorem b140_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_07_rows b140_07_labels 31040068441772432755199637900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_07_rows b140_07_labels]
    decide +kernel

def b140_08_rows : List Row := [(row3 34 50 53), (row3 34 50 54), (row3 34 50 55), (row3 34 50 56), (row3 34 50 57), (row3 34 50 58), (row3 34 50 59), (row3 34 50 60), (row3 34 50 61), (row3 34 50 62), (row3 34 50 63), (row3 34 51 52), (row3 34 51 53), (row3 34 51 54), (row3 34 51 55), (row3 34 51 56)]

def b140_08_labels : List Row := [(row3 237 462 237), (row3 462 462 462), (row3 237 462 237), (row3 234 462 234), (row3 300 462 300), (row3 370 88 211), (row3 278 462 278), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_08_rows b140_08_labels 9639578098876247825349699360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_08_rows b140_08_labels]
    decide +kernel

def b140_09_rows : List Row := [(row3 34 51 57), (row3 34 51 58), (row3 34 51 59), (row3 34 51 60), (row3 34 51 61), (row3 34 51 62), (row3 34 51 63), (row3 34 52 53), (row3 34 52 54), (row3 34 52 55), (row3 34 52 56), (row3 34 52 57), (row3 34 52 58), (row3 34 52 59), (row3 34 52 60), (row3 34 52 61)]

def b140_09_labels : List Row := [(row3 232 462 232), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_09_rows b140_09_labels 12043271573963899502439600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_09_rows b140_09_labels]
    decide +kernel

def b140_10_rows : List Row := [(row3 34 52 62), (row3 34 52 63), (row3 34 53 54), (row3 34 53 55), (row3 34 53 56), (row3 34 53 57), (row3 34 53 58), (row3 34 53 59), (row3 34 53 60), (row3 34 53 61), (row3 34 53 62), (row3 34 53 63), (row3 34 54 55), (row3 34 54 56), (row3 34 54 57), (row3 34 54 58)]

def b140_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_10_rows b140_10_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_10_rows b140_10_labels]
    decide +kernel

def b140_11_rows : List Row := [(row3 34 54 59), (row3 34 54 60), (row3 34 54 61), (row3 34 54 62), (row3 34 54 63), (row3 34 55 56), (row3 34 55 57), (row3 34 55 58), (row3 34 55 59), (row3 34 55 60), (row3 34 55 61), (row3 34 55 62), (row3 34 55 63), (row3 34 56 57), (row3 34 56 58), (row3 34 56 59)]

def b140_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 462 163), (row3 265 266 266), (row3 462 462 462)]

theorem b140_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_11_rows b140_11_labels 1087578753944392879737377400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_11_rows b140_11_labels]
    decide +kernel

def b140_12_rows : List Row := [(row3 34 56 60), (row3 34 56 61), (row3 34 56 62), (row3 34 56 63), (row3 34 57 58), (row3 34 57 59), (row3 34 57 60), (row3 34 57 61), (row3 34 57 62), (row3 34 57 63), (row3 34 58 59), (row3 34 58 60), (row3 34 58 61), (row3 34 58 62), (row3 34 58 63), (row3 34 59 60)]

def b140_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 356 159 91), (row3 273 273 462), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 273 273 462), (row3 180 154 154), (row3 265 266 266), (row3 237 237 237), (row3 462 242 242), (row3 237 237 237), (row3 462 462 462)]

theorem b140_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_12_rows b140_12_labels 7217781410713667741329821300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_12_rows b140_12_labels]
    decide +kernel

def b140_13_rows : List Row := [(row3 34 59 61), (row3 34 59 62), (row3 34 59 63), (row3 34 60 61), (row3 34 60 62), (row3 34 60 63), (row3 34 61 62), (row3 34 61 63), (row3 34 62 63), (row3 35 36 37), (row3 35 36 38), (row3 35 36 39), (row3 35 36 40), (row3 35 36 41), (row3 35 36 42), (row3 35 36 43)]

def b140_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_13_rows b140_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_13_rows b140_13_labels]
    decide +kernel

def b140_14_rows : List Row := [(row3 35 36 44), (row3 35 36 45), (row3 35 36 46), (row3 35 36 47), (row3 35 36 48), (row3 35 36 49), (row3 35 36 50), (row3 35 36 51), (row3 35 36 52), (row3 35 36 53), (row3 35 36 54), (row3 35 36 55), (row3 35 36 56), (row3 35 36 57), (row3 35 36 58), (row3 35 36 59)]

def b140_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_14_rows b140_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_14_rows b140_14_labels]
    decide +kernel

def b140_15_rows : List Row := [(row3 35 36 60), (row3 35 36 61), (row3 35 36 62), (row3 35 36 63), (row3 35 37 38), (row3 35 37 39), (row3 35 37 40), (row3 35 37 41), (row3 35 37 42), (row3 35 37 43), (row3 35 37 44), (row3 35 37 45), (row3 35 37 46), (row3 35 37 47), (row3 35 37 48), (row3 35 37 49)]

def b140_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b140_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b140_15_rows b140_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b140_15_rows b140_15_labels]
    decide +kernel

theorem checked140 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_140 QuarticIntegerComputationalData.ids64_140 60301668741023425021763434380 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b140_00_rows ++ b140_01_rows) ++ (b140_02_rows ++ b140_03_rows)) ++ ((b140_04_rows ++ b140_05_rows) ++ (b140_06_rows ++ b140_07_rows))) ++ (((b140_08_rows ++ b140_09_rows) ++ (b140_10_rows ++ b140_11_rows)) ++ ((b140_12_rows ++ b140_13_rows) ++ (b140_14_rows ++ b140_15_rows))))
    ((((b140_00_labels ++ b140_01_labels) ++ (b140_02_labels ++ b140_03_labels)) ++ ((b140_04_labels ++ b140_05_labels) ++ (b140_06_labels ++ b140_07_labels))) ++ (((b140_08_labels ++ b140_09_labels) ++ (b140_10_labels ++ b140_11_labels)) ++ ((b140_12_labels ++ b140_13_labels) ++ (b140_14_labels ++ b140_15_labels)))) 60301668741023425021763434380
  exact ((((b140_00_checked.append (c := 122482274471057758468260600) b140_01_checked (by decide +kernel)).append (c := 122909638806227879049842100) (b140_02_checked.append (c := 427364335170120581581500) b140_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 42344679545814795772606371720) ((b140_04_checked.append (c := 10229903593479102704981400) b140_05_checked (by decide +kernel)).append (c := 42221769907008567893556529620) (b140_06_checked.append (c := 42211540003415088790851548220) b140_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 60301668741023425021763434380) (((b140_08_checked.append (c := 9651621370450211724852138960) b140_09_checked (by decide +kernel)).append (c := 10739207784494961507827241360) (b140_10_checked.append (c := 1087586414044749782975102400) b140_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 17956989195208629249157062660) ((b140_12_checked.append (c := 7217781410713667741329821300) b140_13_checked (by decide +kernel)).append (c := 7217781410713667741329821300) (b140_14_checked.append (c := 0) b140_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b141_00_rows : List Row := [(row3 35 37 50), (row3 35 37 51), (row3 35 37 52), (row3 35 37 53), (row3 35 37 54), (row3 35 37 55), (row3 35 37 56), (row3 35 37 57), (row3 35 37 58), (row3 35 37 59), (row3 35 37 60), (row3 35 37 61), (row3 35 37 62), (row3 35 37 63), (row3 35 38 39), (row3 35 38 40)]

def b141_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243)]

theorem b141_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_00_rows b141_00_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_00_rows b141_00_labels]
    decide +kernel

def b141_01_rows : List Row := [(row3 35 38 41), (row3 35 38 42), (row3 35 38 43), (row3 35 38 44), (row3 35 38 45), (row3 35 38 46), (row3 35 38 47), (row3 35 38 48), (row3 35 38 49), (row3 35 38 50), (row3 35 38 51), (row3 35 38 52), (row3 35 38 53), (row3 35 38 54), (row3 35 38 55), (row3 35 38 56)]

def b141_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_01_rows b141_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_01_rows b141_01_labels]
    decide +kernel

def b141_02_rows : List Row := [(row3 35 38 57), (row3 35 38 58), (row3 35 38 59), (row3 35 38 60), (row3 35 38 61), (row3 35 38 62), (row3 35 38 63), (row3 35 39 40), (row3 35 39 41), (row3 35 39 42), (row3 35 39 43), (row3 35 39 44), (row3 35 39 45), (row3 35 39 46), (row3 35 39 47), (row3 35 39 48)]

def b141_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_02_rows b141_02_labels 284005379848089539763000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_02_rows b141_02_labels]
    decide +kernel

def b141_03_rows : List Row := [(row3 35 39 49), (row3 35 39 50), (row3 35 39 51), (row3 35 39 52), (row3 35 39 53), (row3 35 39 54), (row3 35 39 55), (row3 35 39 56), (row3 35 39 57), (row3 35 39 58), (row3 35 39 59), (row3 35 39 60), (row3 35 39 61), (row3 35 39 62), (row3 35 39 63), (row3 35 40 41)]

def b141_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 254 10)]

theorem b141_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_03_rows b141_03_labels 517433184366115469454337500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_03_rows b141_03_labels]
    decide +kernel

def b141_04_rows : List Row := [(row3 35 40 42), (row3 35 40 43), (row3 35 40 44), (row3 35 40 45), (row3 35 40 46), (row3 35 40 47), (row3 35 40 48), (row3 35 40 49), (row3 35 40 50), (row3 35 40 51), (row3 35 40 52), (row3 35 40 53), (row3 35 40 54), (row3 35 40 55), (row3 35 40 56), (row3 35 40 57)]

def b141_04_labels : List Row := [(row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 263 263 462), (row3 263 263 462), (row3 225 236 228), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 238 238 462), (row3 243 243 462)]

theorem b141_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_04_rows b141_04_labels 42644354934445843759201500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_04_rows b141_04_labels]
    decide +kernel

def b141_05_rows : List Row := [(row3 35 40 58), (row3 35 40 59), (row3 35 40 60), (row3 35 40 61), (row3 35 40 62), (row3 35 40 63), (row3 35 41 42), (row3 35 41 43), (row3 35 41 44), (row3 35 41 45), (row3 35 41 46), (row3 35 41 47), (row3 35 41 48), (row3 35 41 49), (row3 35 41 50), (row3 35 41 51)]

def b141_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 284 462 284), (row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 235 462 235), (row3 232 462 232), (row3 117 11 214), (row3 223 228 232), (row3 246 462 246)]

theorem b141_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_05_rows b141_05_labels 1710076106430867491984094750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_05_rows b141_05_labels]
    decide +kernel

def b141_06_rows : List Row := [(row3 35 41 52), (row3 35 41 53), (row3 35 41 54), (row3 35 41 55), (row3 35 41 56), (row3 35 41 57), (row3 35 41 58), (row3 35 41 59), (row3 35 41 60), (row3 35 41 61), (row3 35 41 62), (row3 35 41 63), (row3 35 42 43), (row3 35 42 44), (row3 35 42 45), (row3 35 42 46)]

def b141_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 246 462 246), (row3 235 462 235), (row3 251 462 251), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_06_rows b141_06_labels 1708420826892808678176000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_06_rows b141_06_labels]
    decide +kernel

def b141_07_rows : List Row := [(row3 35 42 47), (row3 35 42 48), (row3 35 42 49), (row3 35 42 50), (row3 35 42 51), (row3 35 42 52), (row3 35 42 53), (row3 35 42 54), (row3 35 42 55), (row3 35 42 56), (row3 35 42 57), (row3 35 42 58), (row3 35 42 59), (row3 35 42 60), (row3 35 42 61), (row3 35 42 62)]

def b141_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_07_rows b141_07_labels 96869599284946534157164500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_07_rows b141_07_labels]
    decide +kernel

def b141_08_rows : List Row := [(row3 35 42 63), (row3 35 43 44), (row3 35 43 45), (row3 35 43 46), (row3 35 43 47), (row3 35 43 48), (row3 35 43 49), (row3 35 43 50), (row3 35 43 51), (row3 35 43 52), (row3 35 43 53), (row3 35 43 54), (row3 35 43 55), (row3 35 43 56), (row3 35 43 57), (row3 35 43 58)]

def b141_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 228 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246)]

theorem b141_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_08_rows b141_08_labels 7661357817415170983113500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_08_rows b141_08_labels]
    decide +kernel

def b141_09_rows : List Row := [(row3 35 43 59), (row3 35 43 60), (row3 35 43 61), (row3 35 43 62), (row3 35 43 63), (row3 35 44 45), (row3 35 44 46), (row3 35 44 47), (row3 35 44 48), (row3 35 44 49), (row3 35 44 50), (row3 35 44 51), (row3 35 44 52), (row3 35 44 53), (row3 35 44 54), (row3 35 44 55)]

def b141_09_labels : List Row := [(row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_09_rows b141_09_labels 632871204274213033684500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_09_rows b141_09_labels]
    decide +kernel

def b141_10_rows : List Row := [(row3 35 44 56), (row3 35 44 57), (row3 35 44 58), (row3 35 44 59), (row3 35 44 60), (row3 35 44 61), (row3 35 44 62), (row3 35 44 63), (row3 35 45 46), (row3 35 45 47), (row3 35 45 48), (row3 35 45 49), (row3 35 45 50), (row3 35 45 51), (row3 35 45 52), (row3 35 45 53)]

def b141_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_10_rows b141_10_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_10_rows b141_10_labels]
    decide +kernel

def b141_11_rows : List Row := [(row3 35 45 54), (row3 35 45 55), (row3 35 45 56), (row3 35 45 57), (row3 35 45 58), (row3 35 45 59), (row3 35 45 60), (row3 35 45 61), (row3 35 45 62), (row3 35 45 63), (row3 35 46 47), (row3 35 46 48), (row3 35 46 49), (row3 35 46 50), (row3 35 46 51), (row3 35 46 52)]

def b141_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_11_rows b141_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_11_rows b141_11_labels]
    decide +kernel

def b141_12_rows : List Row := [(row3 35 46 53), (row3 35 46 54), (row3 35 46 55), (row3 35 46 56), (row3 35 46 57), (row3 35 46 58), (row3 35 46 59), (row3 35 46 60), (row3 35 46 61), (row3 35 46 62), (row3 35 46 63), (row3 35 47 48), (row3 35 47 49), (row3 35 47 50), (row3 35 47 51), (row3 35 47 52)]

def b141_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_12_rows b141_12_labels 38992955600732418112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_12_rows b141_12_labels]
    decide +kernel

def b141_13_rows : List Row := [(row3 35 47 53), (row3 35 47 54), (row3 35 47 55), (row3 35 47 56), (row3 35 47 57), (row3 35 47 58), (row3 35 47 59), (row3 35 47 60), (row3 35 47 61), (row3 35 47 62), (row3 35 47 63), (row3 35 48 49), (row3 35 48 50), (row3 35 48 51), (row3 35 48 52), (row3 35 48 53)]

def b141_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 462 293), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b141_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_13_rows b141_13_labels 92102344014234500932711500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_13_rows b141_13_labels]
    decide +kernel

def b141_14_rows : List Row := [(row3 35 48 54), (row3 35 48 55), (row3 35 48 56), (row3 35 48 57), (row3 35 48 58), (row3 35 48 59), (row3 35 48 60), (row3 35 48 61), (row3 35 48 62), (row3 35 48 63), (row3 35 49 50), (row3 35 49 51), (row3 35 49 52), (row3 35 49 53), (row3 35 49 54), (row3 35 49 55)]

def b141_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 118 215 11), (row3 234 234 462), (row3 244 244 462), (row3 462 462 462), (row3 244 244 462), (row3 234 234 462)]

theorem b141_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_14_rows b141_14_labels 1613423479103035372701749250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_14_rows b141_14_labels]
    decide +kernel

def b141_15_rows : List Row := [(row3 35 49 56), (row3 35 49 57), (row3 35 49 58), (row3 35 49 59), (row3 35 49 60), (row3 35 49 61), (row3 35 49 62), (row3 35 49 63), (row3 35 50 51), (row3 35 50 52), (row3 35 50 53), (row3 35 50 54), (row3 35 50 55), (row3 35 50 56), (row3 35 50 57), (row3 35 50 58)]

def b141_15_labels : List Row := [(row3 228 228 462), (row3 293 293 462), (row3 223 228 232), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 293 462 293), (row3 234 462 234), (row3 244 462 244), (row3 462 462 462), (row3 244 462 244), (row3 248 462 248), (row3 228 462 228), (row3 117 11 214)]

theorem b141_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b141_15_rows b141_15_labels 1839274498740033115118912250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b141_15_rows b141_15_labels]
    decide +kernel

theorem checked141 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_141 QuarticIntegerComputationalData.ids64_141 5922173591493000881916990750 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b141_00_rows ++ b141_01_rows) ++ (b141_02_rows ++ b141_03_rows)) ++ ((b141_04_rows ++ b141_05_rows) ++ (b141_06_rows ++ b141_07_rows))) ++ (((b141_08_rows ++ b141_09_rows) ++ (b141_10_rows ++ b141_11_rows)) ++ ((b141_12_rows ++ b141_13_rows) ++ (b141_14_rows ++ b141_15_rows))))
    ((((b141_00_labels ++ b141_01_labels) ++ (b141_02_labels ++ b141_03_labels)) ++ ((b141_04_labels ++ b141_05_labels) ++ (b141_06_labels ++ b141_07_labels))) ++ (((b141_08_labels ++ b141_09_labels) ++ (b141_10_labels ++ b141_11_labels)) ++ ((b141_12_labels ++ b141_13_labels) ++ (b141_14_labels ++ b141_15_labels)))) 5922173591493000881916990750
  exact ((((b141_00_checked.append (c := 8274327477922601325000) b141_01_checked (by decide +kernel)).append (c := 517725464073441481595425500) (b141_02_checked.append (c := 517717189745963558994100500) b141_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 2369023945550594160174062250) ((b141_04_checked.append (c := 1752720461365313335743296250) b141_05_checked (by decide +kernel)).append (c := 1851298481477152678578636750) (b141_06_checked.append (c := 98578020111839342835340500) b141_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 5922173591493000881916990750) (((b141_08_checked.append (c := 8294229021689384016798000) b141_09_checked (by decide +kernel)).append (c := 8310331129503000571443000) (b141_10_checked.append (c := 16102107813616554645000) b141_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 3553149645942406721742928500) ((b141_12_checked.append (c := 92141336969835233350824000) b141_13_checked (by decide +kernel)).append (c := 3544839314812903721171485500) (b141_14_checked.append (c := 3452697977843068487820661500) b141_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b142_00_rows : List Row := [(row3 35 50 59), (row3 35 50 60), (row3 35 50 61), (row3 35 50 62), (row3 35 50 63), (row3 35 51 52), (row3 35 51 53), (row3 35 51 54), (row3 35 51 55), (row3 35 51 56), (row3 35 51 57), (row3 35 51 58), (row3 35 51 59), (row3 35 51 60), (row3 35 51 61), (row3 35 51 62)]

def b142_00_labels : List Row := [(row3 225 236 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 263 263 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_00_rows b142_00_labels 22998583249116857266735500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_00_rows b142_00_labels]
    decide +kernel

def b142_01_rows : List Row := [(row3 35 51 63), (row3 35 52 53), (row3 35 52 54), (row3 35 52 55), (row3 35 52 56), (row3 35 52 57), (row3 35 52 58), (row3 35 52 59), (row3 35 52 60), (row3 35 52 61), (row3 35 52 62), (row3 35 52 63), (row3 35 53 54), (row3 35 53 55), (row3 35 53 56), (row3 35 53 57)]

def b142_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_01_rows b142_01_labels 299986511582989977183000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_01_rows b142_01_labels]
    decide +kernel

def b142_02_rows : List Row := [(row3 35 53 58), (row3 35 53 59), (row3 35 53 60), (row3 35 53 61), (row3 35 53 62), (row3 35 53 63), (row3 35 54 55), (row3 35 54 56), (row3 35 54 57), (row3 35 54 58), (row3 35 54 59), (row3 35 54 60), (row3 35 54 61), (row3 35 54 62), (row3 35 54 63), (row3 35 55 56)]

def b142_02_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_02_rows b142_02_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_02_rows b142_02_labels]
    decide +kernel

def b142_03_rows : List Row := [(row3 35 55 57), (row3 35 55 58), (row3 35 55 59), (row3 35 55 60), (row3 35 55 61), (row3 35 55 62), (row3 35 55 63), (row3 35 56 57), (row3 35 56 58), (row3 35 56 59), (row3 35 56 60), (row3 35 56 61), (row3 35 56 62), (row3 35 56 63), (row3 35 57 58), (row3 35 57 59)]

def b142_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 284 462 284), (row3 238 238 462)]

theorem b142_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_03_rows b142_03_labels 64278611569512891437244000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_03_rows b142_03_labels]
    decide +kernel

def b142_04_rows : List Row := [(row3 35 57 60), (row3 35 57 61), (row3 35 57 62), (row3 35 57 63), (row3 35 58 59), (row3 35 58 60), (row3 35 58 61), (row3 35 58 62), (row3 35 58 63), (row3 35 59 60), (row3 35 59 61), (row3 35 59 62), (row3 35 59 63), (row3 35 60 61), (row3 35 60 62), (row3 35 60 63)]

def b142_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 171 254 10), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 263 462 263), (row3 238 462 238), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_04_rows b142_04_labels 537517548627797629394665500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_04_rows b142_04_labels]
    decide +kernel

def b142_05_rows : List Row := [(row3 35 61 62), (row3 35 61 63), (row3 35 62 63), (row3 36 37 38), (row3 36 37 39), (row3 36 37 40), (row3 36 37 41), (row3 36 37 42), (row3 36 37 43), (row3 36 37 44), (row3 36 37 45), (row3 36 37 46), (row3 36 37 47), (row3 36 37 48), (row3 36 37 49), (row3 36 37 50)]

def b142_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_05_rows b142_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_05_rows b142_05_labels]
    decide +kernel

def b142_06_rows : List Row := [(row3 36 37 51), (row3 36 37 52), (row3 36 37 53), (row3 36 37 54), (row3 36 37 55), (row3 36 37 56), (row3 36 37 57), (row3 36 37 58), (row3 36 37 59), (row3 36 37 60), (row3 36 37 61), (row3 36 37 62), (row3 36 37 63), (row3 36 38 39), (row3 36 38 40), (row3 36 38 41)]

def b142_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_06_rows b142_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_06_rows b142_06_labels]
    decide +kernel

def b142_07_rows : List Row := [(row3 36 38 42), (row3 36 38 43), (row3 36 38 44), (row3 36 38 45), (row3 36 38 46), (row3 36 38 47), (row3 36 38 48), (row3 36 38 49), (row3 36 38 50), (row3 36 38 51), (row3 36 38 52), (row3 36 38 53), (row3 36 38 54), (row3 36 38 55), (row3 36 38 56), (row3 36 38 57)]

def b142_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_07_rows b142_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_07_rows b142_07_labels]
    decide +kernel

def b142_08_rows : List Row := [(row3 36 38 58), (row3 36 38 59), (row3 36 38 60), (row3 36 38 61), (row3 36 38 62), (row3 36 38 63), (row3 36 39 40), (row3 36 39 41), (row3 36 39 42), (row3 36 39 43), (row3 36 39 44), (row3 36 39 45), (row3 36 39 46), (row3 36 39 47), (row3 36 39 48), (row3 36 39 49)]

def b142_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_08_rows b142_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_08_rows b142_08_labels]
    decide +kernel

def b142_09_rows : List Row := [(row3 36 39 50), (row3 36 39 51), (row3 36 39 52), (row3 36 39 53), (row3 36 39 54), (row3 36 39 55), (row3 36 39 56), (row3 36 39 57), (row3 36 39 58), (row3 36 39 59), (row3 36 39 60), (row3 36 39 61), (row3 36 39 62), (row3 36 39 63), (row3 36 40 41), (row3 36 40 42)]

def b142_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_09_rows b142_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_09_rows b142_09_labels]
    decide +kernel

def b142_10_rows : List Row := [(row3 36 40 43), (row3 36 40 44), (row3 36 40 45), (row3 36 40 46), (row3 36 40 47), (row3 36 40 48), (row3 36 40 49), (row3 36 40 50), (row3 36 40 51), (row3 36 40 52), (row3 36 40 53), (row3 36 40 54), (row3 36 40 55), (row3 36 40 56), (row3 36 40 57), (row3 36 40 58)]

def b142_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_10_rows b142_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_10_rows b142_10_labels]
    decide +kernel

def b142_11_rows : List Row := [(row3 36 40 59), (row3 36 40 60), (row3 36 40 61), (row3 36 40 62), (row3 36 40 63), (row3 36 41 42), (row3 36 41 43), (row3 36 41 44), (row3 36 41 45), (row3 36 41 46), (row3 36 41 47), (row3 36 41 48), (row3 36 41 49), (row3 36 41 50), (row3 36 41 51), (row3 36 41 52)]

def b142_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_11_rows b142_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_11_rows b142_11_labels]
    decide +kernel

def b142_12_rows : List Row := [(row3 36 41 53), (row3 36 41 54), (row3 36 41 55), (row3 36 41 56), (row3 36 41 57), (row3 36 41 58), (row3 36 41 59), (row3 36 41 60), (row3 36 41 61), (row3 36 41 62), (row3 36 41 63), (row3 36 42 43), (row3 36 42 44), (row3 36 42 45), (row3 36 42 46), (row3 36 42 47)]

def b142_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_12_rows b142_12_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_12_rows b142_12_labels]
    decide +kernel

def b142_13_rows : List Row := [(row3 36 42 48), (row3 36 42 49), (row3 36 42 50), (row3 36 42 51), (row3 36 42 52), (row3 36 42 53), (row3 36 42 54), (row3 36 42 55), (row3 36 42 56), (row3 36 42 57), (row3 36 42 58), (row3 36 42 59), (row3 36 42 60), (row3 36 42 61), (row3 36 42 62), (row3 36 42 63)]

def b142_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_13_rows b142_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_13_rows b142_13_labels]
    decide +kernel

def b142_14_rows : List Row := [(row3 36 43 44), (row3 36 43 45), (row3 36 43 46), (row3 36 43 47), (row3 36 43 48), (row3 36 43 49), (row3 36 43 50), (row3 36 43 51), (row3 36 43 52), (row3 36 43 53), (row3 36 43 54), (row3 36 43 55), (row3 36 43 56), (row3 36 43 57), (row3 36 43 58), (row3 36 43 59)]

def b142_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_14_rows b142_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_14_rows b142_14_labels]
    decide +kernel

def b142_15_rows : List Row := [(row3 36 43 60), (row3 36 43 61), (row3 36 43 62), (row3 36 43 63), (row3 36 44 45), (row3 36 44 46), (row3 36 44 47), (row3 36 44 48), (row3 36 44 49), (row3 36 44 50), (row3 36 44 51), (row3 36 44 52), (row3 36 44 53), (row3 36 44 54), (row3 36 44 55), (row3 36 44 56)]

def b142_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b142_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b142_15_rows b142_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b142_15_rows b142_15_labels]
    decide +kernel

theorem checked142 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_142 QuarticIntegerComputationalData.ids64_142 625102390058367271313553000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b142_00_rows ++ b142_01_rows) ++ (b142_02_rows ++ b142_03_rows)) ++ ((b142_04_rows ++ b142_05_rows) ++ (b142_06_rows ++ b142_07_rows))) ++ (((b142_08_rows ++ b142_09_rows) ++ (b142_10_rows ++ b142_11_rows)) ++ ((b142_12_rows ++ b142_13_rows) ++ (b142_14_rows ++ b142_15_rows))))
    ((((b142_00_labels ++ b142_01_labels) ++ (b142_02_labels ++ b142_03_labels)) ++ ((b142_04_labels ++ b142_05_labels) ++ (b142_06_labels ++ b142_07_labels))) ++ (((b142_08_labels ++ b142_09_labels) ++ (b142_10_labels ++ b142_11_labels)) ++ ((b142_12_labels ++ b142_13_labels) ++ (b142_14_labels ++ b142_15_labels)))) 625102390058367271313553000
  exact ((((b142_00_checked.append (c := 23298569760699847243918500) b142_01_checked (by decide +kernel)).append (c := 87584841430569641918887500) (b142_02_checked.append (c := 64286271669869794674969000) b142_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 625102390058367271313553000) ((b142_04_checked.append (c := 537517548627797629394665500) b142_05_checked (by decide +kernel)).append (c := 537517548627797629394665500) (b142_06_checked.append (c := 0) b142_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 625102390058367271313553000) (((b142_08_checked.append (c := 0) b142_09_checked (by decide +kernel)).append (c := 0) (b142_10_checked.append (c := 0) b142_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b142_12_checked.append (c := 0) b142_13_checked (by decide +kernel)).append (c := 0) (b142_14_checked.append (c := 0) b142_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b143_00_rows : List Row := [(row3 36 44 57), (row3 36 44 58), (row3 36 44 59), (row3 36 44 60), (row3 36 44 61), (row3 36 44 62), (row3 36 44 63), (row3 36 45 46), (row3 36 45 47), (row3 36 45 48), (row3 36 45 49), (row3 36 45 50), (row3 36 45 51), (row3 36 45 52), (row3 36 45 53), (row3 36 45 54)]

def b143_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_00_rows b143_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_00_rows b143_00_labels]
    decide +kernel

def b143_01_rows : List Row := [(row3 36 45 55), (row3 36 45 56), (row3 36 45 57), (row3 36 45 58), (row3 36 45 59), (row3 36 45 60), (row3 36 45 61), (row3 36 45 62), (row3 36 45 63), (row3 36 46 47), (row3 36 46 48), (row3 36 46 49), (row3 36 46 50), (row3 36 46 51), (row3 36 46 52), (row3 36 46 53)]

def b143_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_01_rows b143_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_01_rows b143_01_labels]
    decide +kernel

def b143_02_rows : List Row := [(row3 36 46 54), (row3 36 46 55), (row3 36 46 56), (row3 36 46 57), (row3 36 46 58), (row3 36 46 59), (row3 36 46 60), (row3 36 46 61), (row3 36 46 62), (row3 36 46 63), (row3 36 47 48), (row3 36 47 49), (row3 36 47 50), (row3 36 47 51), (row3 36 47 52), (row3 36 47 53)]

def b143_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_02_rows b143_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_02_rows b143_02_labels]
    decide +kernel

def b143_03_rows : List Row := [(row3 36 47 54), (row3 36 47 55), (row3 36 47 56), (row3 36 47 57), (row3 36 47 58), (row3 36 47 59), (row3 36 47 60), (row3 36 47 61), (row3 36 47 62), (row3 36 47 63), (row3 36 48 49), (row3 36 48 50), (row3 36 48 51), (row3 36 48 52), (row3 36 48 53), (row3 36 48 54)]

def b143_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_03_rows b143_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_03_rows b143_03_labels]
    decide +kernel

def b143_04_rows : List Row := [(row3 36 48 55), (row3 36 48 56), (row3 36 48 57), (row3 36 48 58), (row3 36 48 59), (row3 36 48 60), (row3 36 48 61), (row3 36 48 62), (row3 36 48 63), (row3 36 49 50), (row3 36 49 51), (row3 36 49 52), (row3 36 49 53), (row3 36 49 54), (row3 36 49 55), (row3 36 49 56)]

def b143_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_04_rows b143_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_04_rows b143_04_labels]
    decide +kernel

def b143_05_rows : List Row := [(row3 36 49 57), (row3 36 49 58), (row3 36 49 59), (row3 36 49 60), (row3 36 49 61), (row3 36 49 62), (row3 36 49 63), (row3 36 50 51), (row3 36 50 52), (row3 36 50 53), (row3 36 50 54), (row3 36 50 55), (row3 36 50 56), (row3 36 50 57), (row3 36 50 58), (row3 36 50 59)]

def b143_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_05_rows b143_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_05_rows b143_05_labels]
    decide +kernel

def b143_06_rows : List Row := [(row3 36 50 60), (row3 36 50 61), (row3 36 50 62), (row3 36 50 63), (row3 36 51 52), (row3 36 51 53), (row3 36 51 54), (row3 36 51 55), (row3 36 51 56), (row3 36 51 57), (row3 36 51 58), (row3 36 51 59), (row3 36 51 60), (row3 36 51 61), (row3 36 51 62), (row3 36 51 63)]

def b143_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_06_rows b143_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_06_rows b143_06_labels]
    decide +kernel

def b143_07_rows : List Row := [(row3 36 52 53), (row3 36 52 54), (row3 36 52 55), (row3 36 52 56), (row3 36 52 57), (row3 36 52 58), (row3 36 52 59), (row3 36 52 60), (row3 36 52 61), (row3 36 52 62), (row3 36 52 63), (row3 36 53 54), (row3 36 53 55), (row3 36 53 56), (row3 36 53 57), (row3 36 53 58)]

def b143_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_07_rows b143_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_07_rows b143_07_labels]
    decide +kernel

def b143_08_rows : List Row := [(row3 36 53 59), (row3 36 53 60), (row3 36 53 61), (row3 36 53 62), (row3 36 53 63), (row3 36 54 55), (row3 36 54 56), (row3 36 54 57), (row3 36 54 58), (row3 36 54 59), (row3 36 54 60), (row3 36 54 61), (row3 36 54 62), (row3 36 54 63), (row3 36 55 56), (row3 36 55 57)]

def b143_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_08_rows b143_08_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_08_rows b143_08_labels]
    decide +kernel

def b143_09_rows : List Row := [(row3 36 55 58), (row3 36 55 59), (row3 36 55 60), (row3 36 55 61), (row3 36 55 62), (row3 36 55 63), (row3 36 56 57), (row3 36 56 58), (row3 36 56 59), (row3 36 56 60), (row3 36 56 61), (row3 36 56 62), (row3 36 56 63), (row3 36 57 58), (row3 36 57 59), (row3 36 57 60)]

def b143_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_09_rows b143_09_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_09_rows b143_09_labels]
    decide +kernel

def b143_10_rows : List Row := [(row3 36 57 61), (row3 36 57 62), (row3 36 57 63), (row3 36 58 59), (row3 36 58 60), (row3 36 58 61), (row3 36 58 62), (row3 36 58 63), (row3 36 59 60), (row3 36 59 61), (row3 36 59 62), (row3 36 59 63), (row3 36 60 61), (row3 36 60 62), (row3 36 60 63), (row3 36 61 62)]

def b143_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_10_rows b143_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_10_rows b143_10_labels]
    decide +kernel

def b143_11_rows : List Row := [(row3 36 61 63), (row3 36 62 63), (row3 37 38 39), (row3 37 38 40), (row3 37 38 41), (row3 37 38 42), (row3 37 38 43), (row3 37 38 44), (row3 37 38 45), (row3 37 38 46), (row3 37 38 47), (row3 37 38 48), (row3 37 38 49), (row3 37 38 50), (row3 37 38 51), (row3 37 38 52)]

def b143_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_11_rows b143_11_labels 3867409411222473623709000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_11_rows b143_11_labels]
    decide +kernel

def b143_12_rows : List Row := [(row3 37 38 53), (row3 37 38 54), (row3 37 38 55), (row3 37 38 56), (row3 37 38 57), (row3 37 38 58), (row3 37 38 59), (row3 37 38 60), (row3 37 38 61), (row3 37 38 62), (row3 37 38 63), (row3 37 39 40), (row3 37 39 41), (row3 37 39 42), (row3 37 39 43), (row3 37 39 44)]

def b143_12_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_12_rows b143_12_labels 4499704358634134852455500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_12_rows b143_12_labels]
    decide +kernel

def b143_13_rows : List Row := [(row3 37 39 45), (row3 37 39 46), (row3 37 39 47), (row3 37 39 48), (row3 37 39 49), (row3 37 39 50), (row3 37 39 51), (row3 37 39 52), (row3 37 39 53), (row3 37 39 54), (row3 37 39 55), (row3 37 39 56), (row3 37 39 57), (row3 37 39 58), (row3 37 39 59), (row3 37 39 60)]

def b143_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_13_rows b143_13_labels 61708800319122667786321500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_13_rows b143_13_labels]
    decide +kernel

def b143_14_rows : List Row := [(row3 37 39 61), (row3 37 39 62), (row3 37 39 63), (row3 37 40 41), (row3 37 40 42), (row3 37 40 43), (row3 37 40 44), (row3 37 40 45), (row3 37 40 46), (row3 37 40 47), (row3 37 40 48), (row3 37 40 49), (row3 37 40 50), (row3 37 40 51), (row3 37 40 52), (row3 37 40 53)]

def b143_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 171 254 10), (row3 263 263 462), (row3 236 236 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b143_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_14_rows b143_14_labels 557962470196159101866470500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_14_rows b143_14_labels]
    decide +kernel

def b143_15_rows : List Row := [(row3 37 40 54), (row3 37 40 55), (row3 37 40 56), (row3 37 40 57), (row3 37 40 58), (row3 37 40 59), (row3 37 40 60), (row3 37 40 61), (row3 37 40 62), (row3 37 40 63), (row3 37 41 42), (row3 37 41 43), (row3 37 41 44), (row3 37 41 45), (row3 37 41 46), (row3 37 41 47)]

def b143_15_labels : List Row := [(row3 250 250 462), (row3 225 236 228), (row3 238 238 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462)]

theorem b143_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b143_15_rows b143_15_labels 2393244616027872702829500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b143_15_rows b143_15_labels]
    decide +kernel

theorem checked143 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_143 QuarticIntegerComputationalData.ids64_143 630431628901166250831786000 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b143_00_rows ++ b143_01_rows) ++ (b143_02_rows ++ b143_03_rows)) ++ ((b143_04_rows ++ b143_05_rows) ++ (b143_06_rows ++ b143_07_rows))) ++ (((b143_08_rows ++ b143_09_rows) ++ (b143_10_rows ++ b143_11_rows)) ++ ((b143_12_rows ++ b143_13_rows) ++ (b143_14_rows ++ b143_15_rows))))
    ((((b143_00_labels ++ b143_01_labels) ++ (b143_02_labels ++ b143_03_labels)) ++ ((b143_04_labels ++ b143_05_labels) ++ (b143_06_labels ++ b143_07_labels))) ++ (((b143_08_labels ++ b143_09_labels) ++ (b143_10_labels ++ b143_11_labels)) ++ ((b143_12_labels ++ b143_13_labels) ++ (b143_14_labels ++ b143_15_labels)))) 630431628901166250831786000
  exact ((((b143_00_checked.append (c := 0) b143_01_checked (by decide +kernel)).append (c := 0) (b143_02_checked.append (c := 0) b143_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 0) ((b143_04_checked.append (c := 0) b143_05_checked (by decide +kernel)).append (c := 0) (b143_06_checked.append (c := 0) b143_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 630431628901166250831786000) (((b143_08_checked.append (c := 0) b143_09_checked (by decide +kernel)).append (c := 3867409411222473623709000) (b143_10_checked.append (c := 3867409411222473623709000) b143_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 630431628901166250831786000) ((b143_12_checked.append (c := 66208504677756802638777000) b143_13_checked (by decide +kernel)).append (c := 626564219489943777208077000) (b143_14_checked.append (c := 560355714812186974569300000) b143_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b144_00_rows : List Row := [(row3 37 41 48), (row3 37 41 49), (row3 37 41 50), (row3 37 41 51), (row3 37 41 52), (row3 37 41 53), (row3 37 41 54), (row3 37 41 55), (row3 37 41 56), (row3 37 41 57), (row3 37 41 58), (row3 37 41 59), (row3 37 41 60), (row3 37 41 61), (row3 37 41 62), (row3 37 41 63)]

def b144_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_00_rows b144_00_labels 38992955600732418112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_00_rows b144_00_labels]
    decide +kernel

def b144_01_rows : List Row := [(row3 37 42 43), (row3 37 42 44), (row3 37 42 45), (row3 37 42 46), (row3 37 42 47), (row3 37 42 48), (row3 37 42 49), (row3 37 42 50), (row3 37 42 51), (row3 37 42 52), (row3 37 42 53), (row3 37 42 54), (row3 37 42 55), (row3 37 42 56), (row3 37 42 57), (row3 37 42 58)]

def b144_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_01_rows b144_01_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_01_rows b144_01_labels]
    decide +kernel

def b144_02_rows : List Row := [(row3 37 42 59), (row3 37 42 60), (row3 37 42 61), (row3 37 42 62), (row3 37 42 63), (row3 37 43 44), (row3 37 43 45), (row3 37 43 46), (row3 37 43 47), (row3 37 43 48), (row3 37 43 49), (row3 37 43 50), (row3 37 43 51), (row3 37 43 52), (row3 37 43 53), (row3 37 43 54)]

def b144_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_02_rows b144_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_02_rows b144_02_labels]
    decide +kernel

def b144_03_rows : List Row := [(row3 37 43 55), (row3 37 43 56), (row3 37 43 57), (row3 37 43 58), (row3 37 43 59), (row3 37 43 60), (row3 37 43 61), (row3 37 43 62), (row3 37 43 63), (row3 37 44 45), (row3 37 44 46), (row3 37 44 47), (row3 37 44 48), (row3 37 44 49), (row3 37 44 50), (row3 37 44 51)]

def b144_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_03_rows b144_03_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_03_rows b144_03_labels]
    decide +kernel

def b144_04_rows : List Row := [(row3 37 44 52), (row3 37 44 53), (row3 37 44 54), (row3 37 44 55), (row3 37 44 56), (row3 37 44 57), (row3 37 44 58), (row3 37 44 59), (row3 37 44 60), (row3 37 44 61), (row3 37 44 62), (row3 37 44 63), (row3 37 45 46), (row3 37 45 47), (row3 37 45 48), (row3 37 45 49)]

def b144_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_04_rows b144_04_labels 1777635757237797601033500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_04_rows b144_04_labels]
    decide +kernel

def b144_05_rows : List Row := [(row3 37 45 50), (row3 37 45 51), (row3 37 45 52), (row3 37 45 53), (row3 37 45 54), (row3 37 45 55), (row3 37 45 56), (row3 37 45 57), (row3 37 45 58), (row3 37 45 59), (row3 37 45 60), (row3 37 45 61), (row3 37 45 62), (row3 37 45 63), (row3 37 46 47), (row3 37 46 48)]

def b144_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 246 462 246), (row3 462 462 462), (row3 284 284 462), (row3 462 462 462)]

theorem b144_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_05_rows b144_05_labels 70542787623969976628710500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_05_rows b144_05_labels]
    decide +kernel

def b144_06_rows : List Row := [(row3 37 46 49), (row3 37 46 50), (row3 37 46 51), (row3 37 46 52), (row3 37 46 53), (row3 37 46 54), (row3 37 46 55), (row3 37 46 56), (row3 37 46 57), (row3 37 46 58), (row3 37 46 59), (row3 37 46 60), (row3 37 46 61), (row3 37 46 62), (row3 37 46 63), (row3 37 47 48)]

def b144_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 293 293 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 235 462 235), (row3 462 462 462), (row3 232 462 232)]

theorem b144_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_06_rows b144_06_labels 98150251417844087405668500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_06_rows b144_06_labels]
    decide +kernel

def b144_07_rows : List Row := [(row3 37 47 49), (row3 37 47 50), (row3 37 47 51), (row3 37 47 52), (row3 37 47 53), (row3 37 47 54), (row3 37 47 55), (row3 37 47 56), (row3 37 47 57), (row3 37 47 58), (row3 37 47 59), (row3 37 47 60), (row3 37 47 61), (row3 37 47 62), (row3 37 47 63), (row3 37 48 49)]

def b144_07_labels : List Row := [(row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 223 228 232), (row3 117 11 214), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 462 251), (row3 235 462 235), (row3 462 462 462)]

theorem b144_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_07_rows b144_07_labels 1646191845153361792607334750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_07_rows b144_07_labels]
    decide +kernel

def b144_08_rows : List Row := [(row3 37 48 50), (row3 37 48 51), (row3 37 48 52), (row3 37 48 53), (row3 37 48 54), (row3 37 48 55), (row3 37 48 56), (row3 37 48 57), (row3 37 48 58), (row3 37 48 59), (row3 37 48 60), (row3 37 48 61), (row3 37 48 62), (row3 37 48 63), (row3 37 49 50), (row3 37 49 51)]

def b144_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 293 462 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_08_rows b144_08_labels 92141002329153392520166500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_08_rows b144_08_labels]
    decide +kernel

def b144_09_rows : List Row := [(row3 37 49 52), (row3 37 49 53), (row3 37 49 54), (row3 37 49 55), (row3 37 49 56), (row3 37 49 57), (row3 37 49 58), (row3 37 49 59), (row3 37 49 60), (row3 37 49 61), (row3 37 49 62), (row3 37 49 63), (row3 37 50 51), (row3 37 50 52), (row3 37 50 53), (row3 37 50 54)]

def b144_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_09_rows b144_09_labels 427364335170120581581500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_09_rows b144_09_labels]
    decide +kernel

def b144_10_rows : List Row := [(row3 37 50 55), (row3 37 50 56), (row3 37 50 57), (row3 37 50 58), (row3 37 50 59), (row3 37 50 60), (row3 37 50 61), (row3 37 50 62), (row3 37 50 63), (row3 37 51 52), (row3 37 51 53), (row3 37 51 54), (row3 37 51 55), (row3 37 51 56), (row3 37 51 57), (row3 37 51 58)]

def b144_10_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b144_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_10_rows b144_10_labels 22980301070709713175000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_10_rows b144_10_labels]
    decide +kernel

def b144_11_rows : List Row := [(row3 37 51 59), (row3 37 51 60), (row3 37 51 61), (row3 37 51 62), (row3 37 51 63), (row3 37 52 53), (row3 37 52 54), (row3 37 52 55), (row3 37 52 56), (row3 37 52 57), (row3 37 52 58), (row3 37 52 59), (row3 37 52 60), (row3 37 52 61), (row3 37 52 62), (row3 37 52 63)]

def b144_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 246 462 246), (row3 462 462 462)]

theorem b144_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_11_rows b144_11_labels 735010947110013796489500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_11_rows b144_11_labels]
    decide +kernel

def b144_12_rows : List Row := [(row3 37 53 54), (row3 37 53 55), (row3 37 53 56), (row3 37 53 57), (row3 37 53 58), (row3 37 53 59), (row3 37 53 60), (row3 37 53 61), (row3 37 53 62), (row3 37 53 63), (row3 37 54 55), (row3 37 54 56), (row3 37 54 57), (row3 37 54 58), (row3 37 54 59), (row3 37 54 60)]

def b144_12_labels : List Row := [(row3 293 293 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 263 263 462), (row3 232 462 232), (row3 462 462 462), (row3 118 11 215), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248)]

theorem b144_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_12_rows b144_12_labels 1727117665968463099951836750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_12_rows b144_12_labels]
    decide +kernel

def b144_13_rows : List Row := [(row3 37 54 61), (row3 37 54 62), (row3 37 54 63), (row3 37 55 56), (row3 37 55 57), (row3 37 55 58), (row3 37 55 59), (row3 37 55 60), (row3 37 55 61), (row3 37 55 62), (row3 37 55 63), (row3 37 56 57), (row3 37 56 58), (row3 37 56 59), (row3 37 56 60), (row3 37 56 61)]

def b144_13_labels : List Row := [(row3 225 236 228), (row3 117 11 214), (row3 228 462 228), (row3 228 228 462), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 250 462), (row3 223 228 232), (row3 293 293 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462)]

theorem b144_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_13_rows b144_13_labels 1747733744383809977606642250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_13_rows b144_13_labels]
    decide +kernel

def b144_14_rows : List Row := [(row3 37 56 62), (row3 37 56 63), (row3 37 57 58), (row3 37 57 59), (row3 37 57 60), (row3 37 57 61), (row3 37 57 62), (row3 37 57 63), (row3 37 58 59), (row3 37 58 60), (row3 37 58 61), (row3 37 58 62), (row3 37 58 63), (row3 37 59 60), (row3 37 59 61), (row3 37 59 62)]

def b144_14_labels : List Row := [(row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 243 462 243)]

theorem b144_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_14_rows b144_14_labels 1792876258349050337673000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_14_rows b144_14_labels]
    decide +kernel

def b144_15_rows : List Row := [(row3 37 59 63), (row3 37 60 61), (row3 37 60 62), (row3 37 60 63), (row3 37 61 62), (row3 37 61 63), (row3 37 62 63), (row3 38 39 40), (row3 38 39 41), (row3 38 39 42), (row3 38 39 43), (row3 38 39 44), (row3 38 39 45), (row3 38 39 46), (row3 38 39 47), (row3 38 39 48)]

def b144_15_labels : List Row := [(row3 462 462 462), (row3 263 263 462), (row3 235 462 235), (row3 462 462 462), (row3 171 10 254), (row3 238 462 238), (row3 284 284 462), (row3 278 279 279), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 163 462), (row3 234 462 234)]

theorem b144_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b144_15_rows b144_15_labels 1752864558973215756332891100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b144_15_rows b144_15_labels]
    decide +kernel

theorem checked144 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_144 QuarticIntegerComputationalData.ids64_144 7139560478612527027293685350 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b144_00_rows ++ b144_01_rows) ++ (b144_02_rows ++ b144_03_rows)) ++ ((b144_04_rows ++ b144_05_rows) ++ (b144_06_rows ++ b144_07_rows))) ++ (((b144_08_rows ++ b144_09_rows) ++ (b144_10_rows ++ b144_11_rows)) ++ ((b144_12_rows ++ b144_13_rows) ++ (b144_14_rows ++ b144_15_rows))))
    ((((b144_00_labels ++ b144_01_labels) ++ (b144_02_labels ++ b144_03_labels)) ++ ((b144_04_labels ++ b144_05_labels) ++ (b144_06_labels ++ b144_07_labels))) ++ (((b144_08_labels ++ b144_09_labels) ++ (b144_10_labels ++ b144_11_labels)) ++ ((b144_12_labels ++ b144_13_labels) ++ (b144_14_labels ++ b144_15_labels)))) 7139560478612527027293685350
  exact ((((b144_00_checked.append (c := 46653055957635655837500) b144_01_checked (by decide +kernel)).append (c := 62755163771252210482500) (b144_02_checked.append (c := 16102107813616554645000) b144_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1816725275116184906453229750) ((b144_04_checked.append (c := 72320423381207774229744000) b144_05_checked (by decide +kernel)).append (c := 1816662519952413654242747250) (b144_06_checked.append (c := 1744342096571205880013003250) b144_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7139560478612527027293685350) (((b144_08_checked.append (c := 92568366664323513101748000) b144_09_checked (by decide +kernel)).append (c := 93326357912504236611412500) (b144_10_checked.append (c := 757991248180723509664500) b144_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 5322835203496342120840455600) ((b144_12_checked.append (c := 3474851410352273077558479000) b144_13_checked (by decide +kernel)).append (c := 5229508845583837884229043100) (b144_14_checked.append (c := 1754657435231564806670564100) b144_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
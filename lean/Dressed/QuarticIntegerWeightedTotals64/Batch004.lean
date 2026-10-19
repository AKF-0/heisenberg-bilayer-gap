import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch003
import Dressed.QuarticIntegerComputationalData64.Batch004


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b033_00_rows : List Row := [(row3 5 34 63), (row3 5 35 36), (row3 5 35 37), (row3 5 35 38), (row3 5 35 39), (row3 5 35 40), (row3 5 35 41), (row3 5 35 42), (row3 5 35 43), (row3 5 35 44), (row3 5 35 45), (row3 5 35 46), (row3 5 35 47), (row3 5 35 48), (row3 5 35 49), (row3 5 35 50)]

def b033_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_00_rows b033_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_00_rows b033_00_labels]
    decide +kernel

def b033_01_rows : List Row := [(row3 5 35 51), (row3 5 35 52), (row3 5 35 53), (row3 5 35 54), (row3 5 35 55), (row3 5 35 56), (row3 5 35 57), (row3 5 35 58), (row3 5 35 59), (row3 5 35 60), (row3 5 35 61), (row3 5 35 62), (row3 5 35 63), (row3 5 36 37), (row3 5 36 38), (row3 5 36 39)]

def b033_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_01_rows b033_01_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_01_rows b033_01_labels]
    decide +kernel

def b033_02_rows : List Row := [(row3 5 36 40), (row3 5 36 41), (row3 5 36 42), (row3 5 36 43), (row3 5 36 44), (row3 5 36 45), (row3 5 36 46), (row3 5 36 47), (row3 5 36 48), (row3 5 36 49), (row3 5 36 50), (row3 5 36 51), (row3 5 36 52), (row3 5 36 53), (row3 5 36 54), (row3 5 36 55)]

def b033_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_02_rows b033_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_02_rows b033_02_labels]
    decide +kernel

def b033_03_rows : List Row := [(row3 5 36 56), (row3 5 36 57), (row3 5 36 58), (row3 5 36 59), (row3 5 36 60), (row3 5 36 61), (row3 5 36 62), (row3 5 36 63), (row3 5 37 38), (row3 5 37 39), (row3 5 37 40), (row3 5 37 41), (row3 5 37 42), (row3 5 37 43), (row3 5 37 44), (row3 5 37 45)]

def b033_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 240 462)]

theorem b033_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_03_rows b033_03_labels 35608273208787467437500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_03_rows b033_03_labels]
    decide +kernel

def b033_04_rows : List Row := [(row3 5 37 46), (row3 5 37 47), (row3 5 37 48), (row3 5 37 49), (row3 5 37 50), (row3 5 37 51), (row3 5 37 52), (row3 5 37 53), (row3 5 37 54), (row3 5 37 55), (row3 5 37 56), (row3 5 37 57), (row3 5 37 58), (row3 5 37 59), (row3 5 37 60), (row3 5 37 61)]

def b033_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 239 239 462), (row3 249 249 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 238 238 462), (row3 254 203 8)]

theorem b033_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_04_rows b033_04_labels 170531378749803878680396500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_04_rows b033_04_labels]
    decide +kernel

def b033_05_rows : List Row := [(row3 5 37 62), (row3 5 37 63), (row3 5 38 39), (row3 5 38 40), (row3 5 38 41), (row3 5 38 42), (row3 5 38 43), (row3 5 38 44), (row3 5 38 45), (row3 5 38 46), (row3 5 38 47), (row3 5 38 48), (row3 5 38 49), (row3 5 38 50), (row3 5 38 51), (row3 5 38 52)]

def b033_05_labels : List Row := [(row3 238 230 232), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_05_rows b033_05_labels 957517361318669267290500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_05_rows b033_05_labels]
    decide +kernel

def b033_06_rows : List Row := [(row3 5 38 53), (row3 5 38 54), (row3 5 38 55), (row3 5 38 56), (row3 5 38 57), (row3 5 38 58), (row3 5 38 59), (row3 5 38 60), (row3 5 38 61), (row3 5 38 62), (row3 5 38 63), (row3 5 39 40), (row3 5 39 41), (row3 5 39 42), (row3 5 39 43), (row3 5 39 44)]

def b033_06_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_06_rows b033_06_labels 11069378410805519925140100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_06_rows b033_06_labels]
    decide +kernel

def b033_07_rows : List Row := [(row3 5 39 45), (row3 5 39 46), (row3 5 39 47), (row3 5 39 48), (row3 5 39 49), (row3 5 39 50), (row3 5 39 51), (row3 5 39 52), (row3 5 39 53), (row3 5 39 54), (row3 5 39 55), (row3 5 39 56), (row3 5 39 57), (row3 5 39 58), (row3 5 39 59), (row3 5 39 60)]

def b033_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_07_rows b033_07_labels 495836240688545342728500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_07_rows b033_07_labels]
    decide +kernel

def b033_08_rows : List Row := [(row3 5 39 61), (row3 5 39 62), (row3 5 39 63), (row3 5 40 41), (row3 5 40 42), (row3 5 40 43), (row3 5 40 44), (row3 5 40 45), (row3 5 40 46), (row3 5 40 47), (row3 5 40 48), (row3 5 40 49), (row3 5 40 50), (row3 5 40 51), (row3 5 40 52), (row3 5 40 53)]

def b033_08_labels : List Row := [(row3 462 462 462), (row3 462 232 232), (row3 279 279 278), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 256 256 255), (row3 237 237 237), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_08_rows b033_08_labels 25281237558802266836430900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_08_rows b033_08_labels]
    decide +kernel

def b033_09_rows : List Row := [(row3 5 40 54), (row3 5 40 55), (row3 5 40 56), (row3 5 40 57), (row3 5 40 58), (row3 5 40 59), (row3 5 40 60), (row3 5 40 61), (row3 5 40 62), (row3 5 40 63), (row3 5 41 42), (row3 5 41 43), (row3 5 41 44), (row3 5 41 45), (row3 5 41 46), (row3 5 41 47)]

def b033_09_labels : List Row := [(row3 249 249 462), (row3 226 237 226), (row3 202 97 334), (row3 262 262 261), (row3 237 237 237), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 237 226 226), (row3 317 317 308), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_09_rows b033_09_labels 3102941400793076431421434200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_09_rows b033_09_labels]
    decide +kernel

def b033_10_rows : List Row := [(row3 5 41 48), (row3 5 41 49), (row3 5 41 50), (row3 5 41 51), (row3 5 41 52), (row3 5 41 53), (row3 5 41 54), (row3 5 41 55), (row3 5 41 56), (row3 5 41 57), (row3 5 41 58), (row3 5 41 59), (row3 5 41 60), (row3 5 41 61), (row3 5 41 62), (row3 5 41 63)]

def b033_10_labels : List Row := [(row3 238 462 238), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 250 462 250), (row3 254 10 171), (row3 236 462 236), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 228 225)]

theorem b033_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_10_rows b033_10_labels 519815915845015498423731000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_10_rows b033_10_labels]
    decide +kernel

def b033_11_rows : List Row := [(row3 5 42 43), (row3 5 42 44), (row3 5 42 45), (row3 5 42 46), (row3 5 42 47), (row3 5 42 48), (row3 5 42 49), (row3 5 42 50), (row3 5 42 51), (row3 5 42 52), (row3 5 42 53), (row3 5 42 54), (row3 5 42 55), (row3 5 42 56), (row3 5 42 57), (row3 5 42 58)]

def b033_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235)]

theorem b033_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_11_rows b033_11_labels 302049148632479576244000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_11_rows b033_11_labels]
    decide +kernel

def b033_12_rows : List Row := [(row3 5 42 59), (row3 5 42 60), (row3 5 42 61), (row3 5 42 62), (row3 5 42 63), (row3 5 43 44), (row3 5 43 45), (row3 5 43 46), (row3 5 43 47), (row3 5 43 48), (row3 5 43 49), (row3 5 43 50), (row3 5 43 51), (row3 5 43 52), (row3 5 43 53), (row3 5 43 54)]

def b033_12_labels : List Row := [(row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_12_rows b033_12_labels 28508345159883985575000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_12_rows b033_12_labels]
    decide +kernel

def b033_13_rows : List Row := [(row3 5 43 55), (row3 5 43 56), (row3 5 43 57), (row3 5 43 58), (row3 5 43 59), (row3 5 43 60), (row3 5 43 61), (row3 5 43 62), (row3 5 43 63), (row3 5 44 45), (row3 5 44 46), (row3 5 44 47), (row3 5 44 48), (row3 5 44 49), (row3 5 44 50), (row3 5 44 51)]

def b033_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_13_rows b033_13_labels 401774040209938496694000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_13_rows b033_13_labels]
    decide +kernel

def b033_14_rows : List Row := [(row3 5 44 52), (row3 5 44 53), (row3 5 44 54), (row3 5 44 55), (row3 5 44 56), (row3 5 44 57), (row3 5 44 58), (row3 5 44 59), (row3 5 44 60), (row3 5 44 61), (row3 5 44 62), (row3 5 44 63), (row3 5 45 46), (row3 5 45 47), (row3 5 45 48), (row3 5 45 49)]

def b033_14_labels : List Row := [(row3 243 243 462), (row3 238 238 462), (row3 250 250 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 247 462), (row3 236 236 462), (row3 254 171 10), (row3 236 225 228), (row3 243 243 462), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b033_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_14_rows b033_14_labels 519887132391433073358606000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_14_rows b033_14_labels]
    decide +kernel

def b033_15_rows : List Row := [(row3 5 45 50), (row3 5 45 51), (row3 5 45 52), (row3 5 45 53), (row3 5 45 54), (row3 5 45 55), (row3 5 45 56), (row3 5 45 57), (row3 5 45 58), (row3 5 45 59), (row3 5 45 60), (row3 5 45 61), (row3 5 45 62), (row3 5 45 63), (row3 5 46 47), (row3 5 46 48)]

def b033_15_labels : List Row := [(row3 462 462 462), (row3 242 462 242), (row3 237 237 237), (row3 256 255 256), (row3 226 226 237), (row3 249 462 249), (row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 202 334 97), (row3 317 308 317), (row3 237 226 226), (row3 462 462 462), (row3 462 462 462)]

theorem b033_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b033_15_rows b033_15_labels 3117506663088926573805703500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b033_15_rows b033_15_labels]
    decide +kernel

theorem checked033 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_033 QuarticIntegerComputationalData.ids64_033 7469262674574559469188736700 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b033_00_rows ++ b033_01_rows) ++ (b033_02_rows ++ b033_03_rows)) ++ ((b033_04_rows ++ b033_05_rows) ++ (b033_06_rows ++ b033_07_rows))) ++ (((b033_08_rows ++ b033_09_rows) ++ (b033_10_rows ++ b033_11_rows)) ++ ((b033_12_rows ++ b033_13_rows) ++ (b033_14_rows ++ b033_15_rows))))
    ((((b033_00_labels ++ b033_01_labels) ++ (b033_02_labels ++ b033_03_labels)) ++ ((b033_04_labels ++ b033_05_labels) ++ (b033_06_labels ++ b033_07_labels))) ++ (((b033_08_labels ++ b033_09_labels) ++ (b033_10_labels ++ b033_11_labels)) ++ ((b033_12_labels ++ b033_13_labels) ++ (b033_14_labels ++ b033_15_labels)))) 7469262674574559469188736700
  exact ((((b033_00_checked.append (c := 8274327477922601325000) b033_01_checked (by decide +kernel)).append (c := 43882600686710068762500) (b033_02_checked.append (c := 35608273208787467437500) b033_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 183097993363303323284318100) ((b033_04_checked.append (c := 171488896111122547947687000) b033_05_checked (by decide +kernel)).append (c := 183054110762616613215555600) (b033_06_checked.append (c := 11565214651494065267868600) b033_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 7469262674574559469188736700) (((b033_08_checked.append (c := 3128222638351878698257865100) b033_09_checked (by decide +kernel)).append (c := 3648340603345526676257840100) (b033_10_checked.append (c := 520117964993647977999975000) b033_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 7286164681211256145904418600) ((b033_12_checked.append (c := 430282385369822482269000) b033_13_checked (by decide +kernel)).append (c := 3637824077865729469646578500) (b033_14_checked.append (c := 3637393795480359647164309500) b033_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b034_00_rows : List Row := [(row3 5 46 49), (row3 5 46 50), (row3 5 46 51), (row3 5 46 52), (row3 5 46 53), (row3 5 46 54), (row3 5 46 55), (row3 5 46 56), (row3 5 46 57), (row3 5 46 58), (row3 5 46 59), (row3 5 46 60), (row3 5 46 61), (row3 5 46 62), (row3 5 46 63), (row3 5 47 48)]

def b034_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 238 238 462), (row3 294 294 462), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 254 171 10), (row3 148 145 137), (row3 310 310 306), (row3 238 462 238)]

theorem b034_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_00_rows b034_00_labels 900761638350707290172356920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_00_rows b034_00_labels]
    decide +kernel

def b034_01_rows : List Row := [(row3 5 47 49), (row3 5 47 50), (row3 5 47 51), (row3 5 47 52), (row3 5 47 53), (row3 5 47 54), (row3 5 47 55), (row3 5 47 56), (row3 5 47 57), (row3 5 47 58), (row3 5 47 59), (row3 5 47 60), (row3 5 47 61), (row3 5 47 62), (row3 5 47 63), (row3 5 48 49)]

def b034_01_labels : List Row := [(row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 228 462), (row3 294 462 294), (row3 254 10 171), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 310 306 310), (row3 148 137 145), (row3 266 265 266)]

theorem b034_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_01_rows b034_01_labels 943300056863351270174593320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_01_rows b034_01_labels]
    decide +kernel

def b034_02_rows : List Row := [(row3 5 48 50), (row3 5 48 51), (row3 5 48 52), (row3 5 48 53), (row3 5 48 54), (row3 5 48 55), (row3 5 48 56), (row3 5 48 57), (row3 5 48 58), (row3 5 48 59), (row3 5 48 60), (row3 5 48 61), (row3 5 48 62), (row3 5 48 63), (row3 5 49 50), (row3 5 49 51)]

def b034_02_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 302 265 302), (row3 336 428 72), (row3 190 199 198), (row3 268 265 268), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 318 315 318), (row3 110 109 111), (row3 244 244 462), (row3 462 462 462)]

theorem b034_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_02_rows b034_02_labels 102525049024270003237513913460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_02_rows b034_02_labels]
    decide +kernel

def b034_03_rows : List Row := [(row3 5 49 52), (row3 5 49 53), (row3 5 49 54), (row3 5 49 55), (row3 5 49 56), (row3 5 49 57), (row3 5 49 58), (row3 5 49 59), (row3 5 49 60), (row3 5 49 61), (row3 5 49 62), (row3 5 49 63), (row3 5 50 51), (row3 5 50 52), (row3 5 50 53), (row3 5 50 54)]

def b034_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 228 234 228), (row3 159 91 356), (row3 279 279 278), (row3 226 234 226), (row3 247 247 462), (row3 462 462 462), (row3 243 243 462), (row3 234 226 226), (row3 320 320 319), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b034_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_03_rows b034_03_labels 6542504081850582458139060000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_03_rows b034_03_labels]
    decide +kernel

def b034_04_rows : List Row := [(row3 5 50 55), (row3 5 50 56), (row3 5 50 57), (row3 5 50 58), (row3 5 50 59), (row3 5 50 60), (row3 5 50 61), (row3 5 50 62), (row3 5 50 63), (row3 5 51 52), (row3 5 51 53), (row3 5 51 54), (row3 5 51 55), (row3 5 51 56), (row3 5 51 57), (row3 5 51 58)]

def b034_04_labels : List Row := [(row3 246 462 246), (row3 258 10 172), (row3 235 462 235), (row3 285 462 285), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 232 228), (row3 244 244 462), (row3 237 237 462), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232)]

theorem b034_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_04_rows b034_04_labels 589860276888478535589393000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_04_rows b034_04_labels]
    decide +kernel

def b034_05_rows : List Row := [(row3 5 51 59), (row3 5 51 60), (row3 5 51 61), (row3 5 51 62), (row3 5 51 63), (row3 5 52 53), (row3 5 52 54), (row3 5 52 55), (row3 5 52 56), (row3 5 52 57), (row3 5 52 58), (row3 5 52 59), (row3 5 52 60), (row3 5 52 61), (row3 5 52 62), (row3 5 52 63)]

def b034_05_labels : List Row := [(row3 285 285 462), (row3 235 235 462), (row3 258 172 10), (row3 235 228 232), (row3 244 244 462), (row3 266 265 266), (row3 228 228 234), (row3 246 462 246), (row3 243 462 243), (row3 462 462 462), (row3 247 462 247), (row3 226 226 234), (row3 279 278 279), (row3 159 356 91), (row3 320 319 320), (row3 234 226 226)]

theorem b034_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_05_rows b034_05_labels 7172814845998564379944785900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_05_rows b034_05_labels]
    decide +kernel

def b034_06_rows : List Row := [(row3 5 53 54), (row3 5 53 55), (row3 5 53 56), (row3 5 53 57), (row3 5 53 58), (row3 5 53 59), (row3 5 53 60), (row3 5 53 61), (row3 5 53 62), (row3 5 53 63), (row3 5 54 55), (row3 5 54 56), (row3 5 54 57), (row3 5 54 58), (row3 5 54 59), (row3 5 54 60)]

def b034_06_labels : List Row := [(row3 302 302 265), (row3 232 462 232), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 268 268 265), (row3 190 198 199), (row3 336 72 428), (row3 110 111 109), (row3 318 318 315), (row3 119 11 216), (row3 260 10 173), (row3 235 462 235), (row3 245 462 245), (row3 234 234 234), (row3 283 278 283)]

theorem b034_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_06_rows b034_06_labels 105338817012208412655315248310 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_06_rows b034_06_labels]
    decide +kernel

def b034_07_rows : List Row := [(row3 5 54 61), (row3 5 54 62), (row3 5 54 63), (row3 5 55 56), (row3 5 55 57), (row3 5 55 58), (row3 5 55 59), (row3 5 55 60), (row3 5 55 61), (row3 5 55 62), (row3 5 55 63), (row3 5 56 57), (row3 5 56 58), (row3 5 56 59), (row3 5 56 60), (row3 5 56 61)]

def b034_07_labels : List Row := [(row3 158 356 89), (row3 395 407 415), (row3 120 112 120), (row3 158 89 356), (row3 283 283 278), (row3 234 234 234), (row3 245 245 462), (row3 235 235 462), (row3 260 173 10), (row3 120 120 112), (row3 395 415 407), (row3 359 73 429), (row3 155 332 93), (row3 259 204 8), (row3 236 236 462), (row3 269 186 9)]

theorem b034_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_07_rows b034_07_labels 227231330509662617448935162640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_07_rows b034_07_labels]
    decide +kernel

def b034_08_rows : List Row := [(row3 5 56 62), (row3 5 56 63), (row3 5 57 58), (row3 5 57 59), (row3 5 57 60), (row3 5 57 61), (row3 5 57 62), (row3 5 57 63), (row3 5 58 59), (row3 5 58 60), (row3 5 58 61), (row3 5 58 62), (row3 5 58 63), (row3 5 59 60), (row3 5 59 61), (row3 5 59 62)]

def b034_08_labels : List Row := [(row3 123 331 92), (row3 44 74 439), (row3 301 278 301), (row3 233 233 462), (row3 462 462 462), (row3 236 236 462), (row3 296 295 296), (row3 126 125 128), (row3 116 213 11), (row3 233 233 462), (row3 259 204 8), (row3 231 227 229), (row3 297 297 295), (row3 301 278 301), (row3 155 332 93), (row3 297 295 297)]

theorem b034_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_08_rows b034_08_labels 554942461646900982721578032550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_08_rows b034_08_labels]
    decide +kernel

def b034_09_rows : List Row := [(row3 5 59 63), (row3 5 60 61), (row3 5 60 62), (row3 5 60 63), (row3 5 61 62), (row3 5 61 63), (row3 5 62 63), (row3 6 7 8), (row3 6 7 9), (row3 6 7 10), (row3 6 7 11), (row3 6 7 12), (row3 6 7 13), (row3 6 7 14), (row3 6 7 15), (row3 6 7 16)]

def b034_09_labels : List Row := [(row3 231 229 227), (row3 359 73 429), (row3 126 128 125), (row3 296 296 295), (row3 44 439 74), (row3 123 92 331), (row3 40 438 413), (row3 460 22 450), (row3 26 453 47), (row3 435 41 95), (row3 163 193 193), (row3 435 95 41), (row3 26 47 453), (row3 460 450 22), (row3 18 19 19), (row3 28 444 37)]

theorem b034_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_09_rows b034_09_labels 3104230058950916352689978681582460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_09_rows b034_09_labels]
    decide +kernel

def b034_10_rows : List Row := [(row3 6 7 17), (row3 6 7 18), (row3 6 7 19), (row3 6 7 20), (row3 6 7 21), (row3 6 7 22), (row3 6 7 23), (row3 6 7 24), (row3 6 7 25), (row3 6 7 26), (row3 6 7 27), (row3 6 7 28), (row3 6 7 29), (row3 6 7 30), (row3 6 7 31), (row3 6 7 32)]

def b034_10_labels : List Row := [(row3 435 42 181), (row3 180 180 462), (row3 462 462 462), (row3 180 462 180), (row3 435 181 42), (row3 28 37 444), (row3 455 447 447), (row3 428 72 336), (row3 193 193 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 428 336 72), (row3 54 65 65), (row3 208 208 462)]

theorem b034_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_10_rows b034_10_labels 13167442204267320080307124010640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_10_rows b034_10_labels]
    decide +kernel

def b034_11_rows : List Row := [(row3 6 7 33), (row3 6 7 34), (row3 6 7 35), (row3 6 7 36), (row3 6 7 37), (row3 6 7 38), (row3 6 7 39), (row3 6 7 40), (row3 6 7 41), (row3 6 7 42), (row3 6 7 43), (row3 6 7 44), (row3 6 7 45), (row3 6 7 46), (row3 6 7 47), (row3 6 7 48)]

def b034_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 208 462 208), (row3 462 337 337), (row3 428 72 336), (row3 193 193 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 428 336 72), (row3 54 65 65), (row3 28 444 37)]

theorem b034_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_11_rows b034_11_labels 4970625497547653658600567292500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_11_rows b034_11_labels]
    decide +kernel

def b034_12_rows : List Row := [(row3 6 7 49), (row3 6 7 50), (row3 6 7 51), (row3 6 7 52), (row3 6 7 53), (row3 6 7 54), (row3 6 7 55), (row3 6 7 56), (row3 6 7 57), (row3 6 7 58), (row3 6 7 59), (row3 6 7 60), (row3 6 7 61), (row3 6 7 62), (row3 6 7 63), (row3 6 8 9)]

def b034_12_labels : List Row := [(row3 435 42 181), (row3 180 180 462), (row3 462 462 462), (row3 180 462 180), (row3 435 181 42), (row3 28 37 444), (row3 455 447 447), (row3 460 22 450), (row3 26 453 47), (row3 435 41 95), (row3 163 193 193), (row3 435 95 41), (row3 26 47 453), (row3 460 450 22), (row3 18 19 19), (row3 34 443 27)]

theorem b034_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_12_rows b034_12_labels 3116327357649020340296987568043020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_12_rows b034_12_labels]
    decide +kernel

def b034_13_rows : List Row := [(row3 6 8 10), (row3 6 8 11), (row3 6 8 12), (row3 6 8 13), (row3 6 8 14), (row3 6 8 15), (row3 6 8 16), (row3 6 8 17), (row3 6 8 18), (row3 6 8 19), (row3 6 8 20), (row3 6 8 21), (row3 6 8 22), (row3 6 8 23), (row3 6 8 24), (row3 6 8 25)]

def b034_13_labels : List Row := [(row3 401 78 427), (row3 155 332 93), (row3 289 299 299), (row3 123 331 92), (row3 419 63 433), (row3 451 442 24), (row3 37 444 28), (row3 410 59 431), (row3 114 368 86), (row3 462 284 284), (row3 234 462 234), (row3 289 305 305), (row3 108 367 84), (row3 411 60 432), (row3 385 77 426), (row3 122 369 86)]

theorem b034_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_13_rows b034_13_labels 40849227092677258379183360050620 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_13_rows b034_13_labels]
    decide +kernel

def b034_14_rows : List Row := [(row3 6 8 26), (row3 6 8 27), (row3 6 8 28), (row3 6 8 29), (row3 6 8 30), (row3 6 8 31), (row3 6 8 32), (row3 6 8 33), (row3 6 8 34), (row3 6 8 35), (row3 6 8 36), (row3 6 8 37), (row3 6 8 38), (row3 6 8 39), (row3 6 8 40), (row3 6 8 41)]

def b034_14_labels : List Row := [(row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 302 302), (row3 121 369 85), (row3 168 333 94), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 284 284), (row3 339 328 342), (row3 193 193 462)]

theorem b034_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_14_rows b034_14_labels 18624174572003378586376588950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_14_rows b034_14_labels]
    decide +kernel

def b034_15_rows : List Row := [(row3 6 8 42), (row3 6 8 43), (row3 6 8 44), (row3 6 8 45), (row3 6 8 46), (row3 6 8 47), (row3 6 8 48), (row3 6 8 49), (row3 6 8 50), (row3 6 8 51), (row3 6 8 52), (row3 6 8 53), (row3 6 8 54), (row3 6 8 55), (row3 6 8 56), (row3 6 8 57)]

def b034_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 191 193 235), (row3 68 76 69), (row3 387 360 390), (row3 180 180 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 140 140 178), (row3 388 362 392), (row3 455 447 447), (row3 49 62 52)]

theorem b034_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b034_15_rows b034_15_labels 7855967410956155099544282946920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b034_15_rows b034_15_labels]
    decide +kernel

theorem checked034 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_034 QuarticIntegerComputationalData.ids64_034 6288425489879050077283185323061210 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b034_00_rows ++ b034_01_rows) ++ (b034_02_rows ++ b034_03_rows)) ++ ((b034_04_rows ++ b034_05_rows) ++ (b034_06_rows ++ b034_07_rows))) ++ (((b034_08_rows ++ b034_09_rows) ++ (b034_10_rows ++ b034_11_rows)) ++ ((b034_12_rows ++ b034_13_rows) ++ (b034_14_rows ++ b034_15_rows))))
    ((((b034_00_labels ++ b034_01_labels) ++ (b034_02_labels ++ b034_03_labels)) ++ ((b034_04_labels ++ b034_05_labels) ++ (b034_06_labels ++ b034_07_labels))) ++ (((b034_08_labels ++ b034_09_labels) ++ (b034_10_labels ++ b034_11_labels)) ++ ((b034_12_labels ++ b034_13_labels) ++ (b034_14_labels ++ b034_15_labels)))) 6288425489879050077283185323061210
  exact ((((b034_00_checked.append (c := 1844061695214058560346950240) b034_01_checked (by decide +kernel)).append (c := 110911614801334644255999923700) (b034_02_checked.append (c := 109067553106120585695652973460) b034_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 451244437446092717275784513550) ((b034_04_checked.append (c := 7762675122887042915534178900) b034_05_checked (by decide +kernel)).append (c := 340332822644758073019784589850) (b034_06_checked.append (c := 332570147521871030104250410950) b034_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 6288425489879050077283185323061210) (((b034_08_checked.append (c := 3104785001412563253672700259615010) b034_09_checked (by decide +kernel)).append (c := 3122923069114378227411607950918150) (b034_10_checked.append (c := 18138067701814973738907691303140) b034_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 6287974245441603984565909538547660) ((b034_12_checked.append (c := 3157176584741697598676170928093640) b034_13_checked (by decide +kernel)).append (c := 3165051176327225757154301587629510) (b034_14_checked.append (c := 7874591585528158478130659535870) b034_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b035_00_rows : List Row := [(row3 6 8 58), (row3 6 8 59), (row3 6 8 60), (row3 6 8 61), (row3 6 8 62), (row3 6 8 63), (row3 6 9 10), (row3 6 9 11), (row3 6 9 12), (row3 6 9 13), (row3 6 9 14), (row3 6 9 15), (row3 6 9 16), (row3 6 9 17), (row3 6 9 18), (row3 6 9 19)]

def b035_00_labels : List Row := [(row3 387 361 391), (row3 191 193 235), (row3 289 291 291), (row3 133 132 137), (row3 409 394 414), (row3 48 61 50), (row3 127 126 137), (row3 288 288 462), (row3 233 233 462), (row3 288 288 462), (row3 123 331 92), (row3 402 404 403), (row3 351 350 348), (row3 127 126 137), (row3 300 300 462), (row3 232 232 462)]

theorem b035_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_00_rows b035_00_labels 3423631644671840719014509034750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_00_rows b035_00_labels]
    decide +kernel

def b035_01_rows : List Row := [(row3 6 9 20), (row3 6 9 21), (row3 6 9 22), (row3 6 9 23), (row3 6 9 24), (row3 6 9 25), (row3 6 9 26), (row3 6 9 27), (row3 6 9 28), (row3 6 9 29), (row3 6 9 30), (row3 6 9 31), (row3 6 9 32), (row3 6 9 33), (row3 6 9 34), (row3 6 9 35)]

def b035_01_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 288 288 462), (row3 142 141 136), (row3 197 196 190), (row3 288 288 462), (row3 232 232 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 273 273 462), (row3 261 261 462), (row3 236 236 462), (row3 462 462 462), (row3 462 462 462)]

theorem b035_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_01_rows b035_01_labels 532875051979975341656404560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_01_rows b035_01_labels]
    decide +kernel

def b035_02_rows : List Row := [(row3 6 9 36), (row3 6 9 37), (row3 6 9 38), (row3 6 9 39), (row3 6 9 40), (row3 6 9 41), (row3 6 9 42), (row3 6 9 43), (row3 6 9 44), (row3 6 9 45), (row3 6 9 46), (row3 6 9 47), (row3 6 9 48), (row3 6 9 49), (row3 6 9 50), (row3 6 9 51)]

def b035_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 199 198 190), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 273 273 462), (row3 345 347 345), (row3 148 145 137), (row3 278 278 462), (row3 462 462 462)]

theorem b035_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_02_rows b035_02_labels 1969796379110283512744286240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_02_rows b035_02_labels]
    decide +kernel

def b035_03_rows : List Row := [(row3 6 9 52), (row3 6 9 53), (row3 6 9 54), (row3 6 9 55), (row3 6 9 56), (row3 6 9 57), (row3 6 9 58), (row3 6 9 59), (row3 6 9 60), (row3 6 9 61), (row3 6 9 62), (row3 6 9 63), (row3 6 10 11), (row3 6 10 12), (row3 6 10 13), (row3 6 10 14)]

def b035_03_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 288 288 462), (row3 147 144 137), (row3 49 52 62), (row3 379 380 380), (row3 146 143 137), (row3 273 273 462), (row3 235 235 462), (row3 288 288 462), (row3 133 132 137), (row3 378 382 381), (row3 235 235 462), (row3 462 462 462), (row3 233 233 462), (row3 289 299 299)]

theorem b035_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_03_rows b035_03_labels 242270195874334284147986844180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_03_rows b035_03_labels]
    decide +kernel

def b035_04_rows : List Row := [(row3 6 10 15), (row3 6 10 16), (row3 6 10 17), (row3 6 10 18), (row3 6 10 19), (row3 6 10 20), (row3 6 10 21), (row3 6 10 22), (row3 6 10 23), (row3 6 10 24), (row3 6 10 25), (row3 6 10 26), (row3 6 10 27), (row3 6 10 28), (row3 6 10 29), (row3 6 10 30)]

def b035_04_labels : List Row := [(row3 126 125 128), (row3 182 178 182), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 292 292), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b035_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_04_rows b035_04_labels 923866993032849640274069160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_04_rows b035_04_labels]
    decide +kernel

def b035_05_rows : List Row := [(row3 6 10 31), (row3 6 10 32), (row3 6 10 33), (row3 6 10 34), (row3 6 10 35), (row3 6 10 36), (row3 6 10 37), (row3 6 10 38), (row3 6 10 39), (row3 6 10 40), (row3 6 10 41), (row3 6 10 42), (row3 6 10 43), (row3 6 10 44), (row3 6 10 45), (row3 6 10 46)]

def b035_05_labels : List Row := [(row3 235 235 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b035_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_05_rows b035_05_labels 3878375052883639404074400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_05_rows b035_05_labels]
    decide +kernel

def b035_06_rows : List Row := [(row3 6 10 47), (row3 6 10 48), (row3 6 10 49), (row3 6 10 50), (row3 6 10 51), (row3 6 10 52), (row3 6 10 53), (row3 6 10 54), (row3 6 10 55), (row3 6 10 56), (row3 6 10 57), (row3 6 10 58), (row3 6 10 59), (row3 6 10 60), (row3 6 10 61), (row3 6 10 62)]

def b035_06_labels : List Row := [(row3 235 235 462), (row3 184 178 184), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 387 391 361), (row3 146 137 143), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291)]

theorem b035_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_06_rows b035_06_labels 15094154213286515618422852890 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_06_rows b035_06_labels]
    decide +kernel

def b035_07_rows : List Row := [(row3 6 10 63), (row3 6 11 12), (row3 6 11 13), (row3 6 11 14), (row3 6 11 15), (row3 6 11 16), (row3 6 11 17), (row3 6 11 18), (row3 6 11 19), (row3 6 11 20), (row3 6 11 21), (row3 6 11 22), (row3 6 11 23), (row3 6 11 24), (row3 6 11 25), (row3 6 11 26)]

def b035_07_labels : List Row := [(row3 149 137 146), (row3 235 235 462), (row3 288 288 462), (row3 155 332 93), (row3 288 288 288), (row3 261 462 261), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 232 235 235), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b035_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_07_rows b035_07_labels 3637555291044243266400439920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_07_rows b035_07_labels]
    decide +kernel

def b035_08_rows : List Row := [(row3 6 11 27), (row3 6 11 28), (row3 6 11 29), (row3 6 11 30), (row3 6 11 31), (row3 6 11 32), (row3 6 11 33), (row3 6 11 34), (row3 6 11 35), (row3 6 11 36), (row3 6 11 37), (row3 6 11 38), (row3 6 11 39), (row3 6 11 40), (row3 6 11 41), (row3 6 11 42)]

def b035_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b035_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_08_rows b035_08_labels 163459592599078778184000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_08_rows b035_08_labels]
    decide +kernel

def b035_09_rows : List Row := [(row3 6 11 43), (row3 6 11 44), (row3 6 11 45), (row3 6 11 46), (row3 6 11 47), (row3 6 11 48), (row3 6 11 49), (row3 6 11 50), (row3 6 11 51), (row3 6 11 52), (row3 6 11 53), (row3 6 11 54), (row3 6 11 55), (row3 6 11 56), (row3 6 11 57), (row3 6 11 58)]

def b035_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 261 462 261), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 232 235 235), (row3 191 235 193), (row3 273 462 273), (row3 235 462 235)]

theorem b035_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_09_rows b035_09_labels 360890936501512050009432000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_09_rows b035_09_labels]
    decide +kernel

def b035_10_rows : List Row := [(row3 6 11 59), (row3 6 11 60), (row3 6 11 61), (row3 6 11 62), (row3 6 11 63), (row3 6 12 13), (row3 6 12 14), (row3 6 12 15), (row3 6 12 16), (row3 6 12 17), (row3 6 12 18), (row3 6 12 19), (row3 6 12 20), (row3 6 12 21), (row3 6 12 22), (row3 6 12 23)]

def b035_10_labels : List Row := [(row3 462 462 462), (row3 235 235 462), (row3 273 273 462), (row3 191 193 235), (row3 288 273 273), (row3 127 126 137), (row3 401 78 427), (row3 126 128 125), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 182 182 178), (row3 289 292 292)]

theorem b035_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_10_rows b035_10_labels 78965444453204800261038380580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_10_rows b035_10_labels]
    decide +kernel

def b035_11_rows : List Row := [(row3 6 12 24), (row3 6 12 25), (row3 6 12 26), (row3 6 12 27), (row3 6 12 28), (row3 6 12 29), (row3 6 12 30), (row3 6 12 31), (row3 6 12 32), (row3 6 12 33), (row3 6 12 34), (row3 6 12 35), (row3 6 12 36), (row3 6 12 37), (row3 6 12 38), (row3 6 12 39)]

def b035_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462)]

theorem b035_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_11_rows b035_11_labels 3998302287344943729458400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_11_rows b035_11_labels]
    decide +kernel

def b035_12_rows : List Row := [(row3 6 12 40), (row3 6 12 41), (row3 6 12 42), (row3 6 12 43), (row3 6 12 44), (row3 6 12 45), (row3 6 12 46), (row3 6 12 47), (row3 6 12 48), (row3 6 12 49), (row3 6 12 50), (row3 6 12 51), (row3 6 12 52), (row3 6 12 53), (row3 6 12 54), (row3 6 12 55)]

def b035_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 184 184 178), (row3 289 291 291)]

theorem b035_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_12_rows b035_12_labels 111769671977259750057658320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_12_rows b035_12_labels]
    decide +kernel

def b035_13_rows : List Row := [(row3 6 12 56), (row3 6 12 57), (row3 6 12 58), (row3 6 12 59), (row3 6 12 60), (row3 6 12 61), (row3 6 12 62), (row3 6 12 63), (row3 6 13 14), (row3 6 13 15), (row3 6 13 16), (row3 6 13 17), (row3 6 13 18), (row3 6 13 19), (row3 6 13 20), (row3 6 13 21)]

def b035_13_labels : List Row := [(row3 289 291 291), (row3 235 462 235), (row3 462 462 462), (row3 235 462 235), (row3 289 291 291), (row3 146 143 137), (row3 387 361 391), (row3 149 146 137), (row3 34 443 27), (row3 402 403 404), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 232 462 232), (row3 300 462 300), (row3 127 137 126)]

theorem b035_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_13_rows b035_13_labels 4999208811378349736194316486730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_13_rows b035_13_labels]
    decide +kernel

def b035_14_rows : List Row := [(row3 6 13 22), (row3 6 13 23), (row3 6 13 24), (row3 6 13 25), (row3 6 13 26), (row3 6 13 27), (row3 6 13 28), (row3 6 13 29), (row3 6 13 30), (row3 6 13 31), (row3 6 13 32), (row3 6 13 33), (row3 6 13 34), (row3 6 13 35), (row3 6 13 36), (row3 6 13 37)]

def b035_14_labels : List Row := [(row3 351 348 350), (row3 142 136 141), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 288 462 288), (row3 197 190 196), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 462 236)]

theorem b035_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_14_rows b035_14_labels 5419167851237352312969293040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_14_rows b035_14_labels]
    decide +kernel

def b035_15_rows : List Row := [(row3 6 13 38), (row3 6 13 39), (row3 6 13 40), (row3 6 13 41), (row3 6 13 42), (row3 6 13 43), (row3 6 13 44), (row3 6 13 45), (row3 6 13 46), (row3 6 13 47), (row3 6 13 48), (row3 6 13 49), (row3 6 13 50), (row3 6 13 51), (row3 6 13 52), (row3 6 13 53)]

def b035_15_labels : List Row := [(row3 261 462 261), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 199 190 198), (row3 273 462 273), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 278 462 278), (row3 148 137 145)]

theorem b035_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b035_15_rows b035_15_labels 377490385444528803575439360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b035_15_rows b035_15_labels]
    decide +kernel

theorem checked035 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_035 QuarticIntegerComputationalData.ids64_035 8772511703288276887575872338530 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b035_00_rows ++ b035_01_rows) ++ (b035_02_rows ++ b035_03_rows)) ++ ((b035_04_rows ++ b035_05_rows) ++ (b035_06_rows ++ b035_07_rows))) ++ (((b035_08_rows ++ b035_09_rows) ++ (b035_10_rows ++ b035_11_rows)) ++ ((b035_12_rows ++ b035_13_rows) ++ (b035_14_rows ++ b035_15_rows))))
    ((((b035_00_labels ++ b035_01_labels) ++ (b035_02_labels ++ b035_03_labels)) ++ ((b035_04_labels ++ b035_05_labels) ++ (b035_06_labels ++ b035_07_labels))) ++ (((b035_08_labels ++ b035_09_labels) ++ (b035_10_labels ++ b035_11_labels)) ++ ((b035_12_labels ++ b035_13_labels) ++ (b035_14_labels ++ b035_15_labels)))) 8772511703288276887575872338530
  exact ((((b035_00_checked.append (c := 3424164519723820694356165439310) b035_01_checked (by decide +kernel)).append (c := 3668404511977265262016896569730) (b035_02_checked.append (c := 244239992253444567660731130420) b035_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 3688063966849681754181398006100) ((b035_04_checked.append (c := 927745368085733279678143560) b035_05_checked (by decide +kernel)).append (c := 19659454872416492164501436370) (b035_06_checked.append (c := 18731709504330758884823292810) b035_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 8772511703288276887575872338530) (((b035_08_checked.append (c := 361054396094111128787616000) b035_09_checked (by decide +kernel)).append (c := 79330497151586256333555454980) (b035_10_checked.append (c := 78969442755492145204767838980) b035_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 5084447736438595133394474332430) ((b035_12_checked.append (c := 4999320581050326995944374145050) b035_13_checked (by decide +kernel)).append (c := 5005117239287008877060918877450) (b035_14_checked.append (c := 5796658236681881116544732400) b035_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b036_00_rows : List Row := [(row3 6 13 54), (row3 6 13 55), (row3 6 13 56), (row3 6 13 57), (row3 6 13 58), (row3 6 13 59), (row3 6 13 60), (row3 6 13 61), (row3 6 13 62), (row3 6 13 63), (row3 6 14 15), (row3 6 14 16), (row3 6 14 17), (row3 6 14 18), (row3 6 14 19), (row3 6 14 20)]

def b036_00_labels : List Row := [(row3 345 345 347), (row3 147 137 144), (row3 133 137 132), (row3 288 462 288), (row3 235 462 235), (row3 273 462 273), (row3 146 137 143), (row3 379 380 380), (row3 49 62 52), (row3 378 381 382), (row3 451 24 442), (row3 108 84 367), (row3 289 305 305), (row3 234 234 462), (row3 462 284 284), (row3 114 86 368)]

theorem b036_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_00_rows b036_00_labels 27988666512299805681818666459280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_00_rows b036_00_labels]
    decide +kernel

def b036_01_rows : List Row := [(row3 6 14 21), (row3 6 14 22), (row3 6 14 23), (row3 6 14 24), (row3 6 14 25), (row3 6 14 26), (row3 6 14 27), (row3 6 14 28), (row3 6 14 29), (row3 6 14 30), (row3 6 14 31), (row3 6 14 32), (row3 6 14 33), (row3 6 14 34), (row3 6 14 35), (row3 6 14 36)]

def b036_01_labels : List Row := [(row3 410 431 59), (row3 37 28 444), (row3 411 432 60), (row3 265 302 302), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 293 293), (row3 122 86 369), (row3 385 426 77), (row3 121 85 369), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b036_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_01_rows b036_01_labels 4962487657793493127740387255180 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_01_rows b036_01_labels]
    decide +kernel

def b036_02_rows : List Row := [(row3 6 14 37), (row3 6 14 38), (row3 6 14 39), (row3 6 14 40), (row3 6 14 41), (row3 6 14 42), (row3 6 14 43), (row3 6 14 44), (row3 6 14 45), (row3 6 14 46), (row3 6 14 47), (row3 6 14 48), (row3 6 14 49), (row3 6 14 50), (row3 6 14 51), (row3 6 14 52)]

def b036_02_labels : List Row := [(row3 462 284 284), (row3 168 94 333), (row3 462 284 284), (row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 462 193), (row3 339 342 328), (row3 191 235 193), (row3 140 178 140), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 180 462 180)]

theorem b036_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_02_rows b036_02_labels 14672377020627309205245736830 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_02_rows b036_02_labels]
    decide +kernel

def b036_03_rows : List Row := [(row3 6 14 53), (row3 6 14 54), (row3 6 14 55), (row3 6 14 56), (row3 6 14 57), (row3 6 14 58), (row3 6 14 59), (row3 6 14 60), (row3 6 14 61), (row3 6 14 62), (row3 6 14 63), (row3 6 15 16), (row3 6 15 17), (row3 6 15 18), (row3 6 15 19), (row3 6 15 20)]

def b036_03_labels : List Row := [(row3 387 390 360), (row3 68 69 76), (row3 388 392 362), (row3 409 414 394), (row3 133 137 132), (row3 289 291 291), (row3 191 235 193), (row3 387 391 361), (row3 49 52 62), (row3 455 447 447), (row3 48 50 61), (row3 406 405 406), (row3 98 101 99), (row3 278 300 288), (row3 462 462 462), (row3 278 288 300)]

theorem b036_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_03_rows b036_03_labels 11232035698546266324649508343990 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_03_rows b036_03_labels]
    decide +kernel

def b036_04_rows : List Row := [(row3 6 15 21), (row3 6 15 22), (row3 6 15 23), (row3 6 15 24), (row3 6 15 25), (row3 6 15 26), (row3 6 15 27), (row3 6 15 28), (row3 6 15 29), (row3 6 15 30), (row3 6 15 31), (row3 6 15 32), (row3 6 15 33), (row3 6 15 34), (row3 6 15 35), (row3 6 15 36)]

def b036_04_labels : List Row := [(row3 98 99 101), (row3 406 406 405), (row3 38 33 33), (row3 109 111 110), (row3 273 304 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 295 304), (row3 109 110 111), (row3 379 380 380), (row3 261 290 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b036_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_04_rows b036_04_labels 1654297800891493450070605764960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_04_rows b036_04_labels]
    decide +kernel

def b036_05_rows : List Row := [(row3 6 15 37), (row3 6 15 38), (row3 6 15 39), (row3 6 15 40), (row3 6 15 41), (row3 6 15 42), (row3 6 15 43), (row3 6 15 44), (row3 6 15 45), (row3 6 15 46), (row3 6 15 47), (row3 6 15 48), (row3 6 15 49), (row3 6 15 50), (row3 6 15 51), (row3 6 15 52)]

def b036_05_labels : List Row := [(row3 462 462 462), (row3 261 288 290), (row3 161 176 176), (row3 199 198 190), (row3 273 273 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 199 190 198), (row3 288 288 288), (row3 348 350 351), (row3 149 146 137), (row3 278 278 462), (row3 462 462 462), (row3 278 462 278)]

theorem b036_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_05_rows b036_05_labels 5900514442942023785354443200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_05_rows b036_05_labels]
    decide +kernel

def b036_06_rows : List Row := [(row3 6 15 53), (row3 6 15 54), (row3 6 15 55), (row3 6 15 56), (row3 6 15 57), (row3 6 15 58), (row3 6 15 59), (row3 6 15 60), (row3 6 15 61), (row3 6 15 62), (row3 6 15 63), (row3 6 16 17), (row3 6 16 18), (row3 6 16 19), (row3 6 16 20), (row3 6 16 21)]

def b036_06_labels : List Row := [(row3 149 137 146), (row3 348 351 350), (row3 107 106 106), (row3 48 50 61), (row3 378 381 382), (row3 149 146 137), (row3 288 273 273), (row3 149 137 146), (row3 378 382 381), (row3 48 61 50), (row3 420 421 421), (row3 140 140 178), (row3 278 278 462), (row3 237 237 462), (row3 462 462 462), (row3 232 232 462)]

theorem b036_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_06_rows b036_06_labels 2873950975473825708672994168560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_06_rows b036_06_labels]
    decide +kernel

def b036_07_rows : List Row := [(row3 6 16 22), (row3 6 16 23), (row3 6 16 24), (row3 6 16 25), (row3 6 16 26), (row3 6 16 27), (row3 6 16 28), (row3 6 16 29), (row3 6 16 30), (row3 6 16 31), (row3 6 16 32), (row3 6 16 33), (row3 6 16 34), (row3 6 16 35), (row3 6 16 36), (row3 6 16 37)]

def b036_07_labels : List Row := [(row3 295 295 462), (row3 367 108 84), (row3 164 164 206), (row3 288 288 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 288 288 462), (row3 273 273 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b036_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_07_rows b036_07_labels 46263854136510730643331006000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_07_rows b036_07_labels]
    decide +kernel

def b036_08_rows : List Row := [(row3 6 16 38), (row3 6 16 39), (row3 6 16 40), (row3 6 16 41), (row3 6 16 42), (row3 6 16 43), (row3 6 16 44), (row3 6 16 45), (row3 6 16 46), (row3 6 16 47), (row3 6 16 48), (row3 6 16 49), (row3 6 16 50), (row3 6 16 51), (row3 6 16 52), (row3 6 16 53)]

def b036_08_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 209 209 206), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 261 261 462), (row3 327 327 327), (row3 184 184 178), (row3 265 265 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462)]

theorem b036_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_08_rows b036_08_labels 773418479872863914284572720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_08_rows b036_08_labels]
    decide +kernel

def b036_09_rows : List Row := [(row3 6 16 54), (row3 6 16 55), (row3 6 16 56), (row3 6 16 57), (row3 6 16 58), (row3 6 16 59), (row3 6 16 60), (row3 6 16 61), (row3 6 16 62), (row3 6 16 63), (row3 6 17 18), (row3 6 17 19), (row3 6 17 20), (row3 6 17 21), (row3 6 17 22), (row3 6 17 23)]

def b036_09_labels : List Row := [(row3 278 278 462), (row3 182 182 178), (row3 68 69 76), (row3 345 345 347), (row3 184 184 178), (row3 261 261 462), (row3 234 234 462), (row3 288 288 462), (row3 140 140 178), (row3 348 351 350), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 306 313 313)]

theorem b036_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_09_rows b036_09_labels 105094627419561936040704411360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_09_rows b036_09_labels]
    decide +kernel

def b036_10_rows : List Row := [(row3 6 17 24), (row3 6 17 25), (row3 6 17 26), (row3 6 17 27), (row3 6 17 28), (row3 6 17 29), (row3 6 17 30), (row3 6 17 31), (row3 6 17 32), (row3 6 17 33), (row3 6 17 34), (row3 6 17 35), (row3 6 17 36), (row3 6 17 37), (row3 6 17 38), (row3 6 17 39)]

def b036_10_labels : List Row := [(row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b036_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_10_rows b036_10_labels 32250760181739016703421120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_10_rows b036_10_labels]
    decide +kernel

def b036_11_rows : List Row := [(row3 6 17 40), (row3 6 17 41), (row3 6 17 42), (row3 6 17 43), (row3 6 17 44), (row3 6 17 45), (row3 6 17 46), (row3 6 17 47), (row3 6 17 48), (row3 6 17 49), (row3 6 17 50), (row3 6 17 51), (row3 6 17 52), (row3 6 17 53), (row3 6 17 54), (row3 6 17 55)]

def b036_11_labels : List Row := [(row3 265 266 266), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 184 178 184), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291)]

theorem b036_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_11_rows b036_11_labels 111749684104849532670094320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_11_rows b036_11_labels]
    decide +kernel

def b036_12_rows : List Row := [(row3 6 17 56), (row3 6 17 57), (row3 6 17 58), (row3 6 17 59), (row3 6 17 60), (row3 6 17 61), (row3 6 17 62), (row3 6 17 63), (row3 6 18 19), (row3 6 18 20), (row3 6 18 21), (row3 6 18 22), (row3 6 18 23), (row3 6 18 24), (row3 6 18 25), (row3 6 18 26)]

def b036_12_labels : List Row := [(row3 387 390 360), (row3 148 137 145), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 291 291), (row3 149 137 146), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 234 228), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b036_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_12_rows b036_12_labels 15322060456307195673755013030 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_12_rows b036_12_labels]
    decide +kernel

def b036_13_rows : List Row := [(row3 6 18 27), (row3 6 18 28), (row3 6 18 29), (row3 6 18 30), (row3 6 18 31), (row3 6 18 32), (row3 6 18 33), (row3 6 18 34), (row3 6 18 35), (row3 6 18 36), (row3 6 18 37), (row3 6 18 38), (row3 6 18 39), (row3 6 18 40), (row3 6 18 41), (row3 6 18 42)]

def b036_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462)]

theorem b036_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_13_rows b036_13_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_13_rows b036_13_labels]
    decide +kernel

def b036_14_rows : List Row := [(row3 6 18 43), (row3 6 18 44), (row3 6 18 45), (row3 6 18 46), (row3 6 18 47), (row3 6 18 48), (row3 6 18 49), (row3 6 18 50), (row3 6 18 51), (row3 6 18 52), (row3 6 18 53), (row3 6 18 54), (row3 6 18 55), (row3 6 18 56), (row3 6 18 57), (row3 6 18 58)]

def b036_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 462 265), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 180 462 180), (row3 278 462 278), (row3 234 462 234)]

theorem b036_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_14_rows b036_14_labels 534581826508337980158763200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_14_rows b036_14_labels]
    decide +kernel

def b036_15_rows : List Row := [(row3 6 18 59), (row3 6 18 60), (row3 6 18 61), (row3 6 18 62), (row3 6 18 63), (row3 6 19 20), (row3 6 19 21), (row3 6 19 22), (row3 6 19 23), (row3 6 19 24), (row3 6 19 25), (row3 6 19 26), (row3 6 19 27), (row3 6 19 28), (row3 6 19 29), (row3 6 19 30)]

def b036_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 462 278), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 244 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b036_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b036_15_rows b036_15_labels 13880803635601666710284700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b036_15_rows b036_15_labels]
    decide +kernel

theorem checked036 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_036 QuarticIntegerComputationalData.ids64_036 48900158082629831329720163376450 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b036_00_rows ++ b036_01_rows) ++ (b036_02_rows ++ b036_03_rows)) ++ ((b036_04_rows ++ b036_05_rows) ++ (b036_06_rows ++ b036_07_rows))) ++ (((b036_08_rows ++ b036_09_rows) ++ (b036_10_rows ++ b036_11_rows)) ++ ((b036_12_rows ++ b036_13_rows) ++ (b036_14_rows ++ b036_15_rows))))
    ((((b036_00_labels ++ b036_01_labels) ++ (b036_02_labels ++ b036_03_labels)) ++ ((b036_04_labels ++ b036_05_labels) ++ (b036_06_labels ++ b036_07_labels))) ++ (((b036_08_labels ++ b036_09_labels) ++ (b036_10_labels ++ b036_11_labels)) ++ ((b036_12_labels ++ b036_13_labels) ++ (b036_14_labels ++ b036_15_labels)))) 48900158082629831329720163376450
  exact ((((b036_00_checked.append (c := 32951154170093298809559053714460) b036_01_checked (by decide +kernel)).append (c := 44197862245660192443413807795280) (b036_02_checked.append (c := 11246708075566893633854754080820) b036_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 48778275390604964356586093178000) ((b036_04_checked.append (c := 1660198315334435473855960208160) b036_05_checked (by decide +kernel)).append (c := 4580413144944771913172285382720) (b036_06_checked.append (c := 2920214829610336439316325174560) b036_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 48900158082629831329720163376450) (((b036_08_checked.append (c := 105868045899434799954988984080) b036_09_checked (by decide +kernel)).append (c := 106012046343721388504362499520) (b036_10_checked.append (c := 144000444286588549373515440) b036_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 121882692024866973134070198450) ((b036_12_checked.append (c := 15322183051001644982838651030) b036_13_checked (by decide +kernel)).append (c := 15870645681145584629707698930) (b036_14_checked.append (c := 548462630143939646869047900) b036_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b037_00_rows : List Row := [(row3 6 19 31), (row3 6 19 32), (row3 6 19 33), (row3 6 19 34), (row3 6 19 35), (row3 6 19 36), (row3 6 19 37), (row3 6 19 38), (row3 6 19 39), (row3 6 19 40), (row3 6 19 41), (row3 6 19 42), (row3 6 19 43), (row3 6 19 44), (row3 6 19 45), (row3 6 19 46)]

def b037_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_00_rows b037_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_00_rows b037_00_labels]
    decide +kernel

def b037_01_rows : List Row := [(row3 6 19 47), (row3 6 19 48), (row3 6 19 49), (row3 6 19 50), (row3 6 19 51), (row3 6 19 52), (row3 6 19 53), (row3 6 19 54), (row3 6 19 55), (row3 6 19 56), (row3 6 19 57), (row3 6 19 58), (row3 6 19 59), (row3 6 19 60), (row3 6 19 61), (row3 6 19 62)]

def b037_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_01_rows b037_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_01_rows b037_01_labels]
    decide +kernel

def b037_02_rows : List Row := [(row3 6 19 63), (row3 6 20 21), (row3 6 20 22), (row3 6 20 23), (row3 6 20 24), (row3 6 20 25), (row3 6 20 26), (row3 6 20 27), (row3 6 20 28), (row3 6 20 29), (row3 6 20 30), (row3 6 20 31), (row3 6 20 32), (row3 6 20 33), (row3 6 20 34), (row3 6 20 35)]

def b037_02_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 278 278 462), (row3 228 228 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_02_rows b037_02_labels 39547682141473742623672320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_02_rows b037_02_labels]
    decide +kernel

def b037_03_rows : List Row := [(row3 6 20 36), (row3 6 20 37), (row3 6 20 38), (row3 6 20 39), (row3 6 20 40), (row3 6 20 41), (row3 6 20 42), (row3 6 20 43), (row3 6 20 44), (row3 6 20 45), (row3 6 20 46), (row3 6 20 47), (row3 6 20 48), (row3 6 20 49), (row3 6 20 50), (row3 6 20 51)]

def b037_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_03_rows b037_03_labels 122594694449309083638000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_03_rows b037_03_labels]
    decide +kernel

def b037_04_rows : List Row := [(row3 6 20 52), (row3 6 20 53), (row3 6 20 54), (row3 6 20 55), (row3 6 20 56), (row3 6 20 57), (row3 6 20 58), (row3 6 20 59), (row3 6 20 60), (row3 6 20 61), (row3 6 20 62), (row3 6 20 63), (row3 6 21 22), (row3 6 21 23), (row3 6 21 24), (row3 6 21 25)]

def b037_04_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 265 265 462), (row3 234 234 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 278 278 462), (row3 180 180 462), (row3 278 278 462), (row3 140 140 178), (row3 306 313 313), (row3 462 462 462), (row3 462 462 462)]

theorem b037_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_04_rows b037_04_labels 5725027411449257764817144640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_04_rows b037_04_labels]
    decide +kernel

def b037_05_rows : List Row := [(row3 6 21 26), (row3 6 21 27), (row3 6 21 28), (row3 6 21 29), (row3 6 21 30), (row3 6 21 31), (row3 6 21 32), (row3 6 21 33), (row3 6 21 34), (row3 6 21 35), (row3 6 21 36), (row3 6 21 37), (row3 6 21 38), (row3 6 21 39), (row3 6 21 40), (row3 6 21 41)]

def b037_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_05_rows b037_05_labels 32250760181739016703421120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_05_rows b037_05_labels]
    decide +kernel

def b037_06_rows : List Row := [(row3 6 21 42), (row3 6 21 43), (row3 6 21 44), (row3 6 21 45), (row3 6 21 46), (row3 6 21 47), (row3 6 21 48), (row3 6 21 49), (row3 6 21 50), (row3 6 21 51), (row3 6 21 52), (row3 6 21 53), (row3 6 21 54), (row3 6 21 55), (row3 6 21 56), (row3 6 21 57)]

def b037_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 266 266), (row3 235 462 235), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 184 184 178), (row3 289 291 291), (row3 289 291 291), (row3 235 462 235)]

theorem b037_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_06_rows b037_06_labels 285200913362587974322679520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_06_rows b037_06_labels]
    decide +kernel

def b037_07_rows : List Row := [(row3 6 21 58), (row3 6 21 59), (row3 6 21 60), (row3 6 21 61), (row3 6 21 62), (row3 6 21 63), (row3 6 22 23), (row3 6 22 24), (row3 6 22 25), (row3 6 22 26), (row3 6 22 27), (row3 6 22 28), (row3 6 22 29), (row3 6 22 30), (row3 6 22 31), (row3 6 22 32)]

def b037_07_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 289 291 291), (row3 148 145 137), (row3 387 360 390), (row3 149 146 137), (row3 367 84 108), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 288 462 288), (row3 164 206 164), (row3 288 462 288), (row3 462 462 462)]

theorem b037_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_07_rows b037_07_labels 61340798634231615169315044870 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_07_rows b037_07_labels]
    decide +kernel

def b037_08_rows : List Row := [(row3 6 22 33), (row3 6 22 34), (row3 6 22 35), (row3 6 22 36), (row3 6 22 37), (row3 6 22 38), (row3 6 22 39), (row3 6 22 40), (row3 6 22 41), (row3 6 22 42), (row3 6 22 43), (row3 6 22 44), (row3 6 22 45), (row3 6 22 46), (row3 6 22 47), (row3 6 22 48)]

def b037_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 273 462 273), (row3 234 462 234), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 209 206 209), (row3 261 462 261), (row3 278 462 278)]

theorem b037_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_08_rows b037_08_labels 65346516301425244199823600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_08_rows b037_08_labels]
    decide +kernel

def b037_09_rows : List Row := [(row3 6 22 49), (row3 6 22 50), (row3 6 22 51), (row3 6 22 52), (row3 6 22 53), (row3 6 22 54), (row3 6 22 55), (row3 6 22 56), (row3 6 22 57), (row3 6 22 58), (row3 6 22 59), (row3 6 22 60), (row3 6 22 61), (row3 6 22 62), (row3 6 22 63), (row3 6 23 24)]

def b037_09_labels : List Row := [(row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 265 462 265), (row3 184 178 184), (row3 327 327 327), (row3 182 178 182), (row3 140 178 140), (row3 288 462 288), (row3 234 462 234), (row3 261 462 261), (row3 184 178 184), (row3 345 347 345), (row3 68 76 69), (row3 348 350 351), (row3 315 318 318)]

theorem b037_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_09_rows b037_09_labels 105853739947277749976495024640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_09_rows b037_09_labels]
    decide +kernel

def b037_10_rows : List Row := [(row3 6 23 25), (row3 6 23 26), (row3 6 23 27), (row3 6 23 28), (row3 6 23 29), (row3 6 23 30), (row3 6 23 31), (row3 6 23 32), (row3 6 23 33), (row3 6 23 34), (row3 6 23 35), (row3 6 23 36), (row3 6 23 37), (row3 6 23 38), (row3 6 23 39), (row3 6 23 40)]

def b037_10_labels : List Row := [(row3 222 222 224), (row3 462 246 246), (row3 462 462 462), (row3 462 246 246), (row3 222 224 222), (row3 315 318 318), (row3 130 104 104), (row3 223 223 224), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 223 224 223), (row3 289 291 291), (row3 265 268 268)]

theorem b037_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_10_rows b037_10_labels 11149927117501099836588617520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_10_rows b037_10_labels]
    decide +kernel

def b037_11_rows : List Row := [(row3 6 23 41), (row3 6 23 42), (row3 6 23 43), (row3 6 23 44), (row3 6 23 45), (row3 6 23 46), (row3 6 23 47), (row3 6 23 48), (row3 6 23 49), (row3 6 23 50), (row3 6 23 51), (row3 6 23 52), (row3 6 23 53), (row3 6 23 54), (row3 6 23 55), (row3 6 23 56)]

def b037_11_labels : List Row := [(row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 268 268), (row3 226 229 229), (row3 182 178 182), (row3 289 291 291), (row3 234 234 462), (row3 462 462 462), (row3 234 462 234), (row3 289 291 291), (row3 182 182 178), (row3 306 314 314), (row3 388 392 362)]

theorem b037_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_11_rows b037_11_labels 23491962319305214439938940670 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_11_rows b037_11_labels]
    decide +kernel

def b037_12_rows : List Row := [(row3 6 23 57), (row3 6 23 58), (row3 6 23 59), (row3 6 23 60), (row3 6 23 61), (row3 6 23 62), (row3 6 23 63), (row3 6 24 25), (row3 6 24 26), (row3 6 24 27), (row3 6 24 28), (row3 6 24 29), (row3 6 24 30), (row3 6 24 31), (row3 6 24 32), (row3 6 24 33)]

def b037_12_labels : List Row := [(row3 147 137 144), (row3 289 291 291), (row3 232 235 235), (row3 289 291 291), (row3 147 144 137), (row3 388 362 392), (row3 107 106 106), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 239 239 462), (row3 462 462 462)]

theorem b037_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_12_rows b037_12_labels 25265191148875787585854804110 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_12_rows b037_12_labels]
    decide +kernel

def b037_13_rows : List Row := [(row3 6 24 34), (row3 6 24 35), (row3 6 24 36), (row3 6 24 37), (row3 6 24 38), (row3 6 24 39), (row3 6 24 40), (row3 6 24 41), (row3 6 24 42), (row3 6 24 43), (row3 6 24 44), (row3 6 24 45), (row3 6 24 46), (row3 6 24 47), (row3 6 24 48), (row3 6 24 49)]

def b037_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 255 256 256), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 209 206 209), (row3 265 266 266)]

theorem b037_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_13_rows b037_13_labels 36927262767439818977308320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_13_rows b037_13_labels]
    decide +kernel

def b037_14_rows : List Row := [(row3 6 24 50), (row3 6 24 51), (row3 6 24 52), (row3 6 24 53), (row3 6 24 54), (row3 6 24 55), (row3 6 24 56), (row3 6 24 57), (row3 6 24 58), (row3 6 24 59), (row3 6 24 60), (row3 6 24 61), (row3 6 24 62), (row3 6 24 63), (row3 6 25 26), (row3 6 25 27)]

def b037_14_labels : List Row := [(row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 265 268 268), (row3 339 342 328), (row3 199 190 198), (row3 265 266 266), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 265 266 266), (row3 199 190 198), (row3 462 462 462), (row3 462 462 462)]

theorem b037_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_14_rows b037_14_labels 5026104141952708604549180550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_14_rows b037_14_labels]
    decide +kernel

def b037_15_rows : List Row := [(row3 6 25 28), (row3 6 25 29), (row3 6 25 30), (row3 6 25 31), (row3 6 25 32), (row3 6 25 33), (row3 6 25 34), (row3 6 25 35), (row3 6 25 36), (row3 6 25 37), (row3 6 25 38), (row3 6 25 39), (row3 6 25 40), (row3 6 25 41), (row3 6 25 42), (row3 6 25 43)]

def b037_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b037_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b037_15_rows b037_15_labels 121705541119974164220000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b037_15_rows b037_15_labels]
    decide +kernel

theorem checked037 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_037 QuarticIntegerComputationalData.ids64_037 238312268155583668457633519880 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b037_00_rows ++ b037_01_rows) ++ (b037_02_rows ++ b037_03_rows)) ++ ((b037_04_rows ++ b037_05_rows) ++ (b037_06_rows ++ b037_07_rows))) ++ (((b037_08_rows ++ b037_09_rows) ++ (b037_10_rows ++ b037_11_rows)) ++ ((b037_12_rows ++ b037_13_rows) ++ (b037_14_rows ++ b037_15_rows))))
    ((((b037_00_labels ++ b037_01_labels) ++ (b037_02_labels ++ b037_03_labels)) ++ ((b037_04_labels ++ b037_05_labels) ++ (b037_06_labels ++ b037_07_labels))) ++ (((b037_08_labels ++ b037_09_labels) ++ (b037_10_labels ++ b037_11_labels)) ++ ((b037_12_labels ++ b037_13_labels) ++ (b037_14_labels ++ b037_15_labels)))) 238312268155583668457633519880
  exact ((((b037_00_checked.append (c := 0) b037_01_checked (by decide +kernel)).append (c := 39670276835923051707310320) (b037_02_checked.append (c := 39670276835923051707310320) b037_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 67422947996061122976865600470) ((b037_04_checked.append (c := 5757278171630996781520565760) b037_05_checked (by decide +kernel)).append (c := 67383277719225199925158290150) (b037_06_checked.append (c := 61625999547594203143637724390) b037_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 238312268155583668457633519880) (((b037_08_checked.append (c := 105919086463579175220694848240) b037_09_checked (by decide +kernel)).append (c := 140560975900385489497222406430) (b037_10_checked.append (c := 34641889436806314276527558190) b037_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 170889320159522545480767919410) ((b037_12_checked.append (c := 25302118411643227404832112430) b037_13_checked (by decide +kernel)).append (c := 30328344259137055983545512980) (b037_14_checked.append (c := 5026225847493828578713400550) b037_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b038_00_rows : List Row := [(row3 6 25 44), (row3 6 25 45), (row3 6 25 46), (row3 6 25 47), (row3 6 25 48), (row3 6 25 49), (row3 6 25 50), (row3 6 25 51), (row3 6 25 52), (row3 6 25 53), (row3 6 25 54), (row3 6 25 55), (row3 6 25 56), (row3 6 25 57), (row3 6 25 58), (row3 6 25 59)]

def b038_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 462 261), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 193 462 193), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462)]

theorem b038_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_00_rows b038_00_labels 356387884338891986772508800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_00_rows b038_00_labels]
    decide +kernel

def b038_01_rows : List Row := [(row3 6 25 60), (row3 6 25 61), (row3 6 25 62), (row3 6 25 63), (row3 6 26 27), (row3 6 26 28), (row3 6 26 29), (row3 6 26 30), (row3 6 26 31), (row3 6 26 32), (row3 6 26 33), (row3 6 26 34), (row3 6 26 35), (row3 6 26 36), (row3 6 26 37), (row3 6 26 38)]

def b038_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_01_rows b038_01_labels 9101466701583106161124800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_01_rows b038_01_labels]
    decide +kernel

def b038_02_rows : List Row := [(row3 6 26 39), (row3 6 26 40), (row3 6 26 41), (row3 6 26 42), (row3 6 26 43), (row3 6 26 44), (row3 6 26 45), (row3 6 26 46), (row3 6 26 47), (row3 6 26 48), (row3 6 26 49), (row3 6 26 50), (row3 6 26 51), (row3 6 26 52), (row3 6 26 53), (row3 6 26 54)]

def b038_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_02_rows b038_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_02_rows b038_02_labels]
    decide +kernel

def b038_03_rows : List Row := [(row3 6 26 55), (row3 6 26 56), (row3 6 26 57), (row3 6 26 58), (row3 6 26 59), (row3 6 26 60), (row3 6 26 61), (row3 6 26 62), (row3 6 26 63), (row3 6 27 28), (row3 6 27 29), (row3 6 27 30), (row3 6 27 31), (row3 6 27 32), (row3 6 27 33), (row3 6 27 34)]

def b038_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_03_rows b038_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_03_rows b038_03_labels]
    decide +kernel

def b038_04_rows : List Row := [(row3 6 27 35), (row3 6 27 36), (row3 6 27 37), (row3 6 27 38), (row3 6 27 39), (row3 6 27 40), (row3 6 27 41), (row3 6 27 42), (row3 6 27 43), (row3 6 27 44), (row3 6 27 45), (row3 6 27 46), (row3 6 27 47), (row3 6 27 48), (row3 6 27 49), (row3 6 27 50)]

def b038_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_04_rows b038_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_04_rows b038_04_labels]
    decide +kernel

def b038_05_rows : List Row := [(row3 6 27 51), (row3 6 27 52), (row3 6 27 53), (row3 6 27 54), (row3 6 27 55), (row3 6 27 56), (row3 6 27 57), (row3 6 27 58), (row3 6 27 59), (row3 6 27 60), (row3 6 27 61), (row3 6 27 62), (row3 6 27 63), (row3 6 28 29), (row3 6 28 30), (row3 6 28 31)]

def b038_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_05_rows b038_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_05_rows b038_05_labels]
    decide +kernel

def b038_06_rows : List Row := [(row3 6 28 32), (row3 6 28 33), (row3 6 28 34), (row3 6 28 35), (row3 6 28 36), (row3 6 28 37), (row3 6 28 38), (row3 6 28 39), (row3 6 28 40), (row3 6 28 41), (row3 6 28 42), (row3 6 28 43), (row3 6 28 44), (row3 6 28 45), (row3 6 28 46), (row3 6 28 47)]

def b038_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_06_rows b038_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_06_rows b038_06_labels]
    decide +kernel

def b038_07_rows : List Row := [(row3 6 28 48), (row3 6 28 49), (row3 6 28 50), (row3 6 28 51), (row3 6 28 52), (row3 6 28 53), (row3 6 28 54), (row3 6 28 55), (row3 6 28 56), (row3 6 28 57), (row3 6 28 58), (row3 6 28 59), (row3 6 28 60), (row3 6 28 61), (row3 6 28 62), (row3 6 28 63)]

def b038_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_07_rows b038_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_07_rows b038_07_labels]
    decide +kernel

def b038_08_rows : List Row := [(row3 6 29 30), (row3 6 29 31), (row3 6 29 32), (row3 6 29 33), (row3 6 29 34), (row3 6 29 35), (row3 6 29 36), (row3 6 29 37), (row3 6 29 38), (row3 6 29 39), (row3 6 29 40), (row3 6 29 41), (row3 6 29 42), (row3 6 29 43), (row3 6 29 44), (row3 6 29 45)]

def b038_08_labels : List Row := [(row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_08_rows b038_08_labels 4572338464461712461804000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_08_rows b038_08_labels]
    decide +kernel

def b038_09_rows : List Row := [(row3 6 29 46), (row3 6 29 47), (row3 6 29 48), (row3 6 29 49), (row3 6 29 50), (row3 6 29 51), (row3 6 29 52), (row3 6 29 53), (row3 6 29 54), (row3 6 29 55), (row3 6 29 56), (row3 6 29 57), (row3 6 29 58), (row3 6 29 59), (row3 6 29 60), (row3 6 29 61)]

def b038_09_labels : List Row := [(row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 235 235 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 273 273 462)]

theorem b038_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_09_rows b038_09_labels 10593592484691797785360800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_09_rows b038_09_labels]
    decide +kernel

def b038_10_rows : List Row := [(row3 6 29 62), (row3 6 29 63), (row3 6 30 31), (row3 6 30 32), (row3 6 30 33), (row3 6 30 34), (row3 6 30 35), (row3 6 30 36), (row3 6 30 37), (row3 6 30 38), (row3 6 30 39), (row3 6 30 40), (row3 6 30 41), (row3 6 30 42), (row3 6 30 43), (row3 6 30 44)]

def b038_10_labels : List Row := [(row3 193 193 462), (row3 273 273 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_10_rows b038_10_labels 361875971793595838005198800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_10_rows b038_10_labels]
    decide +kernel

def b038_11_rows : List Row := [(row3 6 30 45), (row3 6 30 46), (row3 6 30 47), (row3 6 30 48), (row3 6 30 49), (row3 6 30 50), (row3 6 30 51), (row3 6 30 52), (row3 6 30 53), (row3 6 30 54), (row3 6 30 55), (row3 6 30 56), (row3 6 30 57), (row3 6 30 58), (row3 6 30 59), (row3 6 30 60)]

def b038_11_labels : List Row := [(row3 238 462 238), (row3 255 256 256), (row3 238 462 238), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 265 266 266), (row3 209 209 206), (row3 265 268 268), (row3 265 266 266), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 265 266 266)]

theorem b038_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_11_rows b038_11_labels 87312242946512910561944520 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_11_rows b038_11_labels]
    decide +kernel

def b038_12_rows : List Row := [(row3 6 30 61), (row3 6 30 62), (row3 6 30 63), (row3 6 31 32), (row3 6 31 33), (row3 6 31 34), (row3 6 31 35), (row3 6 31 36), (row3 6 31 37), (row3 6 31 38), (row3 6 31 39), (row3 6 31 40), (row3 6 31 41), (row3 6 31 42), (row3 6 31 43), (row3 6 31 44)]

def b038_12_labels : List Row := [(row3 199 198 190), (row3 339 328 342), (row3 199 198 190), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_12_rows b038_12_labels 4975840867314755487128764350 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_12_rows b038_12_labels]
    decide +kernel

def b038_13_rows : List Row := [(row3 6 31 45), (row3 6 31 46), (row3 6 31 47), (row3 6 31 48), (row3 6 31 49), (row3 6 31 50), (row3 6 31 51), (row3 6 31 52), (row3 6 31 53), (row3 6 31 54), (row3 6 31 55), (row3 6 31 56), (row3 6 31 57), (row3 6 31 58), (row3 6 31 59), (row3 6 31 60)]

def b038_13_labels : List Row := [(row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 261 462 261), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 261 261 462), (row3 226 229 229), (row3 191 235 193), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 235 235 462)]

theorem b038_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_13_rows b038_13_labels 361802433972017426845968000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_13_rows b038_13_labels]
    decide +kernel

def b038_14_rows : List Row := [(row3 6 31 61), (row3 6 31 62), (row3 6 31 63), (row3 6 32 33), (row3 6 32 34), (row3 6 32 35), (row3 6 32 36), (row3 6 32 37), (row3 6 32 38), (row3 6 32 39), (row3 6 32 40), (row3 6 32 41), (row3 6 32 42), (row3 6 32 43), (row3 6 32 44), (row3 6 32 45)]

def b038_14_labels : List Row := [(row3 273 273 462), (row3 191 193 235), (row3 288 288 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_14_rows b038_14_labels 380444706051819377766663600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_14_rows b038_14_labels]
    decide +kernel

def b038_15_rows : List Row := [(row3 6 32 46), (row3 6 32 47), (row3 6 32 48), (row3 6 32 49), (row3 6 32 50), (row3 6 32 51), (row3 6 32 52), (row3 6 32 53), (row3 6 32 54), (row3 6 32 55), (row3 6 32 56), (row3 6 32 57), (row3 6 32 58), (row3 6 32 59), (row3 6 32 60), (row3 6 32 61)]

def b038_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 273 462 273), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 223 224 223), (row3 168 94 333), (row3 261 462 261), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b038_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b038_15_rows b038_15_labels 3238462997193940183271443680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b038_15_rows b038_15_labels]
    decide +kernel

theorem checked038 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_038 QuarticIntegerComputationalData.ids64_038 9786394501262269826760781350 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b038_00_rows ++ b038_01_rows) ++ (b038_02_rows ++ b038_03_rows)) ++ ((b038_04_rows ++ b038_05_rows) ++ (b038_06_rows ++ b038_07_rows))) ++ (((b038_08_rows ++ b038_09_rows) ++ (b038_10_rows ++ b038_11_rows)) ++ ((b038_12_rows ++ b038_13_rows) ++ (b038_14_rows ++ b038_15_rows))))
    ((((b038_00_labels ++ b038_01_labels) ++ (b038_02_labels ++ b038_03_labels)) ++ ((b038_04_labels ++ b038_05_labels) ++ (b038_06_labels ++ b038_07_labels))) ++ (((b038_08_labels ++ b038_09_labels) ++ (b038_10_labels ++ b038_11_labels)) ++ ((b038_12_labels ++ b038_13_labels) ++ (b038_14_labels ++ b038_15_labels)))) 9786394501262269826760781350
  exact ((((b038_00_checked.append (c := 365489351040475092933633600) b038_01_checked (by decide +kernel)).append (c := 365489351040475092933633600) (b038_02_checked.append (c := 0) b038_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 365489351040475092933633600) ((b038_04_checked.append (c := 0) b038_05_checked (by decide +kernel)).append (c := 0) (b038_06_checked.append (c := 0) b038_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 9786394501262269826760781350) (((b038_08_checked.append (c := 15165930949153510247164800) b038_09_checked (by decide +kernel)).append (c := 464354145689262258814308120) (b038_10_checked.append (c := 449188214740108748567143320) b038_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 9420905150221794733827147750) ((b038_12_checked.append (c := 5337643301286772913974732350) b038_13_checked (by decide +kernel)).append (c := 8956551004532532475012839630) (b038_14_checked.append (c := 3618907703245759561038107280) b038_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b039_00_rows : List Row := [(row3 6 32 62), (row3 6 32 63), (row3 6 33 34), (row3 6 33 35), (row3 6 33 36), (row3 6 33 37), (row3 6 33 38), (row3 6 33 39), (row3 6 33 40), (row3 6 33 41), (row3 6 33 42), (row3 6 33 43), (row3 6 33 44), (row3 6 33 45), (row3 6 33 46), (row3 6 33 47)]

def b039_00_labels : List Row := [(row3 237 462 237), (row3 261 288 290), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_00_rows b039_00_labels 20973011556476465710207200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_00_rows b039_00_labels]
    decide +kernel

def b039_01_rows : List Row := [(row3 6 33 48), (row3 6 33 49), (row3 6 33 50), (row3 6 33 51), (row3 6 33 52), (row3 6 33 53), (row3 6 33 54), (row3 6 33 55), (row3 6 33 56), (row3 6 33 57), (row3 6 33 58), (row3 6 33 59), (row3 6 33 60), (row3 6 33 61), (row3 6 33 62), (row3 6 33 63)]

def b039_01_labels : List Row := [(row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 284 284), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_01_rows b039_01_labels 62082383370327939168985500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_01_rows b039_01_labels]
    decide +kernel

def b039_02_rows : List Row := [(row3 6 34 35), (row3 6 34 36), (row3 6 34 37), (row3 6 34 38), (row3 6 34 39), (row3 6 34 40), (row3 6 34 41), (row3 6 34 42), (row3 6 34 43), (row3 6 34 44), (row3 6 34 45), (row3 6 34 46), (row3 6 34 47), (row3 6 34 48), (row3 6 34 49), (row3 6 34 50)]

def b039_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_02_rows b039_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_02_rows b039_02_labels]
    decide +kernel

def b039_03_rows : List Row := [(row3 6 34 51), (row3 6 34 52), (row3 6 34 53), (row3 6 34 54), (row3 6 34 55), (row3 6 34 56), (row3 6 34 57), (row3 6 34 58), (row3 6 34 59), (row3 6 34 60), (row3 6 34 61), (row3 6 34 62), (row3 6 34 63), (row3 6 35 36), (row3 6 35 37), (row3 6 35 38)]

def b039_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_03_rows b039_03_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_03_rows b039_03_labels]
    decide +kernel

def b039_04_rows : List Row := [(row3 6 35 39), (row3 6 35 40), (row3 6 35 41), (row3 6 35 42), (row3 6 35 43), (row3 6 35 44), (row3 6 35 45), (row3 6 35 46), (row3 6 35 47), (row3 6 35 48), (row3 6 35 49), (row3 6 35 50), (row3 6 35 51), (row3 6 35 52), (row3 6 35 53), (row3 6 35 54)]

def b039_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_04_rows b039_04_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_04_rows b039_04_labels]
    decide +kernel

def b039_05_rows : List Row := [(row3 6 35 55), (row3 6 35 56), (row3 6 35 57), (row3 6 35 58), (row3 6 35 59), (row3 6 35 60), (row3 6 35 61), (row3 6 35 62), (row3 6 35 63), (row3 6 36 37), (row3 6 36 38), (row3 6 36 39), (row3 6 36 40), (row3 6 36 41), (row3 6 36 42), (row3 6 36 43)]

def b039_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_05_rows b039_05_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_05_rows b039_05_labels]
    decide +kernel

def b039_06_rows : List Row := [(row3 6 36 44), (row3 6 36 45), (row3 6 36 46), (row3 6 36 47), (row3 6 36 48), (row3 6 36 49), (row3 6 36 50), (row3 6 36 51), (row3 6 36 52), (row3 6 36 53), (row3 6 36 54), (row3 6 36 55), (row3 6 36 56), (row3 6 36 57), (row3 6 36 58), (row3 6 36 59)]

def b039_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_06_rows b039_06_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_06_rows b039_06_labels]
    decide +kernel

def b039_07_rows : List Row := [(row3 6 36 60), (row3 6 36 61), (row3 6 36 62), (row3 6 36 63), (row3 6 37 38), (row3 6 37 39), (row3 6 37 40), (row3 6 37 41), (row3 6 37 42), (row3 6 37 43), (row3 6 37 44), (row3 6 37 45), (row3 6 37 46), (row3 6 37 47), (row3 6 37 48), (row3 6 37 49)]

def b039_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_07_rows b039_07_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_07_rows b039_07_labels]
    decide +kernel

def b039_08_rows : List Row := [(row3 6 37 50), (row3 6 37 51), (row3 6 37 52), (row3 6 37 53), (row3 6 37 54), (row3 6 37 55), (row3 6 37 56), (row3 6 37 57), (row3 6 37 58), (row3 6 37 59), (row3 6 37 60), (row3 6 37 61), (row3 6 37 62), (row3 6 37 63), (row3 6 38 39), (row3 6 38 40)]

def b039_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 236 236 462), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_08_rows b039_08_labels 62082383370327939168985500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_08_rows b039_08_labels]
    decide +kernel

def b039_09_rows : List Row := [(row3 6 38 41), (row3 6 38 42), (row3 6 38 43), (row3 6 38 44), (row3 6 38 45), (row3 6 38 46), (row3 6 38 47), (row3 6 38 48), (row3 6 38 49), (row3 6 38 50), (row3 6 38 51), (row3 6 38 52), (row3 6 38 53), (row3 6 38 54), (row3 6 38 55), (row3 6 38 56)]

def b039_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 239 239 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 273 273 462), (row3 223 223 224), (row3 237 237 462)]

theorem b039_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_09_rows b039_09_labels 17676631476158266346348880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_09_rows b039_09_labels]
    decide +kernel

def b039_10_rows : List Row := [(row3 6 38 57), (row3 6 38 58), (row3 6 38 59), (row3 6 38 60), (row3 6 38 61), (row3 6 38 62), (row3 6 38 63), (row3 6 39 40), (row3 6 39 41), (row3 6 39 42), (row3 6 39 43), (row3 6 39 44), (row3 6 39 45), (row3 6 39 46), (row3 6 39 47), (row3 6 39 48)]

def b039_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 261 261 462), (row3 168 333 94), (row3 261 290 288), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234)]

theorem b039_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_10_rows b039_10_labels 3244793297018253228216198000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_10_rows b039_10_labels]
    decide +kernel

def b039_11_rows : List Row := [(row3 6 39 49), (row3 6 39 50), (row3 6 39 51), (row3 6 39 52), (row3 6 39 53), (row3 6 39 54), (row3 6 39 55), (row3 6 39 56), (row3 6 39 57), (row3 6 39 58), (row3 6 39 59), (row3 6 39 60), (row3 6 39 61), (row3 6 39 62), (row3 6 39 63), (row3 6 40 41)]

def b039_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 289 291 291), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 161 176 176), (row3 238 238 462)]

theorem b039_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_11_rows b039_11_labels 389474618101340171004268560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_11_rows b039_11_labels]
    decide +kernel

def b039_12_rows : List Row := [(row3 6 40 42), (row3 6 40 43), (row3 6 40 44), (row3 6 40 45), (row3 6 40 46), (row3 6 40 47), (row3 6 40 48), (row3 6 40 49), (row3 6 40 50), (row3 6 40 51), (row3 6 40 52), (row3 6 40 53), (row3 6 40 54), (row3 6 40 55), (row3 6 40 56), (row3 6 40 57)]

def b039_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 164 206 164), (row3 265 266 266), (row3 237 237 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 315 318 318), (row3 385 426 77), (row3 197 190 196)]

theorem b039_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_12_rows b039_12_labels 67795263731350845097676449020 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_12_rows b039_12_labels]
    decide +kernel

def b039_13_rows : List Row := [(row3 6 40 58), (row3 6 40 59), (row3 6 40 60), (row3 6 40 61), (row3 6 40 62), (row3 6 40 63), (row3 6 41 42), (row3 6 41 43), (row3 6 41 44), (row3 6 41 45), (row3 6 41 46), (row3 6 41 47), (row3 6 41 48), (row3 6 41 49), (row3 6 41 50), (row3 6 41 51)]

def b039_13_labels : List Row := [(row3 265 266 266), (row3 238 238 462), (row3 462 462 462), (row3 238 238 462), (row3 265 302 302), (row3 109 110 111), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b039_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_13_rows b039_13_labels 1158158360242946450436859260 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_13_rows b039_13_labels]
    decide +kernel

def b039_14_rows : List Row := [(row3 6 41 52), (row3 6 41 53), (row3 6 41 54), (row3 6 41 55), (row3 6 41 56), (row3 6 41 57), (row3 6 41 58), (row3 6 41 59), (row3 6 41 60), (row3 6 41 61), (row3 6 41 62), (row3 6 41 63), (row3 6 42 43), (row3 6 42 44), (row3 6 42 45), (row3 6 42 46)]

def b039_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 222 224 222), (row3 122 86 369), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 295 304), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_14_rows b039_14_labels 9965936596081957447855664160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_14_rows b039_14_labels]
    decide +kernel

def b039_15_rows : List Row := [(row3 6 42 47), (row3 6 42 48), (row3 6 42 49), (row3 6 42 50), (row3 6 42 51), (row3 6 42 52), (row3 6 42 53), (row3 6 42 54), (row3 6 42 55), (row3 6 42 56), (row3 6 42 57), (row3 6 42 58), (row3 6 42 59), (row3 6 42 60), (row3 6 42 61), (row3 6 42 62)]

def b039_15_labels : List Row := [(row3 462 462 462), (row3 234 462 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 293 293), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b039_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b039_15_rows b039_15_labels 93421654462050945768670500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b039_15_rows b039_15_labels]
    decide +kernel

theorem checked039 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_039 QuarticIntegerComputationalData.ids64_039 82809862667030683951352636580 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b039_00_rows ++ b039_01_rows) ++ (b039_02_rows ++ b039_03_rows)) ++ ((b039_04_rows ++ b039_05_rows) ++ (b039_06_rows ++ b039_07_rows))) ++ (((b039_08_rows ++ b039_09_rows) ++ (b039_10_rows ++ b039_11_rows)) ++ ((b039_12_rows ++ b039_13_rows) ++ (b039_14_rows ++ b039_15_rows))))
    ((((b039_00_labels ++ b039_01_labels) ++ (b039_02_labels ++ b039_03_labels)) ++ ((b039_04_labels ++ b039_05_labels) ++ (b039_06_labels ++ b039_07_labels))) ++ (((b039_08_labels ++ b039_09_labels) ++ (b039_10_labels ++ b039_11_labels)) ++ ((b039_12_labels ++ b039_13_labels) ++ (b039_14_labels ++ b039_15_labels)))) 82809862667030683951352636580
  exact ((((b039_00_checked.append (c := 83055394926804404879192700) b039_01_checked (by decide +kernel)).append (c := 83055394926804404879192700) (b039_02_checked.append (c := 0) b039_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 83055394926804404879192700) ((b039_04_checked.append (c := 0) b039_05_checked (by decide +kernel)).append (c := 0) (b039_06_checked.append (c := 0) b039_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 82809862667030683951352636580) (((b039_08_checked.append (c := 79759014846486205515334380) b039_09_checked (by decide +kernel)).append (c := 3714026929966079604735800940) (b039_10_checked.append (c := 3634267915119593399220466560) b039_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 82726807272103879546473443880) ((b039_12_checked.append (c := 68953422091593791548113308280) b039_13_checked (by decide +kernel)).append (c := 79012780342137799941737642940) (b039_14_checked.append (c := 10059358250544008393624334660) b039_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b040_00_rows : List Row := [(row3 6 42 63), (row3 6 43 44), (row3 6 43 45), (row3 6 43 46), (row3 6 43 47), (row3 6 43 48), (row3 6 43 49), (row3 6 43 50), (row3 6 43 51), (row3 6 43 52), (row3 6 43 53), (row3 6 43 54), (row3 6 43 55), (row3 6 43 56), (row3 6 43 57), (row3 6 43 58)]

def b040_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b040_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_00_rows b040_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_00_rows b040_00_labels]
    decide +kernel

def b040_01_rows : List Row := [(row3 6 43 59), (row3 6 43 60), (row3 6 43 61), (row3 6 43 62), (row3 6 43 63), (row3 6 44 45), (row3 6 44 46), (row3 6 44 47), (row3 6 44 48), (row3 6 44 49), (row3 6 44 50), (row3 6 44 51), (row3 6 44 52), (row3 6 44 53), (row3 6 44 54), (row3 6 44 55)]

def b040_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 462 246 246)]

theorem b040_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_01_rows b040_01_labels 786408826682880937449000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_01_rows b040_01_labels]
    decide +kernel

def b040_02_rows : List Row := [(row3 6 44 56), (row3 6 44 57), (row3 6 44 58), (row3 6 44 59), (row3 6 44 60), (row3 6 44 61), (row3 6 44 62), (row3 6 44 63), (row3 6 45 46), (row3 6 45 47), (row3 6 45 48), (row3 6 45 49), (row3 6 45 50), (row3 6 45 51), (row3 6 45 52), (row3 6 45 53)]

def b040_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 462 293 293), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462)]

theorem b040_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_02_rows b040_02_labels 110941483508128341312277500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_02_rows b040_02_labels]
    decide +kernel

def b040_03_rows : List Row := [(row3 6 45 54), (row3 6 45 55), (row3 6 45 56), (row3 6 45 57), (row3 6 45 58), (row3 6 45 59), (row3 6 45 60), (row3 6 45 61), (row3 6 45 62), (row3 6 45 63), (row3 6 46 47), (row3 6 46 48), (row3 6 46 49), (row3 6 46 50), (row3 6 46 51), (row3 6 46 52)]

def b040_03_labels : List Row := [(row3 288 288 462), (row3 222 222 224), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 288 288 462), (row3 122 369 86), (row3 273 304 295), (row3 238 462 238), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237)]

theorem b040_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_03_rows b040_03_labels 10010335827202153030137692880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_03_rows b040_03_labels]
    decide +kernel

def b040_04_rows : List Row := [(row3 6 46 53), (row3 6 46 54), (row3 6 46 55), (row3 6 46 56), (row3 6 46 57), (row3 6 46 58), (row3 6 46 59), (row3 6 46 60), (row3 6 46 61), (row3 6 46 62), (row3 6 46 63), (row3 6 47 48), (row3 6 47 49), (row3 6 47 50), (row3 6 47 51), (row3 6 47 52)]

def b040_04_labels : List Row := [(row3 265 266 266), (row3 164 164 206), (row3 315 318 318), (row3 265 302 302), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 265 266 266), (row3 197 196 190), (row3 385 77 426), (row3 109 111 110), (row3 288 462 288), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b040_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_04_rows b040_04_labels 68934238343875631804162174280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_04_rows b040_04_labels]
    decide +kernel

def b040_05_rows : List Row := [(row3 6 47 53), (row3 6 47 54), (row3 6 47 55), (row3 6 47 56), (row3 6 47 57), (row3 6 47 58), (row3 6 47 59), (row3 6 47 60), (row3 6 47 61), (row3 6 47 62), (row3 6 47 63), (row3 6 48 49), (row3 6 48 50), (row3 6 48 51), (row3 6 48 52), (row3 6 48 53)]

def b040_05_labels : List Row := [(row3 235 235 462), (row3 288 288 462), (row3 130 104 104), (row3 121 85 369), (row3 273 462 273), (row3 235 462 235), (row3 462 462 462), (row3 235 235 462), (row3 273 273 462), (row3 121 369 85), (row3 379 380 380), (row3 140 140 178), (row3 278 278 462), (row3 237 237 462), (row3 462 462 462), (row3 232 232 462)]

theorem b040_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_05_rows b040_05_labels 43131062556487565194549919760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_05_rows b040_05_labels]
    decide +kernel

def b040_06_rows : List Row := [(row3 6 48 54), (row3 6 48 55), (row3 6 48 56), (row3 6 48 57), (row3 6 48 58), (row3 6 48 59), (row3 6 48 60), (row3 6 48 61), (row3 6 48 62), (row3 6 48 63), (row3 6 49 50), (row3 6 49 51), (row3 6 49 52), (row3 6 49 53), (row3 6 49 54), (row3 6 49 55)]

def b040_06_labels : List Row := [(row3 295 295 462), (row3 367 108 84), (row3 37 28 444), (row3 351 348 350), (row3 182 182 178), (row3 261 261 462), (row3 234 234 462), (row3 288 288 462), (row3 108 367 84), (row3 406 406 405), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 306 313 313)]

theorem b040_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_06_rows b040_06_labels 4639864013080954820012221763040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_06_rows b040_06_labels]
    decide +kernel

def b040_07_rows : List Row := [(row3 6 49 56), (row3 6 49 57), (row3 6 49 58), (row3 6 49 59), (row3 6 49 60), (row3 6 49 61), (row3 6 49 62), (row3 6 49 63), (row3 6 50 51), (row3 6 50 52), (row3 6 50 53), (row3 6 50 54), (row3 6 50 55), (row3 6 50 56), (row3 6 50 57), (row3 6 50 58)]

def b040_07_labels : List Row := [(row3 410 431 59), (row3 127 137 126), (row3 289 291 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 289 305 305), (row3 98 99 101), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 234 228), (row3 114 86 368), (row3 300 462 300), (row3 234 462 234)]

theorem b040_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_07_rows b040_07_labels 170420047924458897554039702820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_07_rows b040_07_labels]
    decide +kernel

def b040_08_rows : List Row := [(row3 6 50 59), (row3 6 50 60), (row3 6 50 61), (row3 6 50 62), (row3 6 50 63), (row3 6 51 52), (row3 6 51 53), (row3 6 51 54), (row3 6 51 55), (row3 6 51 56), (row3 6 51 57), (row3 6 51 58), (row3 6 51 59), (row3 6 51 60), (row3 6 51 61), (row3 6 51 62)]

def b040_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 462 234), (row3 278 288 300), (row3 462 462 462), (row3 462 462 462), (row3 237 237 462), (row3 462 244 244), (row3 462 284 284), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 232 462), (row3 462 284 284)]

theorem b040_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_08_rows b040_08_labels 154670510777042367947227500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_08_rows b040_08_labels]
    decide +kernel

def b040_09_rows : List Row := [(row3 6 51 63), (row3 6 52 53), (row3 6 52 54), (row3 6 52 55), (row3 6 52 56), (row3 6 52 57), (row3 6 52 58), (row3 6 52 59), (row3 6 52 60), (row3 6 52 61), (row3 6 52 62), (row3 6 52 63), (row3 6 53 54), (row3 6 53 55), (row3 6 53 56), (row3 6 53 57)]

def b040_09_labels : List Row := [(row3 462 462 462), (row3 234 234 462), (row3 278 278 462), (row3 228 228 234), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 300 300 462), (row3 114 368 86), (row3 278 300 288), (row3 140 140 178), (row3 306 313 313), (row3 289 305 305), (row3 235 462 235)]

theorem b040_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_09_rows b040_09_labels 15442596179735468790221523720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_09_rows b040_09_labels]
    decide +kernel

def b040_10_rows : List Row := [(row3 6 53 58), (row3 6 53 59), (row3 6 53 60), (row3 6 53 61), (row3 6 53 62), (row3 6 53 63), (row3 6 54 55), (row3 6 54 56), (row3 6 54 57), (row3 6 54 58), (row3 6 54 59), (row3 6 54 60), (row3 6 54 61), (row3 6 54 62), (row3 6 54 63), (row3 6 55 56)]

def b040_10_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 289 291 291), (row3 127 126 137), (row3 410 59 431), (row3 98 101 99), (row3 367 84 108), (row3 108 84 367), (row3 288 462 288), (row3 234 462 234), (row3 261 462 261), (row3 182 178 182), (row3 351 350 348), (row3 37 444 28), (row3 406 405 406), (row3 411 432 60)]

theorem b040_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_10_rows b040_10_labels 5019341811486677971963672426920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_10_rows b040_10_labels]
    decide +kernel

def b040_11_rows : List Row := [(row3 6 55 57), (row3 6 55 58), (row3 6 55 59), (row3 6 55 60), (row3 6 55 61), (row3 6 55 62), (row3 6 55 63), (row3 6 56 57), (row3 6 56 58), (row3 6 56 59), (row3 6 56 60), (row3 6 56 61), (row3 6 56 62), (row3 6 56 63), (row3 6 57 58), (row3 6 57 59)]

def b040_11_labels : List Row := [(row3 142 136 141), (row3 289 292 292), (row3 232 235 235), (row3 289 292 292), (row3 142 141 136), (row3 411 60 432), (row3 38 33 33), (row3 34 443 27), (row3 401 78 427), (row3 155 332 93), (row3 289 299 299), (row3 123 331 92), (row3 419 63 433), (row3 451 442 24), (row3 127 126 137), (row3 288 288 462)]

theorem b040_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_11_rows b040_11_labels 42613914635174286293295009391380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_11_rows b040_11_labels]
    decide +kernel

def b040_12_rows : List Row := [(row3 6 57 60), (row3 6 57 61), (row3 6 57 62), (row3 6 57 63), (row3 6 58 59), (row3 6 58 60), (row3 6 58 61), (row3 6 58 62), (row3 6 58 63), (row3 6 59 60), (row3 6 59 61), (row3 6 59 62), (row3 6 59 63), (row3 6 60 61), (row3 6 60 62), (row3 6 60 63)]

def b040_12_labels : List Row := [(row3 233 233 462), (row3 288 288 462), (row3 123 331 92), (row3 402 404 403), (row3 235 235 462), (row3 462 462 462), (row3 233 233 462), (row3 289 299 299), (row3 126 125 128), (row3 235 235 462), (row3 288 288 462), (row3 155 332 93), (row3 288 288 288), (row3 127 126 137), (row3 401 78 427), (row3 126 128 125)]

theorem b040_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_12_rows b040_12_labels 143149507948771218819101870640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_12_rows b040_12_labels]
    decide +kernel

def b040_13_rows : List Row := [(row3 6 61 62), (row3 6 61 63), (row3 6 62 63), (row3 7 8 9), (row3 7 8 10), (row3 7 8 11), (row3 7 8 12), (row3 7 8 13), (row3 7 8 14), (row3 7 8 15), (row3 7 8 16), (row3 7 8 17), (row3 7 8 18), (row3 7 8 19), (row3 7 8 20), (row3 7 8 21)]

def b040_13_labels : List Row := [(row3 34 443 27), (row3 402 403 404), (row3 451 24 442), (row3 457 23 461), (row3 34 443 27), (row3 359 73 429), (row3 163 193 139), (row3 44 74 439), (row3 451 442 24), (row3 20 20 17), (row3 450 22 460), (row3 32 452 25), (row3 389 45 436), (row3 462 163 163), (row3 462 462 462), (row3 139 163 124)]

theorem b040_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_13_rows b040_13_labels 11369825501892780131359908470025240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_13_rows b040_13_labels]
    decide +kernel

def b040_14_rows : List Row := [(row3 7 8 22), (row3 7 8 23), (row3 7 8 24), (row3 7 8 25), (row3 7 8 26), (row3 7 8 27), (row3 7 8 28), (row3 7 8 29), (row3 7 8 30), (row3 7 8 31), (row3 7 8 32), (row3 7 8 33), (row3 7 8 34), (row3 7 8 35), (row3 7 8 36), (row3 7 8 37)]

def b040_14_labels : List Row := [(row3 46 46 440), (row3 442 451 24), (row3 56 445 29), (row3 383 43 436), (row3 462 139 139), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 139 124), (row3 74 44 439), (row3 341 71 429), (row3 462 163 163), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b040_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_14_rows b040_14_labels 33786317729372301921242292934380 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_14_rows b040_14_labels]
    decide +kernel

def b040_15_rows : List Row := [(row3 7 8 38), (row3 7 8 39), (row3 7 8 40), (row3 7 8 41), (row3 7 8 42), (row3 7 8 43), (row3 7 8 44), (row3 7 8 45), (row3 7 8 46), (row3 7 8 47), (row3 7 8 48), (row3 7 8 49), (row3 7 8 50), (row3 7 8 51), (row3 7 8 52), (row3 7 8 53)]

def b040_15_labels : List Row := [(row3 462 462 462), (row3 193 163 139), (row3 64 66 55), (row3 358 358 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 163 462 163), (row3 73 359 429), (row3 448 449 454), (row3 35 36 31), (row3 377 377 462), (row3 462 462 462), (row3 462 462 462), (row3 139 462 139)]

theorem b040_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b040_15_rows b040_15_labels 8526904535239884512621587593000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b040_15_rows b040_15_labels]
    decide +kernel

theorem checked040 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_040 QuarticIntegerComputationalData.ids64_040 11464863198804317879667825663972060 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b040_00_rows ++ b040_01_rows) ++ (b040_02_rows ++ b040_03_rows)) ++ ((b040_04_rows ++ b040_05_rows) ++ (b040_06_rows ++ b040_07_rows))) ++ (((b040_08_rows ++ b040_09_rows) ++ (b040_10_rows ++ b040_11_rows)) ++ ((b040_12_rows ++ b040_13_rows) ++ (b040_14_rows ++ b040_15_rows))))
    ((((b040_00_labels ++ b040_01_labels) ++ (b040_02_labels ++ b040_03_labels)) ++ ((b040_04_labels ++ b040_05_labels) ++ (b040_06_labels ++ b040_07_labels))) ++ (((b040_08_labels ++ b040_09_labels) ++ (b040_10_labels ++ b040_11_labels)) ++ ((b040_12_labels ++ b040_13_labels) ++ (b040_14_labels ++ b040_15_labels)))) 11464863198804317879667825663972060
  exact ((((b040_00_checked.append (c := 786408826682880937449000) b040_01_checked (by decide +kernel)).append (c := 10122063719536964252387419380) (b040_02_checked.append (c := 10121277310710281371449970380) b040_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4932471425625313878817360979280) ((b040_04_checked.append (c := 112065300900363196998712094040) b040_05_checked (by decide +kernel)).append (c := 4922349361905776914564973559900) (b040_06_checked.append (c := 4810284061005413717566261465860) b040_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11464863198804317879667825663972060) (((b040_08_checked.append (c := 15597266690512511158168751220) b040_09_checked (by decide +kernel)).append (c := 47648853713351476776416850569520) (b040_10_checked.append (c := 47633256446660964265258681818300) b040_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 11459930727378692565789008302992780) ((b040_12_checked.append (c := 11369968651400728902578727571895880) b040_13_checked (by decide +kernel)).append (c := 11412281873665341089012591452423260) (b040_14_checked.append (c := 42313222264612186433863880527380) b040_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
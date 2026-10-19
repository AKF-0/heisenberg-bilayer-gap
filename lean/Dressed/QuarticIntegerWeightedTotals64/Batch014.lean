import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerDictionaryData64
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData64.Batch013
import Dressed.QuarticIntegerComputationalData64.Batch014


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b113_00_rows : List Row := [(row3 22 47 61), (row3 22 47 62), (row3 22 47 63), (row3 22 48 49), (row3 22 48 50), (row3 22 48 51), (row3 22 48 52), (row3 22 48 53), (row3 22 48 54), (row3 22 48 55), (row3 22 48 56), (row3 22 48 57), (row3 22 48 58), (row3 22 48 59), (row3 22 48 60), (row3 22 48 61)]

def b113_00_labels : List Row := [(row3 462 462 462), (row3 234 234 234), (row3 273 462 273), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 234 234), (row3 462 180 180), (row3 462 278 278), (row3 462 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_00_rows b113_00_labels 781698666569349248275852800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_00_rows b113_00_labels]
    decide +kernel

def b113_01_rows : List Row := [(row3 22 48 62), (row3 22 48 63), (row3 22 49 50), (row3 22 49 51), (row3 22 49 52), (row3 22 49 53), (row3 22 49 54), (row3 22 49 55), (row3 22 49 56), (row3 22 49 57), (row3 22 49 58), (row3 22 49 59), (row3 22 49 60), (row3 22 49 61), (row3 22 49 62), (row3 22 49 63)]

def b113_01_labels : List Row := [(row3 234 228 228), (row3 288 278 300), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 248 248), (row3 462 293 293), (row3 462 228 228), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 250 250), (row3 232 228 223)]

theorem b113_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_01_rows b113_01_labels 129906631580198299430490000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_01_rows b113_01_labels]
    decide +kernel

def b113_02_rows : List Row := [(row3 22 50 51), (row3 22 50 52), (row3 22 50 53), (row3 22 50 54), (row3 22 50 55), (row3 22 50 56), (row3 22 50 57), (row3 22 50 58), (row3 22 50 59), (row3 22 50 60), (row3 22 50 61), (row3 22 50 62), (row3 22 50 63), (row3 22 51 52), (row3 22 51 53), (row3 22 51 54)]

def b113_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_02_rows b113_02_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_02_rows b113_02_labels]
    decide +kernel

def b113_03_rows : List Row := [(row3 22 51 55), (row3 22 51 56), (row3 22 51 57), (row3 22 51 58), (row3 22 51 59), (row3 22 51 60), (row3 22 51 61), (row3 22 51 62), (row3 22 51 63), (row3 22 52 53), (row3 22 52 54), (row3 22 52 55), (row3 22 52 56), (row3 22 52 57), (row3 22 52 58), (row3 22 52 59)]

def b113_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_03_rows b113_03_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_03_rows b113_03_labels]
    decide +kernel

def b113_04_rows : List Row := [(row3 22 52 60), (row3 22 52 61), (row3 22 52 62), (row3 22 52 63), (row3 22 53 54), (row3 22 53 55), (row3 22 53 56), (row3 22 53 57), (row3 22 53 58), (row3 22 53 59), (row3 22 53 60), (row3 22 53 61), (row3 22 53 62), (row3 22 53 63), (row3 22 54 55), (row3 22 54 56)]

def b113_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 279 279), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462)]

theorem b113_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_04_rows b113_04_labels 10655037029359475384943600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_04_rows b113_04_labels]
    decide +kernel

def b113_05_rows : List Row := [(row3 22 54 57), (row3 22 54 58), (row3 22 54 59), (row3 22 54 60), (row3 22 54 61), (row3 22 54 62), (row3 22 54 63), (row3 22 55 56), (row3 22 55 57), (row3 22 55 58), (row3 22 55 59), (row3 22 55 60), (row3 22 55 61), (row3 22 55 62), (row3 22 55 63), (row3 22 56 57)]

def b113_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 180 154 154), (row3 288 462 288), (row3 462 293 293), (row3 462 228 228), (row3 462 248 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 283 283), (row3 163 228 160), (row3 462 139 139)]

theorem b113_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_05_rows b113_05_labels 3215202574324310366397185700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_05_rows b113_05_labels]
    decide +kernel

def b113_06_rows : List Row := [(row3 22 56 58), (row3 22 56 59), (row3 22 56 60), (row3 22 56 61), (row3 22 56 62), (row3 22 56 63), (row3 22 57 58), (row3 22 57 59), (row3 22 57 60), (row3 22 57 61), (row3 22 57 62), (row3 22 57 63), (row3 22 58 59), (row3 22 58 60), (row3 22 58 61), (row3 22 58 62)]

def b113_06_labels : List Row := [(row3 462 293 293), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 265 302 302), (row3 163 139 124), (row3 462 228 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 226 226), (row3 273 295 304), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 249 249)]

theorem b113_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_06_rows b113_06_labels 2893767151704118587134438400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_06_rows b113_06_labels]
    decide +kernel

def b113_07_rows : List Row := [(row3 22 58 63), (row3 22 59 60), (row3 22 59 61), (row3 22 59 62), (row3 22 59 63), (row3 22 60 61), (row3 22 60 62), (row3 22 60 63), (row3 22 61 62), (row3 22 61 63), (row3 22 62 63), (row3 23 24 25), (row3 23 24 26), (row3 23 24 27), (row3 23 24 28), (row3 23 24 29)]

def b113_07_labels : List Row := [(row3 236 228 225), (row3 462 462 462), (row3 462 462 462), (row3 237 237 237), (row3 462 462 462), (row3 462 462 462), (row3 265 266 266), (row3 236 462 236), (row3 180 154 154), (row3 273 462 273), (row3 356 89 158), (row3 354 376 366), (row3 197 190 196), (row3 262 262 261), (row3 232 238 230), (row3 317 317 308)]

theorem b113_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_07_rows b113_07_labels 23947710092472346095128604930 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_07_rows b113_07_labels]
    decide +kernel

def b113_08_rows : List Row := [(row3 23 24 30), (row3 23 24 31), (row3 23 24 32), (row3 23 24 33), (row3 23 24 34), (row3 23 24 35), (row3 23 24 36), (row3 23 24 37), (row3 23 24 38), (row3 23 24 39), (row3 23 24 40), (row3 23 24 41), (row3 23 24 42), (row3 23 24 43), (row3 23 24 44), (row3 23 24 45)]

def b113_08_labels : List Row := [(row3 109 110 111), (row3 74 44 439), (row3 353 375 366), (row3 175 161 175), (row3 279 279 278), (row3 462 236 236), (row3 462 462 462), (row3 228 236 225), (row3 320 320 319), (row3 125 126 128), (row3 195 188 194), (row3 280 280 278), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_08_rows b113_08_labels 543712427377501010862604978410 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_08_rows b113_08_labels]
    decide +kernel

def b113_09_rows : List Row := [(row3 23 24 46), (row3 23 24 47), (row3 23 24 48), (row3 23 24 49), (row3 23 24 50), (row3 23 24 51), (row3 23 24 52), (row3 23 24 53), (row3 23 24 54), (row3 23 24 55), (row3 23 24 56), (row3 23 24 57), (row3 23 24 58), (row3 23 24 59), (row3 23 24 60), (row3 23 24 61)]

def b113_09_labels : List Row := [(row3 232 235 228), (row3 297 297 295), (row3 276 276 275), (row3 234 231 231), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 229 231 227), (row3 151 153 179), (row3 279 279 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462)]

theorem b113_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_09_rows b113_09_labels 6667934032476377519777984280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_09_rows b113_09_labels]
    decide +kernel

def b113_10_rows : List Row := [(row3 23 24 62), (row3 23 24 63), (row3 23 25 26), (row3 23 25 27), (row3 23 25 28), (row3 23 25 29), (row3 23 25 30), (row3 23 25 31), (row3 23 25 32), (row3 23 25 33), (row3 23 25 34), (row3 23 25 35), (row3 23 25 36), (row3 23 25 37), (row3 23 25 38), (row3 23 25 39)]

def b113_10_labels : List Row := [(row3 226 234 226), (row3 296 296 295), (row3 286 462 286), (row3 235 462 235), (row3 247 462 247), (row3 224 224 224), (row3 310 306 310), (row3 121 369 85), (row3 220 222 221), (row3 287 462 287), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 292 289 292)]

theorem b113_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_10_rows b113_10_labels 10281361656994541364801020760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_10_rows b113_10_labels]
    decide +kernel

def b113_11_rows : List Row := [(row3 23 25 40), (row3 23 25 41), (row3 23 25 42), (row3 23 25 43), (row3 23 25 44), (row3 23 25 45), (row3 23 25 46), (row3 23 25 47), (row3 23 25 48), (row3 23 25 49), (row3 23 25 50), (row3 23 25 51), (row3 23 25 52), (row3 23 25 53), (row3 23 25 54), (row3 23 25 55)]

def b113_11_labels : List Row := [(row3 252 462 252), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 235 462 235), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248)]

theorem b113_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_11_rows b113_11_labels 1342397602312710939112500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_11_rows b113_11_labels]
    decide +kernel

def b113_12_rows : List Row := [(row3 23 25 56), (row3 23 25 57), (row3 23 25 58), (row3 23 25 59), (row3 23 25 60), (row3 23 25 61), (row3 23 25 62), (row3 23 25 63), (row3 23 26 27), (row3 23 26 28), (row3 23 26 29), (row3 23 26 30), (row3 23 26 31), (row3 23 26 32), (row3 23 26 33), (row3 23 26 34)]

def b113_12_labels : List Row := [(row3 286 462 286), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 462 251), (row3 226 234 226), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 232 232 462), (row3 254 171 10), (row3 248 248 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_12_rows b113_12_labels 621041087584111676773284000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_12_rows b113_12_labels]
    decide +kernel

def b113_13_rows : List Row := [(row3 23 26 35), (row3 23 26 36), (row3 23 26 37), (row3 23 26 38), (row3 23 26 39), (row3 23 26 40), (row3 23 26 41), (row3 23 26 42), (row3 23 26 43), (row3 23 26 44), (row3 23 26 45), (row3 23 26 46), (row3 23 26 47), (row3 23 26 48), (row3 23 26 49), (row3 23 26 50)]

def b113_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_13_rows b113_13_labels 295728807902769650916000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_13_rows b113_13_labels]
    decide +kernel

def b113_14_rows : List Row := [(row3 23 26 51), (row3 23 26 52), (row3 23 26 53), (row3 23 26 54), (row3 23 26 55), (row3 23 26 56), (row3 23 26 57), (row3 23 26 58), (row3 23 26 59), (row3 23 26 60), (row3 23 26 61), (row3 23 26 62), (row3 23 26 63), (row3 23 27 28), (row3 23 27 29), (row3 23 27 30)]

def b113_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_14_rows b113_14_labels 16102107813616554645000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_14_rows b113_14_labels]
    decide +kernel

def b113_15_rows : List Row := [(row3 23 27 31), (row3 23 27 32), (row3 23 27 33), (row3 23 27 34), (row3 23 27 35), (row3 23 27 36), (row3 23 27 37), (row3 23 27 38), (row3 23 27 39), (row3 23 27 40), (row3 23 27 41), (row3 23 27 42), (row3 23 27 43), (row3 23 27 44), (row3 23 27 45), (row3 23 27 46)]

def b113_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b113_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b113_15_rows b113_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b113_15_rows b113_15_labels]
    decide +kernel

theorem checked113 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_113 QuarticIntegerComputationalData.ids64_113 592263366196854109496091181380 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b113_00_rows ++ b113_01_rows) ++ (b113_02_rows ++ b113_03_rows)) ++ ((b113_04_rows ++ b113_05_rows) ++ (b113_06_rows ++ b113_07_rows))) ++ (((b113_08_rows ++ b113_09_rows) ++ (b113_10_rows ++ b113_11_rows)) ++ ((b113_12_rows ++ b113_13_rows) ++ (b113_14_rows ++ b113_15_rows))))
    ((((b113_00_labels ++ b113_01_labels) ++ (b113_02_labels ++ b113_03_labels)) ++ ((b113_04_labels ++ b113_05_labels) ++ (b113_06_labels ++ b113_07_labels))) ++ (((b113_08_labels ++ b113_09_labels) ++ (b113_10_labels ++ b113_11_labels)) ++ ((b113_12_labels ++ b113_13_labels) ++ (b113_14_labels ++ b113_15_labels)))) 592263366196854109496091181380
  exact ((((b113_00_checked.append (c := 911605298149547547706342800) b113_01_checked (by decide +kernel)).append (c := 911612958249904450944067800) (b113_02_checked.append (c := 7660100356903237725000) b113_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 30978947813780038974989240430) ((b113_04_checked.append (c := 3225857611353669841782129300) b113_05_checked (by decide +kernel)).append (c := 30067334855530134524045172630) (b113_06_checked.append (c := 26841477244176464682263043330) b113_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 592263366196854109496091181380) (((b113_08_checked.append (c := 550380361409977388382382962690) b113_09_checked (by decide +kernel)).append (c := 560663065464574242458123095950) (b113_10_checked.append (c := 10282704054596854075740133260) b113_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 561284418383074070521101940950) ((b113_12_checked.append (c := 621336816392014446424200000) b113_13_checked (by decide +kernel)).append (c := 621352918499828062978845000) (b113_14_checked.append (c := 16102107813616554645000) b113_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b114_00_rows : List Row := [(row3 23 27 47), (row3 23 27 48), (row3 23 27 49), (row3 23 27 50), (row3 23 27 51), (row3 23 27 52), (row3 23 27 53), (row3 23 27 54), (row3 23 27 55), (row3 23 27 56), (row3 23 27 57), (row3 23 27 58), (row3 23 27 59), (row3 23 27 60), (row3 23 27 61), (row3 23 27 62)]

def b114_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_00_rows b114_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_00_rows b114_00_labels]
    decide +kernel

def b114_01_rows : List Row := [(row3 23 27 63), (row3 23 28 29), (row3 23 28 30), (row3 23 28 31), (row3 23 28 32), (row3 23 28 33), (row3 23 28 34), (row3 23 28 35), (row3 23 28 36), (row3 23 28 37), (row3 23 28 38), (row3 23 28 39), (row3 23 28 40), (row3 23 28 41), (row3 23 28 42), (row3 23 28 43)]

def b114_01_labels : List Row := [(row3 462 462 462), (row3 246 246 462), (row3 232 232 462), (row3 254 171 10), (row3 246 246 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 246 462), (row3 235 235 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_01_rows b114_01_labels 519908329898887739330182500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_01_rows b114_01_labels]
    decide +kernel

def b114_02_rows : List Row := [(row3 23 28 44), (row3 23 28 45), (row3 23 28 46), (row3 23 28 47), (row3 23 28 48), (row3 23 28 49), (row3 23 28 50), (row3 23 28 51), (row3 23 28 52), (row3 23 28 53), (row3 23 28 54), (row3 23 28 55), (row3 23 28 56), (row3 23 28 57), (row3 23 28 58), (row3 23 28 59)]

def b114_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_02_rows b114_02_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_02_rows b114_02_labels]
    decide +kernel

def b114_03_rows : List Row := [(row3 23 28 60), (row3 23 28 61), (row3 23 28 62), (row3 23 28 63), (row3 23 29 30), (row3 23 29 31), (row3 23 29 32), (row3 23 29 33), (row3 23 29 34), (row3 23 29 35), (row3 23 29 36), (row3 23 29 37), (row3 23 29 38), (row3 23 29 39), (row3 23 29 40), (row3 23 29 41)]

def b114_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 309 306 309), (row3 122 369 86), (row3 224 224 224), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 224 224 224), (row3 291 289 291), (row3 246 462 246), (row3 462 462 462)]

theorem b114_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_03_rows b114_03_labels 10273171883996211952954185000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_03_rows b114_03_labels]
    decide +kernel

def b114_04_rows : List Row := [(row3 23 29 42), (row3 23 29 43), (row3 23 29 44), (row3 23 29 45), (row3 23 29 46), (row3 23 29 47), (row3 23 29 48), (row3 23 29 49), (row3 23 29 50), (row3 23 29 51), (row3 23 29 52), (row3 23 29 53), (row3 23 29 54), (row3 23 29 55), (row3 23 29 56), (row3 23 29 57)]

def b114_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 246 462 246), (row3 462 462 462)]

theorem b114_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_04_rows b114_04_labels 1247566980584739398737500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_04_rows b114_04_labels]
    decide +kernel

def b114_05_rows : List Row := [(row3 23 29 58), (row3 23 29 59), (row3 23 29 60), (row3 23 29 61), (row3 23 29 62), (row3 23 29 63), (row3 23 30 31), (row3 23 30 32), (row3 23 30 33), (row3 23 30 34), (row3 23 30 35), (row3 23 30 36), (row3 23 30 37), (row3 23 30 38), (row3 23 30 39), (row3 23 30 40)]

def b114_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 234 234 234), (row3 383 43 436), (row3 311 311 306), (row3 228 462 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 228 462 228), (row3 309 309 306), (row3 137 149 146), (row3 232 462 232)]

theorem b114_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_05_rows b114_05_labels 373490972418943376201247485760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_05_rows b114_05_labels]
    decide +kernel

def b114_06_rows : List Row := [(row3 23 30 41), (row3 23 30 42), (row3 23 30 43), (row3 23 30 44), (row3 23 30 45), (row3 23 30 46), (row3 23 30 47), (row3 23 30 48), (row3 23 30 49), (row3 23 30 50), (row3 23 30 51), (row3 23 30 52), (row3 23 30 53), (row3 23 30 54), (row3 23 30 55), (row3 23 30 56)]

def b114_06_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 280 280 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 232 462 232)]

theorem b114_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_06_rows b114_06_labels 61404925456504907954616600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_06_rows b114_06_labels]
    decide +kernel

def b114_07_rows : List Row := [(row3 23 30 57), (row3 23 30 58), (row3 23 30 59), (row3 23 30 60), (row3 23 30 61), (row3 23 30 62), (row3 23 30 63), (row3 23 31 32), (row3 23 31 33), (row3 23 31 34), (row3 23 31 35), (row3 23 31 36), (row3 23 31 37), (row3 23 31 38), (row3 23 31 39), (row3 23 31 40)]

def b114_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 156 82 399), (row3 214 11 117), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 214 11 117), (row3 157 83 399), (row3 95 435 41), (row3 213 11 116)]

theorem b114_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_07_rows b114_07_labels 399121877727675096421245938580 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_07_rows b114_07_labels]
    decide +kernel

def b114_08_rows : List Row := [(row3 23 31 41), (row3 23 31 42), (row3 23 31 43), (row3 23 31 44), (row3 23 31 45), (row3 23 31 46), (row3 23 31 47), (row3 23 31 48), (row3 23 31 49), (row3 23 31 50), (row3 23 31 51), (row3 23 31 52), (row3 23 31 53), (row3 23 31 54), (row3 23 31 55), (row3 23 31 56)]

def b114_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 212 11 115), (row3 325 87 371), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 217 10 169), (row3 303 462 303)]

theorem b114_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_08_rows b114_08_labels 21042313037947695579983367000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_08_rows b114_08_labels]
    decide +kernel

def b114_09_rows : List Row := [(row3 23 31 57), (row3 23 31 58), (row3 23 31 59), (row3 23 31 60), (row3 23 31 61), (row3 23 31 62), (row3 23 31 63), (row3 23 32 33), (row3 23 32 34), (row3 23 32 35), (row3 23 32 36), (row3 23 32 37), (row3 23 32 38), (row3 23 32 39), (row3 23 32 40), (row3 23 32 41)]

def b114_09_labels : List Row := [(row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 286 462 286), (row3 151 153 179), (row3 272 462 272), (row3 237 462 237), (row3 242 462 242), (row3 462 462 462), (row3 249 462 249), (row3 223 224 223), (row3 299 289 299), (row3 169 10 217), (row3 235 462 235)]

theorem b114_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_09_rows b114_09_labels 7870043722406150957909380950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_09_rows b114_09_labels]
    decide +kernel

def b114_10_rows : List Row := [(row3 23 32 42), (row3 23 32 43), (row3 23 32 44), (row3 23 32 45), (row3 23 32 46), (row3 23 32 47), (row3 23 32 48), (row3 23 32 49), (row3 23 32 50), (row3 23 32 51), (row3 23 32 52), (row3 23 32 53), (row3 23 32 54), (row3 23 32 55), (row3 23 32 56), (row3 23 32 57)]

def b114_10_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 227 231 229), (row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 251 462 251), (row3 217 10 169), (row3 235 462 235)]

theorem b114_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_10_rows b114_10_labels 900752365250428925754648750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_10_rows b114_10_labels]
    decide +kernel

def b114_11_rows : List Row := [(row3 23 32 58), (row3 23 32 59), (row3 23 32 60), (row3 23 32 61), (row3 23 32 62), (row3 23 32 63), (row3 23 33 34), (row3 23 33 35), (row3 23 33 36), (row3 23 33 37), (row3 23 33 38), (row3 23 33 39), (row3 23 33 40), (row3 23 33 41), (row3 23 33 42), (row3 23 33 43)]

def b114_11_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 229 231 227), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_11_rows b114_11_labels 3501706642680050972086500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_11_rows b114_11_labels]
    decide +kernel

def b114_12_rows : List Row := [(row3 23 33 44), (row3 23 33 45), (row3 23 33 46), (row3 23 33 47), (row3 23 33 48), (row3 23 33 49), (row3 23 33 50), (row3 23 33 51), (row3 23 33 52), (row3 23 33 53), (row3 23 33 54), (row3 23 33 55), (row3 23 33 56), (row3 23 33 57), (row3 23 33 58), (row3 23 33 59)]

def b114_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_12_rows b114_12_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_12_rows b114_12_labels]
    decide +kernel

def b114_13_rows : List Row := [(row3 23 33 60), (row3 23 33 61), (row3 23 33 62), (row3 23 33 63), (row3 23 34 35), (row3 23 34 36), (row3 23 34 37), (row3 23 34 38), (row3 23 34 39), (row3 23 34 40), (row3 23 34 41), (row3 23 34 42), (row3 23 34 43), (row3 23 34 44), (row3 23 34 45), (row3 23 34 46)]

def b114_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 244 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_13_rows b114_13_labels 34326303503390443192500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_13_rows b114_13_labels]
    decide +kernel

def b114_14_rows : List Row := [(row3 23 34 47), (row3 23 34 48), (row3 23 34 49), (row3 23 34 50), (row3 23 34 51), (row3 23 34 52), (row3 23 34 53), (row3 23 34 54), (row3 23 34 55), (row3 23 34 56), (row3 23 34 57), (row3 23 34 58), (row3 23 34 59), (row3 23 34 60), (row3 23 34 61), (row3 23 34 62)]

def b114_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_14_rows b114_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_14_rows b114_14_labels]
    decide +kernel

def b114_15_rows : List Row := [(row3 23 34 63), (row3 23 35 36), (row3 23 35 37), (row3 23 35 38), (row3 23 35 39), (row3 23 35 40), (row3 23 35 41), (row3 23 35 42), (row3 23 35 43), (row3 23 35 44), (row3 23 35 45), (row3 23 35 46), (row3 23 35 47), (row3 23 35 48), (row3 23 35 49), (row3 23 35 50)]

def b114_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b114_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b114_15_rows b114_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b114_15_rows b114_15_labels]
    decide +kernel

theorem checked114 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_114 QuarticIntegerComputationalData.ids64_114 813285261104455935184459609140 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b114_00_rows ++ b114_01_rows) ++ (b114_02_rows ++ b114_03_rows)) ++ ((b114_04_rows ++ b114_05_rows) ++ (b114_06_rows ++ b114_07_rows))) ++ (((b114_08_rows ++ b114_09_rows) ++ (b114_10_rows ++ b114_11_rows)) ++ ((b114_12_rows ++ b114_13_rows) ++ (b114_14_rows ++ b114_15_rows))))
    ((((b114_00_labels ++ b114_01_labels) ++ (b114_02_labels ++ b114_03_labels)) ++ ((b114_04_labels ++ b114_05_labels) ++ (b114_06_labels ++ b114_07_labels))) ++ (((b114_08_labels ++ b114_09_labels) ++ (b114_10_labels ++ b114_11_labels)) ++ ((b114_12_labels ++ b114_13_labels) ++ (b114_14_labels ++ b114_15_labels)))) 813285261104455935184459609140
  exact ((((b114_00_checked.append (c := 519908329898887739330182500) b114_01_checked (by decide +kernel)).append (c := 10793087873995456595522092500) (b114_02_checked.append (c := 10273179544096568856191910000) b114_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 783468590513051018865368870940) ((b114_04_checked.append (c := 373492219985923960940646223260) b114_05_checked (by decide +kernel)).append (c := 772675502639055562269846778440) (b114_06_checked.append (c := 399183282653131601329200555180) b114_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 813285261104455935184459609140) (((b114_08_checked.append (c := 28912356760353846537892747950) b114_09_checked (by decide +kernel)).append (c := 29816610832246955514619483200) (b114_10_checked.append (c := 904254071893108976726735250) b114_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 29816670591404916319090738200) ((b114_12_checked.append (c := 59759157960804471255000) b114_13_checked (by decide +kernel)).append (c := 59759157960804471255000) (b114_14_checked.append (c := 0) b114_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b115_00_rows : List Row := [(row3 23 35 51), (row3 23 35 52), (row3 23 35 53), (row3 23 35 54), (row3 23 35 55), (row3 23 35 56), (row3 23 35 57), (row3 23 35 58), (row3 23 35 59), (row3 23 35 60), (row3 23 35 61), (row3 23 35 62), (row3 23 35 63), (row3 23 36 37), (row3 23 36 38), (row3 23 36 39)]

def b115_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_00_rows b115_00_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_00_rows b115_00_labels]
    decide +kernel

def b115_01_rows : List Row := [(row3 23 36 40), (row3 23 36 41), (row3 23 36 42), (row3 23 36 43), (row3 23 36 44), (row3 23 36 45), (row3 23 36 46), (row3 23 36 47), (row3 23 36 48), (row3 23 36 49), (row3 23 36 50), (row3 23 36 51), (row3 23 36 52), (row3 23 36 53), (row3 23 36 54), (row3 23 36 55)]

def b115_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_01_rows b115_01_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_01_rows b115_01_labels]
    decide +kernel

def b115_02_rows : List Row := [(row3 23 36 56), (row3 23 36 57), (row3 23 36 58), (row3 23 36 59), (row3 23 36 60), (row3 23 36 61), (row3 23 36 62), (row3 23 36 63), (row3 23 37 38), (row3 23 37 39), (row3 23 37 40), (row3 23 37 41), (row3 23 37 42), (row3 23 37 43), (row3 23 37 44), (row3 23 37 45)]

def b115_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_02_rows b115_02_labels 2057085908239251572356500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_02_rows b115_02_labels]
    decide +kernel

def b115_03_rows : List Row := [(row3 23 37 46), (row3 23 37 47), (row3 23 37 48), (row3 23 37 49), (row3 23 37 50), (row3 23 37 51), (row3 23 37 52), (row3 23 37 53), (row3 23 37 54), (row3 23 37 55), (row3 23 37 56), (row3 23 37 57), (row3 23 37 58), (row3 23 37 59), (row3 23 37 60), (row3 23 37 61)]

def b115_03_labels : List Row := [(row3 462 462 462), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_03_rows b115_03_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_03_rows b115_03_labels]
    decide +kernel

def b115_04_rows : List Row := [(row3 23 37 62), (row3 23 37 63), (row3 23 38 39), (row3 23 38 40), (row3 23 38 41), (row3 23 38 42), (row3 23 38 43), (row3 23 38 44), (row3 23 38 45), (row3 23 38 46), (row3 23 38 47), (row3 23 38 48), (row3 23 38 49), (row3 23 38 50), (row3 23 38 51), (row3 23 38 52)]

def b115_04_labels : List Row := [(row3 462 462 462), (row3 244 244 462), (row3 291 289 291), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 231 231 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_04_rows b115_04_labels 175281855835123845675731700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_04_rows b115_04_labels]
    decide +kernel

def b115_05_rows : List Row := [(row3 23 38 53), (row3 23 38 54), (row3 23 38 55), (row3 23 38 56), (row3 23 38 57), (row3 23 38 58), (row3 23 38 59), (row3 23 38 60), (row3 23 38 61), (row3 23 38 62), (row3 23 38 63), (row3 23 39 40), (row3 23 39 41), (row3 23 39 42), (row3 23 39 43), (row3 23 39 44)]

def b115_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 234 231 231), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_05_rows b115_05_labels 3873979285429075666470000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_05_rows b115_05_labels]
    decide +kernel

def b115_06_rows : List Row := [(row3 23 39 45), (row3 23 39 46), (row3 23 39 47), (row3 23 39 48), (row3 23 39 49), (row3 23 39 50), (row3 23 39 51), (row3 23 39 52), (row3 23 39 53), (row3 23 39 54), (row3 23 39 55), (row3 23 39 56), (row3 23 39 57), (row3 23 39 58), (row3 23 39 59), (row3 23 39 60)]

def b115_06_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 277 277 265), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_06_rows b115_06_labels 105512710879319890351367400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_06_rows b115_06_labels]
    decide +kernel

def b115_07_rows : List Row := [(row3 23 39 61), (row3 23 39 62), (row3 23 39 63), (row3 23 40 41), (row3 23 40 42), (row3 23 40 43), (row3 23 40 44), (row3 23 40 45), (row3 23 40 46), (row3 23 40 47), (row3 23 40 48), (row3 23 40 49), (row3 23 40 50), (row3 23 40 51), (row3 23 40 52), (row3 23 40 53)]

def b115_07_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 276 276 275), (row3 264 264 462), (row3 238 238 462), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 238 238 462), (row3 204 259 8), (row3 277 277 265), (row3 231 231 234), (row3 245 245 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_07_rows b115_07_labels 428601758762346397540977600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_07_rows b115_07_labels]
    decide +kernel

def b115_08_rows : List Row := [(row3 23 40 54), (row3 23 40 55), (row3 23 40 56), (row3 23 40 57), (row3 23 40 58), (row3 23 40 59), (row3 23 40 60), (row3 23 40 61), (row3 23 40 62), (row3 23 40 63), (row3 23 41 42), (row3 23 41 43), (row3 23 41 44), (row3 23 41 45), (row3 23 41 46), (row3 23 41 47)]

def b115_08_labels : List Row := [(row3 245 245 462), (row3 227 231 229), (row3 325 87 371), (row3 280 280 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234), (row3 297 297 295), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462)]

theorem b115_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_08_rows b115_08_labels 9707851655951093899544862300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_08_rows b115_08_labels]
    decide +kernel

def b115_09_rows : List Row := [(row3 23 41 48), (row3 23 41 49), (row3 23 41 50), (row3 23 41 51), (row3 23 41 52), (row3 23 41 53), (row3 23 41 54), (row3 23 41 55), (row3 23 41 56), (row3 23 41 57), (row3 23 41 58), (row3 23 41 59), (row3 23 41 60), (row3 23 41 61), (row3 23 41 62), (row3 23 41 63)]

def b115_09_labels : List Row := [(row3 235 462 235), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 212 11 115), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 235 228)]

theorem b115_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_09_rows b115_09_labels 1676739914270255204756799750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_09_rows b115_09_labels]
    decide +kernel

def b115_10_rows : List Row := [(row3 23 42 43), (row3 23 42 44), (row3 23 42 45), (row3 23 42 46), (row3 23 42 47), (row3 23 42 48), (row3 23 42 49), (row3 23 42 50), (row3 23 42 51), (row3 23 42 52), (row3 23 42 53), (row3 23 42 54), (row3 23 42 55), (row3 23 42 56), (row3 23 42 57), (row3 23 42 58)]

def b115_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_10_rows b115_10_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_10_rows b115_10_labels]
    decide +kernel

def b115_11_rows : List Row := [(row3 23 42 59), (row3 23 42 60), (row3 23 42 61), (row3 23 42 62), (row3 23 42 63), (row3 23 43 44), (row3 23 43 45), (row3 23 43 46), (row3 23 43 47), (row3 23 43 48), (row3 23 43 49), (row3 23 43 50), (row3 23 43 51), (row3 23 43 52), (row3 23 43 53), (row3 23 43 54)]

def b115_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_11_rows b115_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_11_rows b115_11_labels]
    decide +kernel

def b115_12_rows : List Row := [(row3 23 43 55), (row3 23 43 56), (row3 23 43 57), (row3 23 43 58), (row3 23 43 59), (row3 23 43 60), (row3 23 43 61), (row3 23 43 62), (row3 23 43 63), (row3 23 44 45), (row3 23 44 46), (row3 23 44 47), (row3 23 44 48), (row3 23 44 49), (row3 23 44 50), (row3 23 44 51)]

def b115_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_12_rows b115_12_labels 2832593610752454075000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_12_rows b115_12_labels]
    decide +kernel

def b115_13_rows : List Row := [(row3 23 44 52), (row3 23 44 53), (row3 23 44 54), (row3 23 44 55), (row3 23 44 56), (row3 23 44 57), (row3 23 44 58), (row3 23 44 59), (row3 23 44 60), (row3 23 44 61), (row3 23 44 62), (row3 23 44 63), (row3 23 45 46), (row3 23 45 47), (row3 23 45 48), (row3 23 45 49)]

def b115_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 238 462), (row3 462 462 462), (row3 462 462 462)]

theorem b115_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_13_rows b115_13_labels 121705541119974164220000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_13_rows b115_13_labels]
    decide +kernel

def b115_14_rows : List Row := [(row3 23 45 50), (row3 23 45 51), (row3 23 45 52), (row3 23 45 53), (row3 23 45 54), (row3 23 45 55), (row3 23 45 56), (row3 23 45 57), (row3 23 45 58), (row3 23 45 59), (row3 23 45 60), (row3 23 45 61), (row3 23 45 62), (row3 23 45 63), (row3 23 46 47), (row3 23 46 48)]

def b115_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 235 235), (row3 264 264 462), (row3 462 462 462)]

theorem b115_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_14_rows b115_14_labels 33311934096515380311274500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_14_rows b115_14_labels]
    decide +kernel

def b115_15_rows : List Row := [(row3 23 46 49), (row3 23 46 50), (row3 23 46 51), (row3 23 46 52), (row3 23 46 53), (row3 23 46 54), (row3 23 46 55), (row3 23 46 56), (row3 23 46 57), (row3 23 46 58), (row3 23 46 59), (row3 23 46 60), (row3 23 46 61), (row3 23 46 62), (row3 23 46 63), (row3 23 47 48)]

def b115_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 280 280 278), (row3 233 462 233)]

theorem b115_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b115_15_rows b115_15_labels 12792589750523705136744600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b115_15_rows b115_15_labels]
    decide +kernel

theorem checked115 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_115 QuarticIntegerComputationalData.ids64_115 12146176288321645543657016850 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b115_00_rows ++ b115_01_rows) ++ (b115_02_rows ++ b115_03_rows)) ++ ((b115_04_rows ++ b115_05_rows) ++ (b115_06_rows ++ b115_07_rows))) ++ (((b115_08_rows ++ b115_09_rows) ++ (b115_10_rows ++ b115_11_rows)) ++ ((b115_12_rows ++ b115_13_rows) ++ (b115_14_rows ++ b115_15_rows))))
    ((((b115_00_labels ++ b115_01_labels) ++ (b115_02_labels ++ b115_03_labels)) ++ ((b115_04_labels ++ b115_05_labels) ++ (b115_06_labels ++ b115_07_labels))) ++ (((b115_08_labels ++ b115_09_labels) ++ (b115_10_labels ++ b115_11_labels)) ++ ((b115_12_labels ++ b115_13_labels) ++ (b115_14_labels ++ b115_15_labels)))) 12146176288321645543657016850
  exact ((((b115_00_checked.append (c := 0) b115_01_checked (by decide +kernel)).append (c := 2082518762696665600419000) (b115_02_checked.append (c := 2082518762696665600419000) b115_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 715352823524915874834965700) ((b115_04_checked.append (c := 179155835120552921342201700) b115_05_checked (by decide +kernel)).append (c := 713270304762219209234546700) (b115_06_checked.append (c := 534114469641666287892345000) b115_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 12146176288321645543657016850) (((b115_08_checked.append (c := 11384591570221349104301662050) b115_09_checked (by decide +kernel)).append (c := 11384594402814959856755737050) (b115_10_checked.append (c := 2832593610752454075000) b115_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 11430823464796729668822051150) ((b115_12_checked.append (c := 124538134730726618295000) b115_13_checked (by decide +kernel)).append (c := 46229061981769812066314100) (b115_14_checked.append (c := 46104523847039085448019100) b115_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b116_00_rows : List Row := [(row3 23 47 49), (row3 23 47 50), (row3 23 47 51), (row3 23 47 52), (row3 23 47 53), (row3 23 47 54), (row3 23 47 55), (row3 23 47 56), (row3 23 47 57), (row3 23 47 58), (row3 23 47 59), (row3 23 47 60), (row3 23 47 61), (row3 23 47 62), (row3 23 47 63), (row3 23 48 49)]

def b116_00_labels : List Row := [(row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 169 10 217), (row3 213 11 116), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 252 462 252), (row3 195 188 194), (row3 291 289 291)]

theorem b116_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_00_rows b116_00_labels 3203638940330942442089697120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_00_rows b116_00_labels]
    decide +kernel

def b116_01_rows : List Row := [(row3 23 48 50), (row3 23 48 51), (row3 23 48 52), (row3 23 48 53), (row3 23 48 54), (row3 23 48 55), (row3 23 48 56), (row3 23 48 57), (row3 23 48 58), (row3 23 48 59), (row3 23 48 60), (row3 23 48 61), (row3 23 48 62), (row3 23 48 63), (row3 23 49 50), (row3 23 49 51)]

def b116_01_labels : List Row := [(row3 234 234 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 462), (row3 299 289 299), (row3 95 435 41), (row3 137 149 146), (row3 291 289 291), (row3 235 235 462), (row3 462 462 462), (row3 235 235 462), (row3 292 289 292), (row3 125 126 128), (row3 248 248 462), (row3 462 462 462)]

theorem b116_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_01_rows b116_01_labels 354614732598835058351449097550 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_01_rows b116_01_labels]
    decide +kernel

def b116_02_rows : List Row := [(row3 23 49 52), (row3 23 49 53), (row3 23 49 54), (row3 23 49 55), (row3 23 49 56), (row3 23 49 57), (row3 23 49 58), (row3 23 49 59), (row3 23 49 60), (row3 23 49 61), (row3 23 49 62), (row3 23 49 63), (row3 23 50 51), (row3 23 50 52), (row3 23 50 53), (row3 23 50 54)]

def b116_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 248 248 462), (row3 223 224 223), (row3 157 83 399), (row3 309 309 306), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224), (row3 320 320 319), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b116_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_02_rows b116_02_labels 20664293917403397566890127700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_02_rows b116_02_labels]
    decide +kernel

def b116_03_rows : List Row := [(row3 23 50 55), (row3 23 50 56), (row3 23 50 57), (row3 23 50 58), (row3 23 50 59), (row3 23 50 60), (row3 23 50 61), (row3 23 50 62), (row3 23 50 63), (row3 23 51 52), (row3 23 51 53), (row3 23 51 54), (row3 23 51 55), (row3 23 51 56), (row3 23 51 57), (row3 23 51 58)]

def b116_03_labels : List Row := [(row3 249 462 249), (row3 214 11 117), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 248 462 248), (row3 228 236 225), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b116_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_03_rows b116_03_labels 1647878869064325112086543750 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_03_rows b116_03_labels]
    decide +kernel

def b116_04_rows : List Row := [(row3 23 51 59), (row3 23 51 60), (row3 23 51 61), (row3 23 51 62), (row3 23 51 63), (row3 23 52 53), (row3 23 52 54), (row3 23 52 55), (row3 23 52 56), (row3 23 52 57), (row3 23 52 58), (row3 23 52 59), (row3 23 52 60), (row3 23 52 61), (row3 23 52 62), (row3 23 52 63)]

def b116_04_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 236 236)]

theorem b116_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_04_rows b116_04_labels 304737902442970641445500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_04_rows b116_04_labels]
    decide +kernel

def b116_05_rows : List Row := [(row3 23 53 54), (row3 23 53 55), (row3 23 53 56), (row3 23 53 57), (row3 23 53 58), (row3 23 53 59), (row3 23 53 60), (row3 23 53 61), (row3 23 53 62), (row3 23 53 63), (row3 23 54 55), (row3 23 54 56), (row3 23 54 57), (row3 23 54 58), (row3 23 54 59), (row3 23 54 60)]

def b116_05_labels : List Row := [(row3 462 462 462), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 279 279 278), (row3 272 462 272), (row3 214 11 117), (row3 228 462 228), (row3 248 462 248), (row3 462 462 462), (row3 462 462 462)]

theorem b116_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_05_rows b116_05_labels 1705859214380844365850386850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_05_rows b116_05_labels]
    decide +kernel

def b116_06_rows : List Row := [(row3 23 54 61), (row3 23 54 62), (row3 23 54 63), (row3 23 55 56), (row3 23 55 57), (row3 23 55 58), (row3 23 55 59), (row3 23 55 60), (row3 23 55 61), (row3 23 55 62), (row3 23 55 63), (row3 23 56 57), (row3 23 56 58), (row3 23 56 59), (row3 23 56 60), (row3 23 56 61)]

def b116_06_labels : List Row := [(row3 462 462 462), (row3 287 462 287), (row3 175 161 175), (row3 156 82 399), (row3 311 311 306), (row3 224 224 224), (row3 246 246 462), (row3 462 462 462), (row3 248 248 462), (row3 220 222 221), (row3 353 375 366), (row3 383 43 436), (row3 122 369 86), (row3 254 171 10), (row3 462 462 462), (row3 254 171 10)]

theorem b116_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_06_rows b116_06_labels 420808255830902406000462372210 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_06_rows b116_06_labels]
    decide +kernel

def b116_07_rows : List Row := [(row3 23 56 62), (row3 23 56 63), (row3 23 57 58), (row3 23 57 59), (row3 23 57 60), (row3 23 57 61), (row3 23 57 62), (row3 23 57 63), (row3 23 58 59), (row3 23 58 60), (row3 23 58 61), (row3 23 58 62), (row3 23 58 63), (row3 23 59 60), (row3 23 59 61), (row3 23 59 62)]

def b116_07_labels : List Row := [(row3 121 369 85), (row3 74 44 439), (row3 309 306 309), (row3 232 232 462), (row3 462 462 462), (row3 232 232 462), (row3 310 306 310), (row3 109 110 111), (row3 246 246 462), (row3 462 462 462), (row3 246 246 462), (row3 224 224 224), (row3 317 317 308), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247)]

theorem b116_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_07_rows b116_07_labels 536355579765163255531694910240 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_07_rows b116_07_labels]
    decide +kernel

def b116_08_rows : List Row := [(row3 23 59 63), (row3 23 60 61), (row3 23 60 62), (row3 23 60 63), (row3 23 61 62), (row3 23 61 63), (row3 23 62 63), (row3 24 25 26), (row3 24 25 27), (row3 24 25 28), (row3 24 25 29), (row3 24 25 30), (row3 24 25 31), (row3 24 25 32), (row3 24 25 33), (row3 24 25 34)]

def b116_08_labels : List Row := [(row3 232 238 230), (row3 462 462 462), (row3 235 462 235), (row3 262 262 261), (row3 286 462 286), (row3 197 190 196), (row3 354 376 366), (row3 336 428 72), (row3 202 97 334), (row3 254 8 203), (row3 201 201 208), (row3 343 338 330), (row3 54 65 65), (row3 55 66 64), (row3 359 429 73), (row3 159 91 356)]

theorem b116_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_08_rows b116_08_labels 754004539468784005296818416980 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_08_rows b116_08_labels]
    decide +kernel

def b116_09_rows : List Row := [(row3 24 25 35), (row3 24 25 36), (row3 24 25 37), (row3 24 25 38), (row3 24 25 39), (row3 24 25 40), (row3 24 25 41), (row3 24 25 42), (row3 24 25 43), (row3 24 25 44), (row3 24 25 45), (row3 24 25 46), (row3 24 25 47), (row3 24 25 48), (row3 24 25 49), (row3 24 25 50)]

def b116_09_labels : List Row := [(row3 254 10 171), (row3 462 462 462), (row3 263 462 263), (row3 154 154 180), (row3 373 365 352), (row3 344 340 329), (row3 155 93 332), (row3 258 10 172), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 269 462 269), (row3 154 154 180), (row3 200 200 207), (row3 259 8 204), (row3 462 462 462)]

theorem b116_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_09_rows b116_09_labels 23478735184100209330551939900 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_09_rows b116_09_labels]
    decide +kernel

def b116_10_rows : List Row := [(row3 24 25 51), (row3 24 25 52), (row3 24 25 53), (row3 24 25 54), (row3 24 25 55), (row3 24 25 56), (row3 24 25 57), (row3 24 25 58), (row3 24 25 59), (row3 24 25 60), (row3 24 25 61), (row3 24 25 62), (row3 24 25 63), (row3 24 26 27), (row3 24 26 28), (row3 24 26 29)]

def b116_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 264 462 264), (row3 269 462 269), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 256 256 255), (row3 239 462 239), (row3 256 256 255)]

theorem b116_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_10_rows b116_10_labels 2277604338734711571374270100 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_10_rows b116_10_labels]
    decide +kernel

def b116_11_rows : List Row := [(row3 24 26 30), (row3 24 26 31), (row3 24 26 32), (row3 24 26 33), (row3 24 26 34), (row3 24 26 35), (row3 24 26 36), (row3 24 26 37), (row3 24 26 38), (row3 24 26 39), (row3 24 26 40), (row3 24 26 41), (row3 24 26 42), (row3 24 26 43), (row3 24 26 44), (row3 24 26 45)]

def b116_11_labels : List Row := [(row3 206 210 210), (row3 343 330 338), (row3 342 328 339), (row3 190 198 199), (row3 266 266 265), (row3 238 462 238), (row3 462 462 462), (row3 238 462 238), (row3 266 266 265), (row3 190 198 199), (row3 206 209 209), (row3 268 268 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b116_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_11_rows b116_11_labels 10009164714557074034176074540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_11_rows b116_11_labels]
    decide +kernel

def b116_12_rows : List Row := [(row3 24 26 46), (row3 24 26 47), (row3 24 26 48), (row3 24 26 49), (row3 24 26 50), (row3 24 26 51), (row3 24 26 52), (row3 24 26 53), (row3 24 26 54), (row3 24 26 55), (row3 24 26 56), (row3 24 26 57), (row3 24 26 58), (row3 24 26 59), (row3 24 26 60), (row3 24 26 61)]

def b116_12_labels : List Row := [(row3 237 462 237), (row3 266 266 265), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b116_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_12_rows b116_12_labels 9338941988738590811884320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_12_rows b116_12_labels]
    decide +kernel

def b116_13_rows : List Row := [(row3 24 26 62), (row3 24 26 63), (row3 24 27 28), (row3 24 27 29), (row3 24 27 30), (row3 24 27 31), (row3 24 27 32), (row3 24 27 33), (row3 24 27 34), (row3 24 27 35), (row3 24 27 36), (row3 24 27 37), (row3 24 27 38), (row3 24 27 39), (row3 24 27 40), (row3 24 27 41)]

def b116_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 240 462 240), (row3 239 239 239), (row3 256 255 256), (row3 201 208 201), (row3 201 208 201), (row3 262 261 262), (row3 237 237 237), (row3 241 462 241), (row3 462 462 462), (row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 256 255 256), (row3 237 237 237)]

theorem b116_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_13_rows b116_13_labels 536887370300684486422213500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_13_rows b116_13_labels]
    decide +kernel

def b116_14_rows : List Row := [(row3 24 27 42), (row3 24 27 43), (row3 24 27 44), (row3 24 27 45), (row3 24 27 46), (row3 24 27 47), (row3 24 27 48), (row3 24 27 49), (row3 24 27 50), (row3 24 27 51), (row3 24 27 52), (row3 24 27 53), (row3 24 27 54), (row3 24 27 55), (row3 24 27 56), (row3 24 27 57)]

def b116_14_labels : List Row := [(row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 237 237 237), (row3 239 239 239), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 240 462 240), (row3 462 462 462)]

theorem b116_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_14_rows b116_14_labels 211545639428755336642500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_14_rows b116_14_labels]
    decide +kernel

def b116_15_rows : List Row := [(row3 24 27 58), (row3 24 27 59), (row3 24 27 60), (row3 24 27 61), (row3 24 27 62), (row3 24 27 63), (row3 24 28 29), (row3 24 28 30), (row3 24 28 31), (row3 24 28 32), (row3 24 28 33), (row3 24 28 34), (row3 24 28 35), (row3 24 28 36), (row3 24 28 37), (row3 24 28 38)]

def b116_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 240 240 462), (row3 239 239 462), (row3 254 203 8), (row3 257 257 462), (row3 238 238 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462)]

theorem b116_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b116_15_rows b116_15_labels 180377377584989040302446500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b116_15_rows b116_15_labels]
    decide +kernel

theorem checked116 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_116 QuarticIntegerComputationalData.ids64_116 2129497402815672513446958469260 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b116_00_rows ++ b116_01_rows) ++ (b116_02_rows ++ b116_03_rows)) ++ ((b116_04_rows ++ b116_05_rows) ++ (b116_06_rows ++ b116_07_rows))) ++ (((b116_08_rows ++ b116_09_rows) ++ (b116_10_rows ++ b116_11_rows)) ++ ((b116_12_rows ++ b116_13_rows) ++ (b116_14_rows ++ b116_15_rows))))
    ((((b116_00_labels ++ b116_01_labels) ++ (b116_02_labels ++ b116_03_labels)) ++ ((b116_04_labels ++ b116_05_labels) ++ (b116_06_labels ++ b116_07_labels))) ++ (((b116_08_labels ++ b116_09_labels) ++ (b116_10_labels ++ b116_11_labels)) ++ ((b116_12_labels ++ b116_13_labels) ++ (b116_14_labels ++ b116_15_labels)))) 2129497402815672513446958469260
  exact ((((b116_00_checked.append (c := 357818371539166000793538794670) b116_01_checked (by decide +kernel)).append (c := 380130544325633723472515466120) (b116_02_checked.append (c := 22312172786467722678976671450) b116_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1339000543873982672341164580920) ((b116_04_checked.append (c := 1706163952283287336491832350) b116_05_checked (by decide +kernel)).append (c := 958869999548348948868649114800) (b116_06_checked.append (c := 957163835596065661532157282450) b116_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 2129497402815672513446958469260) (((b116_08_checked.append (c := 777483274652884214627370356880) b116_09_checked (by decide +kernel)).append (c := 789770043706176000232920701520) (b116_10_checked.append (c := 12286769053291785605550344640) b116_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 790496858941689841105793888340) ((b116_12_checked.append (c := 546226312289423077234097820) b116_13_checked (by decide +kernel)).append (c := 726815235513840872873186820) (b116_14_checked.append (c := 180588923224417795639089000) b116_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b117_00_rows : List Row := [(row3 24 28 39), (row3 24 28 40), (row3 24 28 41), (row3 24 28 42), (row3 24 28 43), (row3 24 28 44), (row3 24 28 45), (row3 24 28 46), (row3 24 28 47), (row3 24 28 48), (row3 24 28 49), (row3 24 28 50), (row3 24 28 51), (row3 24 28 52), (row3 24 28 53), (row3 24 28 54)]

def b117_00_labels : List Row := [(row3 238 238 462), (row3 239 239 462), (row3 242 242 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 242 462), (row3 240 240 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_00_rows b117_00_labels 180046221051458994172500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_00_rows b117_00_labels]
    decide +kernel

def b117_01_rows : List Row := [(row3 24 28 55), (row3 24 28 56), (row3 24 28 57), (row3 24 28 58), (row3 24 28 59), (row3 24 28 60), (row3 24 28 61), (row3 24 28 62), (row3 24 28 63), (row3 24 29 30), (row3 24 29 31), (row3 24 29 32), (row3 24 29 33), (row3 24 29 34), (row3 24 29 35), (row3 24 29 36)]

def b117_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 256 255 256), (row3 202 334 97), (row3 201 208 201), (row3 262 261 262), (row3 237 237 237), (row3 241 462 241), (row3 462 462 462)]

theorem b117_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_01_rows b117_01_labels 3342059983704580095023073000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_01_rows b117_01_labels]
    decide +kernel

def b117_02_rows : List Row := [(row3 24 29 37), (row3 24 29 38), (row3 24 29 39), (row3 24 29 40), (row3 24 29 41), (row3 24 29 42), (row3 24 29 43), (row3 24 29 44), (row3 24 29 45), (row3 24 29 46), (row3 24 29 47), (row3 24 29 48), (row3 24 29 49), (row3 24 29 50), (row3 24 29 51), (row3 24 29 52)]

def b117_02_labels : List Row := [(row3 241 462 241), (row3 237 237 237), (row3 262 261 262), (row3 256 255 256), (row3 237 237 237), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 237 237 237), (row3 239 239 239), (row3 241 462 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_02_rows b117_02_labels 4986437373089178072777000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_02_rows b117_02_labels]
    decide +kernel

def b117_03_rows : List Row := [(row3 24 29 53), (row3 24 29 54), (row3 24 29 55), (row3 24 29 56), (row3 24 29 57), (row3 24 29 58), (row3 24 29 59), (row3 24 29 60), (row3 24 29 61), (row3 24 29 62), (row3 24 29 63), (row3 24 30 31), (row3 24 30 32), (row3 24 30 33), (row3 24 30 34), (row3 24 30 35)]

def b117_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 241 462 241), (row3 240 462 240), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 336 72 428), (row3 342 328 339), (row3 190 198 199), (row3 266 266 265), (row3 238 462 238)]

theorem b117_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_03_rows b117_03_labels 106022988661798584048758374470 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_03_rows b117_03_labels]
    decide +kernel

def b117_04_rows : List Row := [(row3 24 30 36), (row3 24 30 37), (row3 24 30 38), (row3 24 30 39), (row3 24 30 40), (row3 24 30 41), (row3 24 30 42), (row3 24 30 43), (row3 24 30 44), (row3 24 30 45), (row3 24 30 46), (row3 24 30 47), (row3 24 30 48), (row3 24 30 49), (row3 24 30 50), (row3 24 30 51)]

def b117_04_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 266 266 265), (row3 190 198 199), (row3 206 209 209), (row3 266 266 265), (row3 237 462 237), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 237 462 237), (row3 268 268 265), (row3 256 256 255), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462)]

theorem b117_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_04_rows b117_04_labels 204429913548049798208275800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_04_rows b117_04_labels]
    decide +kernel

def b117_05_rows : List Row := [(row3 24 30 52), (row3 24 30 53), (row3 24 30 54), (row3 24 30 55), (row3 24 30 56), (row3 24 30 57), (row3 24 30 58), (row3 24 30 59), (row3 24 30 60), (row3 24 30 61), (row3 24 30 62), (row3 24 30 63), (row3 24 31 32), (row3 24 31 33), (row3 24 31 34), (row3 24 31 35)]

def b117_05_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 239 462 239), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 55 66 64), (row3 373 365 352), (row3 154 154 180), (row3 263 462 263)]

theorem b117_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_05_rows b117_05_labels 271078202476065186714476022450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_05_rows b117_05_labels]
    decide +kernel

def b117_06_rows : List Row := [(row3 24 31 36), (row3 24 31 37), (row3 24 31 38), (row3 24 31 39), (row3 24 31 40), (row3 24 31 41), (row3 24 31 42), (row3 24 31 43), (row3 24 31 44), (row3 24 31 45), (row3 24 31 46), (row3 24 31 47), (row3 24 31 48), (row3 24 31 49), (row3 24 31 50), (row3 24 31 51)]

def b117_06_labels : List Row := [(row3 462 462 462), (row3 254 10 171), (row3 159 91 356), (row3 359 429 73), (row3 344 340 329), (row3 154 154 180), (row3 269 462 269), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 258 10 172), (row3 155 93 332), (row3 200 200 207), (row3 264 462 264), (row3 462 462 462), (row3 462 462 462)]

theorem b117_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_06_rows b117_06_labels 128036550146107379055834001050 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_06_rows b117_06_labels]
    decide +kernel

def b117_07_rows : List Row := [(row3 24 31 52), (row3 24 31 53), (row3 24 31 54), (row3 24 31 55), (row3 24 31 56), (row3 24 31 57), (row3 24 31 58), (row3 24 31 59), (row3 24 31 60), (row3 24 31 61), (row3 24 31 62), (row3 24 31 63), (row3 24 32 33), (row3 24 32 34), (row3 24 32 35), (row3 24 32 36)]

def b117_07_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 259 8 204), (row3 269 462 269), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 341 429 71), (row3 168 94 333), (row3 254 8 203), (row3 462 462 462)]

theorem b117_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_07_rows b117_07_labels 115089527530838649678840525600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_07_rows b117_07_labels]
    decide +kernel

def b117_08_rows : List Row := [(row3 24 32 37), (row3 24 32 38), (row3 24 32 39), (row3 24 32 40), (row3 24 32 41), (row3 24 32 42), (row3 24 32 43), (row3 24 32 44), (row3 24 32 45), (row3 24 32 46), (row3 24 32 47), (row3 24 32 48), (row3 24 32 49), (row3 24 32 50), (row3 24 32 51), (row3 24 32 52)]

def b117_08_labels : List Row := [(row3 254 8 203), (row3 168 94 333), (row3 341 429 71), (row3 70 434 70), (row3 187 90 357), (row3 218 10 170), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 218 10 170), (row3 187 90 357), (row3 205 96 335), (row3 217 10 169), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_08_rows b117_08_labels 378309836061359661758805704070 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_08_rows b117_08_labels]
    decide +kernel

def b117_09_rows : List Row := [(row3 24 32 53), (row3 24 32 54), (row3 24 32 55), (row3 24 32 56), (row3 24 32 57), (row3 24 32 58), (row3 24 32 59), (row3 24 32 60), (row3 24 32 61), (row3 24 32 62), (row3 24 32 63), (row3 24 33 34), (row3 24 33 35), (row3 24 33 36), (row3 24 33 37), (row3 24 33 38)]

def b117_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 217 10 169), (row3 219 9 185), (row3 238 462 238), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 242 462 242), (row3 238 462 238), (row3 279 279 278), (row3 236 462 236), (row3 462 462 462), (row3 236 462 236), (row3 279 279 278)]

theorem b117_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_09_rows b117_09_labels 27353860112565895981740432450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_09_rows b117_09_labels]
    decide +kernel

def b117_10_rows : List Row := [(row3 24 33 39), (row3 24 33 40), (row3 24 33 41), (row3 24 33 42), (row3 24 33 43), (row3 24 33 44), (row3 24 33 45), (row3 24 33 46), (row3 24 33 47), (row3 24 33 48), (row3 24 33 49), (row3 24 33 50), (row3 24 33 51), (row3 24 33 52), (row3 24 33 53), (row3 24 33 54)]

def b117_10_labels : List Row := [(row3 161 176 176), (row3 165 176 165), (row3 301 301 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 282 282 278), (row3 276 276 275), (row3 233 462 233), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_10_rows b117_10_labels 696631108773785003234497920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_10_rows b117_10_labels]
    decide +kernel

def b117_11_rows : List Row := [(row3 24 33 55), (row3 24 33 56), (row3 24 33 57), (row3 24 33 58), (row3 24 33 59), (row3 24 33 60), (row3 24 33 61), (row3 24 33 62), (row3 24 33 63), (row3 24 34 35), (row3 24 34 36), (row3 24 34 37), (row3 24 34 38), (row3 24 34 39), (row3 24 34 40), (row3 24 34 41)]

def b117_11_labels : List Row := [(row3 236 462 236), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 243 462 243), (row3 234 234 234), (row3 279 278 279), (row3 281 278 281), (row3 226 226 234)]

theorem b117_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_11_rows b117_11_labels 28292939144499380597834400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_11_rows b117_11_labels]
    decide +kernel

def b117_12_rows : List Row := [(row3 24 34 42), (row3 24 34 43), (row3 24 34 44), (row3 24 34 45), (row3 24 34 46), (row3 24 34 47), (row3 24 34 48), (row3 24 34 49), (row3 24 34 50), (row3 24 34 51), (row3 24 34 52), (row3 24 34 53), (row3 24 34 54), (row3 24 34 55), (row3 24 34 56), (row3 24 34 57)]

def b117_12_labels : List Row := [(row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 234 234 234), (row3 237 235 235), (row3 247 462 247), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 242 462 242), (row3 462 462 462)]

theorem b117_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_12_rows b117_12_labels 1291070994464241945022500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_12_rows b117_12_labels]
    decide +kernel

def b117_13_rows : List Row := [(row3 24 34 58), (row3 24 34 59), (row3 24 34 60), (row3 24 34 61), (row3 24 34 62), (row3 24 34 63), (row3 24 35 36), (row3 24 35 37), (row3 24 35 38), (row3 24 35 39), (row3 24 35 40), (row3 24 35 41), (row3 24 35 42), (row3 24 35 43), (row3 24 35 44), (row3 24 35 45)]

def b117_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 238 236 238), (row3 247 247 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_13_rows b117_13_labels 470569125556685726937000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_13_rows b117_13_labels]
    decide +kernel

def b117_14_rows : List Row := [(row3 24 35 46), (row3 24 35 47), (row3 24 35 48), (row3 24 35 49), (row3 24 35 50), (row3 24 35 51), (row3 24 35 52), (row3 24 35 53), (row3 24 35 54), (row3 24 35 55), (row3 24 35 56), (row3 24 35 57), (row3 24 35 58), (row3 24 35 59), (row3 24 35 60), (row3 24 35 61)]

def b117_14_labels : List Row := [(row3 462 462 462), (row3 243 243 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_14_rows b117_14_labels 11285468089421881020000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_14_rows b117_14_labels]
    decide +kernel

def b117_15_rows : List Row := [(row3 24 35 62), (row3 24 35 63), (row3 24 36 37), (row3 24 36 38), (row3 24 36 39), (row3 24 36 40), (row3 24 36 41), (row3 24 36 42), (row3 24 36 43), (row3 24 36 44), (row3 24 36 45), (row3 24 36 46), (row3 24 36 47), (row3 24 36 48), (row3 24 36 49), (row3 24 36 50)]

def b117_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b117_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b117_15_rows b117_15_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b117_15_rows b117_15_labels]
    decide +kernel

theorem checked117 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_117 QuarticIntegerComputationalData.ids64_117 1030169318343088522502138670210 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b117_00_rows ++ b117_01_rows) ++ (b117_02_rows ++ b117_03_rows)) ++ ((b117_04_rows ++ b117_05_rows) ++ (b117_06_rows ++ b117_07_rows))) ++ (((b117_08_rows ++ b117_09_rows) ++ (b117_10_rows ++ b117_11_rows)) ++ ((b117_12_rows ++ b117_13_rows) ++ (b117_14_rows ++ b117_15_rows))))
    ((((b117_00_labels ++ b117_01_labels) ++ (b117_02_labels ++ b117_03_labels)) ++ ((b117_04_labels ++ b117_05_labels) ++ (b117_06_labels ++ b117_07_labels))) ++ (((b117_08_labels ++ b117_09_labels) ++ (b117_10_labels ++ b117_11_labels)) ++ ((b117_12_labels ++ b117_13_labels) ++ (b117_14_labels ++ b117_15_labels)))) 1030169318343088522502138670210
  exact ((((b117_00_checked.append (c := 3342240029925631554017245500) b117_01_checked (by decide +kernel)).append (c := 109370215129097304780848396970) (b117_02_checked.append (c := 106027975099171673226831151470) b117_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 623778925195656570028207221870) ((b117_04_checked.append (c := 271282632389613236512684298250) b117_05_checked (by decide +kernel)).append (c := 514408710066559265247358824900) (b117_06_checked.append (c := 243126077676946028734674526650) b117_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1030169318343088522502138670210) (((b117_08_checked.append (c := 405663696173925557740546136520) b117_09_checked (by decide +kernel)).append (c := 406388620221843842124378468840) (b117_10_checked.append (c := 724924047918284383832332320) b117_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 406390393147431952473931448340) ((b117_12_checked.append (c := 1761640120020927671959500) b117_13_checked (by decide +kernel)).append (c := 1772925588110349552979500) (b117_14_checked.append (c := 11285468089421881020000) b117_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b118_00_rows : List Row := [(row3 24 36 51), (row3 24 36 52), (row3 24 36 53), (row3 24 36 54), (row3 24 36 55), (row3 24 36 56), (row3 24 36 57), (row3 24 36 58), (row3 24 36 59), (row3 24 36 60), (row3 24 36 61), (row3 24 36 62), (row3 24 36 63), (row3 24 37 38), (row3 24 37 39), (row3 24 37 40)]

def b118_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 243 462), (row3 236 236 462), (row3 238 236 238)]

theorem b118_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_00_rows b118_00_labels 754511286430350037413000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_00_rows b118_00_labels]
    decide +kernel

def b118_01_rows : List Row := [(row3 24 37 41), (row3 24 37 42), (row3 24 37 43), (row3 24 37 44), (row3 24 37 45), (row3 24 37 46), (row3 24 37 47), (row3 24 37 48), (row3 24 37 49), (row3 24 37 50), (row3 24 37 51), (row3 24 37 52), (row3 24 37 53), (row3 24 37 54), (row3 24 37 55), (row3 24 37 56)]

def b118_01_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 247 462), (row3 241 241 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_01_rows b118_01_labels 49296594969267195120000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_01_rows b118_01_labels]
    decide +kernel

def b118_02_rows : List Row := [(row3 24 37 57), (row3 24 37 58), (row3 24 37 59), (row3 24 37 60), (row3 24 37 61), (row3 24 37 62), (row3 24 37 63), (row3 24 38 39), (row3 24 38 40), (row3 24 38 41), (row3 24 38 42), (row3 24 38 43), (row3 24 38 44), (row3 24 38 45), (row3 24 38 46), (row3 24 38 47)]

def b118_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 279 278 279), (row3 281 278 281), (row3 234 234 234), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 226 226 234)]

theorem b118_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_02_rows b118_02_labels 98611787447425784148539400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_02_rows b118_02_labels]
    decide +kernel

def b118_03_rows : List Row := [(row3 24 38 48), (row3 24 38 49), (row3 24 38 50), (row3 24 38 51), (row3 24 38 52), (row3 24 38 53), (row3 24 38 54), (row3 24 38 55), (row3 24 38 56), (row3 24 38 57), (row3 24 38 58), (row3 24 38 59), (row3 24 38 60), (row3 24 38 61), (row3 24 38 62), (row3 24 38 63)]

def b118_03_labels : List Row := [(row3 237 235 235), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 242 462 242), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_03_rows b118_03_labels 633223809468359113747500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_03_rows b118_03_labels]
    decide +kernel

def b118_04_rows : List Row := [(row3 24 39 40), (row3 24 39 41), (row3 24 39 42), (row3 24 39 43), (row3 24 39 44), (row3 24 39 45), (row3 24 39 46), (row3 24 39 47), (row3 24 39 48), (row3 24 39 49), (row3 24 39 50), (row3 24 39 51), (row3 24 39 52), (row3 24 39 53), (row3 24 39 54), (row3 24 39 55)]

def b118_04_labels : List Row := [(row3 165 176 165), (row3 282 282 278), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 301 301 278), (row3 276 276 275), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 233 462 233)]

theorem b118_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_04_rows b118_04_labels 467012708509081117825208640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_04_rows b118_04_labels]
    decide +kernel

def b118_05_rows : List Row := [(row3 24 39 56), (row3 24 39 57), (row3 24 39 58), (row3 24 39 59), (row3 24 39 60), (row3 24 39 61), (row3 24 39 62), (row3 24 39 63), (row3 24 40 41), (row3 24 40 42), (row3 24 40 43), (row3 24 40 44), (row3 24 40 45), (row3 24 40 46), (row3 24 40 47), (row3 24 40 48)]

def b118_05_labels : List Row := [(row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 329 344 340), (row3 209 206 209), (row3 256 256 255), (row3 462 239 239), (row3 256 256 255), (row3 209 206 209), (row3 329 344 340), (row3 75 425 326)]

theorem b118_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_05_rows b118_05_labels 83984736135524284379512018680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_05_rows b118_05_labels]
    decide +kernel

def b118_06_rows : List Row := [(row3 24 40 49), (row3 24 40 50), (row3 24 40 51), (row3 24 40 52), (row3 24 40 53), (row3 24 40 54), (row3 24 40 55), (row3 24 40 56), (row3 24 40 57), (row3 24 40 58), (row3 24 40 59), (row3 24 40 60), (row3 24 40 61), (row3 24 40 62), (row3 24 40 63), (row3 24 41 42)]

def b118_06_labels : List Row := [(row3 194 188 195), (row3 267 267 265), (row3 462 238 238), (row3 462 462 462), (row3 462 238 238), (row3 267 267 265), (row3 194 188 195), (row3 205 96 335), (row3 276 276 275), (row3 237 235 235), (row3 241 241 462), (row3 462 462 462), (row3 241 241 462), (row3 237 235 235), (row3 276 276 275), (row3 285 462 285)]

theorem b118_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_06_rows b118_06_labels 14400924428247686122101032460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_06_rows b118_06_labels]
    decide +kernel

def b118_07_rows : List Row := [(row3 24 41 43), (row3 24 41 44), (row3 24 41 45), (row3 24 41 46), (row3 24 41 47), (row3 24 41 48), (row3 24 41 49), (row3 24 41 50), (row3 24 41 51), (row3 24 41 52), (row3 24 41 53), (row3 24 41 54), (row3 24 41 55), (row3 24 41 56), (row3 24 41 57), (row3 24 41 58)]

def b118_07_labels : List Row := [(row3 235 462 235), (row3 243 462 243), (row3 462 462 462), (row3 245 462 245), (row3 226 229 229), (row3 194 188 195), (row3 116 11 213), (row3 232 462 232), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 252 462 252), (row3 217 10 169), (row3 233 462 233), (row3 247 462 247)]

theorem b118_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_07_rows b118_07_labels 3033412798889545994873292420 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_07_rows b118_07_labels]
    decide +kernel

def b118_08_rows : List Row := [(row3 24 41 59), (row3 24 41 60), (row3 24 41 61), (row3 24 41 62), (row3 24 41 63), (row3 24 42 43), (row3 24 42 44), (row3 24 42 45), (row3 24 42 46), (row3 24 42 47), (row3 24 42 48), (row3 24 42 49), (row3 24 42 50), (row3 24 42 51), (row3 24 42 52), (row3 24 42 53)]

def b118_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 245 462), (row3 267 267 265), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_08_rows b118_08_labels 4772956781524091682020400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_08_rows b118_08_labels]
    decide +kernel

def b118_09_rows : List Row := [(row3 24 42 54), (row3 24 42 55), (row3 24 42 56), (row3 24 42 57), (row3 24 42 58), (row3 24 42 59), (row3 24 42 60), (row3 24 42 61), (row3 24 42 62), (row3 24 42 63), (row3 24 43 44), (row3 24 43 45), (row3 24 43 46), (row3 24 43 47), (row3 24 43 48), (row3 24 43 49)]

def b118_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 246 462 246)]

theorem b118_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_09_rows b118_09_labels 111645142702208927487000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_09_rows b118_09_labels]
    decide +kernel

def b118_10_rows : List Row := [(row3 24 43 50), (row3 24 43 51), (row3 24 43 52), (row3 24 43 53), (row3 24 43 54), (row3 24 43 55), (row3 24 43 56), (row3 24 43 57), (row3 24 43 58), (row3 24 43 59), (row3 24 43 60), (row3 24 43 61), (row3 24 43 62), (row3 24 43 63), (row3 24 44 45), (row3 24 44 46)]

def b118_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_10_rows b118_10_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_10_rows b118_10_labels]
    decide +kernel

def b118_11_rows : List Row := [(row3 24 44 47), (row3 24 44 48), (row3 24 44 49), (row3 24 44 50), (row3 24 44 51), (row3 24 44 52), (row3 24 44 53), (row3 24 44 54), (row3 24 44 55), (row3 24 44 56), (row3 24 44 57), (row3 24 44 58), (row3 24 44 59), (row3 24 44 60), (row3 24 44 61), (row3 24 44 62)]

def b118_11_labels : List Row := [(row3 243 243 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_11_rows b118_11_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_11_rows b118_11_labels]
    decide +kernel

def b118_12_rows : List Row := [(row3 24 44 63), (row3 24 45 46), (row3 24 45 47), (row3 24 45 48), (row3 24 45 49), (row3 24 45 50), (row3 24 45 51), (row3 24 45 52), (row3 24 45 53), (row3 24 45 54), (row3 24 45 55), (row3 24 45 56), (row3 24 45 57), (row3 24 45 58), (row3 24 45 59), (row3 24 45 60)]

def b118_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 235 235 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_12_rows b118_12_labels 413694291334688503731000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_12_rows b118_12_labels]
    decide +kernel

def b118_13_rows : List Row := [(row3 24 45 61), (row3 24 45 62), (row3 24 45 63), (row3 24 46 47), (row3 24 46 48), (row3 24 46 49), (row3 24 46 50), (row3 24 46 51), (row3 24 46 52), (row3 24 46 53), (row3 24 46 54), (row3 24 46 55), (row3 24 46 56), (row3 24 46 57), (row3 24 46 58), (row3 24 46 59)]

def b118_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 285 285 462), (row3 267 267 265), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 232 462 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b118_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_13_rows b118_13_labels 77001664468098878131235400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_13_rows b118_13_labels]
    decide +kernel

def b118_14_rows : List Row := [(row3 24 46 60), (row3 24 46 61), (row3 24 46 62), (row3 24 46 63), (row3 24 47 48), (row3 24 47 49), (row3 24 47 50), (row3 24 47 51), (row3 24 47 52), (row3 24 47 53), (row3 24 47 54), (row3 24 47 55), (row3 24 47 56), (row3 24 47 57), (row3 24 47 58), (row3 24 47 59)]

def b118_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 194 188 195), (row3 252 462 252), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 246 462 246), (row3 232 462 232), (row3 116 11 213), (row3 217 10 169), (row3 236 462 236), (row3 243 462 243), (row3 462 462 462)]

theorem b118_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_14_rows b118_14_labels 3030874575059159846627887920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_14_rows b118_14_labels]
    decide +kernel

def b118_15_rows : List Row := [(row3 24 47 60), (row3 24 47 61), (row3 24 47 62), (row3 24 47 63), (row3 24 48 49), (row3 24 48 50), (row3 24 48 51), (row3 24 48 52), (row3 24 48 53), (row3 24 48 54), (row3 24 48 55), (row3 24 48 56), (row3 24 48 57), (row3 24 48 58), (row3 24 48 59), (row3 24 48 60)]

def b118_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 247 462 247), (row3 233 462 233), (row3 329 340 344), (row3 209 209 206), (row3 256 255 256), (row3 462 239 239), (row3 256 255 256), (row3 209 209 206), (row3 329 340 344), (row3 70 434 70), (row3 165 176 165), (row3 281 278 281), (row3 238 236 238), (row3 462 462 462)]

theorem b118_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b118_15_rows b118_15_labels 248567003647893506992849287840 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b118_15_rows b118_15_labels]
    decide +kernel

theorem checked118 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_118 QuarticIntegerComputationalData.ids64_118 353666321348272696004129346660 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b118_00_rows ++ b118_01_rows) ++ (b118_02_rows ++ b118_03_rows)) ++ ((b118_04_rows ++ b118_05_rows) ++ (b118_06_rows ++ b118_07_rows))) ++ (((b118_08_rows ++ b118_09_rows) ++ (b118_10_rows ++ b118_11_rows)) ++ ((b118_12_rows ++ b118_13_rows) ++ (b118_14_rows ++ b118_15_rows))))
    ((((b118_00_labels ++ b118_01_labels) ++ (b118_02_labels ++ b118_03_labels)) ++ ((b118_04_labels ++ b118_05_labels) ++ (b118_06_labels ++ b118_07_labels))) ++ (((b118_08_labels ++ b118_09_labels) ++ (b118_10_labels ++ b118_11_labels)) ++ ((b118_12_labels ++ b118_13_labels) ++ (b118_14_labels ++ b118_15_labels)))) 353666321348272696004129346660
  exact ((((b118_00_checked.append (c := 803807881399617232533000) b118_01_checked (by decide +kernel)).append (c := 100048819138293760494819900) (b118_02_checked.append (c := 99245011256894143262286900) b118_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 101986134890308891374806372100) ((b118_04_checked.append (c := 84451748844033365497337227320) b118_05_checked (by decide +kernel)).append (c := 101886086071170597614311552200) (b118_06_checked.append (c := 17434337227137232116974324880) b118_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 353666321348272696004129346660) (((b118_08_checked.append (c := 4884601924226300609507400) b118_09_checked (by decide +kernel)).append (c := 4892876251704223210832400) (b118_10_checked.append (c := 8274327477922601325000) b118_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 251680186457963804629322974560) ((b118_12_checked.append (c := 77415358759433566634966400) b118_13_checked (by decide +kernel)).append (c := 251675293581712100406112142160) (b118_14_checked.append (c := 251597878222952666839477175760) b118_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b119_00_rows : List Row := [(row3 24 48 61), (row3 24 48 62), (row3 24 48 63), (row3 24 49 50), (row3 24 49 51), (row3 24 49 52), (row3 24 49 53), (row3 24 49 54), (row3 24 49 55), (row3 24 49 56), (row3 24 49 57), (row3 24 49 58), (row3 24 49 59), (row3 24 49 60), (row3 24 49 61), (row3 24 49 62)]

def b119_00_labels : List Row := [(row3 238 236 238), (row3 281 278 281), (row3 165 176 165), (row3 285 285 462), (row3 235 235 462), (row3 243 243 462), (row3 462 462 462), (row3 245 245 462), (row3 226 229 229), (row3 187 90 357), (row3 301 301 278), (row3 226 226 234), (row3 247 247 462), (row3 462 462 462), (row3 243 243 462), (row3 234 234 234)]

theorem b119_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_00_rows b119_00_labels 7054987093565967149793092640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_00_rows b119_00_labels]
    decide +kernel

def b119_01_rows : List Row := [(row3 24 49 63), (row3 24 50 51), (row3 24 50 52), (row3 24 50 53), (row3 24 50 54), (row3 24 50 55), (row3 24 50 56), (row3 24 50 57), (row3 24 50 58), (row3 24 50 59), (row3 24 50 60), (row3 24 50 61), (row3 24 50 62), (row3 24 50 63), (row3 24 51 52), (row3 24 51 53)]

def b119_01_labels : List Row := [(row3 282 282 278), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 245 462 245), (row3 218 10 170), (row3 235 462 235), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462)]

theorem b119_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_01_rows b119_01_labels 546473747512594395255101850 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_01_rows b119_01_labels]
    decide +kernel

def b119_02_rows : List Row := [(row3 24 51 54), (row3 24 51 55), (row3 24 51 56), (row3 24 51 57), (row3 24 51 58), (row3 24 51 59), (row3 24 51 60), (row3 24 51 61), (row3 24 51 62), (row3 24 51 63), (row3 24 52 53), (row3 24 52 54), (row3 24 52 55), (row3 24 52 56), (row3 24 52 57), (row3 24 52 58)]

def b119_02_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_02_rows b119_02_labels 8274327477922601325000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_02_rows b119_02_labels]
    decide +kernel

def b119_03_rows : List Row := [(row3 24 52 59), (row3 24 52 60), (row3 24 52 61), (row3 24 52 62), (row3 24 52 63), (row3 24 53 54), (row3 24 53 55), (row3 24 53 56), (row3 24 53 57), (row3 24 53 58), (row3 24 53 59), (row3 24 53 60), (row3 24 53 61), (row3 24 53 62), (row3 24 53 63), (row3 24 54 55)]

def b119_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 285 462 285)]

theorem b119_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_03_rows b119_03_labels 72962644836167618534356500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_03_rows b119_03_labels]
    decide +kernel

def b119_04_rows : List Row := [(row3 24 54 56), (row3 24 54 57), (row3 24 54 58), (row3 24 54 59), (row3 24 54 60), (row3 24 54 61), (row3 24 54 62), (row3 24 54 63), (row3 24 55 56), (row3 24 55 57), (row3 24 55 58), (row3 24 55 59), (row3 24 55 60), (row3 24 55 61), (row3 24 55 62), (row3 24 55 63)]

def b119_04_labels : List Row := [(row3 218 10 170), (row3 235 462 235), (row3 244 462 244), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 244 462 244), (row3 235 462 235), (row3 187 90 357), (row3 282 282 278), (row3 234 234 234), (row3 243 243 462), (row3 462 462 462), (row3 247 247 462), (row3 226 226 234), (row3 301 301 278)]

theorem b119_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_04_rows b119_04_labels 7259460478983186879368848950 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_04_rows b119_04_labels]
    decide +kernel

def b119_05_rows : List Row := [(row3 24 56 57), (row3 24 56 58), (row3 24 56 59), (row3 24 56 60), (row3 24 56 61), (row3 24 56 62), (row3 24 56 63), (row3 24 57 58), (row3 24 57 59), (row3 24 57 60), (row3 24 57 61), (row3 24 57 62), (row3 24 57 63), (row3 24 58 59), (row3 24 58 60), (row3 24 58 61)]

def b119_05_labels : List Row := [(row3 341 71 429), (row3 168 333 94), (row3 254 203 8), (row3 462 462 462), (row3 254 203 8), (row3 168 333 94), (row3 341 71 429), (row3 279 278 279), (row3 236 236 462), (row3 462 462 462), (row3 236 236 462), (row3 279 278 279), (row3 161 176 176), (row3 243 243 462), (row3 462 462 462), (row3 243 243 462)]

theorem b119_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_05_rows b119_05_labels 225503665395810690481286971680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_05_rows b119_05_labels]
    decide +kernel

def b119_06_rows : List Row := [(row3 24 58 62), (row3 24 58 63), (row3 24 59 60), (row3 24 59 61), (row3 24 59 62), (row3 24 59 63), (row3 24 60 61), (row3 24 60 62), (row3 24 60 63), (row3 24 61 62), (row3 24 61 63), (row3 24 62 63), (row3 25 26 27), (row3 25 26 28), (row3 25 26 29), (row3 25 26 30)]

def b119_06_labels : List Row := [(row3 234 234 234), (row3 279 279 278), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 243 462 243), (row3 236 462 236), (row3 279 279 278), (row3 462 193 193), (row3 462 263 263), (row3 462 462 462), (row3 462 263 263)]

theorem b119_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_06_rows b119_06_labels 645336625594636333218079200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_06_rows b119_06_labels]
    decide +kernel

def b119_07_rows : List Row := [(row3 25 26 31), (row3 25 26 32), (row3 25 26 33), (row3 25 26 34), (row3 25 26 35), (row3 25 26 36), (row3 25 26 37), (row3 25 26 38), (row3 25 26 39), (row3 25 26 40), (row3 25 26 41), (row3 25 26 42), (row3 25 26 43), (row3 25 26 44), (row3 25 26 45), (row3 25 26 46)]

def b119_07_labels : List Row := [(row3 238 192 193), (row3 235 162 163), (row3 462 358 358), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284), (row3 462 285 285), (row3 235 191 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_07_rows b119_07_labels 16079416137618764743605502500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_07_rows b119_07_labels]
    decide +kernel

def b119_08_rows : List Row := [(row3 25 26 47), (row3 25 26 48), (row3 25 26 49), (row3 25 26 50), (row3 25 26 51), (row3 25 26 52), (row3 25 26 53), (row3 25 26 54), (row3 25 26 55), (row3 25 26 56), (row3 25 26 57), (row3 25 26 58), (row3 25 26 59), (row3 25 26 60), (row3 25 26 61), (row3 25 26 62)]

def b119_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 264 264), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_08_rows b119_08_labels 32861954329140895345500000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_08_rows b119_08_labels]
    decide +kernel

def b119_09_rows : List Row := [(row3 25 26 63), (row3 25 27 28), (row3 25 27 29), (row3 25 27 30), (row3 25 27 31), (row3 25 27 32), (row3 25 27 33), (row3 25 27 34), (row3 25 27 35), (row3 25 27 36), (row3 25 27 37), (row3 25 27 38), (row3 25 27 39), (row3 25 27 40), (row3 25 27 41), (row3 25 27 42)]

def b119_09_labels : List Row := [(row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 238 238), (row3 462 261 261), (row3 462 273 273), (row3 462 193 193), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 235 235), (row3 462 235 235), (row3 462 261 261), (row3 462 235 235)]

theorem b119_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_09_rows b119_09_labels 368248386450737944582804800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_09_rows b119_09_labels]
    decide +kernel

def b119_10_rows : List Row := [(row3 25 27 43), (row3 25 27 44), (row3 25 27 45), (row3 25 27 46), (row3 25 27 47), (row3 25 27 48), (row3 25 27 49), (row3 25 27 50), (row3 25 27 51), (row3 25 27 52), (row3 25 27 53), (row3 25 27 54), (row3 25 27 55), (row3 25 27 56), (row3 25 27 57), (row3 25 27 58)]

def b119_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_10_rows b119_10_labels 121705541119974164220000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_10_rows b119_10_labels]
    decide +kernel

def b119_11_rows : List Row := [(row3 25 27 59), (row3 25 27 60), (row3 25 27 61), (row3 25 27 62), (row3 25 27 63), (row3 25 28 29), (row3 25 28 30), (row3 25 28 31), (row3 25 28 32), (row3 25 28 33), (row3 25 28 34), (row3 25 28 35), (row3 25 28 36), (row3 25 28 37), (row3 25 28 38), (row3 25 28 39)]

def b119_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 238 236 238), (row3 462 236 236), (row3 462 263 263), (row3 462 236 236), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243)]

theorem b119_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_11_rows b119_11_labels 20432089590462240995460000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_11_rows b119_11_labels]
    decide +kernel

def b119_12_rows : List Row := [(row3 25 28 40), (row3 25 28 41), (row3 25 28 42), (row3 25 28 43), (row3 25 28 44), (row3 25 28 45), (row3 25 28 46), (row3 25 28 47), (row3 25 28 48), (row3 25 28 49), (row3 25 28 50), (row3 25 28 51), (row3 25 28 52), (row3 25 28 53), (row3 25 28 54), (row3 25 28 55)]

def b119_12_labels : List Row := [(row3 462 243 243), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_12_rows b119_12_labels 100496817745117682217000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_12_rows b119_12_labels]
    decide +kernel

def b119_13_rows : List Row := [(row3 25 28 56), (row3 25 28 57), (row3 25 28 58), (row3 25 28 59), (row3 25 28 60), (row3 25 28 61), (row3 25 28 62), (row3 25 28 63), (row3 25 29 30), (row3 25 29 31), (row3 25 29 32), (row3 25 29 33), (row3 25 29 34), (row3 25 29 35), (row3 25 29 36), (row3 25 29 37)]

def b119_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 261 261 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_13_rows b119_13_labels 2120009397602256017827200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_13_rows b119_13_labels]
    decide +kernel

def b119_14_rows : List Row := [(row3 25 29 38), (row3 25 29 39), (row3 25 29 40), (row3 25 29 41), (row3 25 29 42), (row3 25 29 43), (row3 25 29 44), (row3 25 29 45), (row3 25 29 46), (row3 25 29 47), (row3 25 29 48), (row3 25 29 49), (row3 25 29 50), (row3 25 29 51), (row3 25 29 52), (row3 25 29 53)]

def b119_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b119_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_14_rows b119_14_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_14_rows b119_14_labels]
    decide +kernel

def b119_15_rows : List Row := [(row3 25 29 54), (row3 25 29 55), (row3 25 29 56), (row3 25 29 57), (row3 25 29 58), (row3 25 29 59), (row3 25 29 60), (row3 25 29 61), (row3 25 29 62), (row3 25 29 63), (row3 25 30 31), (row3 25 30 32), (row3 25 30 33), (row3 25 30 34), (row3 25 30 35), (row3 25 30 36)]

def b119_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 192 238), (row3 235 233 236), (row3 462 263 263), (row3 462 236 236), (row3 462 243 243), (row3 462 462 462)]

theorem b119_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b119_15_rows b119_15_labels 367862328085713851039784000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b119_15_rows b119_15_labels]
    decide +kernel

theorem checked119 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_119 QuarticIntegerComputationalData.ids64_119 257954057368462007803491091320 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b119_00_rows ++ b119_01_rows) ++ (b119_02_rows ++ b119_03_rows)) ++ ((b119_04_rows ++ b119_05_rows) ++ (b119_06_rows ++ b119_07_rows))) ++ (((b119_08_rows ++ b119_09_rows) ++ (b119_10_rows ++ b119_11_rows)) ++ ((b119_12_rows ++ b119_13_rows) ++ (b119_14_rows ++ b119_15_rows))))
    ((((b119_00_labels ++ b119_01_labels) ++ (b119_02_labels ++ b119_03_labels)) ++ ((b119_04_labels ++ b119_05_labels) ++ (b119_06_labels ++ b119_07_labels))) ++ (((b119_08_labels ++ b119_09_labels) ++ (b119_10_labels ++ b119_11_labels)) ++ ((b119_12_labels ++ b119_13_labels) ++ (b119_14_labels ++ b119_15_labels)))) 257954057368462007803491091320
  exact ((((b119_00_checked.append (c := 7601460841078561545048194490) b119_01_checked (by decide +kernel)).append (c := 7674431760242207086183875990) (b119_02_checked.append (c := 72970919163645541135681500) b119_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 257162310398249485523663278320) ((b119_04_checked.append (c := 232763125874793877360655820630) b119_05_checked (by decide +kernel)).append (c := 249487878638007278437479402330) (b119_06_checked.append (c := 16724752763213401076823581700) b119_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 257954057368462007803491091320) (((b119_08_checked.append (c := 401110340779878839928304800) b119_09_checked (by decide +kernel)).append (c := 421664135911461055087984800) (b119_10_checked.append (c := 20553795131582215159680000) b119_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 791746970212522279827813000) ((b119_12_checked.append (c := 2220506215347373700044200) b119_13_checked (by decide +kernel)).append (c := 370082834301061224739828200) (b119_14_checked.append (c := 367862328085713851039784000) b119_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals64
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b120_00_rows : List Row := [(row3 25 30 37), (row3 25 30 38), (row3 25 30 39), (row3 25 30 40), (row3 25 30 41), (row3 25 30 42), (row3 25 30 43), (row3 25 30 44), (row3 25 30 45), (row3 25 30 46), (row3 25 30 47), (row3 25 30 48), (row3 25 30 49), (row3 25 30 50), (row3 25 30 51), (row3 25 30 52)]

def b120_00_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 245 245), (row3 462 238 238), (row3 462 243 243), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 241 241), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_00_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_00_rows b120_00_labels 129010416775618138849500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_00_rows b120_00_labels]
    decide +kernel

def b120_01_rows : List Row := [(row3 25 30 53), (row3 25 30 54), (row3 25 30 55), (row3 25 30 56), (row3 25 30 57), (row3 25 30 58), (row3 25 30 59), (row3 25 30 60), (row3 25 30 61), (row3 25 30 62), (row3 25 30 63), (row3 25 31 32), (row3 25 31 33), (row3 25 31 34), (row3 25 31 35), (row3 25 31 36)]

def b120_01_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 288 288 288), (row3 235 193 191), (row3 462 273 273), (row3 462 235 235), (row3 462 462 462)]

theorem b120_01_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_01_rows b120_01_labels 378420610223400566336877600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_01_rows b120_01_labels]
    decide +kernel

def b120_02_rows : List Row := [(row3 25 31 37), (row3 25 31 38), (row3 25 31 39), (row3 25 31 40), (row3 25 31 41), (row3 25 31 42), (row3 25 31 43), (row3 25 31 44), (row3 25 31 45), (row3 25 31 46), (row3 25 31 47), (row3 25 31 48), (row3 25 31 49), (row3 25 31 50), (row3 25 31 51), (row3 25 31 52)]

def b120_02_labels : List Row := [(row3 235 462 235), (row3 273 462 273), (row3 193 235 191), (row3 229 229 226), (row3 462 261 261), (row3 462 235 235), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 261 462 261), (row3 462 462 462), (row3 462 238 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_02_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_02_rows b120_02_labels 361540360568205382044852000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_02_rows b120_02_labels]
    decide +kernel

def b120_03_rows : List Row := [(row3 25 31 53), (row3 25 31 54), (row3 25 31 55), (row3 25 31 56), (row3 25 31 57), (row3 25 31 58), (row3 25 31 59), (row3 25 31 60), (row3 25 31 61), (row3 25 31 62), (row3 25 31 63), (row3 25 32 33), (row3 25 32 34), (row3 25 32 35), (row3 25 32 36), (row3 25 32 37)]

def b120_03_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 193 163 139), (row3 261 288 290), (row3 238 232 230), (row3 462 462 462), (row3 238 462 238)]

theorem b120_03_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_03_rows b120_03_labels 1587035566852993399052635200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_03_rows b120_03_labels]
    decide +kernel

def b120_04_rows : List Row := [(row3 25 32 38), (row3 25 32 39), (row3 25 32 40), (row3 25 32 41), (row3 25 32 42), (row3 25 32 43), (row3 25 32 44), (row3 25 32 45), (row3 25 32 46), (row3 25 32 47), (row3 25 32 48), (row3 25 32 49), (row3 25 32 50), (row3 25 32 51), (row3 25 32 52), (row3 25 32 53)]

def b120_04_labels : List Row := [(row3 261 462 261), (row3 193 232 189), (row3 357 90 187), (row3 288 288 288), (row3 235 232 228), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 273 462 273), (row3 273 462 273), (row3 229 231 227), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_04_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_04_rows b120_04_labels 6970716195139494336281610960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_04_rows b120_04_labels]
    decide +kernel

def b120_05_rows : List Row := [(row3 25 32 54), (row3 25 32 55), (row3 25 32 56), (row3 25 32 57), (row3 25 32 58), (row3 25 32 59), (row3 25 32 60), (row3 25 32 61), (row3 25 32 62), (row3 25 32 63), (row3 25 33 34), (row3 25 33 35), (row3 25 33 36), (row3 25 33 37), (row3 25 33 38), (row3 25 33 39)]

def b120_05_labels : List Row := [(row3 462 462 462), (row3 235 462 235), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 163 163), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 284 284)]

theorem b120_05_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_05_rows b120_05_labels 1174389558609050052561234000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_05_rows b120_05_labels]
    decide +kernel

def b120_06_rows : List Row := [(row3 25 33 40), (row3 25 33 41), (row3 25 33 42), (row3 25 33 43), (row3 25 33 44), (row3 25 33 45), (row3 25 33 46), (row3 25 33 47), (row3 25 33 48), (row3 25 33 49), (row3 25 33 50), (row3 25 33 51), (row3 25 33 52), (row3 25 33 53), (row3 25 33 54), (row3 25 33 55)]

def b120_06_labels : List Row := [(row3 278 301 301), (row3 193 163 193), (row3 462 284 284), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 235 462 235), (row3 265 277 277), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_06_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_06_rows b120_06_labels 1342136596380421342048845000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_06_rows b120_06_labels]
    decide +kernel

def b120_07_rows : List Row := [(row3 25 33 56), (row3 25 33 57), (row3 25 33 58), (row3 25 33 59), (row3 25 33 60), (row3 25 33 61), (row3 25 33 62), (row3 25 33 63), (row3 25 34 35), (row3 25 34 36), (row3 25 34 37), (row3 25 34 38), (row3 25 34 39), (row3 25 34 40), (row3 25 34 41), (row3 25 34 42)]

def b120_07_labels : List Row := [(row3 462 462 462), (row3 238 462 238), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 232 232), (row3 234 226 226), (row3 273 288 273), (row3 462 232 232)]

theorem b120_07_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_07_rows b120_07_labels 33068099731209101220513600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_07_rows b120_07_labels]
    decide +kernel

def b120_08_rows : List Row := [(row3 25 34 43), (row3 25 34 44), (row3 25 34 45), (row3 25 34 46), (row3 25 34 47), (row3 25 34 48), (row3 25 34 49), (row3 25 34 50), (row3 25 34 51), (row3 25 34 52), (row3 25 34 53), (row3 25 34 54), (row3 25 34 55), (row3 25 34 56), (row3 25 34 57), (row3 25 34 58)]

def b120_08_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 231 231), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_08_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_08_rows b120_08_labels 1620447137303983900380000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_08_rows b120_08_labels]
    decide +kernel

def b120_09_rows : List Row := [(row3 25 34 59), (row3 25 34 60), (row3 25 34 61), (row3 25 34 62), (row3 25 34 63), (row3 25 35 36), (row3 25 35 37), (row3 25 35 38), (row3 25 35 39), (row3 25 35 40), (row3 25 35 41), (row3 25 35 42), (row3 25 35 43), (row3 25 35 44), (row3 25 35 45), (row3 25 35 46)]

def b120_09_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 246 246), (row3 462 247 247), (row3 235 232 235), (row3 462 246 246), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_09_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_09_rows b120_09_labels 664800586711858042002000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_09_rows b120_09_labels]
    decide +kernel

def b120_10_rows : List Row := [(row3 25 35 47), (row3 25 35 48), (row3 25 35 49), (row3 25 35 50), (row3 25 35 51), (row3 25 35 52), (row3 25 35 53), (row3 25 35 54), (row3 25 35 55), (row3 25 35 56), (row3 25 35 57), (row3 25 35 58), (row3 25 35 59), (row3 25 35 60), (row3 25 35 61), (row3 25 35 62)]

def b120_10_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 245 245), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_10_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_10_rows b120_10_labels 25432854457414028062500 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_10_rows b120_10_labels]
    decide +kernel

def b120_11_rows : List Row := [(row3 25 35 63), (row3 25 36 37), (row3 25 36 38), (row3 25 36 39), (row3 25 36 40), (row3 25 36 41), (row3 25 36 42), (row3 25 36 43), (row3 25 36 44), (row3 25 36 45), (row3 25 36 46), (row3 25 36 47), (row3 25 36 48), (row3 25 36 49), (row3 25 36 50), (row3 25 36 51)]

def b120_11_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_11_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_11_rows b120_11_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_11_rows b120_11_labels]
    decide +kernel

def b120_12_rows : List Row := [(row3 25 36 52), (row3 25 36 53), (row3 25 36 54), (row3 25 36 55), (row3 25 36 56), (row3 25 36 57), (row3 25 36 58), (row3 25 36 59), (row3 25 36 60), (row3 25 36 61), (row3 25 36 62), (row3 25 36 63), (row3 25 37 38), (row3 25 37 39), (row3 25 37 40), (row3 25 37 41)]

def b120_12_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 243 243), (row3 462 462 462)]

theorem b120_12_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_12_rows b120_12_labels 7660100356903237725000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_12_rows b120_12_labels]
    decide +kernel

def b120_13_rows : List Row := [(row3 25 37 42), (row3 25 37 43), (row3 25 37 44), (row3 25 37 45), (row3 25 37 46), (row3 25 37 47), (row3 25 37 48), (row3 25 37 49), (row3 25 37 50), (row3 25 37 51), (row3 25 37 52), (row3 25 37 53), (row3 25 37 54), (row3 25 37 55), (row3 25 37 56), (row3 25 37 57)]

def b120_13_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_13_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_13_rows b120_13_labels 0 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_13_rows b120_13_labels]
    decide +kernel

def b120_14_rows : List Row := [(row3 25 37 58), (row3 25 37 59), (row3 25 37 60), (row3 25 37 61), (row3 25 37 62), (row3 25 37 63), (row3 25 38 39), (row3 25 38 40), (row3 25 38 41), (row3 25 38 42), (row3 25 38 43), (row3 25 38 44), (row3 25 38 45), (row3 25 38 46), (row3 25 38 47), (row3 25 38 48)]

def b120_14_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 234 234 234), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462)]

theorem b120_14_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_14_rows b120_14_labels 324375074249884818300000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_14_rows b120_14_labels]
    decide +kernel

def b120_15_rows : List Row := [(row3 25 38 49), (row3 25 38 50), (row3 25 38 51), (row3 25 38 52), (row3 25 38 53), (row3 25 38 54), (row3 25 38 55), (row3 25 38 56), (row3 25 38 57), (row3 25 38 58), (row3 25 38 59), (row3 25 38 60), (row3 25 38 61), (row3 25 38 62), (row3 25 38 63), (row3 25 39 40)]

def b120_15_labels : List Row := [(row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 462 462 462), (row3 278 282 282)]

theorem b120_15_checked : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 b120_15_rows b120_15_labels 10280012687121969548778600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
      QuarticIntegerWeightedTotalsLookups.covariance64 QuarticIntegerWeightedTotalsLookups.upper64
      QuarticIntegerWeightedTotalsLookups.covariance64_eq QuarticIntegerWeightedTotalsLookups.upper64_eq
      b120_15_rows b120_15_labels]
    decide +kernel

theorem checked120 : Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64
    upperNumerators64 QuarticIntegerComputationalData.rows64_120 QuarticIntegerComputationalData.ids64_120 11860358726361751811260665960 := by
  change Block 4 4 QuarticIntegerCovarianceData.covarianceNumerators64 upperNumerators64
    ((((b120_00_rows ++ b120_01_rows) ++ (b120_02_rows ++ b120_03_rows)) ++ ((b120_04_rows ++ b120_05_rows) ++ (b120_06_rows ++ b120_07_rows))) ++ (((b120_08_rows ++ b120_09_rows) ++ (b120_10_rows ++ b120_11_rows)) ++ ((b120_12_rows ++ b120_13_rows) ++ (b120_14_rows ++ b120_15_rows))))
    ((((b120_00_labels ++ b120_01_labels) ++ (b120_02_labels ++ b120_03_labels)) ++ ((b120_04_labels ++ b120_05_labels) ++ (b120_06_labels ++ b120_07_labels))) ++ (((b120_08_labels ++ b120_09_labels) ++ (b120_10_labels ++ b120_11_labels)) ++ ((b120_12_labels ++ b120_13_labels) ++ (b120_14_labels ++ b120_15_labels)))) 11860358726361751811260665960
  exact ((((b120_00_checked.append (c := 378549620640176184475727100) b120_01_checked (by decide +kernel)).append (c := 2327125548061374965573214300) (b120_02_checked.append (c := 1948575927421198781097487200) b120_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 11847435997921549797685417860) ((b120_04_checked.append (c := 8145105753748544388842844960) b120_05_checked (by decide +kernel)).append (c := 9520310449860174832112203560) (b120_06_checked.append (c := 1375204696111630443269358600) b120_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 11860358726361751811260665960) (((b120_08_checked.append (c := 2285247724015841942382000) b120_09_checked (by decide +kernel)).append (c := 2310680578473255970444500) (b120_10_checked.append (c := 25432854457414028062500) b120_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 12922728440202013575248100) ((b120_12_checked.append (c := 7660100356903237725000) b120_13_checked (by decide +kernel)).append (c := 10612047861728757604803600) (b120_14_checked.append (c := 10604387761371854367078600) b120_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals64
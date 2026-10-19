import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerData32
import Dressed.QuarticIntegerCovarianceData
import Dressed.QuarticIntegerComputationalData32.Block012
import Dressed.QuarticIntegerComputationalData32.Block013
import Dressed.QuarticIntegerComputationalData32.Block014
import Dressed.QuarticIntegerComputationalData32.Block015
import Dressed.QuarticIntegerComputationalData32.Block016
import Dressed.QuarticIntegerComputationalData32.Block017


/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b012_00_rows : List Row := [(row3 10 17 30), (row3 10 17 31), (row3 10 18 19), (row3 10 18 20), (row3 10 18 21), (row3 10 18 22), (row3 10 18 23), (row3 10 18 24), (row3 10 18 25), (row3 10 18 26), (row3 10 18 27), (row3 10 18 28), (row3 10 18 29), (row3 10 18 30), (row3 10 18 31), (row3 10 19 20)]

def b012_00_labels : List Row := [(row3 508 277 277), (row3 508 508 508), (row3 508 265 265), (row3 508 508 508), (row3 508 508 508), (row3 508 271 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 268 268), (row3 508 508 508), (row3 508 508 508)]

theorem b012_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_00_rows b012_00_labels 3538554148279785113523000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_00_rows b012_00_labels]
    decide +kernel

def b012_01_rows : List Row := [(row3 10 19 21), (row3 10 19 22), (row3 10 19 23), (row3 10 19 24), (row3 10 19 25), (row3 10 19 26), (row3 10 19 27), (row3 10 19 28), (row3 10 19 29), (row3 10 19 30), (row3 10 19 31), (row3 10 20 21), (row3 10 20 22), (row3 10 20 23), (row3 10 20 24), (row3 10 20 25)]

def b012_01_labels : List Row := [(row3 508 508 508), (row3 508 276 276), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 277 277), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 271 271), (row3 508 276 276)]

theorem b012_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_01_rows b012_01_labels 994907257165466826521400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_01_rows b012_01_labels]
    decide +kernel

def b012_02_rows : List Row := [(row3 10 20 26), (row3 10 20 27), (row3 10 20 28), (row3 10 20 29), (row3 10 20 30), (row3 10 20 31), (row3 10 21 22), (row3 10 21 23), (row3 10 21 24), (row3 10 21 25), (row3 10 21 26), (row3 10 21 27), (row3 10 21 28), (row3 10 21 29), (row3 10 21 30), (row3 10 21 31)]

def b012_02_labels : List Row := [(row3 508 508 508), (row3 508 276 276), (row3 508 303 303), (row3 268 268 262), (row3 508 280 280), (row3 268 268 262), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 265 265 265), (row3 508 508 508)]

theorem b012_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_02_rows b012_02_labels 31488996193662933199434960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_02_rows b012_02_labels]
    decide +kernel

def b012_03_rows : List Row := [(row3 10 22 23), (row3 10 22 24), (row3 10 22 25), (row3 10 22 26), (row3 10 22 27), (row3 10 22 28), (row3 10 22 29), (row3 10 22 30), (row3 10 22 31), (row3 10 23 24), (row3 10 23 25), (row3 10 23 26), (row3 10 23 27), (row3 10 23 28), (row3 10 23 29), (row3 10 23 30)]

def b012_03_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 297 300 300), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 265 265 265)]

theorem b012_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_03_rows b012_03_labels 4528819876125234678956280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_03_rows b012_03_labels]
    decide +kernel

def b012_04_rows : List Row := [(row3 10 23 31), (row3 10 24 25), (row3 10 24 26), (row3 10 24 27), (row3 10 24 28), (row3 10 24 29), (row3 10 24 30), (row3 10 24 31), (row3 10 25 26), (row3 10 25 27), (row3 10 25 28), (row3 10 25 29), (row3 10 25 30), (row3 10 25 31), (row3 10 26 27), (row3 10 26 28)]

def b012_04_labels : List Row := [(row3 290 508 290), (row3 508 265 265), (row3 508 508 508), (row3 508 265 265), (row3 508 190 190), (row3 307 310 322), (row3 258 253 253), (row3 307 310 322), (row3 508 508 508), (row3 508 279 279), (row3 508 326 326), (row3 211 258 206), (row3 310 313 313), (row3 262 258 255), (row3 508 508 508), (row3 508 508 508)]

theorem b012_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_04_rows b012_04_labels 1146227101806976669260954720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_04_rows b012_04_labels]
    decide +kernel

def b012_05_rows : List Row := [(row3 10 26 29), (row3 10 26 30), (row3 10 26 31), (row3 10 27 28), (row3 10 27 29), (row3 10 27 30), (row3 10 27 31), (row3 10 28 29), (row3 10 28 30), (row3 10 28 31), (row3 10 29 30), (row3 10 29 31), (row3 10 30 31), (row3 11 12 13), (row3 11 12 14), (row3 11 12 15)]

def b012_05_labels : List Row := [(row3 307 508 307), (row3 190 170 170), (row3 307 508 307), (row3 508 326 326), (row3 262 258 255), (row3 310 313 313), (row3 211 258 206), (row3 210 163 148), (row3 310 340 340), (row3 210 163 148), (row3 364 173 118), (row3 319 332 332), (row3 364 118 173), (row3 361 384 375), (row3 151 152 155), (row3 102 69 467)]

theorem b012_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_05_rows b012_05_labels 254133693221524066958847898680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_05_rows b012_05_labels]
    decide +kernel

def b012_06_rows : List Row := [(row3 11 12 16), (row3 11 12 17), (row3 11 12 18), (row3 11 12 19), (row3 11 12 20), (row3 11 12 21), (row3 11 12 22), (row3 11 12 23), (row3 11 12 24), (row3 11 12 25), (row3 11 12 26), (row3 11 12 27), (row3 11 12 28), (row3 11 12 29), (row3 11 12 30), (row3 11 12 31)]

def b012_06_labels : List Row := [(row3 362 383 372), (row3 219 208 219), (row3 334 334 331), (row3 172 175 178), (row3 237 230 236), (row3 299 299 297), (row3 268 268 262), (row3 312 312 310), (row3 295 295 292), (row3 270 267 267), (row3 276 276 508), (row3 266 267 264), (row3 199 202 224), (row3 298 298 297), (row3 260 265 260), (row3 311 311 310)]

theorem b012_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_06_rows b012_06_labels 10924514797190354233162701138 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_06_rows b012_06_labels]
    decide +kernel

def b012_07_rows : List Row := [(row3 11 13 14), (row3 11 13 15), (row3 11 13 16), (row3 11 13 17), (row3 11 13 18), (row3 11 13 19), (row3 11 13 20), (row3 11 13 21), (row3 11 13 22), (row3 11 13 23), (row3 11 13 24), (row3 11 13 25), (row3 11 13 26), (row3 11 13 27), (row3 11 13 28), (row3 11 13 29)]

def b012_07_labels : List Row := [(row3 339 335 339), (row3 145 403 111), (row3 251 255 252), (row3 318 508 318), (row3 252 256 252), (row3 325 321 325), (row3 281 508 281), (row3 268 508 268), (row3 280 508 280), (row3 265 265 265), (row3 271 508 271), (row3 277 508 277), (row3 508 508 508), (row3 278 508 278), (row3 306 508 306), (row3 268 508 268)]

theorem b012_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_07_rows b012_07_labels 9949405279779086363406090000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_07_rows b012_07_labels]
    decide +kernel

def b012_08_rows : List Row := [(row3 11 13 30), (row3 11 13 31), (row3 11 14 15), (row3 11 14 16), (row3 11 14 17), (row3 11 14 18), (row3 11 14 19), (row3 11 14 20), (row3 11 14 21), (row3 11 14 22), (row3 11 14 23), (row3 11 14 24), (row3 11 14 25), (row3 11 14 26), (row3 11 14 27), (row3 11 14 28)]

def b012_08_labels : List Row := [(row3 280 508 280), (row3 260 265 260), (row3 391 68 462), (row3 324 324 321), (row3 258 508 258), (row3 323 323 321), (row3 188 197 196), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 299 299 297), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 268 508 268)]

theorem b012_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_08_rows b012_08_labels 167285263291190865794859386448 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_08_rows b012_08_labels]
    decide +kernel

def b012_09_rows : List Row := [(row3 11 14 29), (row3 11 14 30), (row3 11 14 31), (row3 11 15 16), (row3 11 15 17), (row3 11 15 18), (row3 11 15 19), (row3 11 15 20), (row3 11 15 21), (row3 11 15 22), (row3 11 15 23), (row3 11 15 24), (row3 11 15 25), (row3 11 15 26), (row3 11 15 27), (row3 11 15 28)]

def b012_09_labels : List Row := [(row3 508 508 508), (row3 268 508 268), (row3 298 298 297), (row3 204 112 404), (row3 245 14 141), (row3 205 113 404), (row3 124 460 67), (row3 247 13 165), (row3 508 508 508), (row3 246 13 164), (row3 347 117 378), (row3 271 508 271), (row3 276 508 276), (row3 508 508 508), (row3 249 11 215), (row3 316 508 316)]

theorem b012_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_09_rows b012_09_labels 187417988164374702137940602820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_09_rows b012_09_labels]
    decide +kernel

def b012_10_rows : List Row := [(row3 11 15 29), (row3 11 15 30), (row3 11 15 31), (row3 11 16 17), (row3 11 16 18), (row3 11 16 19), (row3 11 16 20), (row3 11 16 21), (row3 11 16 22), (row3 11 16 23), (row3 11 16 24), (row3 11 16 25), (row3 11 16 26), (row3 11 16 27), (row3 11 16 28), (row3 11 16 29)]

def b012_10_labels : List Row := [(row3 268 508 268), (row3 306 508 306), (row3 199 202 224), (row3 289 508 289), (row3 259 261 259), (row3 314 308 314), (row3 215 11 249), (row3 271 508 271), (row3 278 508 278), (row3 264 267 266), (row3 271 508 271), (row3 276 508 276), (row3 508 508 508), (row3 278 508 278), (row3 249 11 215), (row3 271 508 271)]

theorem b012_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_10_rows b012_10_labels 3921650350081794089278892220 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_10_rows b012_10_labels]
    decide +kernel

def b012_11_rows : List Row := [(row3 11 16 30), (row3 11 16 31), (row3 11 17 18), (row3 11 17 19), (row3 11 17 20), (row3 11 17 21), (row3 11 17 22), (row3 11 17 23), (row3 11 17 24), (row3 11 17 25), (row3 11 17 26), (row3 11 17 27), (row3 11 17 28), (row3 11 17 29), (row3 11 17 30), (row3 11 17 31)]

def b012_11_labels : List Row := [(row3 278 508 278), (row3 266 267 264), (row3 279 279 508), (row3 265 265 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 277 277 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 276 276 508)]

theorem b012_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_11_rows b012_11_labels 3419960329679659932301200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_11_rows b012_11_labels]
    decide +kernel

def b012_12_rows : List Row := [(row3 11 18 19), (row3 11 18 20), (row3 11 18 21), (row3 11 18 22), (row3 11 18 23), (row3 11 18 24), (row3 11 18 25), (row3 11 18 26), (row3 11 18 27), (row3 11 18 28), (row3 11 18 29), (row3 11 18 30), (row3 11 18 31), (row3 11 19 20), (row3 11 19 21), (row3 11 19 22)]

def b012_12_labels : List Row := [(row3 309 308 309), (row3 277 508 277), (row3 508 508 508), (row3 276 508 276), (row3 267 267 270), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 276 508 276), (row3 276 508 276), (row3 508 508 508), (row3 277 508 277), (row3 270 267 267), (row3 269 508 269), (row3 508 508 508), (row3 271 508 271)]

theorem b012_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_12_rows b012_12_labels 80398517871438949888096920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_12_rows b012_12_labels]
    decide +kernel

def b012_13_rows : List Row := [(row3 11 19 23), (row3 11 19 24), (row3 11 19 25), (row3 11 19 26), (row3 11 19 27), (row3 11 19 28), (row3 11 19 29), (row3 11 19 30), (row3 11 19 31), (row3 11 20 21), (row3 11 20 22), (row3 11 20 23), (row3 11 20 24), (row3 11 20 25), (row3 11 20 26), (row3 11 20 27)]

def b012_13_labels : List Row := [(row3 296 296 286), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 271 508 271), (row3 508 508 508), (row3 271 508 271), (row3 295 295 292), (row3 285 285 508), (row3 272 272 508), (row3 241 282 9), (row3 296 296 286), (row3 267 267 270), (row3 277 277 508), (row3 264 267 266)]

theorem b012_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_13_rows b012_13_labels 239209294818592530764121480 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_13_rows b012_13_labels]
    decide +kernel

def b012_14_rows : List Row := [(row3 11 20 28), (row3 11 20 29), (row3 11 20 30), (row3 11 20 31), (row3 11 21 22), (row3 11 21 23), (row3 11 21 24), (row3 11 21 25), (row3 11 21 26), (row3 11 21 27), (row3 11 21 28), (row3 11 21 29), (row3 11 21 30), (row3 11 21 31), (row3 11 22 23), (row3 11 22 24)]

def b012_14_labels : List Row := [(row3 347 117 378), (row3 299 299 297), (row3 265 265 265), (row3 312 312 310), (row3 508 508 508), (row3 272 272 508), (row3 271 508 271), (row3 276 508 276), (row3 508 508 508), (row3 278 508 278), (row3 246 13 164), (row3 268 508 268), (row3 280 508 280), (row3 268 268 262), (row3 285 285 508), (row3 508 508 508)]

theorem b012_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_14_rows b012_14_labels 5095786243611527907876290730 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_14_rows b012_14_labels]
    decide +kernel

def b012_15_rows : List Row := [(row3 11 22 25), (row3 11 22 26), (row3 11 22 27), (row3 11 22 28), (row3 11 22 29), (row3 11 22 30), (row3 11 22 31), (row3 11 23 24), (row3 11 23 25), (row3 11 23 26), (row3 11 23 27), (row3 11 23 28), (row3 11 23 29), (row3 11 23 30), (row3 11 23 31), (row3 11 24 25)]

def b012_15_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 299 299 297), (row3 269 508 269), (row3 277 508 277), (row3 272 508 272), (row3 215 11 249), (row3 247 13 165), (row3 268 508 268), (row3 281 508 281), (row3 237 230 236), (row3 309 308 309)]

theorem b012_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b012_15_rows b012_15_labels 1434794826593902399127877552 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b012_15_rows b012_15_labels]
    decide +kernel

theorem checked012 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_012 QuarticIntegerComputationalData.ids32_012 641672902326648221114163649548 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b012_00_rows ++ b012_01_rows) ++ (b012_02_rows ++ b012_03_rows)) ++ ((b012_04_rows ++ b012_05_rows) ++ (b012_06_rows ++ b012_07_rows))) ++ (((b012_08_rows ++ b012_09_rows) ++ (b012_10_rows ++ b012_11_rows)) ++ ((b012_12_rows ++ b012_13_rows) ++ (b012_14_rows ++ b012_15_rows))))
    ((((b012_00_labels ++ b012_01_labels) ++ (b012_02_labels ++ b012_03_labels)) ++ ((b012_04_labels ++ b012_05_labels) ++ (b012_06_labels ++ b012_07_labels))) ++ (((b012_08_labels ++ b012_09_labels) ++ (b012_10_labels ++ b012_11_labels)) ++ ((b012_12_labels ++ b012_13_labels) ++ (b012_14_labels ++ b012_15_labels)))) 641672902326648221114163649548
  exact ((((b012_00_checked.append (c := 4533461405445251940044400) b012_01_checked (by decide +kernel)).append (c := 40551277475233419818435640) (b012_02_checked.append (c := 36017816069788167878391240) b012_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 276194391677775717644496080178) ((b012_04_checked.append (c := 255279920323331043628108853400) b012_05_checked (by decide +kernel)).append (c := 276153840400300484224677644538) (b012_06_checked.append (c := 20873920076969440596568791138) b012_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 641672902326648221114163649548) (((b012_08_checked.append (c := 354703251455565567932799989268) b012_09_checked (by decide +kernel)).append (c := 358628321765977041682011182688) (b012_10_checked.append (c := 3925070310411473749211193420) b012_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 365478510648872503469667569370) ((b012_12_checked.append (c := 319607812690031480652218400) b012_13_checked (by decide +kernel)).append (c := 6850188882895461787656386682) (b012_14_checked.append (c := 6530581070205430307004168282) b012_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b013_00_rows : List Row := [(row3 11 24 26), (row3 11 24 27), (row3 11 24 28), (row3 11 24 29), (row3 11 24 30), (row3 11 24 31), (row3 11 25 26), (row3 11 25 27), (row3 11 25 28), (row3 11 25 29), (row3 11 25 30), (row3 11 25 31), (row3 11 26 27), (row3 11 26 28), (row3 11 26 29), (row3 11 26 30)]

def b013_00_labels : List Row := [(row3 265 265 508), (row3 314 308 314), (row3 124 460 67), (row3 188 197 196), (row3 325 321 325), (row3 172 175 178), (row3 279 279 508), (row3 259 261 259), (row3 205 113 404), (row3 323 323 321), (row3 252 256 252), (row3 334 334 331), (row3 289 508 289), (row3 245 14 141), (row3 258 508 258), (row3 318 508 318)]

theorem b013_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_00_rows b013_00_labels 168997813790850495504674736522 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_00_rows b013_00_labels]
    decide +kernel

def b013_01_rows : List Row := [(row3 11 26 31), (row3 11 27 28), (row3 11 27 29), (row3 11 27 30), (row3 11 27 31), (row3 11 28 29), (row3 11 28 30), (row3 11 28 31), (row3 11 29 30), (row3 11 29 31), (row3 11 30 31), (row3 12 13 14), (row3 12 13 15), (row3 12 13 16), (row3 12 13 17), (row3 12 13 18)]

def b013_01_labels : List Row := [(row3 219 208 219), (row3 204 112 404), (row3 324 324 321), (row3 251 255 252), (row3 362 383 372), (row3 391 68 462), (row3 145 403 111), (row3 102 69 467), (row3 339 335 339), (row3 151 152 155), (row3 361 384 375), (row3 369 453 100), (row3 82 94 94), (row3 83 96 95), (row3 368 451 101), (row3 174 119 364)]

theorem b013_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_01_rows b013_01_labels 770821793522546244859301854362 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_01_rows b013_01_labels]
    decide +kernel

def b013_02_rows : List Row := [(row3 12 13 19), (row3 12 13 20), (row3 12 13 21), (row3 12 13 22), (row3 12 13 23), (row3 12 13 24), (row3 12 13 25), (row3 12 13 26), (row3 12 13 27), (row3 12 13 28), (row3 12 13 29), (row3 12 13 30), (row3 12 13 31), (row3 12 14 15), (row3 12 14 16), (row3 12 14 17)]

def b013_02_labels : List Row := [(row3 381 374 360), (row3 356 354 349), (row3 203 123 351), (row3 293 11 216), (row3 201 201 225), (row3 239 239 243), (row3 282 9 241), (row3 508 508 508), (row3 285 508 285), (row3 287 508 287), (row3 272 508 272), (row3 275 508 275), (row3 272 508 272), (row3 369 100 453), (row3 380 359 373), (row3 207 220 221)]

theorem b013_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_02_rows b013_02_labels 64721955372700415997735042000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_02_rows b013_02_labels]
    decide +kernel

def b013_03_rows : List Row := [(row3 12 14 18), (row3 12 14 19), (row3 12 14 20), (row3 12 14 21), (row3 12 14 22), (row3 12 14 23), (row3 12 14 24), (row3 12 14 25), (row3 12 14 26), (row3 12 14 27), (row3 12 14 28), (row3 12 14 29), (row3 12 14 30), (row3 12 14 31), (row3 12 15 16), (row3 12 15 17)]

def b013_03_labels : List Row := [(row3 312 312 310), (row3 207 220 221), (row3 231 238 238), (row3 301 301 297), (row3 268 508 268), (row3 301 301 297), (row3 284 284 283), (row3 272 508 272), (row3 508 508 508), (row3 272 508 272), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 83 96 95), (row3 381 374 360)]

theorem b013_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_03_rows b013_03_labels 121304379207844413393041364552 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_03_rows b013_03_labels]
    decide +kernel

def b013_04_rows : List Row := [(row3 12 15 18), (row3 12 15 19), (row3 12 15 20), (row3 12 15 21), (row3 12 15 22), (row3 12 15 23), (row3 12 15 24), (row3 12 15 25), (row3 12 15 26), (row3 12 15 27), (row3 12 15 28), (row3 12 15 29), (row3 12 15 30), (row3 12 15 31), (row3 12 16 17), (row3 12 16 18)]

def b013_04_labels : List Row := [(row3 174 119 364), (row3 368 451 101), (row3 356 354 349), (row3 201 201 225), (row3 293 11 216), (row3 203 123 351), (row3 239 239 243), (row3 285 508 285), (row3 508 508 508), (row3 282 9 241), (row3 287 508 287), (row3 272 508 272), (row3 275 508 275), (row3 272 508 272), (row3 355 452 99), (row3 183 120 365)]

theorem b013_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_04_rows b013_04_labels 110117534386588011976401098460 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_04_rows b013_04_labels]
    decide +kernel

def b013_05_rows : List Row := [(row3 12 16 19), (row3 12 16 20), (row3 12 16 21), (row3 12 16 22), (row3 12 16 23), (row3 12 16 24), (row3 12 16 25), (row3 12 16 26), (row3 12 16 27), (row3 12 16 28), (row3 12 16 29), (row3 12 16 30), (row3 12 16 31), (row3 12 17 18), (row3 12 17 19), (row3 12 17 20)]

def b013_05_labels : List Row := [(row3 355 452 99), (row3 98 459 98), (row3 228 121 366), (row3 248 12 184), (row3 228 121 366), (row3 242 125 352), (row3 249 11 215), (row3 508 508 508), (row3 249 11 215), (row3 250 10 226), (row3 273 508 273), (row3 274 508 274), (row3 273 508 273), (row3 311 311 310), (row3 208 221 221), (row3 212 221 212)]

theorem b013_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_05_rows b013_05_labels 179862525328511256034913203632 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_05_rows b013_05_labels]
    decide +kernel

def b013_06_rows : List Row := [(row3 12 17 21), (row3 12 17 22), (row3 12 17 23), (row3 12 17 24), (row3 12 17 25), (row3 12 17 26), (row3 12 17 27), (row3 12 17 28), (row3 12 17 29), (row3 12 17 30), (row3 12 17 31), (row3 12 18 19), (row3 12 18 20), (row3 12 18 21), (row3 12 18 22), (row3 12 18 23)]

def b013_06_labels : List Row := [(row3 315 315 297), (row3 268 508 268), (row3 302 302 297), (row3 295 295 292), (row3 269 508 269), (row3 508 508 508), (row3 272 508 272), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 311 310 311), (row3 312 310 312), (row3 260 260 265), (row3 278 508 278), (row3 260 260 265)]

theorem b013_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_06_rows b013_06_labels 187682192294011248703377600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_06_rows b013_06_labels]
    decide +kernel

def b013_07_rows : List Row := [(row3 12 18 24), (row3 12 18 25), (row3 12 18 26), (row3 12 18 27), (row3 12 18 28), (row3 12 18 29), (row3 12 18 30), (row3 12 18 31), (row3 12 19 20), (row3 12 19 21), (row3 12 19 22), (row3 12 19 23), (row3 12 19 24), (row3 12 19 25), (row3 12 19 26), (row3 12 19 27)]

def b013_07_labels : List Row := [(row3 271 268 268), (row3 277 508 277), (row3 508 508 508), (row3 277 508 277), (row3 274 508 274), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 212 221 212), (row3 302 302 297), (row3 268 508 268), (row3 315 315 297), (row3 295 295 292), (row3 272 508 272), (row3 508 508 508), (row3 269 508 269)]

theorem b013_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_07_rows b013_07_labels 209954669560686150605182152 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_07_rows b013_07_labels]
    decide +kernel

def b013_08_rows : List Row := [(row3 12 19 28), (row3 12 19 29), (row3 12 19 30), (row3 12 19 31), (row3 12 20 21), (row3 12 20 22), (row3 12 20 23), (row3 12 20 24), (row3 12 20 25), (row3 12 20 26), (row3 12 20 27), (row3 12 20 28), (row3 12 20 29), (row3 12 20 30), (row3 12 20 31), (row3 12 21 22)]

def b013_08_labels : List Row := [(row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 349 356 354), (row3 238 231 238), (row3 349 356 354), (row3 103 449 348), (row3 236 230 237), (row3 300 300 297), (row3 236 230 237), (row3 242 125 352), (row3 295 295 292), (row3 271 268 268), (row3 295 295 292), (row3 305 508 305)]

theorem b013_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_08_rows b013_08_labels 43898404452482748437620562916 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_08_rows b013_08_labels]
    decide +kernel

def b013_09_rows : List Row := [(row3 12 21 23), (row3 12 21 24), (row3 12 21 25), (row3 12 21 26), (row3 12 21 27), (row3 12 21 28), (row3 12 21 29), (row3 12 21 30), (row3 12 21 31), (row3 12 22 23), (row3 12 22 24), (row3 12 22 25), (row3 12 22 26), (row3 12 22 27), (row3 12 22 28), (row3 12 22 29)]

def b013_09_labels : List Row := [(row3 259 263 263), (row3 236 230 237), (row3 165 13 247), (row3 268 508 268), (row3 281 508 281), (row3 249 11 215), (row3 269 508 269), (row3 277 508 277), (row3 272 508 272), (row3 305 305 508), (row3 300 300 297), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508)]

theorem b013_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_09_rows b013_09_labels 1390514126687012351032169352 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_09_rows b013_09_labels]
    decide +kernel

def b013_10_rows : List Row := [(row3 12 22 30), (row3 12 22 31), (row3 12 23 24), (row3 12 23 25), (row3 12 23 26), (row3 12 23 27), (row3 12 23 28), (row3 12 23 29), (row3 12 23 30), (row3 12 23 31), (row3 12 24 25), (row3 12 24 26), (row3 12 24 27), (row3 12 24 28), (row3 12 24 29), (row3 12 24 30)]

def b013_10_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 236 230 237), (row3 281 508 281), (row3 268 508 268), (row3 165 13 247), (row3 249 11 215), (row3 272 508 272), (row3 277 508 277), (row3 269 508 269), (row3 349 354 356), (row3 238 238 231), (row3 349 354 356), (row3 98 459 98), (row3 212 221 212), (row3 312 310 312)]

theorem b013_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_10_rows b013_10_labels 112262654876298788303361485316 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_10_rows b013_10_labels]
    decide +kernel

def b013_11_rows : List Row := [(row3 12 24 31), (row3 12 25 26), (row3 12 25 27), (row3 12 25 28), (row3 12 25 29), (row3 12 25 30), (row3 12 25 31), (row3 12 26 27), (row3 12 26 28), (row3 12 26 29), (row3 12 26 30), (row3 12 26 31), (row3 12 27 28), (row3 12 27 29), (row3 12 27 30), (row3 12 27 31)]

def b013_11_labels : List Row := [(row3 212 221 212), (row3 305 305 508), (row3 259 263 263), (row3 228 121 366), (row3 315 315 297), (row3 260 260 265), (row3 302 302 297), (row3 305 508 305), (row3 248 12 184), (row3 268 508 268), (row3 278 508 278), (row3 268 508 268), (row3 228 121 366), (row3 302 302 297), (row3 260 260 265), (row3 315 315 297)]

theorem b013_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_11_rows b013_11_labels 6668555442891376846500866772 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_11_rows b013_11_labels]
    decide +kernel

def b013_12_rows : List Row := [(row3 12 28 29), (row3 12 28 30), (row3 12 28 31), (row3 12 29 30), (row3 12 29 31), (row3 12 30 31), (row3 13 14 15), (row3 13 14 16), (row3 13 14 17), (row3 13 14 18), (row3 13 14 19), (row3 13 14 20), (row3 13 14 21), (row3 13 14 22), (row3 13 14 23), (row3 13 14 24)]

def b013_12_labels : List Row := [(row3 355 99 452), (row3 183 365 120), (row3 355 99 452), (row3 311 310 311), (row3 208 221 221), (row3 311 311 310), (row3 210 181 210), (row3 268 209 210), (row3 508 367 367), (row3 508 210 210), (row3 508 317 317), (row3 508 305 305), (row3 271 233 234), (row3 508 304 304), (row3 508 508 508), (row3 508 508 508)]

theorem b013_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_12_rows b013_12_labels 109119201811911328387716959400 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_12_rows b013_12_labels]
    decide +kernel

def b013_13_rows : List Row := [(row3 13 14 25), (row3 13 14 26), (row3 13 14 27), (row3 13 14 28), (row3 13 14 29), (row3 13 14 30), (row3 13 14 31), (row3 13 15 16), (row3 13 15 17), (row3 13 15 18), (row3 13 15 19), (row3 13 15 20), (row3 13 15 21), (row3 13 15 22), (row3 13 15 23), (row3 13 15 24)]

def b013_13_labels : List Row := [(row3 508 285 285), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 310 310 319), (row3 262 211 207), (row3 307 307 319), (row3 211 262 207), (row3 263 263 259), (row3 508 290 290), (row3 268 268 262), (row3 290 508 290), (row3 508 508 508)]

theorem b013_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_13_rows b013_13_labels 716430418122881778725914320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_13_rows b013_13_labels]
    decide +kernel

def b013_14_rows : List Row := [(row3 13 15 25), (row3 13 15 26), (row3 13 15 27), (row3 13 15 28), (row3 13 15 29), (row3 13 15 30), (row3 13 15 31), (row3 13 16 17), (row3 13 16 18), (row3 13 16 19), (row3 13 16 20), (row3 13 16 21), (row3 13 16 22), (row3 13 16 23), (row3 13 16 24), (row3 13 16 25)]

def b013_14_labels : List Row := [(row3 508 272 272), (row3 508 508 508), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 234 211 189), (row3 290 307 310), (row3 234 262 229), (row3 366 121 228), (row3 307 307 307), (row3 268 268 262), (row3 290 508 290), (row3 290 508 290), (row3 266 267 264)]

theorem b013_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_14_rows b013_14_labels 3826289789040167126840311920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_14_rows b013_14_labels]
    decide +kernel

def b013_15_rows : List Row := [(row3 13 16 26), (row3 13 16 27), (row3 13 16 28), (row3 13 16 29), (row3 13 16 30), (row3 13 16 31), (row3 13 17 18), (row3 13 17 19), (row3 13 17 20), (row3 13 17 21), (row3 13 17 22), (row3 13 17 23), (row3 13 17 24), (row3 13 17 25), (row3 13 17 26), (row3 13 17 27)]

def b013_15_labels : List Row := [(row3 508 508 508), (row3 271 508 271), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 211 211), (row3 508 316 316), (row3 297 315 315), (row3 235 211 235), (row3 508 303 303), (row3 508 508 508), (row3 271 508 271), (row3 286 296 296), (row3 508 508 508), (row3 508 508 508)]

theorem b013_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b013_15_rows b013_15_labels 1125394321365030898495372800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b013_15_rows b013_15_labels]
    decide +kernel

theorem checked013 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_013 QuarticIntegerComputationalData.ids32_013 1695231083709694869295669502076 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b013_00_rows ++ b013_01_rows) ++ (b013_02_rows ++ b013_03_rows)) ++ ((b013_04_rows ++ b013_05_rows) ++ (b013_06_rows ++ b013_07_rows))) ++ (((b013_08_rows ++ b013_09_rows) ++ (b013_10_rows ++ b013_11_rows)) ++ ((b013_12_rows ++ b013_13_rows) ++ (b013_14_rows ++ b013_15_rows))))
    ((((b013_00_labels ++ b013_01_labels) ++ (b013_02_labels ++ b013_03_labels)) ++ ((b013_04_labels ++ b013_05_labels) ++ (b013_06_labels ++ b013_07_labels))) ++ (((b013_08_labels ++ b013_09_labels) ++ (b013_10_labels ++ b013_11_labels)) ++ ((b013_12_labels ++ b013_13_labels) ++ (b013_14_labels ++ b013_15_labels)))) 1695231083709694869295669502076
  exact ((((b013_00_checked.append (c := 939819607313396740363976590884) b013_01_checked (by decide +kernel)).append (c := 1125845941893941569754752997436) (b013_02_checked.append (c := 186026334580544829390776406552) b013_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 1416223638470895535165375859280) ((b013_04_checked.append (c := 289980059715099268011314302092) b013_05_checked (by decide +kernel)).append (c := 290377696576953965410622861844) (b013_06_checked.append (c := 397636861854697399308559752) b013_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 1695231083709694869295669502076) (((b013_08_checked.append (c := 45288918579169760788652732268) b013_09_checked (by decide +kernel)).append (c := 164220128898359925938515084356) (b013_10_checked.append (c := 118931210319190165149862352088) b013_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 279007445238799334130293642796) ((b013_12_checked.append (c := 109835632230034210166442873720) b013_13_checked (by decide +kernel)).append (c := 114787316340439408191778558440) (b013_14_checked.append (c := 4951684110405198025335684720) b013_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b014_00_rows : List Row := [(row3 13 17 28), (row3 13 17 29), (row3 13 17 30), (row3 13 17 31), (row3 13 18 19), (row3 13 18 20), (row3 13 18 21), (row3 13 18 22), (row3 13 18 23), (row3 13 18 24), (row3 13 18 25), (row3 13 18 26), (row3 13 18 27), (row3 13 18 28), (row3 13 18 29), (row3 13 18 30)]

def b014_00_labels : List Row := [(row3 508 508 508), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 262 262), (row3 265 260 260), (row3 290 307 290), (row3 508 268 268), (row3 508 508 508), (row3 508 508 508), (row3 270 267 267), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b014_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_00_rows b014_00_labels 17281747379018795161413960 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_00_rows b014_00_labels]
    decide +kernel

def b014_01_rows : List Row := [(row3 13 18 31), (row3 13 19 20), (row3 13 19 21), (row3 13 19 22), (row3 13 19 23), (row3 13 19 24), (row3 13 19 25), (row3 13 19 26), (row3 13 19 27), (row3 13 19 28), (row3 13 19 29), (row3 13 19 30), (row3 13 19 31), (row3 13 20 21), (row3 13 20 22), (row3 13 20 23)]

def b014_01_labels : List Row := [(row3 508 508 508), (row3 297 302 302), (row3 268 262 268), (row3 508 278 278), (row3 508 508 508), (row3 271 508 271), (row3 508 277 277), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 351 203 123), (row3 297 301 301), (row3 225 201 201)]

theorem b014_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_01_rows b014_01_labels 1776576942615905324099419320 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_01_rows b014_01_labels]
    decide +kernel

def b014_02_rows : List Row := [(row3 13 20 24), (row3 13 20 25), (row3 13 20 26), (row3 13 20 27), (row3 13 20 28), (row3 13 20 29), (row3 13 20 30), (row3 13 20 31), (row3 13 21 22), (row3 13 21 23), (row3 13 21 24), (row3 13 21 25), (row3 13 21 26), (row3 13 21 27), (row3 13 21 28), (row3 13 21 29)]

def b014_02_labels : List Row := [(row3 378 117 347), (row3 310 312 312), (row3 265 265 265), (row3 297 299 299), (row3 286 296 296), (row3 266 267 264), (row3 508 277 277), (row3 270 267 267), (row3 234 271 233), (row3 290 508 290), (row3 307 508 307), (row3 378 117 347), (row3 290 508 290), (row3 268 508 268), (row3 271 508 271), (row3 290 508 290)]

theorem b014_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_02_rows b014_02_labels 8880728845252811962095444000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_02_rows b014_02_labels]
    decide +kernel

def b014_03_rows : List Row := [(row3 13 21 30), (row3 13 21 31), (row3 13 22 23), (row3 13 22 24), (row3 13 22 25), (row3 13 22 26), (row3 13 22 27), (row3 13 22 28), (row3 13 22 29), (row3 13 22 30), (row3 13 22 31), (row3 13 23 24), (row3 13 23 25), (row3 13 23 26), (row3 13 23 27), (row3 13 23 28)]

def b014_03_labels : List Row := [(row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 297 299 299), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 265 265 265), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b014_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_03_rows b014_03_labels 8498620764699886810908720 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_03_rows b014_03_labels]
    decide +kernel

def b014_04_rows : List Row := [(row3 13 23 29), (row3 13 23 30), (row3 13 23 31), (row3 13 24 25), (row3 13 24 26), (row3 13 24 27), (row3 13 24 28), (row3 13 24 29), (row3 13 24 30), (row3 13 24 31), (row3 13 25 26), (row3 13 25 27), (row3 13 25 28), (row3 13 25 29), (row3 13 25 30), (row3 13 25 31)]

def b014_04_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 351 203 123), (row3 290 290 508), (row3 234 233 271), (row3 235 211 235), (row3 307 307 307), (row3 268 262 268), (row3 290 307 290), (row3 225 201 201), (row3 297 301 301), (row3 297 315 315), (row3 366 121 228), (row3 297 302 302), (row3 265 260 260)]

theorem b014_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_04_rows b014_04_labels 5401130707177330330657182600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_04_rows b014_04_labels]
    decide +kernel

def b014_05_rows : List Row := [(row3 13 26 27), (row3 13 26 28), (row3 13 26 29), (row3 13 26 30), (row3 13 26 31), (row3 13 27 28), (row3 13 27 29), (row3 13 27 30), (row3 13 27 31), (row3 13 28 29), (row3 13 28 30), (row3 13 28 31), (row3 13 29 30), (row3 13 29 31), (row3 13 30 31), (row3 14 15 16)]

def b014_05_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 508 508 508), (row3 508 508 508), (row3 508 303 303), (row3 268 268 262), (row3 508 278 278), (row3 508 268 268), (row3 234 211 189), (row3 508 316 316), (row3 508 211 211), (row3 234 229 262), (row3 290 310 307), (row3 508 262 262), (row3 209 268 210)]

theorem b014_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_05_rows b014_05_labels 1768246466275991393787892680 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_05_rows b014_05_labels]
    decide +kernel

def b014_06_rows : List Row := [(row3 14 15 17), (row3 14 15 18), (row3 14 15 19), (row3 14 15 20), (row3 14 15 21), (row3 14 15 22), (row3 14 15 23), (row3 14 15 24), (row3 14 15 25), (row3 14 15 26), (row3 14 15 27), (row3 14 15 28), (row3 14 15 29), (row3 14 15 30), (row3 14 15 31), (row3 14 16 17)]

def b014_06_labels : List Row := [(row3 317 508 317), (row3 210 508 210), (row3 367 508 367), (row3 305 508 305), (row3 508 508 508), (row3 304 508 304), (row3 233 271 234), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 285 508 285), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 304 508 304)]

theorem b014_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_06_rows b014_06_labels 6771631525118000674554231600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_06_rows b014_06_labels]
    decide +kernel

def b014_07_rows : List Row := [(row3 14 16 18), (row3 14 16 19), (row3 14 16 20), (row3 14 16 21), (row3 14 16 22), (row3 14 16 23), (row3 14 16 24), (row3 14 16 25), (row3 14 16 26), (row3 14 16 27), (row3 14 16 28), (row3 14 16 29), (row3 14 16 30), (row3 14 16 31), (row3 14 17 18), (row3 14 17 19)]

def b014_07_labels : List Row := [(row3 268 508 268), (row3 304 508 304), (row3 184 12 248), (row3 262 268 268), (row3 278 508 278), (row3 262 268 268), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 278 508 278), (row3 274 508 274), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b014_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_07_rows b014_07_labels 512002158829518294282809700 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_07_rows b014_07_labels]
    decide +kernel

def b014_08_rows : List Row := [(row3 14 17 20), (row3 14 17 21), (row3 14 17 22), (row3 14 17 23), (row3 14 17 24), (row3 14 17 25), (row3 14 17 26), (row3 14 17 27), (row3 14 17 28), (row3 14 17 29), (row3 14 17 30), (row3 14 17 31), (row3 14 18 19), (row3 14 18 20), (row3 14 18 21), (row3 14 18 22)]

def b014_08_labels : List Row := [(row3 268 508 268), (row3 303 303 508), (row3 508 508 508), (row3 278 278 508), (row3 508 508 508), (row3 271 508 271), (row3 276 276 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 278 508 278), (row3 268 268 508), (row3 508 508 508)]

theorem b014_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_08_rows b014_08_labels 31084808421524495809932000 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_08_rows b014_08_labels]
    decide +kernel

def b014_09_rows : List Row := [(row3 14 18 23), (row3 14 18 24), (row3 14 18 25), (row3 14 18 26), (row3 14 18 27), (row3 14 18 28), (row3 14 18 29), (row3 14 18 30), (row3 14 18 31), (row3 14 19 20), (row3 14 19 21), (row3 14 19 22), (row3 14 19 23), (row3 14 19 24), (row3 14 19 25), (row3 14 19 26)]

def b014_09_labels : List Row := [(row3 268 268 508), (row3 508 508 508), (row3 276 508 276), (row3 271 271 508), (row3 276 508 276), (row3 508 508 508), (row3 508 508 508), (row3 274 508 274), (row3 508 508 508), (row3 268 508 268), (row3 278 278 508), (row3 508 508 508), (row3 303 303 508), (row3 508 508 508), (row3 508 508 508), (row3 276 276 508)]

theorem b014_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_09_rows b014_09_labels 31881025947577644457885800 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_09_rows b014_09_labels]
    decide +kernel

def b014_10_rows : List Row := [(row3 14 19 27), (row3 14 19 28), (row3 14 19 29), (row3 14 19 30), (row3 14 19 31), (row3 14 20 21), (row3 14 20 22), (row3 14 20 23), (row3 14 20 24), (row3 14 20 25), (row3 14 20 26), (row3 14 20 27), (row3 14 20 28), (row3 14 20 29), (row3 14 20 30), (row3 14 20 31)]

def b014_10_labels : List Row := [(row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 216 293 11), (row3 268 268 508), (row3 216 293 11), (row3 303 303 508), (row3 262 268 268), (row3 280 280 508), (row3 262 268 268), (row3 271 271 508), (row3 276 276 508), (row3 508 508 508), (row3 276 276 508)]

theorem b014_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_10_rows b014_10_labels 476445628614711931618422600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_10_rows b014_10_labels]
    decide +kernel

def b014_11_rows : List Row := [(row3 14 21 22), (row3 14 21 23), (row3 14 21 24), (row3 14 21 25), (row3 14 21 26), (row3 14 21 27), (row3 14 21 28), (row3 14 21 29), (row3 14 21 30), (row3 14 21 31), (row3 14 22 23), (row3 14 22 24), (row3 14 22 25), (row3 14 22 26), (row3 14 22 27), (row3 14 22 28)]

def b014_11_labels : List Row := [(row3 304 508 304), (row3 262 268 268), (row3 268 508 268), (row3 164 13 246), (row3 262 268 268), (row3 280 508 280), (row3 276 508 276), (row3 271 508 271), (row3 278 508 278), (row3 508 508 508), (row3 304 304 508), (row3 508 508 508), (row3 268 508 268), (row3 303 303 508), (row3 268 508 268), (row3 508 508 508)]

theorem b014_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_11_rows b014_11_labels 832310392776315776782920450 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_11_rows b014_11_labels]
    decide +kernel

def b014_12_rows : List Row := [(row3 14 22 29), (row3 14 22 30), (row3 14 22 31), (row3 14 23 24), (row3 14 23 25), (row3 14 23 26), (row3 14 23 27), (row3 14 23 28), (row3 14 23 29), (row3 14 23 30), (row3 14 23 31), (row3 14 24 25), (row3 14 24 26), (row3 14 24 27), (row3 14 24 28), (row3 14 24 29)]

def b014_12_labels : List Row := [(row3 508 508 508), (row3 271 508 271), (row3 508 508 508), (row3 268 508 268), (row3 280 508 280), (row3 262 268 268), (row3 164 13 246), (row3 276 508 276), (row3 508 508 508), (row3 278 508 278), (row3 271 508 271), (row3 304 508 304), (row3 268 268 508), (row3 304 508 304), (row3 508 508 508), (row3 508 508 508)]

theorem b014_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_12_rows b014_12_labels 804163984033302426763820250 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_12_rows b014_12_labels]
    decide +kernel

def b014_13_rows : List Row := [(row3 14 24 30), (row3 14 24 31), (row3 14 25 26), (row3 14 25 27), (row3 14 25 28), (row3 14 25 29), (row3 14 25 30), (row3 14 25 31), (row3 14 26 27), (row3 14 26 28), (row3 14 26 29), (row3 14 26 30), (row3 14 26 31), (row3 14 27 28), (row3 14 27 29), (row3 14 27 30)]

def b014_13_labels : List Row := [(row3 278 508 278), (row3 508 508 508), (row3 216 293 11), (row3 262 268 268), (row3 268 268 508), (row3 303 303 508), (row3 262 268 268), (row3 278 278 508), (row3 216 11 293), (row3 278 508 278), (row3 268 508 268), (row3 184 12 248), (row3 268 508 268), (row3 268 268 508), (row3 278 278 508), (row3 262 268 268)]

theorem b014_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_13_rows b014_13_labels 961726436837025988721793300 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_13_rows b014_13_labels]
    decide +kernel

def b014_14_rows : List Row := [(row3 14 27 31), (row3 14 28 29), (row3 14 28 30), (row3 14 28 31), (row3 14 29 30), (row3 14 29 31), (row3 14 30 31), (row3 15 16 17), (row3 15 16 18), (row3 15 16 19), (row3 15 16 20), (row3 15 16 21), (row3 15 16 22), (row3 15 16 23), (row3 15 16 24), (row3 15 16 25)]

def b014_14_labels : List Row := [(row3 303 303 508), (row3 508 508 508), (row3 268 508 268), (row3 508 508 508), (row3 304 508 304), (row3 508 508 508), (row3 304 304 508), (row3 234 262 229), (row3 290 307 310), (row3 234 211 189), (row3 366 121 228), (row3 290 508 290), (row3 268 268 262), (row3 307 307 307), (row3 290 508 290), (row3 271 508 271)]

theorem b014_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_14_rows b014_14_labels 3911095668175727523512353920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_14_rows b014_14_labels]
    decide +kernel

def b014_15_rows : List Row := [(row3 15 16 26), (row3 15 16 27), (row3 15 16 28), (row3 15 16 29), (row3 15 16 30), (row3 15 16 31), (row3 15 17 18), (row3 15 17 19), (row3 15 17 20), (row3 15 17 21), (row3 15 17 22), (row3 15 17 23), (row3 15 17 24), (row3 15 17 25), (row3 15 17 26), (row3 15 17 27)]

def b014_15_labels : List Row := [(row3 508 508 508), (row3 266 267 264), (row3 273 508 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 262 262), (row3 508 316 316), (row3 297 302 302), (row3 508 508 508), (row3 508 278 278), (row3 268 262 268), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 508 277 277)]

theorem b014_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b014_15_rows b014_15_labels 69845653264145122155629160 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b014_15_rows b014_15_labels]
    decide +kernel

theorem checked014 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_014 QuarticIntegerComputationalData.ids32_014 32254650611483607571272060060 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b014_00_rows ++ b014_01_rows) ++ (b014_02_rows ++ b014_03_rows)) ++ ((b014_04_rows ++ b014_05_rows) ++ (b014_06_rows ++ b014_07_rows))) ++ (((b014_08_rows ++ b014_09_rows) ++ (b014_10_rows ++ b014_11_rows)) ++ ((b014_12_rows ++ b014_13_rows) ++ (b014_14_rows ++ b014_15_rows))))
    ((((b014_00_labels ++ b014_01_labels) ++ (b014_02_labels ++ b014_03_labels)) ++ ((b014_04_labels ++ b014_05_labels) ++ (b014_06_labels ++ b014_07_labels))) ++ (((b014_08_labels ++ b014_09_labels) ++ (b014_10_labels ++ b014_11_labels)) ++ ((b014_12_labels ++ b014_13_labels) ++ (b014_14_labels ++ b014_15_labels)))) 32254650611483607571272060060
  exact ((((b014_00_checked.append (c := 1793858689994924119260833280) b014_01_checked (by decide +kernel)).append (c := 10683086156012435968167186000) (b014_02_checked.append (c := 8889227466017511848906352720) b014_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 25136097013413276661449302580) ((b014_04_checked.append (c := 7169377173453321724445075280) b014_05_checked (by decide +kernel)).append (c := 14453010857400840693282116580) (b014_06_checked.append (c := 7283633683947518968837041300) b014_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 32254650611483607571272060060) (((b014_08_checked.append (c := 62965834369102140267817800) b014_09_checked (by decide +kernel)).append (c := 1371721855760129848669160850) (b014_10_checked.append (c := 1308756021391027708401343050) b014_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 7118553598070330909822757480) ((b014_12_checked.append (c := 1765890420870328415485613550) b014_13_checked (by decide +kernel)).append (c := 5746831742310201061153596630) (b014_14_checked.append (c := 3980941321439872645667983080) b014_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b015_00_rows : List Row := [(row3 15 17 28), (row3 15 17 29), (row3 15 17 30), (row3 15 17 31), (row3 15 18 19), (row3 15 18 20), (row3 15 18 21), (row3 15 18 22), (row3 15 18 23), (row3 15 18 24), (row3 15 18 25), (row3 15 18 26), (row3 15 18 27), (row3 15 18 28), (row3 15 18 29), (row3 15 18 30)]

def b015_00_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 508 211 211), (row3 265 260 260), (row3 508 508 508), (row3 508 268 268), (row3 290 307 290), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 270 267 267), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b015_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_00_rows b015_00_labels 476679166555867141270680360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_00_rows b015_00_labels]
    decide +kernel

def b015_01_rows : List Row := [(row3 15 18 31), (row3 15 19 20), (row3 15 19 21), (row3 15 19 22), (row3 15 19 23), (row3 15 19 24), (row3 15 19 25), (row3 15 19 26), (row3 15 19 27), (row3 15 19 28), (row3 15 19 29), (row3 15 19 30), (row3 15 19 31), (row3 15 20 21), (row3 15 20 22), (row3 15 20 23)]

def b015_01_labels : List Row := [(row3 508 508 508), (row3 297 315 315), (row3 508 508 508), (row3 508 303 303), (row3 235 211 235), (row3 271 508 271), (row3 508 508 508), (row3 508 508 508), (row3 286 296 296), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 273 508 273), (row3 225 201 201), (row3 297 301 301), (row3 351 203 123)]

theorem b015_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_01_rows b015_01_labels 2373452942965140418656060360 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_01_rows b015_01_labels]
    decide +kernel

def b015_02_rows : List Row := [(row3 15 20 24), (row3 15 20 25), (row3 15 20 26), (row3 15 20 27), (row3 15 20 28), (row3 15 20 29), (row3 15 20 30), (row3 15 20 31), (row3 15 21 22), (row3 15 21 23), (row3 15 21 24), (row3 15 21 25), (row3 15 21 26), (row3 15 21 27), (row3 15 21 28), (row3 15 21 29)]

def b015_02_labels : List Row := [(row3 378 117 347), (row3 297 299 299), (row3 265 265 265), (row3 310 312 312), (row3 286 296 296), (row3 270 267 267), (row3 508 277 277), (row3 266 267 264), (row3 508 508 508), (row3 290 290 508), (row3 290 508 290), (row3 508 508 508), (row3 508 508 508), (row3 265 265 265), (row3 508 508 508), (row3 508 508 508)]

theorem b015_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_02_rows b015_02_labels 4379765083945889958009260040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_02_rows b015_02_labels]
    decide +kernel

def b015_03_rows : List Row := [(row3 15 21 30), (row3 15 21 31), (row3 15 22 23), (row3 15 22 24), (row3 15 22 25), (row3 15 22 26), (row3 15 22 27), (row3 15 22 28), (row3 15 22 29), (row3 15 22 30), (row3 15 22 31), (row3 15 23 24), (row3 15 23 25), (row3 15 23 26), (row3 15 23 27), (row3 15 23 28)]

def b015_03_labels : List Row := [(row3 508 508 508), (row3 508 508 508), (row3 234 233 271), (row3 268 508 268), (row3 508 508 508), (row3 508 508 508), (row3 297 299 299), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 271 508 271), (row3 307 508 307), (row3 268 508 268), (row3 290 508 290), (row3 378 117 347), (row3 271 508 271)]

theorem b015_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_03_rows b015_03_labels 4500652032433614194300969640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_03_rows b015_03_labels]
    decide +kernel

def b015_04_rows : List Row := [(row3 15 23 29), (row3 15 23 30), (row3 15 23 31), (row3 15 24 25), (row3 15 24 26), (row3 15 24 27), (row3 15 24 28), (row3 15 24 29), (row3 15 24 30), (row3 15 24 31), (row3 15 25 26), (row3 15 25 27), (row3 15 25 28), (row3 15 25 29), (row3 15 25 30), (row3 15 25 31)]

def b015_04_labels : List Row := [(row3 508 508 508), (row3 271 508 271), (row3 290 508 290), (row3 234 233 271), (row3 290 290 508), (row3 351 203 123), (row3 235 211 235), (row3 290 307 290), (row3 268 262 268), (row3 307 307 307), (row3 508 508 508), (row3 297 301 301), (row3 508 303 303), (row3 508 268 268), (row3 508 278 278), (row3 268 268 262)]

theorem b015_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_04_rows b015_04_labels 2080802636156788746617121120 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_04_rows b015_04_labels]
    decide +kernel

def b015_05_rows : List Row := [(row3 15 26 27), (row3 15 26 28), (row3 15 26 29), (row3 15 26 30), (row3 15 26 31), (row3 15 27 28), (row3 15 27 29), (row3 15 27 30), (row3 15 27 31), (row3 15 28 29), (row3 15 28 30), (row3 15 28 31), (row3 15 29 30), (row3 15 29 31), (row3 15 30 31), (row3 16 17 18)]

def b015_05_labels : List Row := [(row3 225 201 201), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 290 508 290), (row3 297 315 315), (row3 265 260 260), (row3 297 302 302), (row3 366 121 228), (row3 508 211 211), (row3 508 316 316), (row3 234 211 189), (row3 508 262 262), (row3 290 307 310), (row3 234 262 229), (row3 508 234 234)]

theorem b015_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_05_rows b015_05_labels 5002380260531527207195731600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_05_rows b015_05_labels]
    decide +kernel

def b015_06_rows : List Row := [(row3 16 17 19), (row3 16 17 20), (row3 16 17 21), (row3 16 17 22), (row3 16 17 23), (row3 16 17 24), (row3 16 17 25), (row3 16 17 26), (row3 16 17 27), (row3 16 17 28), (row3 16 17 29), (row3 16 17 30), (row3 16 17 31), (row3 16 18 19), (row3 16 18 20), (row3 16 18 21)]

def b015_06_labels : List Row := [(row3 508 353 353), (row3 452 99 355), (row3 211 189 234), (row3 508 304 304), (row3 262 229 234), (row3 223 218 218), (row3 308 314 314), (row3 508 508 508), (row3 508 289 289), (row3 508 287 287), (row3 272 508 272), (row3 508 508 508), (row3 508 508 508), (row3 508 234 234), (row3 120 365 183), (row3 307 310 290)]

theorem b015_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_06_rows b015_06_labels 58770585025904319428531191392 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_06_rows b015_06_labels]
    decide +kernel

def b015_07_rows : List Row := [(row3 16 18 22), (row3 16 18 23), (row3 16 18 24), (row3 16 18 25), (row3 16 18 26), (row3 16 18 27), (row3 16 18 28), (row3 16 18 29), (row3 16 18 30), (row3 16 18 31), (row3 16 19 20), (row3 16 19 21), (row3 16 19 22), (row3 16 19 23), (row3 16 19 24), (row3 16 19 25)]

def b015_07_labels : List Row := [(row3 508 268 268), (row3 307 310 290), (row3 508 307 307), (row3 261 259 259), (row3 508 508 508), (row3 261 259 259), (row3 508 273 273), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508), (row3 452 99 355), (row3 262 229 234), (row3 508 304 304), (row3 211 189 234), (row3 223 218 218), (row3 508 289 289)]

theorem b015_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_07_rows b015_07_labels 51457090138175856543988781352 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_07_rows b015_07_labels]
    decide +kernel

def b015_08_rows : List Row := [(row3 16 19 26), (row3 16 19 27), (row3 16 19 28), (row3 16 19 29), (row3 16 19 30), (row3 16 19 31), (row3 16 20 21), (row3 16 20 22), (row3 16 20 23), (row3 16 20 24), (row3 16 20 25), (row3 16 20 26), (row3 16 20 27), (row3 16 20 28), (row3 16 20 29), (row3 16 20 30)]

def b015_08_labels : List Row := [(row3 508 508 508), (row3 308 314 314), (row3 508 287 287), (row3 508 508 508), (row3 508 508 508), (row3 272 508 272), (row3 95 83 96), (row3 373 380 359), (row3 95 83 96), (row3 478 43 106), (row3 372 383 362), (row3 170 170 190), (row3 372 383 362), (row3 371 382 363), (row3 199 202 224), (row3 508 304 304)]

theorem b015_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_08_rows b015_08_labels 2237279732018887254044996792820 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_08_rows b015_08_labels]
    decide +kernel

def b015_09_rows : List Row := [(row3 16 20 31), (row3 16 21 22), (row3 16 21 23), (row3 16 21 24), (row3 16 21 25), (row3 16 21 26), (row3 16 21 27), (row3 16 21 28), (row3 16 21 29), (row3 16 21 30), (row3 16 21 31), (row3 16 22 23), (row3 16 22 24), (row3 16 22 25), (row3 16 22 26), (row3 16 22 27)]

def b015_09_labels : List Row := [(row3 199 202 224), (row3 210 268 209), (row3 319 310 310), (row3 358 357 358), (row3 404 112 204), (row3 307 508 307), (row3 252 255 251), (row3 199 202 224), (row3 307 508 307), (row3 268 508 268), (row3 508 508 508), (row3 210 209 268), (row3 187 195 195), (row3 321 324 324), (row3 508 508 508), (row3 321 324 324)]

theorem b015_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_09_rows b015_09_labels 17932939598601819323790954984 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_09_rows b015_09_labels]
    decide +kernel

def b015_10_rows : List Row := [(row3 16 22 28), (row3 16 22 29), (row3 16 22 30), (row3 16 22 31), (row3 16 23 24), (row3 16 23 25), (row3 16 23 26), (row3 16 23 27), (row3 16 23 28), (row3 16 23 29), (row3 16 23 30), (row3 16 23 31), (row3 16 24 25), (row3 16 24 26), (row3 16 24 27), (row3 16 24 28)]

def b015_10_labels : List Row := [(row3 508 304 304), (row3 268 508 268), (row3 508 508 508), (row3 268 508 268), (row3 358 357 358), (row3 252 255 251), (row3 307 508 307), (row3 404 112 204), (row3 199 202 224), (row3 508 508 508), (row3 268 508 268), (row3 307 508 307), (row3 105 97 97), (row3 357 357 357), (row3 105 97 97), (row3 478 43 106)]

theorem b015_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_10_rows b015_10_labels 1777659619831389667190760837408 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_10_rows b015_10_labels]
    decide +kernel

def b015_11_rows : List Row := [(row3 16 24 29), (row3 16 24 30), (row3 16 24 31), (row3 16 25 26), (row3 16 25 27), (row3 16 25 28), (row3 16 25 29), (row3 16 25 30), (row3 16 25 31), (row3 16 26 27), (row3 16 26 28), (row3 16 26 29), (row3 16 26 30), (row3 16 26 31), (row3 16 27 28), (row3 16 27 29)]

def b015_11_labels : List Row := [(row3 358 357 358), (row3 187 195 195), (row3 358 357 358), (row3 180 150 150), (row3 335 337 337), (row3 372 383 362), (row3 404 112 204), (row3 321 324 324), (row3 252 255 251), (row3 180 150 150), (row3 170 170 190), (row3 307 508 307), (row3 508 508 508), (row3 307 508 307), (row3 372 383 362), (row3 252 255 251)]

theorem b015_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_11_rows b015_11_labels 31281749370994805623773306324 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_11_rows b015_11_labels]
    decide +kernel

def b015_12_rows : List Row := [(row3 16 27 30), (row3 16 27 31), (row3 16 28 29), (row3 16 28 30), (row3 16 28 31), (row3 16 29 30), (row3 16 29 31), (row3 16 30 31), (row3 17 18 19), (row3 17 18 20), (row3 17 18 21), (row3 17 18 22), (row3 17 18 23), (row3 17 18 24), (row3 17 18 25), (row3 17 18 26)]

def b015_12_labels : List Row := [(row3 321 324 324), (row3 404 112 204), (row3 95 96 83), (row3 373 359 380), (row3 95 96 83), (row3 210 209 268), (row3 319 310 310), (row3 210 268 209), (row3 508 508 508), (row3 311 310 311), (row3 211 211 508), (row3 508 508 508), (row3 262 262 508), (row3 508 265 265), (row3 309 308 309), (row3 265 265 508)]

theorem b015_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_12_rows b015_12_labels 247824465946666125046582281540 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_12_rows b015_12_labels]
    decide +kernel

def b015_13_rows : List Row := [(row3 17 18 27), (row3 17 18 28), (row3 17 18 29), (row3 17 18 30), (row3 17 18 31), (row3 17 19 20), (row3 17 19 21), (row3 17 19 22), (row3 17 19 23), (row3 17 19 24), (row3 17 19 25), (row3 17 19 26), (row3 17 19 27), (row3 17 19 28), (row3 17 19 29), (row3 17 19 30)]

def b015_13_labels : List Row := [(row3 279 508 279), (row3 508 508 508), (row3 508 272 272), (row3 275 508 275), (row3 508 508 508), (row3 221 221 208), (row3 316 316 508), (row3 508 508 508), (row3 316 316 508), (row3 309 309 308), (row3 508 265 265), (row3 279 279 508), (row3 265 508 265), (row3 508 508 508), (row3 508 508 508), (row3 508 508 508)]

theorem b015_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_13_rows b015_13_labels 271653976883371230153455760 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_13_rows b015_13_labels]
    decide +kernel

def b015_14_rows : List Row := [(row3 17 19 31), (row3 17 20 21), (row3 17 20 22), (row3 17 20 23), (row3 17 20 24), (row3 17 20 25), (row3 17 20 26), (row3 17 20 27), (row3 17 20 28), (row3 17 20 29), (row3 17 20 30), (row3 17 20 31), (row3 17 21 22), (row3 17 21 23), (row3 17 21 24), (row3 17 21 25)]

def b015_14_labels : List Row := [(row3 508 508 508), (row3 101 368 451), (row3 221 207 220), (row3 360 381 374), (row3 86 454 379), (row3 178 175 172), (row3 313 313 310), (row3 219 208 219), (row3 214 232 213), (row3 311 311 310), (row3 508 268 268), (row3 298 298 297), (row3 367 508 367), (row3 207 262 211), (row3 176 188 177), (row3 67 460 124)]

theorem b015_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_14_rows b015_14_labels 286414004914880146847226938934 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_14_rows b015_14_labels]
    decide +kernel

def b015_15_rows : List Row := [(row3 17 21 26), (row3 17 21 27), (row3 17 21 28), (row3 17 21 29), (row3 17 21 30), (row3 17 21 31), (row3 17 22 23), (row3 17 22 24), (row3 17 22 25), (row3 17 22 26), (row3 17 22 27), (row3 17 22 28), (row3 17 22 29), (row3 17 22 30), (row3 17 22 31), (row3 17 23 24)]

def b015_15_labels : List Row := [(row3 206 258 211), (row3 318 508 318), (row3 316 508 316), (row3 214 232 213), (row3 306 508 306), (row3 508 508 508), (row3 317 317 508), (row3 324 324 321), (row3 196 197 188), (row3 326 326 508), (row3 258 508 258), (row3 508 508 508), (row3 298 298 297), (row3 268 508 268), (row3 508 508 508), (row3 193 188 194)]

theorem b015_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b015_15_rows b015_15_labels 7625923428041108396017522776 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b015_15_rows b015_15_labels]
    decide +kernel

theorem checked015 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_015 QuarticIntegerComputationalData.ids32_015 4735331496373013301341871886410 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b015_00_rows ++ b015_01_rows) ++ (b015_02_rows ++ b015_03_rows)) ++ ((b015_04_rows ++ b015_05_rows) ++ (b015_06_rows ++ b015_07_rows))) ++ (((b015_08_rows ++ b015_09_rows) ++ (b015_10_rows ++ b015_11_rows)) ++ ((b015_12_rows ++ b015_13_rows) ++ (b015_14_rows ++ b015_15_rows))))
    ((((b015_00_labels ++ b015_01_labels) ++ (b015_02_labels ++ b015_03_labels)) ++ ((b015_04_labels ++ b015_05_labels) ++ (b015_06_labels ++ b015_07_labels))) ++ (((b015_08_labels ++ b015_09_labels) ++ (b015_10_labels ++ b015_11_labels)) ++ ((b015_12_labels ++ b015_13_labels) ++ (b015_14_labels ++ b015_15_labels)))) 4735331496373013301341871886410
  exact ((((b015_00_checked.append (c := 2850132109521007559926740720) b015_01_checked (by decide +kernel)).append (c := 11730549225900511712236970400) (b015_02_checked.append (c := 8880417116379504152310229680) b015_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 129041407286669003638569795864) ((b015_04_checked.append (c := 7083182896688315953812852720) b015_05_checked (by decide +kernel)).append (c := 117310858060768491926332825464) (b015_06_checked.append (c := 110227675164080175972519972744) b015_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 4735331496373013301341871886410) (((b015_08_checked.append (c := 2255212671617489073368787747804) b015_09_checked (by decide +kernel)).append (c := 4064154040819873546183321891536) (b015_10_checked.append (c := 1808941369202384472814534143732) b015_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 4606290089086344297703302090546) ((b015_12_checked.append (c := 248096119923549496276735737300) b015_13_checked (by decide +kernel)).append (c := 542136048266470751519980199010) (b015_14_checked.append (c := 294039928342921255243244461710) b015_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b016_00_rows : List Row := [(row3 17 23 25), (row3 17 23 26), (row3 17 23 27), (row3 17 23 28), (row3 17 23 29), (row3 17 23 30), (row3 17 23 31), (row3 17 24 25), (row3 17 24 26), (row3 17 24 27), (row3 17 24 28), (row3 17 24 29), (row3 17 24 30), (row3 17 24 31), (row3 17 25 26), (row3 17 25 27)]

def b016_00_labels : List Row := [(row3 325 321 325), (row3 255 258 262), (row3 141 14 245), (row3 306 508 306), (row3 508 268 268), (row3 280 508 280), (row3 268 508 268), (row3 104 407 450), (row3 192 192 187), (row3 370 393 394), (row3 67 460 124), (row3 178 175 172), (row3 325 321 325), (row3 196 197 188), (row3 370 394 393), (row3 192 187 192)]

theorem b016_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_00_rows b016_00_labels 203800882367177641972015278594 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_00_rows b016_00_labels]
    decide +kernel

def b016_01_rows : List Row := [(row3 17 25 28), (row3 17 25 29), (row3 17 25 30), (row3 17 25 31), (row3 17 26 27), (row3 17 26 28), (row3 17 26 29), (row3 17 26 30), (row3 17 26 31), (row3 17 27 28), (row3 17 27 29), (row3 17 27 30), (row3 17 27 31), (row3 17 28 29), (row3 17 28 30), (row3 17 28 31)]

def b016_01_labels : List Row := [(row3 176 188 177), (row3 86 454 379), (row3 193 188 194), (row3 324 324 321), (row3 166 13 320), (row3 318 508 318), (row3 219 208 219), (row3 141 14 245), (row3 258 508 258), (row3 206 258 211), (row3 313 313 310), (row3 255 258 262), (row3 326 326 508), (row3 101 368 451), (row3 207 211 262), (row3 367 367 508)]

theorem b016_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_01_rows b016_01_labels 123895405575414272509154380164 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_01_rows b016_01_labels]
    decide +kernel

def b016_02_rows : List Row := [(row3 17 29 30), (row3 17 29 31), (row3 17 30 31), (row3 18 19 20), (row3 18 19 21), (row3 18 19 22), (row3 18 19 23), (row3 18 19 24), (row3 18 19 25), (row3 18 19 26), (row3 18 19 27), (row3 18 19 28), (row3 18 19 29), (row3 18 19 30), (row3 18 19 31), (row3 18 20 21)]

def b016_02_labels : List Row := [(row3 360 374 381), (row3 221 220 207), (row3 317 317 508), (row3 310 311 311), (row3 262 262 508), (row3 508 508 508), (row3 211 211 508), (row3 265 508 265), (row3 508 279 279), (row3 265 265 508), (row3 308 309 309), (row3 508 508 508), (row3 508 508 508), (row3 508 275 275), (row3 272 508 272), (row3 364 174 119)]

theorem b016_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_02_rows b016_02_labels 8400309590953077208181791920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_02_rows b016_02_labels]
    decide +kernel

def b016_03_rows : List Row := [(row3 18 20 22), (row3 18 20 23), (row3 18 20 24), (row3 18 20 25), (row3 18 20 26), (row3 18 20 27), (row3 18 20 28), (row3 18 20 29), (row3 18 20 30), (row3 18 20 31), (row3 18 21 22), (row3 18 21 23), (row3 18 21 24), (row3 18 21 25), (row3 18 21 26), (row3 18 21 27)]

def b016_03_labels : List Row := [(row3 310 312 312), (row3 364 174 119), (row3 405 114 240), (row3 331 334 334), (row3 253 253 258), (row3 331 334 334), (row3 297 299 299), (row3 260 265 260), (row3 508 280 280), (row3 260 265 260), (row3 210 508 210), (row3 319 307 307), (row3 322 508 322), (row3 404 113 205), (row3 322 310 307), (row3 252 256 252)]

theorem b016_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_03_rows b016_03_labels 21449383171585936841866408920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_03_rows b016_03_labels]
    decide +kernel

def b016_04_rows : List Row := [(row3 18 21 28), (row3 18 21 29), (row3 18 21 30), (row3 18 21 31), (row3 18 22 23), (row3 18 22 24), (row3 18 22 25), (row3 18 22 26), (row3 18 22 27), (row3 18 22 28), (row3 18 22 29), (row3 18 22 30), (row3 18 22 31), (row3 18 23 24), (row3 18 23 25), (row3 18 23 26)]

def b016_04_labels : List Row := [(row3 268 508 268), (row3 307 508 307), (row3 260 265 260), (row3 508 508 508), (row3 210 210 508), (row3 258 508 258), (row3 321 323 323), (row3 190 190 508), (row3 321 323 323), (row3 508 508 508), (row3 268 508 268), (row3 297 299 299), (row3 268 508 268), (row3 322 508 322), (row3 252 256 252), (row3 322 310 307)]

theorem b016_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_04_rows b016_04_labels 1733574773623844510102811600 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_04_rows b016_04_labels]
    decide +kernel

def b016_05_rows : List Row := [(row3 18 23 27), (row3 18 23 28), (row3 18 23 29), (row3 18 23 30), (row3 18 23 31), (row3 18 24 25), (row3 18 24 26), (row3 18 24 27), (row3 18 24 28), (row3 18 24 29), (row3 18 24 30), (row3 18 24 31), (row3 18 25 26), (row3 18 25 27), (row3 18 25 28), (row3 18 25 29)]

def b016_05_labels : List Row := [(row3 404 113 205), (row3 268 508 268), (row3 508 508 508), (row3 260 265 260), (row3 307 508 307), (row3 377 156 116), (row3 327 327 508), (row3 377 156 116), (row3 190 190 508), (row3 322 310 307), (row3 253 253 258), (row3 322 310 307), (row3 377 156 116), (row3 335 336 336), (row3 321 323 323), (row3 404 113 205)]

theorem b016_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_05_rows b016_05_labels 31978947246243859736912477880 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_05_rows b016_05_labels]
    decide +kernel

def b016_06_rows : List Row := [(row3 18 25 30), (row3 18 25 31), (row3 18 26 27), (row3 18 26 28), (row3 18 26 29), (row3 18 26 30), (row3 18 26 31), (row3 18 27 28), (row3 18 27 29), (row3 18 27 30), (row3 18 27 31), (row3 18 28 29), (row3 18 28 30), (row3 18 28 31), (row3 18 29 30), (row3 18 29 31)]

def b016_06_labels : List Row := [(row3 331 334 334), (row3 252 256 252), (row3 377 116 156), (row3 258 508 258), (row3 322 508 322), (row3 405 114 240), (row3 322 508 322), (row3 321 323 323), (row3 252 256 252), (row3 331 334 334), (row3 404 113 205), (row3 210 508 210), (row3 310 312 312), (row3 210 508 210), (row3 364 174 119), (row3 319 307 307)]

theorem b016_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_06_rows b016_06_labels 26369052115950535193453275200 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_06_rows b016_06_labels]
    decide +kernel

def b016_07_rows : List Row := [(row3 18 30 31), (row3 19 20 21), (row3 19 20 22), (row3 19 20 23), (row3 19 20 24), (row3 19 20 25), (row3 19 20 26), (row3 19 20 27), (row3 19 20 28), (row3 19 20 29), (row3 19 20 30), (row3 19 20 31), (row3 19 21 22), (row3 19 21 23), (row3 19 21 24), (row3 19 21 25)]

def b016_07_labels : List Row := [(row3 364 119 174), (row3 360 381 374), (row3 221 207 220), (row3 101 368 451), (row3 86 454 379), (row3 219 208 219), (row3 313 313 310), (row3 178 175 172), (row3 214 232 213), (row3 298 298 297), (row3 508 268 268), (row3 311 311 310), (row3 317 508 317), (row3 207 211 262), (row3 193 188 194), (row3 141 14 245)]

theorem b016_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_07_rows b016_07_labels 123629826144444984515963536164 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_07_rows b016_07_labels]
    decide +kernel

def b016_08_rows : List Row := [(row3 19 21 26), (row3 19 21 27), (row3 19 21 28), (row3 19 21 29), (row3 19 21 30), (row3 19 21 31), (row3 19 22 23), (row3 19 22 24), (row3 19 22 25), (row3 19 22 26), (row3 19 22 27), (row3 19 22 28), (row3 19 22 29), (row3 19 22 30), (row3 19 22 31), (row3 19 23 24)]

def b016_08_labels : List Row := [(row3 255 258 262), (row3 325 321 325), (row3 306 508 306), (row3 268 508 268), (row3 280 508 280), (row3 508 268 268), (row3 367 367 508), (row3 324 324 321), (row3 258 508 258), (row3 326 326 508), (row3 196 197 188), (row3 508 508 508), (row3 508 508 508), (row3 268 508 268), (row3 298 298 297), (row3 176 188 177)]

theorem b016_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_08_rows b016_08_labels 10303687603033066355223033624 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_08_rows b016_08_labels]
    decide +kernel

def b016_09_rows : List Row := [(row3 19 23 25), (row3 19 23 26), (row3 19 23 27), (row3 19 23 28), (row3 19 23 29), (row3 19 23 30), (row3 19 23 31), (row3 19 24 25), (row3 19 24 26), (row3 19 24 27), (row3 19 24 28), (row3 19 24 29), (row3 19 24 30), (row3 19 24 31), (row3 19 25 26), (row3 19 25 27)]

def b016_09_labels : List Row := [(row3 318 508 318), (row3 206 258 211), (row3 67 460 124), (row3 316 508 316), (row3 508 508 508), (row3 306 508 306), (row3 214 232 213), (row3 370 393 394), (row3 192 192 187), (row3 104 407 450), (row3 67 460 124), (row3 196 197 188), (row3 325 321 325), (row3 178 175 172), (row3 166 320 13), (row3 192 192 187)]

theorem b016_09_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_09_rows b016_09_labels 360987270458319905332042364736 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_09_rows b016_09_labels]
    decide +kernel

def b016_10_rows : List Row := [(row3 19 25 28), (row3 19 25 29), (row3 19 25 30), (row3 19 25 31), (row3 19 26 27), (row3 19 26 28), (row3 19 26 29), (row3 19 26 30), (row3 19 26 31), (row3 19 27 28), (row3 19 27 29), (row3 19 27 30), (row3 19 27 31), (row3 19 28 29), (row3 19 28 30), (row3 19 28 31)]

def b016_10_labels : List Row := [(row3 206 258 211), (row3 326 326 508), (row3 255 258 262), (row3 313 313 310), (row3 370 393 394), (row3 318 508 318), (row3 258 508 258), (row3 141 14 245), (row3 219 208 219), (row3 176 188 177), (row3 324 324 321), (row3 193 188 194), (row3 86 454 379), (row3 367 367 508), (row3 207 211 262), (row3 101 368 451)]

theorem b016_10_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_10_rows b016_10_labels 129771868396771019450692799544 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_10_rows b016_10_labels]
    decide +kernel

def b016_11_rows : List Row := [(row3 19 29 30), (row3 19 29 31), (row3 19 30 31), (row3 20 21 22), (row3 20 21 23), (row3 20 21 24), (row3 20 21 25), (row3 20 21 26), (row3 20 21 27), (row3 20 21 28), (row3 20 21 29), (row3 20 21 30), (row3 20 21 31), (row3 20 22 23), (row3 20 22 24), (row3 20 22 25)]

def b016_11_labels : List Row := [(row3 317 508 317), (row3 221 207 220), (row3 360 381 374), (row3 369 453 100), (row3 82 94 94), (row3 42 477 84), (row3 69 467 102), (row3 173 118 364), (row3 384 375 361), (row3 406 400 392), (row3 171 122 350), (row3 294 11 217), (row3 200 198 222), (row3 369 100 453), (row3 455 88 410), (row3 152 155 151)]

theorem b016_11_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_11_rows b016_11_labels 3007152594786223850216986412094 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_11_rows b016_11_labels]
    decide +kernel

def b016_12_rows : List Row := [(row3 20 22 26), (row3 20 22 27), (row3 20 22 28), (row3 20 22 29), (row3 20 22 30), (row3 20 22 31), (row3 20 23 24), (row3 20 23 25), (row3 20 23 26), (row3 20 23 27), (row3 20 23 28), (row3 20 23 29), (row3 20 23 30), (row3 20 23 31), (row3 20 24 25), (row3 20 24 26)]

def b016_12_labels : List Row := [(row3 340 340 310), (row3 152 155 151), (row3 231 182 182), (row3 328 328 327), (row3 257 508 257), (row3 328 328 327), (row3 42 477 84), (row3 384 375 361), (row3 173 118 364), (row3 69 467 102), (row3 406 400 392), (row3 200 198 222), (row3 294 11 217), (row3 171 122 350), (row3 479 491 481), (row3 78 81 87)]

theorem b016_12_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_12_rows b016_12_labels 6092756346961063941347145396966 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_12_rows b016_12_labels]
    decide +kernel

def b016_13_rows : List Row := [(row3 20 24 27), (row3 20 24 28), (row3 20 24 29), (row3 20 24 30), (row3 20 24 31), (row3 20 25 26), (row3 20 25 27), (row3 20 25 28), (row3 20 25 29), (row3 20 25 30), (row3 20 25 31), (row3 20 26 27), (row3 20 26 28), (row3 20 26 29), (row3 20 26 30), (row3 20 26 31)]

def b016_13_labels : List Row := [(row3 479 491 481), (row3 28 501 473), (row3 79 80 85), (row3 420 412 399), (row3 79 80 85), (row3 397 422 415), (row3 135 134 134), (row3 79 80 85), (row3 62 464 418), (row3 169 160 169), (row3 346 346 344), (row3 397 415 422), (row3 420 412 399), (row3 169 160 169), (row3 129 15 244), (row3 169 160 169)]

theorem b016_13_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_13_rows b016_13_labels 390881881457190180816033321079920 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_13_rows b016_13_labels]
    decide +kernel

def b016_14_rows : List Row := [(row3 20 27 28), (row3 20 27 29), (row3 20 27 30), (row3 20 27 31), (row3 20 28 29), (row3 20 28 30), (row3 20 28 31), (row3 20 29 30), (row3 20 29 31), (row3 20 30 31), (row3 21 22 23), (row3 21 22 24), (row3 21 22 25), (row3 21 22 26), (row3 21 22 27), (row3 21 22 28)]

def b016_14_labels : List Row := [(row3 79 80 85), (row3 346 346 344), (row3 169 160 169), (row3 62 464 418), (row3 479 481 491), (row3 78 87 81), (row3 479 481 491), (row3 397 415 422), (row3 135 134 134), (row3 397 422 415), (row3 210 181 210), (row3 161 153 154), (row3 462 68 391), (row3 163 148 210), (row3 335 339 339), (row3 508 330 330)]

theorem b016_14_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_14_rows b016_14_labels 7646968283101566906134309887932 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_14_rows b016_14_labels]
    decide +kernel

def b016_15_rows : List Row := [(row3 21 22 29), (row3 21 22 30), (row3 21 22 31), (row3 21 23 24), (row3 21 23 25), (row3 21 23 26), (row3 21 23 27), (row3 21 23 28), (row3 21 23 29), (row3 21 23 30), (row3 21 23 31), (row3 21 24 25), (row3 21 24 26), (row3 21 24 27), (row3 21 24 28), (row3 21 24 29)]

def b016_15_labels : List Row := [(row3 188 186 185), (row3 321 329 329), (row3 258 508 258), (row3 386 386 387), (row3 111 403 145), (row3 332 332 319), (row3 403 111 145), (row3 149 149 179), (row3 508 319 319), (row3 254 254 252), (row3 319 508 319), (row3 475 57 41), (row3 388 390 387), (row3 93 77 76), (row3 490 39 73), (row3 408 408 409)]

theorem b016_15_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b016_15_rows b016_15_labels 7896283931394686449617637946040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b016_15_rows b016_15_labels]
    decide +kernel

theorem checked016 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_016 QuarticIntegerComputationalData.ids32_016 416567362820877240106975008881298 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    ((((b016_00_rows ++ b016_01_rows) ++ (b016_02_rows ++ b016_03_rows)) ++ ((b016_04_rows ++ b016_05_rows) ++ (b016_06_rows ++ b016_07_rows))) ++ (((b016_08_rows ++ b016_09_rows) ++ (b016_10_rows ++ b016_11_rows)) ++ ((b016_12_rows ++ b016_13_rows) ++ (b016_14_rows ++ b016_15_rows))))
    ((((b016_00_labels ++ b016_01_labels) ++ (b016_02_labels ++ b016_03_labels)) ++ ((b016_04_labels ++ b016_05_labels) ++ (b016_06_labels ++ b016_07_labels))) ++ (((b016_08_labels ++ b016_09_labels) ++ (b016_10_labels ++ b016_11_labels)) ++ ((b016_12_labels ++ b016_13_labels) ++ (b016_14_labels ++ b016_15_labels)))) 416567362820877240106975008881298
  exact ((((b016_00_checked.append (c := 327696287942591914481169658758) b016_01_checked (by decide +kernel)).append (c := 357545980705130928531217859598) (b016_02_checked.append (c := 29849692762539014050048200840) b016_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 541257380985394152487649960442) ((b016_04_checked.append (c := 33712522019867704247015289480) b016_05_checked (by decide +kernel)).append (c := 183711400280263223956432100844) (b016_06_checked.append (c := 149998878260395519709416811364) b016_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 416567362820877240106975008881298) (((b016_08_checked.append (c := 371290958061352971687265398360) b016_09_checked (by decide +kernel)).append (c := 3508215421244347841354944609998) (b016_10_checked.append (c := 3136924463182994869667679211638) b016_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 416026105439891845954487358920856) ((b016_12_checked.append (c := 396974637804151244757380466476886) b016_13_checked (by decide +kernel)).append (c := 412517890018647498113132414310858) (b016_14_checked.append (c := 15543252214496253355751947833972) b016_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals32
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b017_00_rows : List Row := [(row3 21 24 30), (row3 21 24 31), (row3 21 25 26), (row3 21 25 27), (row3 21 25 28), (row3 21 25 29), (row3 21 25 30), (row3 21 25 31), (row3 21 26 27), (row3 21 26 28), (row3 21 26 29), (row3 21 26 30), (row3 21 26 31), (row3 21 27 28), (row3 21 27 29), (row3 21 27 30)]

def b017_00_labels : List Row := [(row3 158 168 167), (row3 388 385 389), (row3 58 48 59), (row3 416 421 396), (row3 434 436 426), (row3 490 39 73), (row3 413 423 398), (row3 131 132 147), (row3 402 110 133), (row3 131 132 147), (row3 388 385 389), (row3 428 108 157), (row3 338 508 338), (row3 413 423 398), (row3 158 168 167), (row3 341 343 343)]

theorem b017_00_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_00_rows b017_00_labels 7850710297299021231549762439884 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_00_rows b017_00_labels]
    decide +kernel

def b017_01_rows : List Row := [(row3 21 27 31), (row3 21 28 29), (row3 21 28 30), (row3 21 28 31), (row3 21 29 30), (row3 21 29 31), (row3 21 30 31), (row3 22 23 24), (row3 22 23 25), (row3 22 23 26), (row3 22 23 27), (row3 22 23 28), (row3 22 23 29), (row3 22 23 30), (row3 22 23 31), (row3 22 24 25)]

def b017_01_labels : List Row := [(row3 428 108 157), (row3 475 57 41), (row3 416 396 421), (row3 58 59 48), (row3 93 76 77), (row3 388 387 390), (row3 402 110 133), (row3 153 161 154), (row3 339 335 339), (row3 148 163 210), (row3 68 462 391), (row3 330 508 330), (row3 508 258 258), (row3 329 321 329), (row3 186 188 185), (row3 89 429 456)]

theorem b017_01_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_01_rows b017_01_labels 2969857860449706075010347030612 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_01_rows b017_01_labels]
    decide +kernel

def b017_02_rows : List Row := [(row3 22 24 26), (row3 22 24 27), (row3 22 24 28), (row3 22 24 29), (row3 22 24 30), (row3 22 24 31), (row3 22 25 26), (row3 22 25 27), (row3 22 25 28), (row3 22 25 29), (row3 22 25 30), (row3 22 25 31), (row3 22 26 27), (row3 22 26 28), (row3 22 26 29), (row3 22 26 30)]

def b017_02_labels : List Row := [(row3 139 139 159), (row3 89 429 456), (row3 49 468 191), (row3 143 138 137), (row3 343 341 343), (row3 143 138 137), (row3 70 411 461), (row3 144 136 136), (row3 140 162 140), (row3 61 463 417), (row3 143 138 137), (row3 342 342 341), (row3 70 461 411), (row3 345 508 345), (row3 140 162 140), (row3 49 468 191)]

theorem b017_02_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_02_rows b017_02_labels 1353901257142131439141014184416 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_02_rows b017_02_labels]
    decide +kernel

def b017_03_rows : List Row := [(row3 22 26 31), (row3 22 27 28), (row3 22 27 29), (row3 22 27 30), (row3 22 27 31), (row3 22 28 29), (row3 22 28 30), (row3 22 28 31), (row3 22 29 30), (row3 22 29 31), (row3 22 30 31), (row3 23 24 25), (row3 23 24 26), (row3 23 24 27), (row3 23 24 28), (row3 23 24 29)]

def b017_03_labels : List Row := [(row3 140 162 140), (row3 140 162 140), (row3 342 342 341), (row3 143 138 137), (row3 61 463 417), (row3 70 411 461), (row3 139 139 159), (row3 70 411 461), (row3 89 429 456), (row3 144 136 136), (row3 89 456 429), (row3 93 77 76), (row3 388 390 387), (row3 475 57 41), (row3 490 39 73), (row3 388 385 389)]

theorem b017_03_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_03_rows b017_03_labels 8524335362339589242905670611032 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_03_rows b017_03_labels]
    decide +kernel

def b017_04_rows : List Row := [(row3 23 24 30), (row3 23 24 31), (row3 23 25 26), (row3 23 25 27), (row3 23 25 28), (row3 23 25 29), (row3 23 25 30), (row3 23 25 31), (row3 23 26 27), (row3 23 26 28), (row3 23 26 29), (row3 23 26 30), (row3 23 26 31), (row3 23 27 28), (row3 23 27 29), (row3 23 27 30)]

def b017_04_labels : List Row := [(row3 158 168 167), (row3 408 408 409), (row3 402 133 110), (row3 416 396 421), (row3 413 423 398), (row3 428 108 157), (row3 341 343 343), (row3 158 168 167), (row3 58 59 48), (row3 131 132 147), (row3 338 508 338), (row3 428 108 157), (row3 388 385 389), (row3 434 436 426), (row3 131 132 147), (row3 413 423 398)]

theorem b017_04_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_04_rows b017_04_labels 2338328870886890527587778499964 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_04_rows b017_04_labels]
    decide +kernel

def b017_05_rows : List Row := [(row3 23 27 31), (row3 23 28 29), (row3 23 28 30), (row3 23 28 31), (row3 23 29 30), (row3 23 29 31), (row3 23 30 31), (row3 24 25 26), (row3 24 25 27), (row3 24 25 28), (row3 24 25 29), (row3 24 25 30), (row3 24 25 31), (row3 24 26 27), (row3 24 26 28), (row3 24 26 29)]

def b017_05_labels : List Row := [(row3 490 39 73), (row3 58 59 48), (row3 416 396 421), (row3 475 57 41), (row3 402 133 110), (row3 388 390 387), (row3 93 77 76), (row3 56 40 476), (row3 492 480 480), (row3 502 29 487), (row3 488 35 474), (row3 430 458 91), (row3 75 74 92), (row3 56 476 40), (row3 37 486 45), (row3 425 424 425)]

theorem b017_05_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_05_rows b017_05_labels 469175492119226800610272529340732 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_05_rows b017_05_labels]
    decide +kernel

def b017_06_rows : List Row := [(row3 24 26 30), (row3 24 26 31), (row3 24 27 28), (row3 24 27 29), (row3 24 27 30), (row3 24 27 31), (row3 24 28 29), (row3 24 28 30), (row3 24 28 31), (row3 24 29 30), (row3 24 29 31), (row3 24 30 31), (row3 25 26 27), (row3 25 26 28), (row3 25 26 29), (row3 25 26 30)]

def b017_06_labels : List Row := [(row3 427 107 126), (row3 425 424 425), (row3 502 29 487), (row3 75 74 92), (row3 430 458 91), (row3 488 35 474), (row3 23 24 24), (row3 500 493 493), (row3 23 24 24), (row3 66 52 52), (row3 437 438 438), (row3 66 52 52), (row3 71 469 71), (row3 444 440 433), (row3 38 489 51), (row3 50 472 72)]

theorem b017_06_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_06_rows b017_06_labels 1479670539141885927637189895060424 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_06_rows b017_06_labels]
    decide +kernel

def b017_07_rows : List Row := [(row3 25 26 31), (row3 25 27 28), (row3 25 27 29), (row3 25 27 30), (row3 25 27 31), (row3 25 28 29), (row3 25 28 30), (row3 25 28 31), (row3 25 29 30), (row3 25 29 31), (row3 25 30 31), (row3 26 27 28), (row3 26 27 29), (row3 26 27 30), (row3 26 27 31), (row3 26 28 29)]

def b017_07_labels : List Row := [(row3 127 109 401), (row3 55 55 60), (row3 465 63 435), (row3 130 130 128), (row3 63 465 435), (row3 32 498 503), (row3 53 64 54), (row3 494 495 499), (row3 494 499 495), (row3 53 54 64), (row3 65 466 441), (row3 440 444 433), (row3 109 127 401), (row3 472 50 72), (row3 489 38 51), (row3 485 44 36)]

theorem b017_07_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_07_rows b017_07_labels 517147035703179712788890379189792 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_07_rows b017_07_labels]
    decide +kernel

def b017_08_rows : List Row := [(row3 26 28 30), (row3 26 28 31), (row3 26 29 30), (row3 26 29 31), (row3 26 30 31), (row3 27 28 29), (row3 27 28 30), (row3 27 28 31), (row3 27 29 30), (row3 27 29 31), (row3 27 30 31), (row3 28 29 30), (row3 28 29 31), (row3 28 30 31), (row3 29 30 31)]

def b017_08_labels : List Row := [(row3 445 439 446), (row3 485 44 36), (row3 485 44 36), (row3 431 432 432), (row3 485 36 44), (row3 494 495 499), (row3 53 64 54), (row3 32 498 503), (row3 65 441 466), (row3 53 64 54), (row3 494 495 499), (row3 497 504 31), (row3 22 21 21), (row3 497 31 504), (row3 483 33 483)]

theorem b017_08_checked : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 b017_08_rows b017_08_labels 2102833635837189057134082542802216 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
      QuarticIntegerWeightedTotalsLookups.covariance32 QuarticIntegerWeightedTotalsLookups.upper32
      QuarticIntegerWeightedTotalsLookups.covariance32_eq QuarticIntegerWeightedTotalsLookups.upper32_eq
      b017_08_rows b017_08_labels]
    decide +kernel

theorem checked017 : Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32
    upperNumerators32 QuarticIntegerComputationalData.rows32_017 QuarticIntegerComputationalData.ids32_017 4591863836449598836686629919159072 := by
  change Block 4 2 QuarticIntegerCovarianceData.covarianceNumerators32 upperNumerators32
    (((b017_00_rows ++ b017_01_rows) ++ (b017_02_rows ++ b017_03_rows)) ++ ((b017_04_rows ++ b017_05_rows) ++ (b017_06_rows ++ (b017_07_rows ++ b017_08_rows))))
    (((b017_00_labels ++ b017_01_labels) ++ (b017_02_labels ++ b017_03_labels)) ++ ((b017_04_labels ++ b017_05_labels) ++ (b017_06_labels ++ (b017_07_labels ++ b017_08_labels)))) 4591863836449598836686629919159072
  exact (((b017_00_checked.append (c := 10820568157748727306560109470496) b017_01_checked (by decide +kernel)).append (c := 20698804777230447988606794265944) (b017_02_checked.append (c := 9878236619481720682046684795448) b017_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 4591863836449598836686629919159072) ((b017_04_checked.append (c := 471513820990113691137860307840696) b017_05_checked (by decide +kernel)).append (c := 4571165031672368388698023124893128) (b017_06_checked.append (c := 4099651210682254697560162817052432) (b017_07_checked.append (c := 2619980671540368769922972921992008) b017_08_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals32
import Dressed.QuarticIntegerWeightedTotalsGuarded
import Dressed.QuarticIntegerDataConstructors
import Dressed.QuarticIntegerData16
import Dressed.QuarticIntegerCovarianceData

/-! Exact weighted integer totals from at most16 supports per kernel reduction.
Balanced proved compositions preserve every source row and matching label. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals16
open QuarticRootedRowTable QuarticIntegerData QuarticIntegerWeightedTotals
open QuarticIntegerWeightedList QuarticIntegerMeanEvaluation
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def b000_00_rows : List Row := [(row3 1 2 3), (row3 1 2 4), (row3 1 2 5), (row3 1 2 6), (row3 1 2 7), (row3 1 2 8), (row3 1 2 9), (row3 1 2 10), (row3 1 2 11), (row3 1 2 12), (row3 1 2 13), (row3 1 2 14), (row3 1 2 15), (row3 1 3 4), (row3 1 3 5), (row3 1 3 6)]

def b000_00_labels : List Row := [(row3 6 42 6), (row3 7 41 39), (row3 5 5 5), (row3 39 41 7), (row3 36 8 36), (row3 37 9 10), (row3 38 40 38), (row3 10 9 37), (row3 12 35 12), (row3 7 41 39), (row3 5 5 5), (row3 39 41 7), (row3 36 8 36), (row3 5 5 5), (row3 7 39 41), (row3 36 36 8)]

theorem b000_00_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_00_rows b000_00_labels 2380216667038435273710650735508816 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_00_rows b000_00_labels]
    decide +kernel

def b000_01_rows : List Row := [(row3 1 3 7), (row3 1 3 8), (row3 1 3 9), (row3 1 3 10), (row3 1 3 11), (row3 1 3 12), (row3 1 3 13), (row3 1 3 14), (row3 1 3 15), (row3 1 4 5), (row3 1 4 6), (row3 1 4 7), (row3 1 4 8), (row3 1 4 9), (row3 1 4 10), (row3 1 4 11)]

def b000_01_labels : List Row := [(row3 39 7 41), (row3 38 38 40), (row3 37 10 9), (row3 12 12 35), (row3 10 37 9), (row3 5 5 5), (row3 7 39 41), (row3 36 36 8), (row3 39 7 41), (row3 6 6 42), (row3 36 36 8), (row3 39 7 41), (row3 39 7 41), (row3 36 36 8), (row3 12 12 35), (row3 10 37 9)]

theorem b000_01_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_01_rows b000_01_labels 2044806613347559647829158183307584 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_01_rows b000_01_labels]
    decide +kernel

def b000_02_rows : List Row := [(row3 1 4 12), (row3 1 4 13), (row3 1 4 14), (row3 1 4 15), (row3 1 5 6), (row3 1 5 7), (row3 1 5 8), (row3 1 5 9), (row3 1 5 10), (row3 1 5 11), (row3 1 5 12), (row3 1 5 13), (row3 1 5 14), (row3 1 5 15), (row3 1 6 7), (row3 1 6 8)]

def b000_02_labels : List Row := [(row3 5 5 5), (row3 7 39 41), (row3 37 10 9), (row3 38 38 40), (row3 39 41 7), (row3 36 8 36), (row3 36 8 36), (row3 39 41 7), (row3 10 9 37), (row3 12 35 12), (row3 7 41 39), (row3 5 5 5), (row3 38 40 38), (row3 37 9 10), (row3 11 34 32), (row3 14 33 28)]

theorem b000_02_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_02_rows b000_02_labels 909385688714857654477390338128544 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_02_rows b000_02_labels]
    decide +kernel

def b000_03_rows : List Row := [(row3 1 6 9), (row3 1 6 10), (row3 1 6 11), (row3 1 6 12), (row3 1 6 13), (row3 1 6 14), (row3 1 6 15), (row3 1 7 8), (row3 1 7 9), (row3 1 7 10), (row3 1 7 11), (row3 1 7 12), (row3 1 7 13), (row3 1 7 14), (row3 1 7 15), (row3 1 8 9)]

def b000_03_labels : List Row := [(row3 15 13 13), (row3 27 31 30), (row3 24 16 18), (row3 37 9 10), (row3 38 38 40), (row3 15 13 13), (row3 14 33 28), (row3 15 13 13), (row3 14 28 33), (row3 24 18 16), (row3 27 30 31), (row3 38 40 38), (row3 37 10 9), (row3 14 28 33), (row3 15 13 13), (row3 11 32 34)]

theorem b000_03_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_03_rows b000_03_labels 17901922544768964029444973700656 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_03_rows b000_03_labels]
    decide +kernel

def b000_04_rows : List Row := [(row3 1 8 10), (row3 1 8 11), (row3 1 8 12), (row3 1 8 13), (row3 1 8 14), (row3 1 8 15), (row3 1 9 10), (row3 1 9 11), (row3 1 9 12), (row3 1 9 13), (row3 1 9 14), (row3 1 9 15), (row3 1 10 11), (row3 1 10 12), (row3 1 10 13), (row3 1 10 14)]

def b000_04_labels : List Row := [(row3 24 18 16), (row3 27 30 31), (row3 39 41 7), (row3 36 36 8), (row3 14 28 33), (row3 15 13 13), (row3 27 31 30), (row3 24 16 18), (row3 36 8 36), (row3 39 7 41), (row3 15 13 13), (row3 14 33 28), (row3 17 3 20), (row3 12 35 12), (row3 10 37 9), (row3 27 30 31)]

theorem b000_04_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_04_rows b000_04_labels 289821453608605162232008153570848 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_04_rows b000_04_labels]
    decide +kernel

def b000_05_rows : List Row := [(row3 1 10 15), (row3 1 11 12), (row3 1 11 13), (row3 1 11 14), (row3 1 11 15), (row3 1 12 13), (row3 1 12 14), (row3 1 12 15), (row3 1 13 14), (row3 1 13 15), (row3 1 14 15), (row3 2 3 4), (row3 2 3 5), (row3 2 3 6), (row3 2 3 7), (row3 2 3 8)]

def b000_05_labels : List Row := [(row3 24 16 18), (row3 10 9 37), (row3 12 12 35), (row3 24 18 16), (row3 27 31 30), (row3 6 6 42), (row3 36 36 8), (row3 39 7 41), (row3 39 41 7), (row3 36 8 36), (row3 11 34 32), (row3 41 7 39), (row3 8 36 36), (row3 41 39 7), (row3 5 5 5), (row3 9 37 10)]

theorem b000_05_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_05_rows b000_05_labels 1908793725936689076209188932721056 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_05_rows b000_05_labels]
    decide +kernel

def b000_06_rows : List Row := [(row3 2 3 9), (row3 2 3 10), (row3 2 3 11), (row3 2 3 12), (row3 2 3 13), (row3 2 3 14), (row3 2 3 15), (row3 2 4 5), (row3 2 4 6), (row3 2 4 7), (row3 2 4 8), (row3 2 4 9), (row3 2 4 10), (row3 2 4 11), (row3 2 4 12), (row3 2 4 13)]

def b000_06_labels : List Row := [(row3 35 12 12), (row3 9 10 37), (row3 40 38 38), (row3 41 7 39), (row3 8 36 36), (row3 41 39 7), (row3 5 5 5), (row3 36 36 8), (row3 32 11 34), (row3 36 36 8), (row3 10 37 9), (row3 28 14 33), (row3 18 24 16), (row3 28 14 33), (row3 40 38 38), (row3 13 15 13)]

theorem b000_06_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_06_rows b000_06_labels 473279336209307900911682602660656 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_06_rows b000_06_labels]
    decide +kernel

def b000_07_rows : List Row := [(row3 2 4 14), (row3 2 4 15), (row3 2 5 6), (row3 2 5 7), (row3 2 5 8), (row3 2 5 9), (row3 2 5 10), (row3 2 5 11), (row3 2 5 12), (row3 2 5 13), (row3 2 5 14), (row3 2 5 15), (row3 2 6 7), (row3 2 6 8), (row3 2 6 9), (row3 2 6 10)]

def b000_07_labels : List Row := [(row3 30 27 31), (row3 13 15 13), (row3 36 36 8), (row3 29 29 29), (row3 26 25 26), (row3 15 13 13), (row3 26 26 25), (row3 19 19 19), (row3 13 13 15), (row3 29 29 29), (row3 13 15 13), (row3 25 26 26), (row3 36 8 36), (row3 18 16 24), (row3 28 33 14), (row3 10 9 37)]

theorem b000_07_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_07_rows b000_07_labels 16487231416429629660157438946208 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_07_rows b000_07_labels]
    decide +kernel

def b000_08_rows : List Row := [(row3 2 6 11), (row3 2 6 12), (row3 2 6 13), (row3 2 6 14), (row3 2 6 15), (row3 2 7 8), (row3 2 7 9), (row3 2 7 10), (row3 2 7 11), (row3 2 7 12), (row3 2 7 13), (row3 2 7 14), (row3 2 7 15), (row3 2 8 9), (row3 2 8 10), (row3 2 8 11)]

def b000_08_labels : List Row := [(row3 28 33 14), (row3 30 31 27), (row3 13 13 15), (row3 40 38 38), (row3 13 13 15), (row3 26 25 26), (row3 19 19 19), (row3 26 26 25), (row3 15 13 13), (row3 13 13 15), (row3 25 26 26), (row3 13 15 13), (row3 29 29 29), (row3 24 18 16), (row3 21 21 43), (row3 24 18 16)]

theorem b000_08_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_08_rows b000_08_labels 6031508195889460109860736375280 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_08_rows b000_08_labels]
    decide +kernel

def b000_09_rows : List Row := [(row3 2 8 12), (row3 2 8 13), (row3 2 8 14), (row3 2 8 15), (row3 2 9 10), (row3 2 9 11), (row3 2 9 12), (row3 2 9 13), (row3 2 9 14), (row3 2 9 15), (row3 2 10 11), (row3 2 10 12), (row3 2 10 13), (row3 2 10 14), (row3 2 10 15), (row3 2 11 12)]

def b000_09_labels : List Row := [(row3 10 9 37), (row3 26 26 25), (row3 18 24 16), (row3 26 26 25), (row3 24 18 16), (row3 22 23 23), (row3 28 33 14), (row3 15 13 13), (row3 28 14 33), (row3 19 19 19), (row3 24 16 18), (row3 18 16 24), (row3 26 25 26), (row3 10 37 9), (row3 26 25 26), (row3 28 33 14)]

theorem b000_09_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_09_rows b000_09_labels 4835229082895962354214265887376 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_09_rows b000_09_labels]
    decide +kernel

def b000_10_rows : List Row := [(row3 2 11 13), (row3 2 11 14), (row3 2 11 15), (row3 2 12 13), (row3 2 12 14), (row3 2 12 15), (row3 2 13 14), (row3 2 13 15), (row3 2 14 15), (row3 3 4 5), (row3 3 4 6), (row3 3 4 7), (row3 3 4 8), (row3 3 4 9), (row3 3 4 10), (row3 3 4 11)]

def b000_10_labels : List Row := [(row3 19 19 19), (row3 28 14 33), (row3 15 13 13), (row3 36 36 8), (row3 32 11 34), (row3 36 36 8), (row3 36 36 8), (row3 29 29 29), (row3 36 8 36), (row3 39 7 41), (row3 36 36 8), (row3 6 6 42), (row3 39 7 41), (row3 10 37 9), (row3 12 12 35), (row3 36 36 8)]

theorem b000_10_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_10_rows b000_10_labels 1483452439000408099059500068443648 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_10_rows b000_10_labels]
    decide +kernel

def b000_11_rows : List Row := [(row3 3 4 12), (row3 3 4 13), (row3 3 4 14), (row3 3 4 15), (row3 3 5 6), (row3 3 5 7), (row3 3 5 8), (row3 3 5 9), (row3 3 5 10), (row3 3 5 11), (row3 3 5 12), (row3 3 5 13), (row3 3 5 14), (row3 3 5 15), (row3 3 6 7), (row3 3 6 8)]

def b000_11_labels : List Row := [(row3 5 5 5), (row3 38 38 40), (row3 37 10 9), (row3 7 39 41), (row3 11 32 34), (row3 36 36 8), (row3 15 13 13), (row3 27 30 31), (row3 24 18 16), (row3 14 28 33), (row3 38 40 38), (row3 15 13 13), (row3 14 28 33), (row3 37 10 9), (row3 39 7 41), (row3 14 33 28)]

theorem b000_11_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_11_rows b000_11_labels 462570288116904142639923771427296 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_11_rows b000_11_labels]
    decide +kernel

def b000_12_rows : List Row := [(row3 3 6 9), (row3 3 6 10), (row3 3 6 11), (row3 3 6 12), (row3 3 6 13), (row3 3 6 14), (row3 3 6 15), (row3 3 7 8), (row3 3 7 9), (row3 3 7 10), (row3 3 7 11), (row3 3 7 12), (row3 3 7 13), (row3 3 7 14), (row3 3 7 15), (row3 3 8 9)]

def b000_12_labels : List Row := [(row3 24 16 18), (row3 27 31 30), (row3 15 13 13), (row3 37 9 10), (row3 14 33 28), (row3 15 13 13), (row3 38 38 40), (row3 36 8 36), (row3 12 35 12), (row3 10 9 37), (row3 39 41 7), (row3 7 41 39), (row3 37 9 10), (row3 38 40 38), (row3 5 5 5), (row3 27 30 31)]

theorem b000_12_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_12_rows b000_12_labels 461629409053088705415204099059904 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_12_rows b000_12_labels]
    decide +kernel

def b000_13_rows : List Row := [(row3 3 8 10), (row3 3 8 11), (row3 3 8 12), (row3 3 8 13), (row3 3 8 14), (row3 3 8 15), (row3 3 9 10), (row3 3 9 11), (row3 3 9 12), (row3 3 9 13), (row3 3 9 14), (row3 3 9 15), (row3 3 10 11), (row3 3 10 12), (row3 3 10 13), (row3 3 10 14)]

def b000_13_labels : List Row := [(row3 24 18 16), (row3 11 32 34), (row3 39 41 7), (row3 15 13 13), (row3 14 28 33), (row3 36 36 8), (row3 17 20 3), (row3 24 18 16), (row3 10 9 37), (row3 27 31 30), (row3 24 18 16), (row3 12 12 35), (row3 27 30 31), (row3 12 35 12), (row3 24 16 18), (row3 27 30 31)]

theorem b000_13_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_13_rows b000_13_labels 152125181407228205205506732922768 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_13_rows b000_13_labels]
    decide +kernel

def b000_14_rows : List Row := [(row3 3 10 15), (row3 3 11 12), (row3 3 11 13), (row3 3 11 14), (row3 3 11 15), (row3 3 12 13), (row3 3 12 14), (row3 3 12 15), (row3 3 13 14), (row3 3 13 15), (row3 3 14 15), (row3 4 5 6), (row3 4 5 7), (row3 4 5 8), (row3 4 5 9), (row3 4 5 10)]

def b000_14_labels : List Row := [(row3 10 37 9), (row3 36 8 36), (row3 14 33 28), (row3 15 13 13), (row3 39 7 41), (row3 39 7 41), (row3 36 36 8), (row3 6 6 42), (row3 11 32 34), (row3 36 36 8), (row3 39 7 41), (row3 39 41 7), (row3 5 5 5), (row3 5 5 5), (row3 39 41 7), (row3 10 9 37)]

theorem b000_14_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_14_rows b000_14_labels 2212526867885748937282957975583136 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_14_rows b000_14_labels]
    decide +kernel

def b000_15_rows : List Row := [(row3 4 5 11), (row3 4 5 12), (row3 4 5 13), (row3 4 5 14), (row3 4 5 15), (row3 4 6 7), (row3 4 6 8), (row3 4 6 9), (row3 4 6 10), (row3 4 6 11), (row3 4 6 12), (row3 4 6 13), (row3 4 6 14), (row3 4 6 15), (row3 4 7 8), (row3 4 7 9)]

def b000_15_labels : List Row := [(row3 38 40 38), (row3 7 41 39), (row3 36 8 36), (row3 12 35 12), (row3 37 9 10), (row3 39 7 41), (row3 38 38 40), (row3 15 13 13), (row3 27 31 30), (row3 15 13 13), (row3 37 9 10), (row3 14 33 28), (row3 24 16 18), (row3 14 33 28), (row3 5 5 5), (row3 38 40 38)]

theorem b000_15_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b000_15_rows b000_15_labels 461746527976871272311375414296976 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b000_15_rows b000_15_labels]
    decide +kernel

def rows000 : List Row := ((((b000_00_rows ++ b000_01_rows) ++ (b000_02_rows ++ b000_03_rows)) ++ ((b000_04_rows ++ b000_05_rows) ++ (b000_06_rows ++ b000_07_rows))) ++ (((b000_08_rows ++ b000_09_rows) ++ (b000_10_rows ++ b000_11_rows)) ++ ((b000_12_rows ++ b000_13_rows) ++ (b000_14_rows ++ b000_15_rows))))

def labels000 : List Row := ((((b000_00_labels ++ b000_01_labels) ++ (b000_02_labels ++ b000_03_labels)) ++ ((b000_04_labels ++ b000_05_labels) ++ (b000_06_labels ++ b000_07_labels))) ++ (((b000_08_labels ++ b000_09_labels) ++ (b000_10_labels ++ b000_11_labels)) ++ ((b000_12_labels ++ b000_13_labels) ++ (b000_14_labels ++ b000_15_labels))))

theorem checked000 : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 rows000 labels000 13285610089535688093438224422540752 := by
  change Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
    ((((b000_00_rows ++ b000_01_rows) ++ (b000_02_rows ++ b000_03_rows)) ++ ((b000_04_rows ++ b000_05_rows) ++ (b000_06_rows ++ b000_07_rows))) ++ (((b000_08_rows ++ b000_09_rows) ++ (b000_10_rows ++ b000_11_rows)) ++ ((b000_12_rows ++ b000_13_rows) ++ (b000_14_rows ++ b000_15_rows))))
    ((((b000_00_labels ++ b000_01_labels) ++ (b000_02_labels ++ b000_03_labels)) ++ ((b000_04_labels ++ b000_05_labels) ++ (b000_06_labels ++ b000_07_labels))) ++ (((b000_08_labels ++ b000_09_labels) ++ (b000_10_labels ++ b000_11_labels)) ++ ((b000_12_labels ++ b000_13_labels) ++ (b000_14_labels ++ b000_15_labels)))) 13285610089535688093438224422540752
  exact ((((b000_00_checked.append (c := 4425023280385994921539808918816400) b000_01_checked (by decide +kernel)).append (c := 5352310891645621540046644230645600) (b000_02_checked.append (c := 927287611259626618506835311829200) b000_03_checked (by decide +kernel)) (by decide +kernel)).append (c := 8040692638816653309059681358544368) ((b000_04_checked.append (c := 2198615179545294238441197086291904) b000_05_checked (by decide +kernel)).append (c := 2688381747171031769013037127898768) (b000_06_checked.append (c := 489766567625737530571840041606864) b000_07_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 13285610089535688093438224422540752) (((b000_08_checked.append (c := 10866737278785422464075002262656) b000_09_checked (by decide +kernel)).append (c := 1956889464396097664163498842133600) (b000_10_checked.append (c := 1946022727117312241699423839870944) b000_11_checked (by decide +kernel)) (by decide +kernel)).append (c := 5244917450719034784378543063996384) ((b000_12_checked.append (c := 613754590460316910620710831982672) b000_13_checked (by decide +kernel)).append (c := 3288027986322937120215044221862784) (b000_14_checked.append (c := 2674273395862620209594333389880112) b000_15_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals16

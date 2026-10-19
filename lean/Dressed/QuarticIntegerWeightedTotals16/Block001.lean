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

def b001_00_rows : List Row := [(row3 4 7 10), (row3 4 7 11), (row3 4 7 12), (row3 4 7 13), (row3 4 7 14), (row3 4 7 15), (row3 4 8 9), (row3 4 8 10), (row3 4 8 11), (row3 4 8 12), (row3 4 8 13), (row3 4 8 14), (row3 4 8 15), (row3 4 9 10), (row3 4 9 11), (row3 4 9 12)]

def b001_00_labels : List Row := [(row3 10 9 37), (row3 39 41 7), (row3 7 41 39), (row3 37 9 10), (row3 12 35 12), (row3 36 8 36), (row3 39 41 7), (row3 10 9 37), (row3 39 41 7), (row3 6 42 6), (row3 36 8 36), (row3 12 35 12), (row3 36 8 36), (row3 27 31 30), (row3 15 13 13), (row3 36 8 36)]

theorem b001_00_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_00_rows b001_00_labels 1744357425932894308160284607595504 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_00_rows b001_00_labels]
    decide +kernel

def b001_01_rows : List Row := [(row3 4 9 13), (row3 4 9 14), (row3 4 9 15), (row3 4 10 11), (row3 4 10 12), (row3 4 10 13), (row3 4 10 14), (row3 4 10 15), (row3 4 11 12), (row3 4 11 13), (row3 4 11 14), (row3 4 11 15), (row3 4 12 13), (row3 4 12 14), (row3 4 12 15), (row3 4 13 14)]

def b001_01_labels : List Row := [(row3 11 34 32), (row3 24 16 18), (row3 14 33 28), (row3 27 30 31), (row3 12 35 12), (row3 24 16 18), (row3 17 3 20), (row3 24 16 18), (row3 36 8 36), (row3 14 33 28), (row3 24 16 18), (row3 11 34 32), (row3 39 7 41), (row3 10 37 9), (row3 39 7 41), (row3 27 30 31)]

theorem b001_01_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_01_rows b001_01_labels 290449173303877281607368484893168 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_01_rows b001_01_labels]
    decide +kernel

def b001_02_rows : List Row := [(row3 4 13 15), (row3 4 14 15), (row3 5 6 7), (row3 5 6 8), (row3 5 6 9), (row3 5 6 10), (row3 5 6 11), (row3 5 6 12), (row3 5 6 13), (row3 5 6 14), (row3 5 6 15), (row3 5 7 8), (row3 5 7 9), (row3 5 7 10), (row3 5 7 11), (row3 5 7 12)]

def b001_02_labels : List Row := [(row3 15 13 13), (row3 27 31 30), (row3 36 8 36), (row3 13 13 15), (row3 40 38 38), (row3 10 9 37), (row3 28 33 14), (row3 30 31 27), (row3 13 13 15), (row3 28 33 14), (row3 18 16 24), (row3 29 29 29), (row3 13 15 13), (row3 26 26 25), (row3 15 13 13), (row3 13 13 15)]

theorem b001_02_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_02_rows b001_02_labels 15322161029077335841883728786128 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_02_rows b001_02_labels]
    decide +kernel

def b001_03_rows : List Row := [(row3 5 7 13), (row3 5 7 14), (row3 5 7 15), (row3 5 8 9), (row3 5 8 10), (row3 5 8 11), (row3 5 8 12), (row3 5 8 13), (row3 5 8 14), (row3 5 8 15), (row3 5 9 10), (row3 5 9 11), (row3 5 9 12), (row3 5 9 13), (row3 5 9 14), (row3 5 9 15)]

def b001_03_labels : List Row := [(row3 25 26 26), (row3 19 19 19), (row3 26 25 26), (row3 36 36 8), (row3 26 26 25), (row3 15 13 13), (row3 36 8 36), (row3 29 29 29), (row3 19 19 19), (row3 26 25 26), (row3 10 9 37), (row3 28 33 14), (row3 32 34 11), (row3 36 8 36), (row3 28 33 14), (row3 18 16 24)]

theorem b001_03_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_03_rows b001_03_labels 24499612117094495837755896007488 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_03_rows b001_03_labels]
    decide +kernel

def b001_04_rows : List Row := [(row3 5 10 11), (row3 5 10 12), (row3 5 10 13), (row3 5 10 14), (row3 5 10 15), (row3 5 11 12), (row3 5 11 13), (row3 5 11 14), (row3 5 11 15), (row3 5 12 13), (row3 5 12 14), (row3 5 12 15), (row3 5 13 14), (row3 5 13 15), (row3 5 14 15), (row3 6 7 8)]

def b001_04_labels : List Row := [(row3 24 16 18), (row3 18 16 24), (row3 26 25 26), (row3 24 16 18), (row3 21 43 21), (row3 28 33 14), (row3 19 19 19), (row3 22 23 23), (row3 24 16 18), (row3 36 36 8), (row3 28 14 33), (row3 10 37 9), (row3 15 13 13), (row3 26 25 26), (row3 24 16 18), (row3 13 13 15)]

theorem b001_04_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_04_rows b001_04_labels 9016407976762450318451441996448 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_04_rows b001_04_labels]
    decide +kernel

def b001_05_rows : List Row := [(row3 6 7 9), (row3 6 7 10), (row3 6 7 11), (row3 6 7 12), (row3 6 7 13), (row3 6 7 14), (row3 6 7 15), (row3 6 8 9), (row3 6 8 10), (row3 6 8 11), (row3 6 8 12), (row3 6 8 13), (row3 6 8 14), (row3 6 8 15), (row3 6 9 10), (row3 6 9 11)]

def b001_05_labels : List Row := [(row3 33 28 14), (row3 9 10 37), (row3 38 40 38), (row3 31 30 27), (row3 16 18 24), (row3 33 28 14), (row3 13 13 15), (row3 14 28 33), (row3 18 24 16), (row3 14 28 33), (row3 12 35 12), (row3 19 19 19), (row3 23 22 23), (row3 19 19 19), (row3 12 12 35), (row3 19 19 19)]

theorem b001_05_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_05_rows b001_05_labels 7436335449639831961846225711008 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_05_rows b001_05_labels]
    decide +kernel

def b001_06_rows : List Row := [(row3 6 9 12), (row3 6 9 13), (row3 6 9 14), (row3 6 9 15), (row3 6 10 11), (row3 6 10 12), (row3 6 10 13), (row3 6 10 14), (row3 6 10 15), (row3 6 11 12), (row3 6 11 13), (row3 6 11 14), (row3 6 11 15), (row3 6 12 13), (row3 6 12 14), (row3 6 12 15)]

def b001_06_labels : List Row := [(row3 18 16 24), (row3 14 33 28), (row3 19 19 19), (row3 23 23 22), (row3 12 35 12), (row3 20 3 17), (row3 18 16 24), (row3 12 35 12), (row3 18 16 24), (row3 18 16 24), (row3 23 23 22), (row3 19 19 19), (row3 14 33 28), (row3 12 12 35), (row3 18 24 16), (row3 12 12 35)]

theorem b001_06_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_06_rows b001_06_labels 1715233930041469991208246095040 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_06_rows b001_06_labels]
    decide +kernel

def b001_07_rows : List Row := [(row3 6 13 14), (row3 6 13 15), (row3 6 14 15), (row3 7 8 9), (row3 7 8 10), (row3 7 8 11), (row3 7 8 12), (row3 7 8 13), (row3 7 8 14), (row3 7 8 15), (row3 7 9 10), (row3 7 9 11), (row3 7 9 12), (row3 7 9 13), (row3 7 9 14), (row3 7 9 15)]

def b001_07_labels : List Row := [(row3 14 28 33), (row3 19 19 19), (row3 14 33 28), (row3 15 13 13), (row3 26 26 25), (row3 36 36 8), (row3 36 8 36), (row3 26 25 26), (row3 19 19 19), (row3 29 29 29), (row3 24 18 16), (row3 28 14 33), (row3 28 33 14), (row3 24 16 18), (row3 22 23 23), (row3 19 19 19)]

theorem b001_07_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_07_rows b001_07_labels 12674524427002532851009352173440 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_07_rows b001_07_labels]
    decide +kernel

def b001_08_rows : List Row := [(row3 7 10 11), (row3 7 10 12), (row3 7 10 13), (row3 7 10 14), (row3 7 10 15), (row3 7 11 12), (row3 7 11 13), (row3 7 11 14), (row3 7 11 15), (row3 7 12 13), (row3 7 12 14), (row3 7 12 15), (row3 7 13 14), (row3 7 13 15), (row3 7 14 15), (row3 8 9 10)]

def b001_08_labels : List Row := [(row3 10 37 9), (row3 18 16 24), (row3 21 43 21), (row3 24 16 18), (row3 26 25 26), (row3 32 34 11), (row3 18 16 24), (row3 28 33 14), (row3 36 8 36), (row3 10 37 9), (row3 28 14 33), (row3 36 36 8), (row3 24 18 16), (row3 26 26 25), (row3 15 13 13), (row3 10 9 37)]

theorem b001_08_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_08_rows b001_08_labels 22643519285199039851086722425664 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_08_rows b001_08_labels]
    decide +kernel

def b001_09_rows : List Row := [(row3 8 9 11), (row3 8 9 12), (row3 8 9 13), (row3 8 9 14), (row3 8 9 15), (row3 8 10 11), (row3 8 10 12), (row3 8 10 13), (row3 8 10 14), (row3 8 10 15), (row3 8 11 12), (row3 8 11 13), (row3 8 11 14), (row3 8 11 15), (row3 8 12 13), (row3 8 12 14)]

def b001_09_labels : List Row := [(row3 40 38 38), (row3 41 7 39), (row3 36 8 36), (row3 28 33 14), (row3 13 13 15), (row3 10 37 9), (row3 9 37 10), (row3 26 25 26), (row3 24 16 18), (row3 26 25 26), (row3 41 7 39), (row3 13 13 15), (row3 28 33 14), (row3 36 8 36), (row3 5 5 5), (row3 40 38 38)]

theorem b001_09_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_09_rows b001_09_labels 463348952195244217066066456898976 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_09_rows b001_09_labels]
    decide +kernel

def b001_10_rows : List Row := [(row3 8 12 15), (row3 8 13 14), (row3 8 13 15), (row3 8 14 15), (row3 9 10 11), (row3 9 10 12), (row3 9 10 13), (row3 9 10 14), (row3 9 10 15), (row3 9 11 12), (row3 9 11 13), (row3 9 11 14), (row3 9 11 15), (row3 9 12 13), (row3 9 12 14), (row3 9 12 15)]

def b001_10_labels : List Row := [(row3 5 5 5), (row3 15 13 13), (row3 29 29 29), (row3 15 13 13), (row3 12 35 12), (row3 31 30 27), (row3 9 37 10), (row3 12 35 12), (row3 18 16 24), (row3 13 13 15), (row3 33 14 28), (row3 19 19 19), (row3 14 33 28), (row3 7 39 41), (row3 13 15 13), (row3 38 38 40)]

theorem b001_10_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_10_rows b001_10_labels 312992831425272332691610815375408 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_10_rows b001_10_labels]
    decide +kernel

def b001_11_rows : List Row := [(row3 9 13 14), (row3 9 13 15), (row3 9 14 15), (row3 10 11 12), (row3 10 11 13), (row3 10 11 14), (row3 10 11 15), (row3 10 12 13), (row3 10 12 14), (row3 10 12 15), (row3 10 13 14), (row3 10 13 15), (row3 10 14 15), (row3 11 12 13), (row3 11 12 14), (row3 11 12 15)]

def b001_11_labels : List Row := [(row3 38 40 38), (row3 13 13 15), (row3 14 33 28), (row3 30 31 27), (row3 16 18 24), (row3 35 12 12), (row3 37 9 10), (row3 37 10 9), (row3 30 27 31), (row3 37 10 9), (row3 37 10 9), (row3 25 26 26), (row3 37 9 10), (row3 38 38 40), (row3 13 15 13), (row3 7 39 41)]

theorem b001_11_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_11_rows b001_11_labels 155069423223811885736142852482640 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_11_rows b001_11_labels]
    decide +kernel

def b001_12_rows : List Row := [(row3 11 13 14), (row3 11 13 15), (row3 11 14 15), (row3 12 13 14), (row3 12 13 15), (row3 12 14 15), (row3 13 14 15)]

def b001_12_labels : List Row := [(row3 14 28 33), (row3 13 15 13), (row3 38 38 40), (row3 39 41 7), (row3 5 5 5), (row3 39 7 41), (row3 36 8 36)]

theorem b001_12_checked : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 b001_12_rows b001_12_labels 449876643516988881199569420838560 := by
  constructor
  · decide +kernel
  · rw [weightedList_eq_guarded 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
      QuarticIntegerWeightedTotalsLookups.covariance16 QuarticIntegerWeightedTotalsLookups.upper16
      QuarticIntegerWeightedTotalsLookups.covariance16_eq QuarticIntegerWeightedTotalsLookups.upper16_eq
      b001_12_rows b001_12_labels]
    decide +kernel

def rows001 : List Row := (((b001_00_rows ++ (b001_01_rows ++ b001_02_rows)) ++ (b001_03_rows ++ (b001_04_rows ++ b001_05_rows))) ++ ((b001_06_rows ++ (b001_07_rows ++ b001_08_rows)) ++ ((b001_09_rows ++ b001_10_rows) ++ (b001_11_rows ++ b001_12_rows))))

def labels001 : List Row := (((b001_00_labels ++ (b001_01_labels ++ b001_02_labels)) ++ (b001_03_labels ++ (b001_04_labels ++ b001_05_labels))) ++ ((b001_06_labels ++ (b001_07_labels ++ b001_08_labels)) ++ ((b001_09_labels ++ b001_10_labels) ++ (b001_11_labels ++ b001_12_labels))))

theorem checked001 : Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16
    upperNumerators16 rows001 labels001 3509402243812906063114284251279472 := by
  change Block 2 2 QuarticIntegerCovarianceData.covarianceNumerators16 upperNumerators16
    (((b001_00_rows ++ (b001_01_rows ++ b001_02_rows)) ++ (b001_03_rows ++ (b001_04_rows ++ b001_05_rows))) ++ ((b001_06_rows ++ (b001_07_rows ++ b001_08_rows)) ++ ((b001_09_rows ++ b001_10_rows) ++ (b001_11_rows ++ b001_12_rows))))
    (((b001_00_labels ++ (b001_01_labels ++ b001_02_labels)) ++ (b001_03_labels ++ (b001_04_labels ++ b001_05_labels))) ++ ((b001_06_labels ++ (b001_07_labels ++ b001_08_labels)) ++ ((b001_09_labels ++ b001_10_labels) ++ (b001_11_labels ++ b001_12_labels)))) 3509402243812906063114284251279472
  exact (((b001_00_checked.append (c := 2050128760265848925609536821274800) (b001_01_checked.append (c := 305771334332954617449252213679296) b001_02_checked (by decide +kernel)) (by decide +kernel)).append (c := 2091081115809345703727590384989744) (b001_03_checked.append (c := 40952355543496778118053563714944) (b001_04_checked.append (c := 16452743426402282280297667707456) b001_05_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (c := 3509402243812906063114284251279472) ((b001_06_checked.append (c := 37033277642243042693304320694144) (b001_07_checked.append (c := 35318043712201572702096074599104) b001_08_checked (by decide +kernel)) (by decide +kernel)).append (c := 1418321128003560359386693866289728) ((b001_09_checked.append (c := 776341783620516549757677272274384) b001_10_checked (by decide +kernel)).append (c := 1381287850361317316693389545595584) (b001_11_checked.append (c := 604946066740800766935712273321200) b001_12_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end BilayerDressed.QuarticIntegerWeightedTotals16

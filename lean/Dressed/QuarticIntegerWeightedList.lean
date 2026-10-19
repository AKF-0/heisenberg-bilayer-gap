import Dressed.QuarticIntegerMeanEvaluation
import Mathlib.Data.List.OfFn

/-! The exact weighted integer sum is a structural zip-fold of the aligned row
and ID lists. This is only a change of representation, not a numerical estimate. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerWeightedList
open BilayerGap QuarticRootedRowTable QuarticIntegerCovariance QuarticIntegerMeanEvaluation
set_option maxHeartbeats 1000000

theorem sum_getD_zip {α β γ : Type*} [AddCommMonoid γ]
    (xs : Array α) (ys : Array β) (dx : α) (dy : β) (f : α→β→γ)
    (R : ℕ) (hx : xs.size=R) (hy : ys.size=R) :
    (∑ i : Fin R,f (xs.getD i.val dx) (ys.getD i.val dy))=
      (List.zipWith f xs.toList ys.toList).sum := by
  rw [←List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [hx,hy]
  · intro i hi hj
    have hxi : i < xs.size := by simpa [hx] using hi
    have hyi : i < ys.size := by simpa [hy] using hi
    simp [Array.getD,hxi,hyi]

variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def rowWeight (nums upper : Array ℤ) (r labels : Row) : ℤ :=
  ∑ a : Fin 3,upper.getD (labels a) 0 *
    matchingWeightNumerator n m nums (sites n m r) a

def weightedList (nums upper : Array ℤ) (raw ids : List Row) : ℤ :=
  (List.zipWith (rowWeight n m nums upper) raw ids).sum

theorem weightedList_append (nums upper : Array ℤ) (rs rt ls lt : List Row)
    (hlen : rs.length=ls.length) :
    weightedList n m nums upper (rs++rt) (ls++lt)=
      weightedList n m nums upper rs ls+weightedList n m nums upper rt lt := by
  unfold weightedList
  rw [List.zipWith_append hlen,List.sum_append]

theorem weightedNumerator_eq_list (R : ℕ) (raw : Array Row) (nums upper : Array ℤ)
    (ids : Array Row) (hr : raw.size=R) (hi : ids.size=R) :
    weightedNumerator n m R raw nums upper ids=
      weightedList n m nums upper raw.toList ids.toList := by
  exact sum_getD_zip raw ids 0 0 (rowWeight n m nums upper) R hr hi

end BilayerDressed.QuarticIntegerWeightedList

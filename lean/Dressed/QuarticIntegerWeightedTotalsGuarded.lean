import Dressed.QuarticIntegerWeightedTotalsLookups

/-! A zero envelope has exactly zero weighted contribution. An explicit branch
avoids evaluating unused covariance entries, without deleting any row or label. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerWeightedTotals
open QuarticRootedRowTable QuarticIntegerWeightedList
set_option maxHeartbeats 800000
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def guardedRowWeight (nums upper : ℕ→ℤ) (r labels : Row) : ℤ :=
  ∑ a : Fin 3,if upper (labels a)=0 then 0 else
    upper (labels a)*lookupMatchingWeight n m nums (sites n m r) a

def guardedWeightedList (nums upper : ℕ→ℤ) (rows labels : List Row) : ℤ :=
  (List.zipWith (guardedRowWeight n m nums upper) rows labels).sum

theorem lookupWeightedList_eq_guarded (nums upper : ℕ→ℤ) (rows labels : List Row) :
    lookupWeightedList n m nums upper rows labels =
      guardedWeightedList n m nums upper rows labels := by
  have hf : lookupRowWeight n m nums upper=guardedRowWeight n m nums upper := by
    funext r ls
    unfold lookupRowWeight guardedRowWeight
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : upper (ls a)=0 <;> simp [h]
  simp only [lookupWeightedList,guardedWeightedList,hf]

/-- Exact replacement, with no row-validity or positive-weight premise. -/
theorem weightedList_eq_guarded (nums upper : Array ℤ) (nc uc : ℕ→ℤ)
    (hn : ∀ i,nums.getD i 0=nc i) (hu : ∀ i,upper.getD i 0=uc i)
    (rows labels : List Row) :
    weightedList n m nums upper rows labels =
      guardedWeightedList n m nc uc rows labels := by
  rw [weightedList_eq_lookup n m nums upper nc uc hn hu,
    lookupWeightedList_eq_guarded]

end BilayerDressed.QuarticIntegerWeightedTotals

import Dressed.QuarticIntegerWeightedList

/-! Exact weighted totals compose from bounded aligned list folds. The sum is
never replaced by a numerical assumption or a sampled estimate. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerWeightedTotals
open QuarticRootedRowTable QuarticIntegerWeightedList
set_option maxHeartbeats 800000

/-- A bounded fold certificate records both alignment and its exact integer sum. -/
structure Block (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]
    (nums upper : Array ℤ) (rows labels : List Row) (total : ℤ) : Prop where
  length_eq : rows.length = labels.length
  total_eq : weightedList n m nums upper rows labels = total

/-- Balanced compositions preserve all rows, labels, and integer weights. -/
theorem Block.append {n m : ℕ} [NeZero (2*n)] [NeZero (2*m)]
    {nums upper : Array ℤ} {rs rt ls lt : List Row} {a b c : ℤ}
    (hs : Block n m nums upper rs ls a) (ht : Block n m nums upper rt lt b)
    (hadd : a+b=c) : Block n m nums upper (rs++rt) (ls++lt) c where
  length_eq := by simp only [List.length_append, hs.length_eq, ht.length_eq]
  total_eq := by
    rw [weightedList_append n m nums upper rs rt ls lt hs.length_eq,
      hs.total_eq, ht.total_eq, hadd]

end BilayerDressed.QuarticIntegerWeightedTotals

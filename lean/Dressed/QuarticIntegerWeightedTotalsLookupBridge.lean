import Dressed.QuarticIntegerWeightedTotalsBridge

/-! Exact replacement of finite-array lookups by proved lookup functions. This
changes only evaluation cost, never the integer weights or the rows. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerWeightedTotals
open BilayerGap QuarticRootedRowTable QuarticIntegerCovariance
open QuarticIntegerWeightedList QuarticPhysicalMean
set_option maxHeartbeats 800000

variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def lookupCovariance (nums : ℕ→ℤ) (u v : Torus.Vertex n m) : ℤ :=
  nums (QuarticRowMajor.index n m (v-u)).val

def lookupMatchingWeight (nums : ℕ→ℤ) (v : Fin 4→Torus.Vertex n m)
    (label : Fin 3) : ℤ :=
  let w := pairedSites v label
  9*lookupCovariance n m nums (w 0) (w 1)*lookupCovariance n m nums (w 2) (w 3)+
  3*lookupCovariance n m nums (w 0) (w 2)*lookupCovariance n m nums (w 1) (w 3)+
  3*lookupCovariance n m nums (w 0) (w 3)*lookupCovariance n m nums (w 1) (w 2)

def lookupRowWeight (nums upper : ℕ→ℤ) (r labels : Row) : ℤ :=
  ∑ a : Fin 3,upper (labels a) * lookupMatchingWeight n m nums (sites n m r) a

def lookupWeightedList (nums upper : ℕ→ℤ) (rows labels : List Row) : ℤ :=
  (List.zipWith (lookupRowWeight n m nums upper) rows labels).sum

/-- Pointwise exact lookup identities suffice, including default indices. -/
theorem weightedList_eq_lookup (nums upper : Array ℤ) (nc uc : ℕ→ℤ)
    (hn : ∀ i,nums.getD i 0=nc i) (hu : ∀ i,upper.getD i 0=uc i)
    (rows labels : List Row) :
    weightedList n m nums upper rows labels =
      lookupWeightedList n m nc uc rows labels := by
  have hf : rowWeight n m nums upper = lookupRowWeight n m nc uc := by
    funext r ls
    simp only [rowWeight,lookupRowWeight,matchingWeightNumerator,
      lookupMatchingWeight,cachedNumerator,lookupCovariance,hn,hu]
  simp only [weightedList,lookupWeightedList,hf]

end BilayerDressed.QuarticIntegerWeightedTotals

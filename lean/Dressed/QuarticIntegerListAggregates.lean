import Dressed.QuarticIntegerTable
import Dressed.QuarticIntegerCovarianceCache
import Mathlib.Data.List.OfFn

/-! Exact list-fold forms of the finite integer aggregates. These avoid repeated
linear Array indexing inside the kernel's numerical verification. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerListAggregates
open QuarticIntegerArrays QuarticRootedRowTable QuarticIntegerTable
set_option maxHeartbeats 1000000

/-- A generic array-indexed sum is the same as one linear list traversal. -/
theorem sum_getD_eq_list_sum {α β : Type*} [AddCommMonoid β]
    (xs : Array α) (fallback : α) (f : α→β) (R : ℕ) (hsize : xs.size=R) :
    (∑ i : Fin R,f (xs.getD i.val fallback))=(xs.toList.map f).sum := by
  subst R
  rw [←List.sum_ofFn]
  congr 1
  have he : List.ofFn (fun i : Fin xs.size=>xs.getD i.val fallback)=xs.toList := by
    conv_lhs => arg 1; ext i; rw [Array.getD,dif_pos i.isLt]
    exact List.ofFn_get xs.toList
  rw [List.ofFn_comp',he]

/-- Signed Gram coefficients, accumulated by a single structural fold. -/
def gramList (dictionary : Array Coefficients) (ids : List Row) : QuarticIntegerNorm.NormCoefficients :=
  (ids.map (fun labels=>QuarticIntegerNorm.gram (fun a=>dictionary.getD (labels a) 0))).sum

theorem gramList_append (dictionary : Array Coefficients) (xs ys : List Row) :
    gramList dictionary (xs++ys)=gramList dictionary xs+gramList dictionary ys := by
  simp [gramList,List.map_append,List.sum_append]

theorem normCoefficients_eq_gramList (R b : ℕ) (dictionary : Array Coefficients) (ids : Array Row)
    (hsize : ids.size=R) :
    normCoefficients R dictionary ids b=b • gramList dictionary ids.toList := by
  unfold normCoefficients gramList
  congr 1
  exact sum_getD_eq_list_sum ids 0
    (fun labels=>QuarticIntegerNorm.gram (fun a=>dictionary.getD (labels a) 0)) R hsize

end BilayerDressed.QuarticIntegerListAggregates

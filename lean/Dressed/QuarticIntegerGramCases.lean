import Dressed.QuarticIntegerListAggregates

/-! Reusable literal Gram entries are justified by exact signed dictionary
lookups. This avoids reevaluating a dictionary during every convolution. -/
namespace BilayerDressed.QuarticIntegerListAggregates
open QuarticIntegerArrays QuarticRootedRowTable QuarticIntegerNorm

theorem gram_eq_of_entries (dictionary : Array Coefficients) (labels : Row)
    (a b c : Coefficients)
    (h0 : dictionary.getD (labels 0) 0=a)
    (h1 : dictionary.getD (labels 1) 0=b)
    (h2 : dictionary.getD (labels 2) 0=c) :
    gram (fun i=>dictionary.getD (labels i) 0)=gram ![a,b,c] := by
  congr 1
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end BilayerDressed.QuarticIntegerListAggregates

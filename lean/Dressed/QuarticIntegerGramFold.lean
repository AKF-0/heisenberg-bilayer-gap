import Dressed.QuarticIntegerListAggregates

/-! One-step structural fold rules permit bounded signed Gram certificates
without unfolding a complete global row table. -/
namespace BilayerDressed.QuarticIntegerListAggregates
open QuarticIntegerArrays QuarticRootedRowTable

theorem gramList_nil (dictionary : Array Coefficients) : gramList dictionary []=0 := by
  simp only [gramList,List.map_nil,List.sum_nil]

theorem gramList_cons (dictionary : Array Coefficients) (labels : Row) (tail : List Row) :
    gramList dictionary (labels::tail)=
      QuarticIntegerNorm.gram (fun a=>dictionary.getD (labels a) 0)+gramList dictionary tail := by
  simp only [gramList,List.map_cons,List.sum_cons]

end BilayerDressed.QuarticIntegerListAggregates

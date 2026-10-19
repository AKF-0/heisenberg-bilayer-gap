import Dressed.QuarticIntegerThreeMatching
import Dressed.QuarticIntegerDataConstructors

/-!
# Literal matching-tuple adapter for exact signed coefficient certificates

The three small tuple equalities are proved before placing the tuple under the
actual forward coefficient. This prevents concrete definitional matching from
normalizing an entire closed coefficient merely to identify two presentations
of the same four sites. The returned `Matches` relation and all three signed
coefficient premises are unchanged. Finite site indices retain their bounds;
no additional validity, symmetry, or numerical coefficient premise is introduced.
-/
namespace BilayerDressed.QuarticIntegerListCertificate
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
set_option maxHeartbeats 1000000

variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

theorem matching0_literal (a b c : Fin ((2*n)*(2*m))) :
    matching n m (row3 a.val b.val c.val) 0 =
      fun i => (QuarticRowMajor.index n m).symm ((![0,a,b,c]) i) := by
  funext i
  fin_cases i <;>
    simp [matching,QuarticRootedRowTable.sites,QuarticRootedRowTable.values,row3]

theorem matching1_literal (a b c : Fin ((2*n)*(2*m))) :
    matching n m (row3 a.val b.val c.val) 1 =
      fun i => (QuarticRowMajor.index n m).symm ((![0,b,a,c]) i) := by
  funext i
  fin_cases i <;>
    simp [matching,QuarticRootedRowTable.sites,QuarticRootedRowTable.values,row3]

theorem matching2_literal (a b c : Fin ((2*n)*(2*m))) :
    matching n m (row3 a.val b.val c.val) 2 =
      fun i => (QuarticRowMajor.index n m).symm ((![0,c,a,b]) i) := by
  funext i
  fin_cases i <;>
    simp [matching,QuarticRootedRowTable.sites,QuarticRootedRowTable.values,row3]

theorem matches_of_literal_row3 (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
    (a b c : Fin ((2*n)*(2*m))) (x y z : ℕ)
    (h0 : forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m)
      (fun i => (QuarticRowMajor.index n m).symm ((![0,a,b,c]) i))=dictionary.getD x 0)
    (h1 : forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m)
      (fun i => (QuarticRowMajor.index n m).symm ((![0,b,a,c]) i))=dictionary.getD y 0)
    (h2 : forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m)
      (fun i => (QuarticRowMajor.index n m).symm ((![0,c,a,b]) i))=dictionary.getD z 0) :
    Matches n m kd dictionary (row3 a.val b.val c.val) (row3 x y z) := by
  apply matches_of_three n m kd dictionary
  · rw [matching0_literal]
    exact h0
  · rw [matching1_literal]
    exact h1
  · rw [matching2_literal]
    exact h2

end BilayerDressed.QuarticIntegerListCertificate

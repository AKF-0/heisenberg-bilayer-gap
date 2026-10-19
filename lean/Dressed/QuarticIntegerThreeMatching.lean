import Dressed.QuarticIntegerListCertificate

/-! Abstract three-column assembly keeps concrete finite computations separate
from finite-case elaboration. The accepted relation is unchanged. -/
namespace BilayerDressed.QuarticIntegerListCertificate
open BilayerGap QuarticIntegerArrays QuarticRootedRowTable
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

theorem matches_of_three (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
    (r labels : Row)
    (h0 : QuarticIntegerDirect.forward (cachedKernel n m kd)
      (Torus.xNext n m) (Torus.yNext n m) (matching n m r 0)=dictionary.getD (labels 0) 0)
    (h1 : QuarticIntegerDirect.forward (cachedKernel n m kd)
      (Torus.xNext n m) (Torus.yNext n m) (matching n m r 1)=dictionary.getD (labels 1) 0)
    (h2 : QuarticIntegerDirect.forward (cachedKernel n m kd)
      (Torus.xNext n m) (Torus.yNext n m) (matching n m r 2)=dictionary.getD (labels 2) 0) :
    Matches n m kd dictionary r labels := by
  intro a
  fin_cases a
  · exact h0
  · exact h1
  · exact h2

end BilayerDressed.QuarticIntegerListCertificate

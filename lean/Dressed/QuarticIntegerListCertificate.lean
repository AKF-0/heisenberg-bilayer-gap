import Dressed.QuarticIntegerTable
import Mathlib.Data.List.Forall2

/-! Linear structural certificates avoid repeatedly indexing the full row list.
Forall₂ keeps raw rows and dictionary IDs aligned; its get theorem derives the
unchanged all-index Checked relation used by the physical proof. -/
namespace BilayerDressed.QuarticIntegerListCertificate
open BilayerGap QuarticIntegerArrays QuarticRootedRowTable QuarticIntegerTable
set_option maxHeartbeats 800000
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def matching (r : Row) (a : Fin 3) : Fin 4→Torus.Vertex n m :=
  let s := sites n m r
  (![![s 0,s 1,s 2,s 3],![s 0,s 2,s 1,s 3],![s 0,s 3,s 1,s 2]]) a

def Matches (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
    (r labels : Row) : Prop := ∀ a : Fin 3,
  QuarticIntegerDirect.forward (cachedKernel n m kd)
    (Torus.xNext n m) (Torus.yNext n m) (matching n m r a)=
      dictionary.getD (labels a) 0

instance (kd : Array KernelCoefficients) (dictionary : Array Coefficients)
    (r labels : Row) : Decidable (Matches n m kd dictionary r labels) :=
  inferInstanceAs (Decidable (∀ a : Fin 3,
    QuarticIntegerDirect.forward (cachedKernel n m kd)
      (Torus.xNext n m) (Torus.yNext n m) (matching n m r a)=
        dictionary.getD (labels a) 0))

theorem checked_of_forall₂ (R : ℕ) (kd : Array KernelCoefficients)
    (raw : Array Row) (dictionary : Array Coefficients) (ids : Array Row)
    (hsize : raw.size=R)
    (hrows : List.Forall₂ (Matches n m kd dictionary) raw.toList ids.toList) :
    Checked n m R kd raw dictionary ids := by
  intro i a
  have hr : i.val < raw.toList.length := by simpa only [Array.length_toList,hsize] using i.isLt
  have hi : i.val < ids.toList.length := by rw [←hrows.length_eq]; exact hr
  have he := hrows.get hr hi a
  simpa only [Matches,matching,matchingSites,row,expected,Array.getD,
    Array.size,Array.getInternal,dif_pos hr,dif_pos hi] using he

end BilayerDressed.QuarticIntegerListCertificate

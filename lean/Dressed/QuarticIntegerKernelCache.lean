import Dressed.QuarticIntegerArrays
import Dressed.QuarticRowMajorEnumeration

/-! A small rooted displacement table replaces repeated walk computations.
The cached integer kernel is identified with the actual graph-walk kernel
before it is used in any larger quartic arithmetic certificate. -/
namespace BilayerDressed.QuarticIntegerArrays
open BilayerGap CubicSeedChecks
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

theorem kernel_rooted (u v : Torus.Vertex n m) :
    kernel n m u v=kernel n m 0 (v-u) := by
  simp only [kernel,adjacency_rooted n m u v,offWalk2_rooted n m u v,walk3_rooted n m u v]

/-- Array lookup uses the proved row-major displacement coordinate. -/
def cachedKernel (data : Array KernelCoefficients) (u v : Torus.Vertex n m) : KernelCoefficients :=
  data.getD (QuarticRowMajor.index n m (v-u)).val 0

/-- The only numerical kernel prerequisite has at most64*3 integer entries. -/
theorem cachedKernel_eq (data : Array KernelCoefficients)
    (hdata : ∀ q : Torus.Vertex n m,∀ i : Fin 3,
      (data.getD (QuarticRowMajor.index n m q).val 0) i=kernel n m 0 q i) :
    cachedKernel n m data=kernel n m := by
  funext u v i
  rw [cachedKernel,hdata]
  exact congrFun (kernel_rooted n m u v).symm i

end BilayerDressed.QuarticIntegerArrays

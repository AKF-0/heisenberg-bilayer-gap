import Dressed.QuarticIntegerTransport
import Dressed.QuarticIntegerThreeMatching

/-! Exact reuse of signed representative coefficients through a proved kernel
cache and an explicitly checked translation/orientation tuple identity. -/
namespace BilayerDressed.QuarticIntegerListCertificate
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticCoefficientFibers
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

theorem forward_eq_of_representative (kd : Array KernelCoefficients)
    (hcache : cachedKernel n m kd=kernel n m)
    (s rep : Fin 4 → Torus.Vertex n m) (shift : Torus.Vertex n m) (i : Fin 8)
    (expected : Coefficients)
    (heq : rep=orientations (fun j=>s j+shift) i)
    (hrep : forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m) rep=expected) :
    forward (cachedKernel n m kd) (Torus.xNext n m) (Torus.yNext n m) s=expected := by
  have ht := QuarticIntegerTransport.coefficients_eq_of_translation_orientation n m s shift i rep heq
  change forward (kernel n m) (Torus.xNext n m) (Torus.yNext n m) rep=
    forward (kernel n m) (Torus.xNext n m) (Torus.yNext n m) s at ht
  rw [←hcache] at ht
  exact ht.symm.trans hrep

end BilayerDressed.QuarticIntegerListCertificate

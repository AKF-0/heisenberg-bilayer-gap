import Dressed.QuarticIntegerSeedSymmetries
import Dressed.QuarticIntegerThreeMatching

/-! Exact signed cache reuse through a concrete spatial/translation/orientation
witness. The complete tuple identity, injectivity and representative coefficient
are proved inputs; no dictionary ID or orbit-counting premise is substituted. -/
namespace BilayerDressed.QuarticIntegerListCertificate
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticCoefficientFibers
open QuarticIntegerSpatialTransport QuarticIntegerSeedSymmetries

theorem forward16_eq_of_spatial_representative (code : Fin 8)
    (s rep : Fin 4→Torus.Vertex 2 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 2 2) (i : Fin 8) (expected : Coefficients)
    (heq : rep=orientations (fun j=>squareMap 2 code (s j)+shift) i)
    (hrep : forward (cachedKernel 2 2 kernelData16)
      (Torus.xNext 2 2) (Torus.yNext 2 2) rep=expected) :
    forward (cachedKernel 2 2 kernelData16)
      (Torus.xNext 2 2) (Torus.yNext 2 2) s=expected := by
  have ht := coefficients16_eq_of_spatial_witness code s hs shift i rep heq
  change forward (kernel 2 2) (Torus.xNext 2 2) (Torus.yNext 2 2) rep=
    forward (kernel 2 2) (Torus.xNext 2 2) (Torus.yNext 2 2) s at ht
  rw [←cachedKernel16_eq] at ht
  exact ht.symm.trans hrep

theorem forward32_eq_of_spatial_representative (code : Fin 4)
    (s rep : Fin 4→Torus.Vertex 4 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 2) (i : Fin 8) (expected : Coefficients)
    (heq : rep=orientations (fun j=>rectangularMap 4 2 code (s j)+shift) i)
    (hrep : forward (cachedKernel 4 2 kernelData32)
      (Torus.xNext 4 2) (Torus.yNext 4 2) rep=expected) :
    forward (cachedKernel 4 2 kernelData32)
      (Torus.xNext 4 2) (Torus.yNext 4 2) s=expected := by
  have ht := coefficients32_eq_of_spatial_witness code s hs shift i rep heq
  change forward (kernel 4 2) (Torus.xNext 4 2) (Torus.yNext 4 2) rep=
    forward (kernel 4 2) (Torus.xNext 4 2) (Torus.yNext 4 2) s at ht
  rw [←cachedKernel32_eq] at ht
  exact ht.symm.trans hrep

theorem forward64_eq_of_spatial_representative (code : Fin 8)
    (s rep : Fin 4→Torus.Vertex 4 4) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 4) (i : Fin 8) (expected : Coefficients)
    (heq : rep=orientations (fun j=>squareMap 4 code (s j)+shift) i)
    (hrep : forward (cachedKernel 4 4 kernelData64)
      (Torus.xNext 4 4) (Torus.yNext 4 4) rep=expected) :
    forward (cachedKernel 4 4 kernelData64)
      (Torus.xNext 4 4) (Torus.yNext 4 4) s=expected := by
  have ht := coefficients64_eq_of_spatial_witness code s hs shift i rep heq
  change forward (kernel 4 4) (Torus.xNext 4 4) (Torus.yNext 4 4) rep=
    forward (kernel 4 4) (Torus.xNext 4 4) (Torus.yNext 4 4) s at ht
  rw [←cachedKernel64_eq] at ht
  exact ht.symm.trans hrep

end BilayerDressed.QuarticIntegerListCertificate

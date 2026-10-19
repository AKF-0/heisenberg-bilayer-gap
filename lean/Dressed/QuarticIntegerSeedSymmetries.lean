import Dressed.QuarticIntegerSpatialTransport
import Dressed.QuarticIntegerKernelData

/-! Small exact root-cache symmetry certificates and their actual signed-array
consequences. Only the 16/32/64-entry kernel rows are checked here. Large matching
representative coverage and acceptance tables remain separate obligations. -/
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerSeedSymmetries
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerLocalCases
open QuarticIntegerTransport QuarticIntegerSpatialTransport QuarticCoefficientFibers
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

section Cache
variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def rootEntry (data : Array KernelCoefficients) (q : Torus.Vertex n m) : KernelCoefficients :=
  data.getD (QuarticRowMajor.index n m q).val 0

theorem cached_symmetric (data : Array KernelCoefficients)
    (hX : ∀ q, rootEntry n m data (reflectX n m q) = rootEntry n m data q)
    (hY : ∀ q, rootEntry n m data (reflectY n m q) = rootEntry n m data q) :
    ∀ u v, cachedKernel n m data u v = cachedKernel n m data v u := by
  have hn (q : Torus.Vertex n m) : rootEntry n m data (-q) = rootEntry n m data q := by
    change rootEntry n m data (reflectY n m (reflectX n m q)) = _
    rw [hY, hX]
  intro u v
  change rootEntry n m data (v-u) = rootEntry n m data (u-v)
  rw [show u-v = -(v-u) by abel, hn]

theorem cached_equiv (data : Array KernelCoefficients) (e : Torus.Vertex n m ≃ Torus.Vertex n m)
    (hsub : ∀ u v, e (v-u) = e v-e u)
    (hroot : ∀ q, rootEntry n m data (e q) = rootEntry n m data q) :
    ∀ u v, cachedKernel n m data (e u) (e v) = cachedKernel n m data u v := by
  intro u v
  change rootEntry n m data (e v-e u) = rootEntry n m data (v-u)
  rw [←hsub u v, hroot]

theorem cached_translation (data : Array KernelCoefficients) (shift : Torus.Vertex n m) :
    ∀ u v, cachedKernel n m data (u+shift) (v+shift) = cachedKernel n m data u v := by
  intro u v
  simp only [cachedKernel, add_sub_add_right_eq_sub]

end Cache

/-- Every entry and every signed coefficient is checked, not a coupling sample. -/
theorem root16_symmetries :
    (∀ q : Torus.Vertex 2 2, rootEntry 2 2 kernelData16 (reflectX 2 2 q) = rootEntry 2 2 kernelData16 q) ∧
    (∀ q : Torus.Vertex 2 2, rootEntry 2 2 kernelData16 (reflectY 2 2 q) = rootEntry 2 2 kernelData16 q) ∧
    (∀ q : Torus.Vertex 2 2, rootEntry 2 2 kernelData16 (swapAxes 2 q) = rootEntry 2 2 kernelData16 q) := by
  decide +kernel

/-- The rectangle has only coordinate reflections; no axis-swap certificate is asserted. -/
theorem root32_symmetries :
    (∀ q : Torus.Vertex 4 2, rootEntry 4 2 kernelData32 (reflectX 4 2 q) = rootEntry 4 2 kernelData32 q) ∧
    (∀ q : Torus.Vertex 4 2, rootEntry 4 2 kernelData32 (reflectY 4 2 q) = rootEntry 4 2 kernelData32 q) := by
  decide +kernel

theorem root64_symmetries :
    (∀ q : Torus.Vertex 4 4, rootEntry 4 4 kernelData64 (reflectX 4 4 q) = rootEntry 4 4 kernelData64 q) ∧
    (∀ q : Torus.Vertex 4 4, rootEntry 4 4 kernelData64 (reflectY 4 4 q) = rootEntry 4 4 kernelData64 q) ∧
    (∀ q : Torus.Vertex 4 4, rootEntry 4 4 kernelData64 (swapAxes 4 q) = rootEntry 4 4 kernelData64 q) := by
  decide +kernel

theorem cached16_preserves (code : Fin 8) :
    PreservesForward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (squareMap 2 code) :=
  squareMap_preserves 2 _ (cached_symmetric 2 2 _ root16_symmetries.1 root16_symmetries.2.1)
    (cached_equiv 2 2 _ _ (reflectX_sub 2 2) root16_symmetries.1)
    (cached_equiv 2 2 _ _ (reflectY_sub 2 2) root16_symmetries.2.1)
    (cached_equiv 2 2 _ _ (swapAxes_sub 2) root16_symmetries.2.2) code

theorem cached32_preserves (code : Fin 4) :
    PreservesForward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (rectangularMap 4 2 code) :=
  rectangularMap_preserves 4 2 _ (cached_symmetric 4 2 _ root32_symmetries.1 root32_symmetries.2)
    (cached_equiv 4 2 _ _ (reflectX_sub 4 2) root32_symmetries.1)
    (cached_equiv 4 2 _ _ (reflectY_sub 4 2) root32_symmetries.2) code

theorem cached64_preserves (code : Fin 8) :
    PreservesForward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (squareMap 4 code) :=
  squareMap_preserves 4 _ (cached_symmetric 4 4 _ root64_symmetries.1 root64_symmetries.2.1)
    (cached_equiv 4 4 _ _ (reflectX_sub 4 4) root64_symmetries.1)
    (cached_equiv 4 4 _ _ (reflectY_sub 4 4) root64_symmetries.2.1)
    (cached_equiv 4 4 _ _ (swapAxes_sub 4) root64_symmetries.2.2) code

/-- Actual graph-walk kernels inherit the fully discharged finite cache symmetries. -/
theorem kernel16_preserves (code : Fin 8) :
    PreservesForward (kernel 2 2) (Torus.xNext 2 2) (Torus.yNext 2 2) (squareMap 2 code) := by
  simpa only [cachedKernel16_eq] using cached16_preserves code

theorem kernel32_preserves (code : Fin 4) :
    PreservesForward (kernel 4 2) (Torus.xNext 4 2) (Torus.yNext 4 2) (rectangularMap 4 2 code) := by
  simpa only [cachedKernel32_eq] using cached32_preserves code

theorem kernel64_preserves (code : Fin 8) :
    PreservesForward (kernel 4 4) (Torus.xNext 4 4) (Torus.yNext 4 4) (squareMap 4 code) := by
  simpa only [cachedKernel64_eq] using cached64_preserves code

theorem coefficients16_eq_of_spatial_witness
    (code : Fin 8) (s : Fin 4 → Torus.Vertex 2 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 2 2) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 2 2)
    (hw : s' = orientations (fun j => squareMap 2 code (s j)+shift) i) :
    coefficients 2 2 s' = coefficients 2 2 s :=
  forward_eq_of_spatial_witness 2 2 (kernel 2 2) (squareMap 2 code) (kernel16_preserves code)
    s hs shift i s' (fun u v => kernel_translation 2 2 u v shift) hw

theorem fastCached16_eq_of_spatial_witness
    (code : Fin 8) (s : Fin 4 → Torus.Vertex 2 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 2 2) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 2 2)
    (hw : s' = orientations (fun j => squareMap 2 code (s j)+shift) i) :
    fastForward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) s' =
      fastForward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) s :=
  fastForward_eq_of_spatial_witness 2 2 _ (squareMap 2 code) (cached16_preserves code)
    s hs shift i s' (cached_translation 2 2 kernelData16 shift) hw

theorem coefficients32_eq_of_spatial_witness
    (code : Fin 4) (s : Fin 4 → Torus.Vertex 4 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 2) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 4 2)
    (hw : s' = orientations (fun j => rectangularMap 4 2 code (s j)+shift) i) :
    coefficients 4 2 s' = coefficients 4 2 s :=
  forward_eq_of_spatial_witness 4 2 (kernel 4 2) (rectangularMap 4 2 code) (kernel32_preserves code)
    s hs shift i s' (fun u v => kernel_translation 4 2 u v shift) hw

theorem fastCached32_eq_of_spatial_witness
    (code : Fin 4) (s : Fin 4 → Torus.Vertex 4 2) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 2) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 4 2)
    (hw : s' = orientations (fun j => rectangularMap 4 2 code (s j)+shift) i) :
    fastForward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) s' =
      fastForward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) s :=
  fastForward_eq_of_spatial_witness 4 2 _ (rectangularMap 4 2 code) (cached32_preserves code)
    s hs shift i s' (cached_translation 4 2 kernelData32 shift) hw

theorem coefficients64_eq_of_spatial_witness
    (code : Fin 8) (s : Fin 4 → Torus.Vertex 4 4) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 4) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 4 4)
    (hw : s' = orientations (fun j => squareMap 4 code (s j)+shift) i) :
    coefficients 4 4 s' = coefficients 4 4 s :=
  forward_eq_of_spatial_witness 4 4 (kernel 4 4) (squareMap 4 code) (kernel64_preserves code)
    s hs shift i s' (fun u v => kernel_translation 4 4 u v shift) hw

theorem fastCached64_eq_of_spatial_witness
    (code : Fin 8) (s : Fin 4 → Torus.Vertex 4 4) (hs : Function.Injective s)
    (shift : Torus.Vertex 4 4) (i : Fin 8) (s' : Fin 4 → Torus.Vertex 4 4)
    (hw : s' = orientations (fun j => squareMap 4 code (s j)+shift) i) :
    fastForward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) s' =
      fastForward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) s :=
  fastForward_eq_of_spatial_witness 4 4 _ (squareMap 4 code) (cached64_preserves code)
    s hs shift i s' (cached_translation 4 4 kernelData64 shift) hw

end BilayerDressed.QuarticIntegerSeedSymmetries

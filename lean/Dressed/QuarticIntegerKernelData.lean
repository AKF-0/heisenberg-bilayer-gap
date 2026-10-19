import Dressed.QuarticIntegerKernelCache

/-! Small kernel-checked integer root rows for the actual three cubic graphs.
These rows are witnesses, not assumed kernel values. -/
namespace BilayerDressed.QuarticIntegerArrays
open BilayerGap
set_option maxRecDepth 20000

def kernelData16 : Array KernelCoefficients := #[
  ![0,0,0],
  ![-16,-8,-10],
  ![0,16,8],
  ![-16,-8,-10],
  ![-16,-8,-10],
  ![0,16,8],
  ![0,0,-30],
  ![0,16,8],
  ![0,16,8],
  ![0,0,-30],
  ![0,0,0],
  ![0,0,-30],
  ![-16,-8,-10],
  ![0,16,8],
  ![0,0,-30],
  ![0,16,8]]

set_option maxHeartbeats 0 in
theorem kernelData16_checked : ∀ q : Torus.Vertex 2 2,∀ i : Fin 3,
    (kernelData16.getD (QuarticRowMajor.index 2 2 q).val 0) i=kernel 2 2 0 q i := by
  decide +kernel

theorem cachedKernel16_eq : cachedKernel 2 2 kernelData16=kernel 2 2 :=
  cachedKernel_eq 2 2 kernelData16 kernelData16_checked

def kernelData32 : Array KernelCoefficients := #[
  ![0,0,0],
  ![-16,-8,-10],
  ![0,16,8],
  ![-16,-8,-10],
  ![-16,-8,-5],
  ![0,16,8],
  ![0,0,-30],
  ![0,16,8],
  ![0,8,4],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,-15],
  ![0,0,-5],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-5],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,8,4],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,-15],
  ![-16,-8,-5],
  ![0,16,8],
  ![0,0,-30],
  ![0,16,8]]

set_option maxHeartbeats 0 in
theorem kernelData32_checked : ∀ q : Torus.Vertex 4 2,∀ i : Fin 3,
    (kernelData32.getD (QuarticRowMajor.index 4 2 q).val 0) i=kernel 4 2 0 q i := by
  decide +kernel

theorem cachedKernel32_eq : cachedKernel 4 2 kernelData32=kernel 4 2 :=
  cachedKernel_eq 4 2 kernelData32 kernelData32_checked

def kernelData64 : Array KernelCoefficients := #[
  ![0,0,0],
  ![-16,-8,-5],
  ![0,8,4],
  ![0,0,-5],
  ![0,0,0],
  ![0,0,-5],
  ![0,8,4],
  ![-16,-8,-5],
  ![-16,-8,-5],
  ![0,16,8],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-15],
  ![0,16,8],
  ![0,8,4],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-15],
  ![0,0,-5],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-5],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,8,4],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-15],
  ![-16,-8,-5],
  ![0,16,8],
  ![0,0,-15],
  ![0,0,0],
  ![0,0,0],
  ![0,0,0],
  ![0,0,-15],
  ![0,16,8]]

set_option maxHeartbeats 0 in
theorem kernelData64_checked : ∀ q : Torus.Vertex 4 4,∀ i : Fin 3,
    (kernelData64.getD (QuarticRowMajor.index 4 4 q).val 0) i=kernel 4 4 0 q i := by
  decide +kernel

theorem cachedKernel64_eq : cachedKernel 4 4 kernelData64=kernel 4 4 :=
  cachedKernel_eq 4 4 kernelData64 kernelData64_checked

end BilayerDressed.QuarticIntegerArrays

import Dressed.QuarticIntegerKernelData

/-!
# Exact balanced normal forms for the three cached cubic kernels

A balanced decision tree replaces kernel-linear array indexing in repeated closed
quartic coefficient checks. Identical subtrees are collapsed. Each equality is
proved for every in-range displacement index by kernel reduction, then lifted to
the actual two-site cached kernel. No graph, coefficient, sign, or acceptance
relation changes. Values of the auxiliary natural-index trees outside the stated
finite range are immaterial and are not identified with the defaulted arrays.
-/
namespace BilayerDressed.QuarticIntegerBalancedKernel
open BilayerGap QuarticIntegerArrays
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Balanced literal lookup, used only with indices below 16. -/
def rootTree16 (i : ℕ) : KernelCoefficients :=
  if i < 8 then
    if i < 4 then
      if i < 2 then
        if i < 1 then
          ![0,0,0]
        else
          ![-16,-8,-10]
      else
        if i < 3 then
          ![0,16,8]
        else
          ![-16,-8,-10]
    else
      if i < 6 then
        if i < 5 then
          ![-16,-8,-10]
        else
          ![0,16,8]
      else
        if i < 7 then
          ![0,0,-30]
        else
          ![0,16,8]
  else
    if i < 12 then
      if i < 10 then
        if i < 9 then
          ![0,16,8]
        else
          ![0,0,-30]
      else
        if i < 11 then
          ![0,0,0]
        else
          ![0,0,-30]
    else
      if i < 14 then
        if i < 13 then
          ![-16,-8,-10]
        else
          ![0,16,8]
      else
        if i < 15 then
          ![0,0,-30]
        else
          ![0,16,8]

/-- Every in-range entry is exactly the frozen signed coefficient triple. -/
theorem rootTree16_eq (i : Fin 16) :
    kernelData16.getD i.val 0 = rootTree16 i.val := by
  fin_cases i <;> rfl

/-- The same row-major displacement, with balanced literal lookup. -/
def treeKernel16 (u v : Torus.Vertex 2 2) : KernelCoefficients :=
  rootTree16 (QuarticRowMajor.index 2 2 (v-u)).val

/-- Drop-in rewrite before kernel-checking an actual quartic matching. -/
theorem cachedKernel16_eq_tree :
    cachedKernel 2 2 kernelData16 = treeKernel16 := by
  funext u v
  exact rootTree16_eq _

/-- Balanced literal lookup, used only with indices below 32. -/
def rootTree32 (i : ℕ) : KernelCoefficients :=
  if i < 16 then
    if i < 8 then
      if i < 4 then
        if i < 2 then
          if i < 1 then
            ![0,0,0]
          else
            ![-16,-8,-10]
        else
          if i < 3 then
            ![0,16,8]
          else
            ![-16,-8,-10]
      else
        if i < 6 then
          if i < 5 then
            ![-16,-8,-5]
          else
            ![0,16,8]
        else
          if i < 7 then
            ![0,0,-30]
          else
            ![0,16,8]
    else
      if i < 12 then
        if i < 10 then
          if i < 9 then
            ![0,8,4]
          else
            ![0,0,-15]
        else
          if i < 11 then
            ![0,0,0]
          else
            ![0,0,-15]
      else
        if i < 14 then
          if i < 13 then
            ![0,0,-5]
          else
            ![0,0,0]
        else
          ![0,0,0]
  else
    if i < 24 then
      if i < 20 then
        ![0,0,0]
      else
        if i < 22 then
          if i < 21 then
            ![0,0,-5]
          else
            ![0,0,0]
        else
          ![0,0,0]
    else
      if i < 28 then
        if i < 26 then
          if i < 25 then
            ![0,8,4]
          else
            ![0,0,-15]
        else
          if i < 27 then
            ![0,0,0]
          else
            ![0,0,-15]
      else
        if i < 30 then
          if i < 29 then
            ![-16,-8,-5]
          else
            ![0,16,8]
        else
          if i < 31 then
            ![0,0,-30]
          else
            ![0,16,8]

/-- Every in-range entry is exactly the frozen signed coefficient triple. -/
theorem rootTree32_eq (i : Fin 32) :
    kernelData32.getD i.val 0 = rootTree32 i.val := by
  fin_cases i <;> rfl

/-- The same row-major displacement, with balanced literal lookup. -/
def treeKernel32 (u v : Torus.Vertex 4 2) : KernelCoefficients :=
  rootTree32 (QuarticRowMajor.index 4 2 (v-u)).val

/-- Drop-in rewrite before kernel-checking an actual quartic matching. -/
theorem cachedKernel32_eq_tree :
    cachedKernel 4 2 kernelData32 = treeKernel32 := by
  funext u v
  exact rootTree32_eq _

/-- Balanced literal lookup, used only with indices below 64. -/
def rootTree64 (i : ℕ) : KernelCoefficients :=
  if i < 32 then
    if i < 16 then
      if i < 8 then
        if i < 4 then
          if i < 2 then
            if i < 1 then
              ![0,0,0]
            else
              ![-16,-8,-5]
          else
            if i < 3 then
              ![0,8,4]
            else
              ![0,0,-5]
        else
          if i < 6 then
            if i < 5 then
              ![0,0,0]
            else
              ![0,0,-5]
          else
            if i < 7 then
              ![0,8,4]
            else
              ![-16,-8,-5]
      else
        if i < 12 then
          if i < 10 then
            if i < 9 then
              ![-16,-8,-5]
            else
              ![0,16,8]
          else
            if i < 11 then
              ![0,0,-15]
            else
              ![0,0,0]
        else
          if i < 14 then
            ![0,0,0]
          else
            if i < 15 then
              ![0,0,-15]
            else
              ![0,16,8]
    else
      if i < 24 then
        if i < 20 then
          if i < 18 then
            if i < 17 then
              ![0,8,4]
            else
              ![0,0,-15]
          else
            ![0,0,0]
        else
          if i < 22 then
            ![0,0,0]
          else
            if i < 23 then
              ![0,0,0]
            else
              ![0,0,-15]
      else
        if i < 28 then
          if i < 26 then
            if i < 25 then
              ![0,0,-5]
            else
              ![0,0,0]
          else
            ![0,0,0]
        else
          ![0,0,0]
  else
    if i < 48 then
      if i < 40 then
        ![0,0,0]
      else
        if i < 44 then
          if i < 42 then
            if i < 41 then
              ![0,0,-5]
            else
              ![0,0,0]
          else
            ![0,0,0]
        else
          ![0,0,0]
    else
      if i < 56 then
        if i < 52 then
          if i < 50 then
            if i < 49 then
              ![0,8,4]
            else
              ![0,0,-15]
          else
            ![0,0,0]
        else
          if i < 54 then
            ![0,0,0]
          else
            if i < 55 then
              ![0,0,0]
            else
              ![0,0,-15]
      else
        if i < 60 then
          if i < 58 then
            if i < 57 then
              ![-16,-8,-5]
            else
              ![0,16,8]
          else
            if i < 59 then
              ![0,0,-15]
            else
              ![0,0,0]
        else
          if i < 62 then
            ![0,0,0]
          else
            if i < 63 then
              ![0,0,-15]
            else
              ![0,16,8]

/-- Every in-range entry is exactly the frozen signed coefficient triple. -/
theorem rootTree64_eq (i : Fin 64) :
    kernelData64.getD i.val 0 = rootTree64 i.val := by
  fin_cases i <;> rfl

/-- The same row-major displacement, with balanced literal lookup. -/
def treeKernel64 (u v : Torus.Vertex 4 4) : KernelCoefficients :=
  rootTree64 (QuarticRowMajor.index 4 4 (v-u)).val

/-- Drop-in rewrite before kernel-checking an actual quartic matching. -/
theorem cachedKernel64_eq_tree :
    cachedKernel 4 4 kernelData64 = treeKernel64 := by
  funext u v
  exact rootTree64_eq _

end BilayerDressed.QuarticIntegerBalancedKernel

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3008 : Rep := ⟨![0,11,17,61],462⟩
def representative_3009 : Rep := ⟨![0,11,17,62],462⟩
def representative_3010 : Rep := ⟨![0,11,17,63],462⟩
def representative_3011 : Rep := ⟨![0,11,18,29],462⟩
def representative_3012 : Rep := ⟨![0,11,18,30],462⟩
def representative_3013 : Rep := ⟨![0,11,18,31],462⟩
def representative_3014 : Rep := ⟨![0,11,18,32],462⟩
def representative_3015 : Rep := ⟨![0,11,18,36],462⟩
def representative_3016 : Rep := ⟨![0,11,18,37],462⟩
def representative_3017 : Rep := ⟨![0,11,18,38],462⟩
def representative_3018 : Rep := ⟨![0,11,18,39],462⟩
def representative_3019 : Rep := ⟨![0,11,18,40],462⟩
def representative_3020 : Rep := ⟨![0,11,18,41],462⟩
def representative_3021 : Rep := ⟨![0,11,18,44],462⟩
def representative_3022 : Rep := ⟨![0,11,18,45],462⟩
def representative_3023 : Rep := ⟨![0,11,18,46],462⟩
def representative_3024 : Rep := ⟨![0,11,18,47],462⟩
def representative_3025 : Rep := ⟨![0,11,18,48],462⟩
def representative_3026 : Rep := ⟨![0,11,18,49],462⟩
def representative_3027 : Rep := ⟨![0,11,18,51],462⟩
def representative_3028 : Rep := ⟨![0,11,18,52],462⟩
def representative_3029 : Rep := ⟨![0,11,18,53],462⟩
def representative_3030 : Rep := ⟨![0,11,18,54],462⟩
def representative_3031 : Rep := ⟨![0,11,18,55],462⟩
def representative_3032 : Rep := ⟨![0,11,18,56],462⟩
def representative_3033 : Rep := ⟨![0,11,18,57],462⟩
def representative_3034 : Rep := ⟨![0,11,18,60],462⟩
def representative_3035 : Rep := ⟨![0,11,18,61],462⟩
def representative_3036 : Rep := ⟨![0,11,18,62],462⟩
def representative_3037 : Rep := ⟨![0,11,18,63],462⟩
def representative_3038 : Rep := ⟨![0,11,19,24],462⟩
def representative_3039 : Rep := ⟨![0,11,19,30],462⟩
def representative_3040 : Rep := ⟨![0,11,19,31],462⟩
def representative_3041 : Rep := ⟨![0,11,19,32],462⟩
def representative_3042 : Rep := ⟨![0,11,19,33],462⟩
def representative_3043 : Rep := ⟨![0,11,19,37],462⟩
def representative_3044 : Rep := ⟨![0,11,19,38],462⟩
def representative_3045 : Rep := ⟨![0,11,19,39],462⟩
def representative_3046 : Rep := ⟨![0,11,19,40],462⟩
def representative_3047 : Rep := ⟨![0,11,19,41],462⟩
def representative_3048 : Rep := ⟨![0,11,19,45],462⟩
def representative_3049 : Rep := ⟨![0,11,19,46],462⟩
def representative_3050 : Rep := ⟨![0,11,19,47],462⟩
def representative_3051 : Rep := ⟨![0,11,19,48],462⟩
def representative_3052 : Rep := ⟨![0,11,19,49],462⟩
def representative_3053 : Rep := ⟨![0,11,19,50],462⟩
def representative_3054 : Rep := ⟨![0,11,19,52],462⟩
def representative_3055 : Rep := ⟨![0,11,19,53],462⟩
def representative_3056 : Rep := ⟨![0,11,19,54],462⟩
def representative_3057 : Rep := ⟨![0,11,19,55],462⟩
def representative_3058 : Rep := ⟨![0,11,19,56],462⟩
def representative_3059 : Rep := ⟨![0,11,19,61],462⟩
def representative_3060 : Rep := ⟨![0,11,19,62],462⟩
def representative_3061 : Rep := ⟨![0,11,19,63],462⟩
def representative_3062 : Rep := ⟨![0,11,20,24],462⟩
def representative_3063 : Rep := ⟨![0,11,20,31],462⟩
def representative_3064 : Rep := ⟨![0,11,20,32],462⟩
def representative_3065 : Rep := ⟨![0,11,20,33],462⟩
def representative_3066 : Rep := ⟨![0,11,20,34],462⟩
def representative_3067 : Rep := ⟨![0,11,20,38],462⟩
def representative_3068 : Rep := ⟨![0,11,20,39],462⟩
def representative_3069 : Rep := ⟨![0,11,20,40],462⟩
def representative_3070 : Rep := ⟨![0,11,20,41],462⟩
def representative_3071 : Rep := ⟨![0,11,20,42],462⟩
theorem coefficient_3008 : validRep representative_3008 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3008)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3009 : validRep representative_3009 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3009)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3010 : validRep representative_3010 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3010)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3011 : validRep representative_3011 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3011)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3012 : validRep representative_3012 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3012)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3013 : validRep representative_3013 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3013)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3014 : validRep representative_3014 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3014)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3015 : validRep representative_3015 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3015)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3016 : validRep representative_3016 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3016)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3017 : validRep representative_3017 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3017)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3018 : validRep representative_3018 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3018)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3019 : validRep representative_3019 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3019)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3020 : validRep representative_3020 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3020)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3021 : validRep representative_3021 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3021)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3022 : validRep representative_3022 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3022)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3023 : validRep representative_3023 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3023)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3024 : validRep representative_3024 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3024)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3025 : validRep representative_3025 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3025)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3026 : validRep representative_3026 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3026)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3027 : validRep representative_3027 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3027)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3028 : validRep representative_3028 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3028)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3029 : validRep representative_3029 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3029)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3030 : validRep representative_3030 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3030)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3031 : validRep representative_3031 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3031)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3032 : validRep representative_3032 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3032)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3033 : validRep representative_3033 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3033)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3034 : validRep representative_3034 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3034)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3035 : validRep representative_3035 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3035)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3036 : validRep representative_3036 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3036)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3037 : validRep representative_3037 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3037)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3038 : validRep representative_3038 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3038)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3039 : validRep representative_3039 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3039)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3040 : validRep representative_3040 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3040)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3041 : validRep representative_3041 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3041)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3042 : validRep representative_3042 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3042)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3043 : validRep representative_3043 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3043)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3044 : validRep representative_3044 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3044)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3045 : validRep representative_3045 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3045)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3046 : validRep representative_3046 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3046)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3047 : validRep representative_3047 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3047)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3048 : validRep representative_3048 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3048)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3049 : validRep representative_3049 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3049)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3050 : validRep representative_3050 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3050)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3051 : validRep representative_3051 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3051)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3052 : validRep representative_3052 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3052)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3053 : validRep representative_3053 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3053)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3054 : validRep representative_3054 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3054)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3055 : validRep representative_3055 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3055)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3056 : validRep representative_3056 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3056)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3057 : validRep representative_3057 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3057)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3058 : validRep representative_3058 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3058)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3059 : validRep representative_3059 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3059)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3060 : validRep representative_3060 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3060)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3061 : validRep representative_3061 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3061)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3062 : validRep representative_3062 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3062)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3063 : validRep representative_3063 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3063)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3064 : validRep representative_3064 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3064)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3065 : validRep representative_3065 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3065)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3066 : validRep representative_3066 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3066)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3067 : validRep representative_3067 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3067)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3068 : validRep representative_3068 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3068)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3069 : validRep representative_3069 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3069)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3070 : validRep representative_3070 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3070)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3071 : validRep representative_3071 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3071)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_047 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3040 (QuarticIntegerRepresentativeTree.Tree.branch 3024 (QuarticIntegerRepresentativeTree.Tree.branch 3016 (QuarticIntegerRepresentativeTree.Tree.branch 3012 (QuarticIntegerRepresentativeTree.Tree.branch 3010 (QuarticIntegerRepresentativeTree.Tree.branch 3009 (QuarticIntegerRepresentativeTree.Tree.leaf 3008 representative_3008) (QuarticIntegerRepresentativeTree.Tree.leaf 3009 representative_3009)) (QuarticIntegerRepresentativeTree.Tree.branch 3011 (QuarticIntegerRepresentativeTree.Tree.leaf 3010 representative_3010) (QuarticIntegerRepresentativeTree.Tree.leaf 3011 representative_3011))) (QuarticIntegerRepresentativeTree.Tree.branch 3014 (QuarticIntegerRepresentativeTree.Tree.branch 3013 (QuarticIntegerRepresentativeTree.Tree.leaf 3012 representative_3012) (QuarticIntegerRepresentativeTree.Tree.leaf 3013 representative_3013)) (QuarticIntegerRepresentativeTree.Tree.branch 3015 (QuarticIntegerRepresentativeTree.Tree.leaf 3014 representative_3014) (QuarticIntegerRepresentativeTree.Tree.leaf 3015 representative_3015)))) (QuarticIntegerRepresentativeTree.Tree.branch 3020 (QuarticIntegerRepresentativeTree.Tree.branch 3018 (QuarticIntegerRepresentativeTree.Tree.branch 3017 (QuarticIntegerRepresentativeTree.Tree.leaf 3016 representative_3016) (QuarticIntegerRepresentativeTree.Tree.leaf 3017 representative_3017)) (QuarticIntegerRepresentativeTree.Tree.branch 3019 (QuarticIntegerRepresentativeTree.Tree.leaf 3018 representative_3018) (QuarticIntegerRepresentativeTree.Tree.leaf 3019 representative_3019))) (QuarticIntegerRepresentativeTree.Tree.branch 3022 (QuarticIntegerRepresentativeTree.Tree.branch 3021 (QuarticIntegerRepresentativeTree.Tree.leaf 3020 representative_3020) (QuarticIntegerRepresentativeTree.Tree.leaf 3021 representative_3021)) (QuarticIntegerRepresentativeTree.Tree.branch 3023 (QuarticIntegerRepresentativeTree.Tree.leaf 3022 representative_3022) (QuarticIntegerRepresentativeTree.Tree.leaf 3023 representative_3023))))) (QuarticIntegerRepresentativeTree.Tree.branch 3032 (QuarticIntegerRepresentativeTree.Tree.branch 3028 (QuarticIntegerRepresentativeTree.Tree.branch 3026 (QuarticIntegerRepresentativeTree.Tree.branch 3025 (QuarticIntegerRepresentativeTree.Tree.leaf 3024 representative_3024) (QuarticIntegerRepresentativeTree.Tree.leaf 3025 representative_3025)) (QuarticIntegerRepresentativeTree.Tree.branch 3027 (QuarticIntegerRepresentativeTree.Tree.leaf 3026 representative_3026) (QuarticIntegerRepresentativeTree.Tree.leaf 3027 representative_3027))) (QuarticIntegerRepresentativeTree.Tree.branch 3030 (QuarticIntegerRepresentativeTree.Tree.branch 3029 (QuarticIntegerRepresentativeTree.Tree.leaf 3028 representative_3028) (QuarticIntegerRepresentativeTree.Tree.leaf 3029 representative_3029)) (QuarticIntegerRepresentativeTree.Tree.branch 3031 (QuarticIntegerRepresentativeTree.Tree.leaf 3030 representative_3030) (QuarticIntegerRepresentativeTree.Tree.leaf 3031 representative_3031)))) (QuarticIntegerRepresentativeTree.Tree.branch 3036 (QuarticIntegerRepresentativeTree.Tree.branch 3034 (QuarticIntegerRepresentativeTree.Tree.branch 3033 (QuarticIntegerRepresentativeTree.Tree.leaf 3032 representative_3032) (QuarticIntegerRepresentativeTree.Tree.leaf 3033 representative_3033)) (QuarticIntegerRepresentativeTree.Tree.branch 3035 (QuarticIntegerRepresentativeTree.Tree.leaf 3034 representative_3034) (QuarticIntegerRepresentativeTree.Tree.leaf 3035 representative_3035))) (QuarticIntegerRepresentativeTree.Tree.branch 3038 (QuarticIntegerRepresentativeTree.Tree.branch 3037 (QuarticIntegerRepresentativeTree.Tree.leaf 3036 representative_3036) (QuarticIntegerRepresentativeTree.Tree.leaf 3037 representative_3037)) (QuarticIntegerRepresentativeTree.Tree.branch 3039 (QuarticIntegerRepresentativeTree.Tree.leaf 3038 representative_3038) (QuarticIntegerRepresentativeTree.Tree.leaf 3039 representative_3039)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3056 (QuarticIntegerRepresentativeTree.Tree.branch 3048 (QuarticIntegerRepresentativeTree.Tree.branch 3044 (QuarticIntegerRepresentativeTree.Tree.branch 3042 (QuarticIntegerRepresentativeTree.Tree.branch 3041 (QuarticIntegerRepresentativeTree.Tree.leaf 3040 representative_3040) (QuarticIntegerRepresentativeTree.Tree.leaf 3041 representative_3041)) (QuarticIntegerRepresentativeTree.Tree.branch 3043 (QuarticIntegerRepresentativeTree.Tree.leaf 3042 representative_3042) (QuarticIntegerRepresentativeTree.Tree.leaf 3043 representative_3043))) (QuarticIntegerRepresentativeTree.Tree.branch 3046 (QuarticIntegerRepresentativeTree.Tree.branch 3045 (QuarticIntegerRepresentativeTree.Tree.leaf 3044 representative_3044) (QuarticIntegerRepresentativeTree.Tree.leaf 3045 representative_3045)) (QuarticIntegerRepresentativeTree.Tree.branch 3047 (QuarticIntegerRepresentativeTree.Tree.leaf 3046 representative_3046) (QuarticIntegerRepresentativeTree.Tree.leaf 3047 representative_3047)))) (QuarticIntegerRepresentativeTree.Tree.branch 3052 (QuarticIntegerRepresentativeTree.Tree.branch 3050 (QuarticIntegerRepresentativeTree.Tree.branch 3049 (QuarticIntegerRepresentativeTree.Tree.leaf 3048 representative_3048) (QuarticIntegerRepresentativeTree.Tree.leaf 3049 representative_3049)) (QuarticIntegerRepresentativeTree.Tree.branch 3051 (QuarticIntegerRepresentativeTree.Tree.leaf 3050 representative_3050) (QuarticIntegerRepresentativeTree.Tree.leaf 3051 representative_3051))) (QuarticIntegerRepresentativeTree.Tree.branch 3054 (QuarticIntegerRepresentativeTree.Tree.branch 3053 (QuarticIntegerRepresentativeTree.Tree.leaf 3052 representative_3052) (QuarticIntegerRepresentativeTree.Tree.leaf 3053 representative_3053)) (QuarticIntegerRepresentativeTree.Tree.branch 3055 (QuarticIntegerRepresentativeTree.Tree.leaf 3054 representative_3054) (QuarticIntegerRepresentativeTree.Tree.leaf 3055 representative_3055))))) (QuarticIntegerRepresentativeTree.Tree.branch 3064 (QuarticIntegerRepresentativeTree.Tree.branch 3060 (QuarticIntegerRepresentativeTree.Tree.branch 3058 (QuarticIntegerRepresentativeTree.Tree.branch 3057 (QuarticIntegerRepresentativeTree.Tree.leaf 3056 representative_3056) (QuarticIntegerRepresentativeTree.Tree.leaf 3057 representative_3057)) (QuarticIntegerRepresentativeTree.Tree.branch 3059 (QuarticIntegerRepresentativeTree.Tree.leaf 3058 representative_3058) (QuarticIntegerRepresentativeTree.Tree.leaf 3059 representative_3059))) (QuarticIntegerRepresentativeTree.Tree.branch 3062 (QuarticIntegerRepresentativeTree.Tree.branch 3061 (QuarticIntegerRepresentativeTree.Tree.leaf 3060 representative_3060) (QuarticIntegerRepresentativeTree.Tree.leaf 3061 representative_3061)) (QuarticIntegerRepresentativeTree.Tree.branch 3063 (QuarticIntegerRepresentativeTree.Tree.leaf 3062 representative_3062) (QuarticIntegerRepresentativeTree.Tree.leaf 3063 representative_3063)))) (QuarticIntegerRepresentativeTree.Tree.branch 3068 (QuarticIntegerRepresentativeTree.Tree.branch 3066 (QuarticIntegerRepresentativeTree.Tree.branch 3065 (QuarticIntegerRepresentativeTree.Tree.leaf 3064 representative_3064) (QuarticIntegerRepresentativeTree.Tree.leaf 3065 representative_3065)) (QuarticIntegerRepresentativeTree.Tree.branch 3067 (QuarticIntegerRepresentativeTree.Tree.leaf 3066 representative_3066) (QuarticIntegerRepresentativeTree.Tree.leaf 3067 representative_3067))) (QuarticIntegerRepresentativeTree.Tree.branch 3070 (QuarticIntegerRepresentativeTree.Tree.branch 3069 (QuarticIntegerRepresentativeTree.Tree.leaf 3068 representative_3068) (QuarticIntegerRepresentativeTree.Tree.leaf 3069 representative_3069)) (QuarticIntegerRepresentativeTree.Tree.branch 3071 (QuarticIntegerRepresentativeTree.Tree.leaf 3070 representative_3070) (QuarticIntegerRepresentativeTree.Tree.leaf 3071 representative_3071)))))))
theorem accepted_047 : All validRep tree_047 := ⟨⟨⟨⟨⟨⟨coefficient_3008,coefficient_3009⟩,⟨coefficient_3010,coefficient_3011⟩⟩,⟨⟨coefficient_3012,coefficient_3013⟩,⟨coefficient_3014,coefficient_3015⟩⟩⟩,⟨⟨⟨coefficient_3016,coefficient_3017⟩,⟨coefficient_3018,coefficient_3019⟩⟩,⟨⟨coefficient_3020,coefficient_3021⟩,⟨coefficient_3022,coefficient_3023⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3024,coefficient_3025⟩,⟨coefficient_3026,coefficient_3027⟩⟩,⟨⟨coefficient_3028,coefficient_3029⟩,⟨coefficient_3030,coefficient_3031⟩⟩⟩,⟨⟨⟨coefficient_3032,coefficient_3033⟩,⟨coefficient_3034,coefficient_3035⟩⟩,⟨⟨coefficient_3036,coefficient_3037⟩,⟨coefficient_3038,coefficient_3039⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3040,coefficient_3041⟩,⟨coefficient_3042,coefficient_3043⟩⟩,⟨⟨coefficient_3044,coefficient_3045⟩,⟨coefficient_3046,coefficient_3047⟩⟩⟩,⟨⟨⟨coefficient_3048,coefficient_3049⟩,⟨coefficient_3050,coefficient_3051⟩⟩,⟨⟨coefficient_3052,coefficient_3053⟩,⟨coefficient_3054,coefficient_3055⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3056,coefficient_3057⟩,⟨coefficient_3058,coefficient_3059⟩⟩,⟨⟨coefficient_3060,coefficient_3061⟩,⟨coefficient_3062,coefficient_3063⟩⟩⟩,⟨⟨⟨coefficient_3064,coefficient_3065⟩,⟨coefficient_3066,coefficient_3067⟩⟩,⟨⟨coefficient_3068,coefficient_3069⟩,⟨coefficient_3070,coefficient_3071⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

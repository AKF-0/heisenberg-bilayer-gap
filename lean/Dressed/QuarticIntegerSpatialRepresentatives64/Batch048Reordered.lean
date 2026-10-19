import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3072 : Rep := ⟨![0,11,20,45],462⟩
def representative_3073 : Rep := ⟨![0,11,20,46],462⟩
def representative_3074 : Rep := ⟨![0,11,20,47],462⟩
def representative_3075 : Rep := ⟨![0,11,20,48],462⟩
def representative_3076 : Rep := ⟨![0,11,20,49],462⟩
def representative_3077 : Rep := ⟨![0,11,20,50],462⟩
def representative_3078 : Rep := ⟨![0,11,20,51],462⟩
def representative_3079 : Rep := ⟨![0,11,20,53],462⟩
def representative_3080 : Rep := ⟨![0,11,20,54],462⟩
def representative_3081 : Rep := ⟨![0,11,20,55],462⟩
def representative_3082 : Rep := ⟨![0,11,20,62],462⟩
def representative_3083 : Rep := ⟨![0,11,20,63],462⟩
def representative_3084 : Rep := ⟨![0,11,21,24],462⟩
def representative_3085 : Rep := ⟨![0,11,21,25],462⟩
def representative_3086 : Rep := ⟨![0,11,21,32],462⟩
def representative_3087 : Rep := ⟨![0,11,21,33],462⟩
def representative_3088 : Rep := ⟨![0,11,21,34],462⟩
def representative_3089 : Rep := ⟨![0,11,21,35],462⟩
def representative_3090 : Rep := ⟨![0,11,21,39],462⟩
def representative_3091 : Rep := ⟨![0,11,21,40],462⟩
def representative_3092 : Rep := ⟨![0,11,21,41],462⟩
def representative_3093 : Rep := ⟨![0,11,21,42],462⟩
def representative_3094 : Rep := ⟨![0,11,21,43],462⟩
def representative_3095 : Rep := ⟨![0,11,21,44],462⟩
def representative_3096 : Rep := ⟨![0,11,21,46],462⟩
def representative_3097 : Rep := ⟨![0,11,21,47],462⟩
def representative_3098 : Rep := ⟨![0,11,21,48],462⟩
def representative_3099 : Rep := ⟨![0,11,21,49],462⟩
def representative_3100 : Rep := ⟨![0,11,21,50],462⟩
def representative_3101 : Rep := ⟨![0,11,21,51],462⟩
def representative_3102 : Rep := ⟨![0,11,21,52],462⟩
def representative_3103 : Rep := ⟨![0,11,21,54],462⟩
def representative_3104 : Rep := ⟨![0,11,21,55],462⟩
def representative_3105 : Rep := ⟨![0,11,21,62],462⟩
def representative_3106 : Rep := ⟨![0,11,22,25],462⟩
def representative_3107 : Rep := ⟨![0,11,22,26],462⟩
def representative_3108 : Rep := ⟨![0,11,22,32],462⟩
def representative_3109 : Rep := ⟨![0,11,22,33],462⟩
def representative_3110 : Rep := ⟨![0,11,22,34],462⟩
def representative_3111 : Rep := ⟨![0,11,22,35],462⟩
def representative_3112 : Rep := ⟨![0,11,22,36],462⟩
def representative_3113 : Rep := ⟨![0,11,22,40],462⟩
def representative_3114 : Rep := ⟨![0,11,22,41],462⟩
def representative_3115 : Rep := ⟨![0,11,22,42],462⟩
def representative_3116 : Rep := ⟨![0,11,22,43],462⟩
def representative_3117 : Rep := ⟨![0,11,22,44],462⟩
def representative_3118 : Rep := ⟨![0,11,22,45],462⟩
def representative_3119 : Rep := ⟨![0,11,22,47],462⟩
def representative_3120 : Rep := ⟨![0,11,22,48],462⟩
def representative_3121 : Rep := ⟨![0,11,22,49],462⟩
def representative_3122 : Rep := ⟨![0,11,22,50],462⟩
def representative_3123 : Rep := ⟨![0,11,22,51],462⟩
def representative_3124 : Rep := ⟨![0,11,22,52],462⟩
def representative_3125 : Rep := ⟨![0,11,22,53],462⟩
def representative_3126 : Rep := ⟨![0,11,22,55],462⟩
def representative_3127 : Rep := ⟨![0,11,22,60],462⟩
def representative_3128 : Rep := ⟨![0,11,22,61],462⟩
def representative_3129 : Rep := ⟨![0,11,23,26],462⟩
def representative_3130 : Rep := ⟨![0,11,23,27],462⟩
def representative_3131 : Rep := ⟨![0,11,23,28],462⟩
def representative_3132 : Rep := ⟨![0,11,23,33],462⟩
def representative_3133 : Rep := ⟨![0,11,23,34],462⟩
def representative_3134 : Rep := ⟨![0,11,23,35],462⟩
def representative_3135 : Rep := ⟨![0,11,23,36],462⟩
theorem coefficient_3072 : validRep representative_3072 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3072)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3073 : validRep representative_3073 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3073)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3074 : validRep representative_3074 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3074)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3075 : validRep representative_3075 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3075)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3076 : validRep representative_3076 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3076)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3077 : validRep representative_3077 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3077)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3078 : validRep representative_3078 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3078)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3079 : validRep representative_3079 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3079)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3080 : validRep representative_3080 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3080)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3081 : validRep representative_3081 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3081)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3082 : validRep representative_3082 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3082)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3083 : validRep representative_3083 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3083)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3084 : validRep representative_3084 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3084)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3085 : validRep representative_3085 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3085)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3086 : validRep representative_3086 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3086)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3087 : validRep representative_3087 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3087)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3088 : validRep representative_3088 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3088)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3089 : validRep representative_3089 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3089)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3090 : validRep representative_3090 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3090)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3091 : validRep representative_3091 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3091)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3092 : validRep representative_3092 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3092)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3093 : validRep representative_3093 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3093)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3094 : validRep representative_3094 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3094)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3095 : validRep representative_3095 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3095)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3096 : validRep representative_3096 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3096)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3097 : validRep representative_3097 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3097)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3098 : validRep representative_3098 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3098)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3099 : validRep representative_3099 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3099)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3100 : validRep representative_3100 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3100)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3101 : validRep representative_3101 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3101)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3102 : validRep representative_3102 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3102)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3103 : validRep representative_3103 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3103)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3104 : validRep representative_3104 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3104)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3105 : validRep representative_3105 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3105)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3106 : validRep representative_3106 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3106)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3107 : validRep representative_3107 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3107)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3108 : validRep representative_3108 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3108)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3109 : validRep representative_3109 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3109)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3110 : validRep representative_3110 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3110)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3111 : validRep representative_3111 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3111)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3112 : validRep representative_3112 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3112)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3113 : validRep representative_3113 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3113)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3114 : validRep representative_3114 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3114)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3115 : validRep representative_3115 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3115)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3116 : validRep representative_3116 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3116)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3117 : validRep representative_3117 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3117)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3118 : validRep representative_3118 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3118)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3119 : validRep representative_3119 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3119)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3120 : validRep representative_3120 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3120)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3121 : validRep representative_3121 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3121)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3122 : validRep representative_3122 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3122)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3123 : validRep representative_3123 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3123)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3124 : validRep representative_3124 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3124)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3125 : validRep representative_3125 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3125)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3126 : validRep representative_3126 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3126)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3127 : validRep representative_3127 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3127)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3128 : validRep representative_3128 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3128)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3129 : validRep representative_3129 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3129)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3130 : validRep representative_3130 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3130)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3131 : validRep representative_3131 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3131)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3132 : validRep representative_3132 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3132)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3133 : validRep representative_3133 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3133)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3134 : validRep representative_3134 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3134)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3135 : validRep representative_3135 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3135)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_048 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3104 (QuarticIntegerRepresentativeTree.Tree.branch 3088 (QuarticIntegerRepresentativeTree.Tree.branch 3080 (QuarticIntegerRepresentativeTree.Tree.branch 3076 (QuarticIntegerRepresentativeTree.Tree.branch 3074 (QuarticIntegerRepresentativeTree.Tree.branch 3073 (QuarticIntegerRepresentativeTree.Tree.leaf 3072 representative_3072) (QuarticIntegerRepresentativeTree.Tree.leaf 3073 representative_3073)) (QuarticIntegerRepresentativeTree.Tree.branch 3075 (QuarticIntegerRepresentativeTree.Tree.leaf 3074 representative_3074) (QuarticIntegerRepresentativeTree.Tree.leaf 3075 representative_3075))) (QuarticIntegerRepresentativeTree.Tree.branch 3078 (QuarticIntegerRepresentativeTree.Tree.branch 3077 (QuarticIntegerRepresentativeTree.Tree.leaf 3076 representative_3076) (QuarticIntegerRepresentativeTree.Tree.leaf 3077 representative_3077)) (QuarticIntegerRepresentativeTree.Tree.branch 3079 (QuarticIntegerRepresentativeTree.Tree.leaf 3078 representative_3078) (QuarticIntegerRepresentativeTree.Tree.leaf 3079 representative_3079)))) (QuarticIntegerRepresentativeTree.Tree.branch 3084 (QuarticIntegerRepresentativeTree.Tree.branch 3082 (QuarticIntegerRepresentativeTree.Tree.branch 3081 (QuarticIntegerRepresentativeTree.Tree.leaf 3080 representative_3080) (QuarticIntegerRepresentativeTree.Tree.leaf 3081 representative_3081)) (QuarticIntegerRepresentativeTree.Tree.branch 3083 (QuarticIntegerRepresentativeTree.Tree.leaf 3082 representative_3082) (QuarticIntegerRepresentativeTree.Tree.leaf 3083 representative_3083))) (QuarticIntegerRepresentativeTree.Tree.branch 3086 (QuarticIntegerRepresentativeTree.Tree.branch 3085 (QuarticIntegerRepresentativeTree.Tree.leaf 3084 representative_3084) (QuarticIntegerRepresentativeTree.Tree.leaf 3085 representative_3085)) (QuarticIntegerRepresentativeTree.Tree.branch 3087 (QuarticIntegerRepresentativeTree.Tree.leaf 3086 representative_3086) (QuarticIntegerRepresentativeTree.Tree.leaf 3087 representative_3087))))) (QuarticIntegerRepresentativeTree.Tree.branch 3096 (QuarticIntegerRepresentativeTree.Tree.branch 3092 (QuarticIntegerRepresentativeTree.Tree.branch 3090 (QuarticIntegerRepresentativeTree.Tree.branch 3089 (QuarticIntegerRepresentativeTree.Tree.leaf 3088 representative_3088) (QuarticIntegerRepresentativeTree.Tree.leaf 3089 representative_3089)) (QuarticIntegerRepresentativeTree.Tree.branch 3091 (QuarticIntegerRepresentativeTree.Tree.leaf 3090 representative_3090) (QuarticIntegerRepresentativeTree.Tree.leaf 3091 representative_3091))) (QuarticIntegerRepresentativeTree.Tree.branch 3094 (QuarticIntegerRepresentativeTree.Tree.branch 3093 (QuarticIntegerRepresentativeTree.Tree.leaf 3092 representative_3092) (QuarticIntegerRepresentativeTree.Tree.leaf 3093 representative_3093)) (QuarticIntegerRepresentativeTree.Tree.branch 3095 (QuarticIntegerRepresentativeTree.Tree.leaf 3094 representative_3094) (QuarticIntegerRepresentativeTree.Tree.leaf 3095 representative_3095)))) (QuarticIntegerRepresentativeTree.Tree.branch 3100 (QuarticIntegerRepresentativeTree.Tree.branch 3098 (QuarticIntegerRepresentativeTree.Tree.branch 3097 (QuarticIntegerRepresentativeTree.Tree.leaf 3096 representative_3096) (QuarticIntegerRepresentativeTree.Tree.leaf 3097 representative_3097)) (QuarticIntegerRepresentativeTree.Tree.branch 3099 (QuarticIntegerRepresentativeTree.Tree.leaf 3098 representative_3098) (QuarticIntegerRepresentativeTree.Tree.leaf 3099 representative_3099))) (QuarticIntegerRepresentativeTree.Tree.branch 3102 (QuarticIntegerRepresentativeTree.Tree.branch 3101 (QuarticIntegerRepresentativeTree.Tree.leaf 3100 representative_3100) (QuarticIntegerRepresentativeTree.Tree.leaf 3101 representative_3101)) (QuarticIntegerRepresentativeTree.Tree.branch 3103 (QuarticIntegerRepresentativeTree.Tree.leaf 3102 representative_3102) (QuarticIntegerRepresentativeTree.Tree.leaf 3103 representative_3103)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3120 (QuarticIntegerRepresentativeTree.Tree.branch 3112 (QuarticIntegerRepresentativeTree.Tree.branch 3108 (QuarticIntegerRepresentativeTree.Tree.branch 3106 (QuarticIntegerRepresentativeTree.Tree.branch 3105 (QuarticIntegerRepresentativeTree.Tree.leaf 3104 representative_3104) (QuarticIntegerRepresentativeTree.Tree.leaf 3105 representative_3105)) (QuarticIntegerRepresentativeTree.Tree.branch 3107 (QuarticIntegerRepresentativeTree.Tree.leaf 3106 representative_3106) (QuarticIntegerRepresentativeTree.Tree.leaf 3107 representative_3107))) (QuarticIntegerRepresentativeTree.Tree.branch 3110 (QuarticIntegerRepresentativeTree.Tree.branch 3109 (QuarticIntegerRepresentativeTree.Tree.leaf 3108 representative_3108) (QuarticIntegerRepresentativeTree.Tree.leaf 3109 representative_3109)) (QuarticIntegerRepresentativeTree.Tree.branch 3111 (QuarticIntegerRepresentativeTree.Tree.leaf 3110 representative_3110) (QuarticIntegerRepresentativeTree.Tree.leaf 3111 representative_3111)))) (QuarticIntegerRepresentativeTree.Tree.branch 3116 (QuarticIntegerRepresentativeTree.Tree.branch 3114 (QuarticIntegerRepresentativeTree.Tree.branch 3113 (QuarticIntegerRepresentativeTree.Tree.leaf 3112 representative_3112) (QuarticIntegerRepresentativeTree.Tree.leaf 3113 representative_3113)) (QuarticIntegerRepresentativeTree.Tree.branch 3115 (QuarticIntegerRepresentativeTree.Tree.leaf 3114 representative_3114) (QuarticIntegerRepresentativeTree.Tree.leaf 3115 representative_3115))) (QuarticIntegerRepresentativeTree.Tree.branch 3118 (QuarticIntegerRepresentativeTree.Tree.branch 3117 (QuarticIntegerRepresentativeTree.Tree.leaf 3116 representative_3116) (QuarticIntegerRepresentativeTree.Tree.leaf 3117 representative_3117)) (QuarticIntegerRepresentativeTree.Tree.branch 3119 (QuarticIntegerRepresentativeTree.Tree.leaf 3118 representative_3118) (QuarticIntegerRepresentativeTree.Tree.leaf 3119 representative_3119))))) (QuarticIntegerRepresentativeTree.Tree.branch 3128 (QuarticIntegerRepresentativeTree.Tree.branch 3124 (QuarticIntegerRepresentativeTree.Tree.branch 3122 (QuarticIntegerRepresentativeTree.Tree.branch 3121 (QuarticIntegerRepresentativeTree.Tree.leaf 3120 representative_3120) (QuarticIntegerRepresentativeTree.Tree.leaf 3121 representative_3121)) (QuarticIntegerRepresentativeTree.Tree.branch 3123 (QuarticIntegerRepresentativeTree.Tree.leaf 3122 representative_3122) (QuarticIntegerRepresentativeTree.Tree.leaf 3123 representative_3123))) (QuarticIntegerRepresentativeTree.Tree.branch 3126 (QuarticIntegerRepresentativeTree.Tree.branch 3125 (QuarticIntegerRepresentativeTree.Tree.leaf 3124 representative_3124) (QuarticIntegerRepresentativeTree.Tree.leaf 3125 representative_3125)) (QuarticIntegerRepresentativeTree.Tree.branch 3127 (QuarticIntegerRepresentativeTree.Tree.leaf 3126 representative_3126) (QuarticIntegerRepresentativeTree.Tree.leaf 3127 representative_3127)))) (QuarticIntegerRepresentativeTree.Tree.branch 3132 (QuarticIntegerRepresentativeTree.Tree.branch 3130 (QuarticIntegerRepresentativeTree.Tree.branch 3129 (QuarticIntegerRepresentativeTree.Tree.leaf 3128 representative_3128) (QuarticIntegerRepresentativeTree.Tree.leaf 3129 representative_3129)) (QuarticIntegerRepresentativeTree.Tree.branch 3131 (QuarticIntegerRepresentativeTree.Tree.leaf 3130 representative_3130) (QuarticIntegerRepresentativeTree.Tree.leaf 3131 representative_3131))) (QuarticIntegerRepresentativeTree.Tree.branch 3134 (QuarticIntegerRepresentativeTree.Tree.branch 3133 (QuarticIntegerRepresentativeTree.Tree.leaf 3132 representative_3132) (QuarticIntegerRepresentativeTree.Tree.leaf 3133 representative_3133)) (QuarticIntegerRepresentativeTree.Tree.branch 3135 (QuarticIntegerRepresentativeTree.Tree.leaf 3134 representative_3134) (QuarticIntegerRepresentativeTree.Tree.leaf 3135 representative_3135)))))))
theorem accepted_048 : All validRep tree_048 := ⟨⟨⟨⟨⟨⟨coefficient_3072,coefficient_3073⟩,⟨coefficient_3074,coefficient_3075⟩⟩,⟨⟨coefficient_3076,coefficient_3077⟩,⟨coefficient_3078,coefficient_3079⟩⟩⟩,⟨⟨⟨coefficient_3080,coefficient_3081⟩,⟨coefficient_3082,coefficient_3083⟩⟩,⟨⟨coefficient_3084,coefficient_3085⟩,⟨coefficient_3086,coefficient_3087⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3088,coefficient_3089⟩,⟨coefficient_3090,coefficient_3091⟩⟩,⟨⟨coefficient_3092,coefficient_3093⟩,⟨coefficient_3094,coefficient_3095⟩⟩⟩,⟨⟨⟨coefficient_3096,coefficient_3097⟩,⟨coefficient_3098,coefficient_3099⟩⟩,⟨⟨coefficient_3100,coefficient_3101⟩,⟨coefficient_3102,coefficient_3103⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3104,coefficient_3105⟩,⟨coefficient_3106,coefficient_3107⟩⟩,⟨⟨coefficient_3108,coefficient_3109⟩,⟨coefficient_3110,coefficient_3111⟩⟩⟩,⟨⟨⟨coefficient_3112,coefficient_3113⟩,⟨coefficient_3114,coefficient_3115⟩⟩,⟨⟨coefficient_3116,coefficient_3117⟩,⟨coefficient_3118,coefficient_3119⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3120,coefficient_3121⟩,⟨coefficient_3122,coefficient_3123⟩⟩,⟨⟨coefficient_3124,coefficient_3125⟩,⟨coefficient_3126,coefficient_3127⟩⟩⟩,⟨⟨⟨coefficient_3128,coefficient_3129⟩,⟨coefficient_3130,coefficient_3131⟩⟩,⟨⟨coefficient_3132,coefficient_3133⟩,⟨coefficient_3134,coefficient_3135⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

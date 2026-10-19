import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3136 : Rep := ⟨![0,11,23,37],462⟩
def representative_3137 : Rep := ⟨![0,11,23,41],462⟩
def representative_3138 : Rep := ⟨![0,11,23,42],462⟩
def representative_3139 : Rep := ⟨![0,11,23,43],462⟩
def representative_3140 : Rep := ⟨![0,11,23,44],462⟩
def representative_3141 : Rep := ⟨![0,11,23,45],462⟩
def representative_3142 : Rep := ⟨![0,11,23,48],462⟩
def representative_3143 : Rep := ⟨![0,11,23,49],462⟩
def representative_3144 : Rep := ⟨![0,11,23,50],462⟩
def representative_3145 : Rep := ⟨![0,11,23,51],462⟩
def representative_3146 : Rep := ⟨![0,11,23,52],462⟩
def representative_3147 : Rep := ⟨![0,11,23,53],462⟩
def representative_3148 : Rep := ⟨![0,11,23,54],462⟩
def representative_3149 : Rep := ⟨![0,11,23,60],462⟩
def representative_3150 : Rep := ⟨![0,11,24,35],462⟩
def representative_3151 : Rep := ⟨![0,11,24,36],462⟩
def representative_3152 : Rep := ⟨![0,11,24,37],462⟩
def representative_3153 : Rep := ⟨![0,11,24,42],462⟩
def representative_3154 : Rep := ⟨![0,11,24,43],462⟩
def representative_3155 : Rep := ⟨![0,11,24,44],462⟩
def representative_3156 : Rep := ⟨![0,11,24,45],462⟩
def representative_3157 : Rep := ⟨![0,11,24,46],462⟩
def representative_3158 : Rep := ⟨![0,11,24,50],462⟩
def representative_3159 : Rep := ⟨![0,11,24,51],462⟩
def representative_3160 : Rep := ⟨![0,11,24,52],462⟩
def representative_3161 : Rep := ⟨![0,11,24,53],462⟩
def representative_3162 : Rep := ⟨![0,11,24,54],462⟩
def representative_3163 : Rep := ⟨![0,11,25,36],462⟩
def representative_3164 : Rep := ⟨![0,11,25,37],462⟩
def representative_3165 : Rep := ⟨![0,11,25,38],462⟩
def representative_3166 : Rep := ⟨![0,11,25,43],462⟩
def representative_3167 : Rep := ⟨![0,11,25,44],462⟩
def representative_3168 : Rep := ⟨![0,11,25,45],462⟩
def representative_3169 : Rep := ⟨![0,11,25,46],462⟩
def representative_3170 : Rep := ⟨![0,11,25,47],462⟩
def representative_3171 : Rep := ⟨![0,11,25,52],462⟩
def representative_3172 : Rep := ⟨![0,11,25,53],462⟩
def representative_3173 : Rep := ⟨![0,11,25,54],462⟩
def representative_3174 : Rep := ⟨![0,11,25,55],462⟩
def representative_3175 : Rep := ⟨![0,11,26,37],462⟩
def representative_3176 : Rep := ⟨![0,11,26,38],462⟩
def representative_3177 : Rep := ⟨![0,11,26,39],462⟩
def representative_3178 : Rep := ⟨![0,11,26,40],462⟩
def representative_3179 : Rep := ⟨![0,11,26,44],462⟩
def representative_3180 : Rep := ⟨![0,11,26,45],462⟩
def representative_3181 : Rep := ⟨![0,11,26,46],462⟩
def representative_3182 : Rep := ⟨![0,11,26,47],462⟩
def representative_3183 : Rep := ⟨![0,11,26,48],462⟩
def representative_3184 : Rep := ⟨![0,11,26,52],462⟩
def representative_3185 : Rep := ⟨![0,11,26,53],462⟩
def representative_3186 : Rep := ⟨![0,11,26,54],462⟩
def representative_3187 : Rep := ⟨![0,11,26,55],462⟩
def representative_3188 : Rep := ⟨![0,11,27,32],462⟩
def representative_3189 : Rep := ⟨![0,11,27,38],462⟩
def representative_3190 : Rep := ⟨![0,11,27,39],462⟩
def representative_3191 : Rep := ⟨![0,11,27,40],462⟩
def representative_3192 : Rep := ⟨![0,11,27,41],462⟩
def representative_3193 : Rep := ⟨![0,11,27,45],462⟩
def representative_3194 : Rep := ⟨![0,11,27,46],462⟩
def representative_3195 : Rep := ⟨![0,11,27,47],462⟩
def representative_3196 : Rep := ⟨![0,11,27,48],462⟩
def representative_3197 : Rep := ⟨![0,11,27,53],462⟩
def representative_3198 : Rep := ⟨![0,11,27,54],462⟩
def representative_3199 : Rep := ⟨![0,11,27,55],462⟩
theorem coefficient_3136 : validRep representative_3136 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3136)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3137 : validRep representative_3137 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3137)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3138 : validRep representative_3138 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3138)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3139 : validRep representative_3139 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3139)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3140 : validRep representative_3140 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3140)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3141 : validRep representative_3141 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3141)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3142 : validRep representative_3142 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3142)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3143 : validRep representative_3143 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3143)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3144 : validRep representative_3144 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3144)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3145 : validRep representative_3145 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3145)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3146 : validRep representative_3146 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3146)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3147 : validRep representative_3147 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3147)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3148 : validRep representative_3148 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3148)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3149 : validRep representative_3149 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3149)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3150 : validRep representative_3150 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3150)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3151 : validRep representative_3151 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3151)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3152 : validRep representative_3152 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3152)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3153 : validRep representative_3153 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3153)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3154 : validRep representative_3154 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3154)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3155 : validRep representative_3155 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3155)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3156 : validRep representative_3156 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3156)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3157 : validRep representative_3157 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3157)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3158 : validRep representative_3158 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3158)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3159 : validRep representative_3159 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3159)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3160 : validRep representative_3160 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3160)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3161 : validRep representative_3161 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3161)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3162 : validRep representative_3162 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3162)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3163 : validRep representative_3163 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3163)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3164 : validRep representative_3164 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3164)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3165 : validRep representative_3165 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3165)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3166 : validRep representative_3166 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3166)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3167 : validRep representative_3167 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3167)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3168 : validRep representative_3168 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3168)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3169 : validRep representative_3169 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3169)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3170 : validRep representative_3170 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3170)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3171 : validRep representative_3171 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3171)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3172 : validRep representative_3172 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3172)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3173 : validRep representative_3173 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3173)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3174 : validRep representative_3174 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3174)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3175 : validRep representative_3175 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3175)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3176 : validRep representative_3176 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3176)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3177 : validRep representative_3177 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3177)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3178 : validRep representative_3178 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3178)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3179 : validRep representative_3179 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3179)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3180 : validRep representative_3180 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3180)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3181 : validRep representative_3181 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3181)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3182 : validRep representative_3182 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3182)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3183 : validRep representative_3183 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3183)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3184 : validRep representative_3184 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3184)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3185 : validRep representative_3185 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3185)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3186 : validRep representative_3186 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3186)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3187 : validRep representative_3187 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3187)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3188 : validRep representative_3188 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3188)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3189 : validRep representative_3189 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3189)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3190 : validRep representative_3190 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3190)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3191 : validRep representative_3191 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3191)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3192 : validRep representative_3192 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3192)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3193 : validRep representative_3193 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3193)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3194 : validRep representative_3194 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3194)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3195 : validRep representative_3195 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3195)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3196 : validRep representative_3196 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3196)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3197 : validRep representative_3197 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3197)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3198 : validRep representative_3198 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3198)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3199 : validRep representative_3199 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3199)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_049 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3168 (QuarticIntegerRepresentativeTree.Tree.branch 3152 (QuarticIntegerRepresentativeTree.Tree.branch 3144 (QuarticIntegerRepresentativeTree.Tree.branch 3140 (QuarticIntegerRepresentativeTree.Tree.branch 3138 (QuarticIntegerRepresentativeTree.Tree.branch 3137 (QuarticIntegerRepresentativeTree.Tree.leaf 3136 representative_3136) (QuarticIntegerRepresentativeTree.Tree.leaf 3137 representative_3137)) (QuarticIntegerRepresentativeTree.Tree.branch 3139 (QuarticIntegerRepresentativeTree.Tree.leaf 3138 representative_3138) (QuarticIntegerRepresentativeTree.Tree.leaf 3139 representative_3139))) (QuarticIntegerRepresentativeTree.Tree.branch 3142 (QuarticIntegerRepresentativeTree.Tree.branch 3141 (QuarticIntegerRepresentativeTree.Tree.leaf 3140 representative_3140) (QuarticIntegerRepresentativeTree.Tree.leaf 3141 representative_3141)) (QuarticIntegerRepresentativeTree.Tree.branch 3143 (QuarticIntegerRepresentativeTree.Tree.leaf 3142 representative_3142) (QuarticIntegerRepresentativeTree.Tree.leaf 3143 representative_3143)))) (QuarticIntegerRepresentativeTree.Tree.branch 3148 (QuarticIntegerRepresentativeTree.Tree.branch 3146 (QuarticIntegerRepresentativeTree.Tree.branch 3145 (QuarticIntegerRepresentativeTree.Tree.leaf 3144 representative_3144) (QuarticIntegerRepresentativeTree.Tree.leaf 3145 representative_3145)) (QuarticIntegerRepresentativeTree.Tree.branch 3147 (QuarticIntegerRepresentativeTree.Tree.leaf 3146 representative_3146) (QuarticIntegerRepresentativeTree.Tree.leaf 3147 representative_3147))) (QuarticIntegerRepresentativeTree.Tree.branch 3150 (QuarticIntegerRepresentativeTree.Tree.branch 3149 (QuarticIntegerRepresentativeTree.Tree.leaf 3148 representative_3148) (QuarticIntegerRepresentativeTree.Tree.leaf 3149 representative_3149)) (QuarticIntegerRepresentativeTree.Tree.branch 3151 (QuarticIntegerRepresentativeTree.Tree.leaf 3150 representative_3150) (QuarticIntegerRepresentativeTree.Tree.leaf 3151 representative_3151))))) (QuarticIntegerRepresentativeTree.Tree.branch 3160 (QuarticIntegerRepresentativeTree.Tree.branch 3156 (QuarticIntegerRepresentativeTree.Tree.branch 3154 (QuarticIntegerRepresentativeTree.Tree.branch 3153 (QuarticIntegerRepresentativeTree.Tree.leaf 3152 representative_3152) (QuarticIntegerRepresentativeTree.Tree.leaf 3153 representative_3153)) (QuarticIntegerRepresentativeTree.Tree.branch 3155 (QuarticIntegerRepresentativeTree.Tree.leaf 3154 representative_3154) (QuarticIntegerRepresentativeTree.Tree.leaf 3155 representative_3155))) (QuarticIntegerRepresentativeTree.Tree.branch 3158 (QuarticIntegerRepresentativeTree.Tree.branch 3157 (QuarticIntegerRepresentativeTree.Tree.leaf 3156 representative_3156) (QuarticIntegerRepresentativeTree.Tree.leaf 3157 representative_3157)) (QuarticIntegerRepresentativeTree.Tree.branch 3159 (QuarticIntegerRepresentativeTree.Tree.leaf 3158 representative_3158) (QuarticIntegerRepresentativeTree.Tree.leaf 3159 representative_3159)))) (QuarticIntegerRepresentativeTree.Tree.branch 3164 (QuarticIntegerRepresentativeTree.Tree.branch 3162 (QuarticIntegerRepresentativeTree.Tree.branch 3161 (QuarticIntegerRepresentativeTree.Tree.leaf 3160 representative_3160) (QuarticIntegerRepresentativeTree.Tree.leaf 3161 representative_3161)) (QuarticIntegerRepresentativeTree.Tree.branch 3163 (QuarticIntegerRepresentativeTree.Tree.leaf 3162 representative_3162) (QuarticIntegerRepresentativeTree.Tree.leaf 3163 representative_3163))) (QuarticIntegerRepresentativeTree.Tree.branch 3166 (QuarticIntegerRepresentativeTree.Tree.branch 3165 (QuarticIntegerRepresentativeTree.Tree.leaf 3164 representative_3164) (QuarticIntegerRepresentativeTree.Tree.leaf 3165 representative_3165)) (QuarticIntegerRepresentativeTree.Tree.branch 3167 (QuarticIntegerRepresentativeTree.Tree.leaf 3166 representative_3166) (QuarticIntegerRepresentativeTree.Tree.leaf 3167 representative_3167)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3184 (QuarticIntegerRepresentativeTree.Tree.branch 3176 (QuarticIntegerRepresentativeTree.Tree.branch 3172 (QuarticIntegerRepresentativeTree.Tree.branch 3170 (QuarticIntegerRepresentativeTree.Tree.branch 3169 (QuarticIntegerRepresentativeTree.Tree.leaf 3168 representative_3168) (QuarticIntegerRepresentativeTree.Tree.leaf 3169 representative_3169)) (QuarticIntegerRepresentativeTree.Tree.branch 3171 (QuarticIntegerRepresentativeTree.Tree.leaf 3170 representative_3170) (QuarticIntegerRepresentativeTree.Tree.leaf 3171 representative_3171))) (QuarticIntegerRepresentativeTree.Tree.branch 3174 (QuarticIntegerRepresentativeTree.Tree.branch 3173 (QuarticIntegerRepresentativeTree.Tree.leaf 3172 representative_3172) (QuarticIntegerRepresentativeTree.Tree.leaf 3173 representative_3173)) (QuarticIntegerRepresentativeTree.Tree.branch 3175 (QuarticIntegerRepresentativeTree.Tree.leaf 3174 representative_3174) (QuarticIntegerRepresentativeTree.Tree.leaf 3175 representative_3175)))) (QuarticIntegerRepresentativeTree.Tree.branch 3180 (QuarticIntegerRepresentativeTree.Tree.branch 3178 (QuarticIntegerRepresentativeTree.Tree.branch 3177 (QuarticIntegerRepresentativeTree.Tree.leaf 3176 representative_3176) (QuarticIntegerRepresentativeTree.Tree.leaf 3177 representative_3177)) (QuarticIntegerRepresentativeTree.Tree.branch 3179 (QuarticIntegerRepresentativeTree.Tree.leaf 3178 representative_3178) (QuarticIntegerRepresentativeTree.Tree.leaf 3179 representative_3179))) (QuarticIntegerRepresentativeTree.Tree.branch 3182 (QuarticIntegerRepresentativeTree.Tree.branch 3181 (QuarticIntegerRepresentativeTree.Tree.leaf 3180 representative_3180) (QuarticIntegerRepresentativeTree.Tree.leaf 3181 representative_3181)) (QuarticIntegerRepresentativeTree.Tree.branch 3183 (QuarticIntegerRepresentativeTree.Tree.leaf 3182 representative_3182) (QuarticIntegerRepresentativeTree.Tree.leaf 3183 representative_3183))))) (QuarticIntegerRepresentativeTree.Tree.branch 3192 (QuarticIntegerRepresentativeTree.Tree.branch 3188 (QuarticIntegerRepresentativeTree.Tree.branch 3186 (QuarticIntegerRepresentativeTree.Tree.branch 3185 (QuarticIntegerRepresentativeTree.Tree.leaf 3184 representative_3184) (QuarticIntegerRepresentativeTree.Tree.leaf 3185 representative_3185)) (QuarticIntegerRepresentativeTree.Tree.branch 3187 (QuarticIntegerRepresentativeTree.Tree.leaf 3186 representative_3186) (QuarticIntegerRepresentativeTree.Tree.leaf 3187 representative_3187))) (QuarticIntegerRepresentativeTree.Tree.branch 3190 (QuarticIntegerRepresentativeTree.Tree.branch 3189 (QuarticIntegerRepresentativeTree.Tree.leaf 3188 representative_3188) (QuarticIntegerRepresentativeTree.Tree.leaf 3189 representative_3189)) (QuarticIntegerRepresentativeTree.Tree.branch 3191 (QuarticIntegerRepresentativeTree.Tree.leaf 3190 representative_3190) (QuarticIntegerRepresentativeTree.Tree.leaf 3191 representative_3191)))) (QuarticIntegerRepresentativeTree.Tree.branch 3196 (QuarticIntegerRepresentativeTree.Tree.branch 3194 (QuarticIntegerRepresentativeTree.Tree.branch 3193 (QuarticIntegerRepresentativeTree.Tree.leaf 3192 representative_3192) (QuarticIntegerRepresentativeTree.Tree.leaf 3193 representative_3193)) (QuarticIntegerRepresentativeTree.Tree.branch 3195 (QuarticIntegerRepresentativeTree.Tree.leaf 3194 representative_3194) (QuarticIntegerRepresentativeTree.Tree.leaf 3195 representative_3195))) (QuarticIntegerRepresentativeTree.Tree.branch 3198 (QuarticIntegerRepresentativeTree.Tree.branch 3197 (QuarticIntegerRepresentativeTree.Tree.leaf 3196 representative_3196) (QuarticIntegerRepresentativeTree.Tree.leaf 3197 representative_3197)) (QuarticIntegerRepresentativeTree.Tree.branch 3199 (QuarticIntegerRepresentativeTree.Tree.leaf 3198 representative_3198) (QuarticIntegerRepresentativeTree.Tree.leaf 3199 representative_3199)))))))
theorem accepted_049 : All validRep tree_049 := ⟨⟨⟨⟨⟨⟨coefficient_3136,coefficient_3137⟩,⟨coefficient_3138,coefficient_3139⟩⟩,⟨⟨coefficient_3140,coefficient_3141⟩,⟨coefficient_3142,coefficient_3143⟩⟩⟩,⟨⟨⟨coefficient_3144,coefficient_3145⟩,⟨coefficient_3146,coefficient_3147⟩⟩,⟨⟨coefficient_3148,coefficient_3149⟩,⟨coefficient_3150,coefficient_3151⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3152,coefficient_3153⟩,⟨coefficient_3154,coefficient_3155⟩⟩,⟨⟨coefficient_3156,coefficient_3157⟩,⟨coefficient_3158,coefficient_3159⟩⟩⟩,⟨⟨⟨coefficient_3160,coefficient_3161⟩,⟨coefficient_3162,coefficient_3163⟩⟩,⟨⟨coefficient_3164,coefficient_3165⟩,⟨coefficient_3166,coefficient_3167⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3168,coefficient_3169⟩,⟨coefficient_3170,coefficient_3171⟩⟩,⟨⟨coefficient_3172,coefficient_3173⟩,⟨coefficient_3174,coefficient_3175⟩⟩⟩,⟨⟨⟨coefficient_3176,coefficient_3177⟩,⟨coefficient_3178,coefficient_3179⟩⟩,⟨⟨coefficient_3180,coefficient_3181⟩,⟨coefficient_3182,coefficient_3183⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3184,coefficient_3185⟩,⟨coefficient_3186,coefficient_3187⟩⟩,⟨⟨coefficient_3188,coefficient_3189⟩,⟨coefficient_3190,coefficient_3191⟩⟩⟩,⟨⟨⟨coefficient_3192,coefficient_3193⟩,⟨coefficient_3194,coefficient_3195⟩⟩,⟨⟨coefficient_3196,coefficient_3197⟩,⟨coefficient_3198,coefficient_3199⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

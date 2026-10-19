import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3200 : Rep := ⟨![0,11,28,32],462⟩
def representative_3201 : Rep := ⟨![0,11,28,39],462⟩
def representative_3202 : Rep := ⟨![0,11,28,40],462⟩
def representative_3203 : Rep := ⟨![0,11,28,41],462⟩
def representative_3204 : Rep := ⟨![0,11,28,42],462⟩
def representative_3205 : Rep := ⟨![0,11,28,46],462⟩
def representative_3206 : Rep := ⟨![0,11,28,47],462⟩
def representative_3207 : Rep := ⟨![0,11,28,54],462⟩
def representative_3208 : Rep := ⟨![0,11,28,55],462⟩
def representative_3209 : Rep := ⟨![0,11,29,32],462⟩
def representative_3210 : Rep := ⟨![0,11,29,33],462⟩
def representative_3211 : Rep := ⟨![0,11,29,40],462⟩
def representative_3212 : Rep := ⟨![0,11,29,41],462⟩
def representative_3213 : Rep := ⟨![0,11,29,42],462⟩
def representative_3214 : Rep := ⟨![0,11,29,43],462⟩
def representative_3215 : Rep := ⟨![0,11,29,47],462⟩
def representative_3216 : Rep := ⟨![0,11,29,54],462⟩
def representative_3217 : Rep := ⟨![0,11,30,33],462⟩
def representative_3218 : Rep := ⟨![0,11,30,34],462⟩
def representative_3219 : Rep := ⟨![0,11,30,40],462⟩
def representative_3220 : Rep := ⟨![0,11,30,41],462⟩
def representative_3221 : Rep := ⟨![0,11,30,42],462⟩
def representative_3222 : Rep := ⟨![0,11,30,43],462⟩
def representative_3223 : Rep := ⟨![0,11,30,44],462⟩
def representative_3224 : Rep := ⟨![0,11,30,52],462⟩
def representative_3225 : Rep := ⟨![0,11,30,53],462⟩
def representative_3226 : Rep := ⟨![0,11,31,34],462⟩
def representative_3227 : Rep := ⟨![0,11,31,35],462⟩
def representative_3228 : Rep := ⟨![0,11,31,36],462⟩
def representative_3229 : Rep := ⟨![0,11,31,41],462⟩
def representative_3230 : Rep := ⟨![0,11,31,42],462⟩
def representative_3231 : Rep := ⟨![0,11,31,43],462⟩
def representative_3232 : Rep := ⟨![0,11,31,44],462⟩
def representative_3233 : Rep := ⟨![0,11,31,45],462⟩
def representative_3234 : Rep := ⟨![0,11,31,52],462⟩
def representative_3235 : Rep := ⟨![0,11,32,43],462⟩
def representative_3236 : Rep := ⟨![0,11,32,44],462⟩
def representative_3237 : Rep := ⟨![0,11,32,45],462⟩
def representative_3238 : Rep := ⟨![0,11,33,44],462⟩
def representative_3239 : Rep := ⟨![0,11,33,45],462⟩
def representative_3240 : Rep := ⟨![0,11,33,46],462⟩
def representative_3241 : Rep := ⟨![0,11,34,45],462⟩
def representative_3242 : Rep := ⟨![0,11,34,46],462⟩
def representative_3243 : Rep := ⟨![0,11,34,47],462⟩
def representative_3244 : Rep := ⟨![0,11,35,40],462⟩
def representative_3245 : Rep := ⟨![0,11,35,46],462⟩
def representative_3246 : Rep := ⟨![0,11,35,47],462⟩
def representative_3247 : Rep := ⟨![0,11,36,47],462⟩
def representative_3248 : Rep := ⟨![0,11,39,44],462⟩
def representative_3249 : Rep := ⟨![0,12,1,13],462⟩
def representative_3250 : Rep := ⟨![0,12,1,19],462⟩
def representative_3251 : Rep := ⟨![0,12,1,20],462⟩
def representative_3252 : Rep := ⟨![0,12,1,21],462⟩
def representative_3253 : Rep := ⟨![0,12,1,22],462⟩
def representative_3254 : Rep := ⟨![0,12,1,23],462⟩
def representative_3255 : Rep := ⟨![0,12,1,27],462⟩
def representative_3256 : Rep := ⟨![0,12,1,28],462⟩
def representative_3257 : Rep := ⟨![0,12,1,29],462⟩
def representative_3258 : Rep := ⟨![0,12,1,30],462⟩
def representative_3259 : Rep := ⟨![0,12,1,31],462⟩
def representative_3260 : Rep := ⟨![0,12,1,32],462⟩
def representative_3261 : Rep := ⟨![0,12,1,34],462⟩
def representative_3262 : Rep := ⟨![0,12,1,35],462⟩
def representative_3263 : Rep := ⟨![0,12,1,36],462⟩
theorem coefficient_3200 : validRep representative_3200 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3200)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3201 : validRep representative_3201 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3201)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3202 : validRep representative_3202 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3202)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3203 : validRep representative_3203 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3203)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3204 : validRep representative_3204 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3204)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3205 : validRep representative_3205 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3205)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3206 : validRep representative_3206 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3206)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3207 : validRep representative_3207 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3207)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3208 : validRep representative_3208 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3208)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3209 : validRep representative_3209 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3209)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3210 : validRep representative_3210 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3210)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3211 : validRep representative_3211 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3211)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3212 : validRep representative_3212 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3212)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3213 : validRep representative_3213 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3213)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3214 : validRep representative_3214 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3214)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3215 : validRep representative_3215 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3215)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3216 : validRep representative_3216 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3216)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3217 : validRep representative_3217 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3217)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3218 : validRep representative_3218 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3218)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3219 : validRep representative_3219 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3219)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3220 : validRep representative_3220 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3220)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3221 : validRep representative_3221 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3221)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3222 : validRep representative_3222 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3222)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3223 : validRep representative_3223 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3223)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3224 : validRep representative_3224 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3224)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3225 : validRep representative_3225 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3225)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3226 : validRep representative_3226 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3226)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3227 : validRep representative_3227 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3227)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3228 : validRep representative_3228 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3228)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3229 : validRep representative_3229 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3229)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3230 : validRep representative_3230 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3230)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3231 : validRep representative_3231 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3231)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3232 : validRep representative_3232 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3232)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3233 : validRep representative_3233 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3233)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3234 : validRep representative_3234 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3234)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3235 : validRep representative_3235 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3235)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3236 : validRep representative_3236 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3236)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3237 : validRep representative_3237 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3237)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3238 : validRep representative_3238 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3238)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3239 : validRep representative_3239 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3239)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3240 : validRep representative_3240 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3240)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3241 : validRep representative_3241 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3241)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3242 : validRep representative_3242 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3242)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3243 : validRep representative_3243 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3243)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3244 : validRep representative_3244 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3244)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3245 : validRep representative_3245 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3245)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3246 : validRep representative_3246 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3246)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3247 : validRep representative_3247 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3247)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3248 : validRep representative_3248 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3248)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3249 : validRep representative_3249 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3249)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3250 : validRep representative_3250 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3250)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3251 : validRep representative_3251 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3251)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3252 : validRep representative_3252 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3252)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3253 : validRep representative_3253 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3253)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3254 : validRep representative_3254 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3254)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3255 : validRep representative_3255 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3255)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3256 : validRep representative_3256 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3256)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3257 : validRep representative_3257 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3257)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3258 : validRep representative_3258 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3258)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3259 : validRep representative_3259 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3259)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3260 : validRep representative_3260 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3260)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3261 : validRep representative_3261 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3261)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3262 : validRep representative_3262 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3262)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3263 : validRep representative_3263 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3263)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_050 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3232 (QuarticIntegerRepresentativeTree.Tree.branch 3216 (QuarticIntegerRepresentativeTree.Tree.branch 3208 (QuarticIntegerRepresentativeTree.Tree.branch 3204 (QuarticIntegerRepresentativeTree.Tree.branch 3202 (QuarticIntegerRepresentativeTree.Tree.branch 3201 (QuarticIntegerRepresentativeTree.Tree.leaf 3200 representative_3200) (QuarticIntegerRepresentativeTree.Tree.leaf 3201 representative_3201)) (QuarticIntegerRepresentativeTree.Tree.branch 3203 (QuarticIntegerRepresentativeTree.Tree.leaf 3202 representative_3202) (QuarticIntegerRepresentativeTree.Tree.leaf 3203 representative_3203))) (QuarticIntegerRepresentativeTree.Tree.branch 3206 (QuarticIntegerRepresentativeTree.Tree.branch 3205 (QuarticIntegerRepresentativeTree.Tree.leaf 3204 representative_3204) (QuarticIntegerRepresentativeTree.Tree.leaf 3205 representative_3205)) (QuarticIntegerRepresentativeTree.Tree.branch 3207 (QuarticIntegerRepresentativeTree.Tree.leaf 3206 representative_3206) (QuarticIntegerRepresentativeTree.Tree.leaf 3207 representative_3207)))) (QuarticIntegerRepresentativeTree.Tree.branch 3212 (QuarticIntegerRepresentativeTree.Tree.branch 3210 (QuarticIntegerRepresentativeTree.Tree.branch 3209 (QuarticIntegerRepresentativeTree.Tree.leaf 3208 representative_3208) (QuarticIntegerRepresentativeTree.Tree.leaf 3209 representative_3209)) (QuarticIntegerRepresentativeTree.Tree.branch 3211 (QuarticIntegerRepresentativeTree.Tree.leaf 3210 representative_3210) (QuarticIntegerRepresentativeTree.Tree.leaf 3211 representative_3211))) (QuarticIntegerRepresentativeTree.Tree.branch 3214 (QuarticIntegerRepresentativeTree.Tree.branch 3213 (QuarticIntegerRepresentativeTree.Tree.leaf 3212 representative_3212) (QuarticIntegerRepresentativeTree.Tree.leaf 3213 representative_3213)) (QuarticIntegerRepresentativeTree.Tree.branch 3215 (QuarticIntegerRepresentativeTree.Tree.leaf 3214 representative_3214) (QuarticIntegerRepresentativeTree.Tree.leaf 3215 representative_3215))))) (QuarticIntegerRepresentativeTree.Tree.branch 3224 (QuarticIntegerRepresentativeTree.Tree.branch 3220 (QuarticIntegerRepresentativeTree.Tree.branch 3218 (QuarticIntegerRepresentativeTree.Tree.branch 3217 (QuarticIntegerRepresentativeTree.Tree.leaf 3216 representative_3216) (QuarticIntegerRepresentativeTree.Tree.leaf 3217 representative_3217)) (QuarticIntegerRepresentativeTree.Tree.branch 3219 (QuarticIntegerRepresentativeTree.Tree.leaf 3218 representative_3218) (QuarticIntegerRepresentativeTree.Tree.leaf 3219 representative_3219))) (QuarticIntegerRepresentativeTree.Tree.branch 3222 (QuarticIntegerRepresentativeTree.Tree.branch 3221 (QuarticIntegerRepresentativeTree.Tree.leaf 3220 representative_3220) (QuarticIntegerRepresentativeTree.Tree.leaf 3221 representative_3221)) (QuarticIntegerRepresentativeTree.Tree.branch 3223 (QuarticIntegerRepresentativeTree.Tree.leaf 3222 representative_3222) (QuarticIntegerRepresentativeTree.Tree.leaf 3223 representative_3223)))) (QuarticIntegerRepresentativeTree.Tree.branch 3228 (QuarticIntegerRepresentativeTree.Tree.branch 3226 (QuarticIntegerRepresentativeTree.Tree.branch 3225 (QuarticIntegerRepresentativeTree.Tree.leaf 3224 representative_3224) (QuarticIntegerRepresentativeTree.Tree.leaf 3225 representative_3225)) (QuarticIntegerRepresentativeTree.Tree.branch 3227 (QuarticIntegerRepresentativeTree.Tree.leaf 3226 representative_3226) (QuarticIntegerRepresentativeTree.Tree.leaf 3227 representative_3227))) (QuarticIntegerRepresentativeTree.Tree.branch 3230 (QuarticIntegerRepresentativeTree.Tree.branch 3229 (QuarticIntegerRepresentativeTree.Tree.leaf 3228 representative_3228) (QuarticIntegerRepresentativeTree.Tree.leaf 3229 representative_3229)) (QuarticIntegerRepresentativeTree.Tree.branch 3231 (QuarticIntegerRepresentativeTree.Tree.leaf 3230 representative_3230) (QuarticIntegerRepresentativeTree.Tree.leaf 3231 representative_3231)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3248 (QuarticIntegerRepresentativeTree.Tree.branch 3240 (QuarticIntegerRepresentativeTree.Tree.branch 3236 (QuarticIntegerRepresentativeTree.Tree.branch 3234 (QuarticIntegerRepresentativeTree.Tree.branch 3233 (QuarticIntegerRepresentativeTree.Tree.leaf 3232 representative_3232) (QuarticIntegerRepresentativeTree.Tree.leaf 3233 representative_3233)) (QuarticIntegerRepresentativeTree.Tree.branch 3235 (QuarticIntegerRepresentativeTree.Tree.leaf 3234 representative_3234) (QuarticIntegerRepresentativeTree.Tree.leaf 3235 representative_3235))) (QuarticIntegerRepresentativeTree.Tree.branch 3238 (QuarticIntegerRepresentativeTree.Tree.branch 3237 (QuarticIntegerRepresentativeTree.Tree.leaf 3236 representative_3236) (QuarticIntegerRepresentativeTree.Tree.leaf 3237 representative_3237)) (QuarticIntegerRepresentativeTree.Tree.branch 3239 (QuarticIntegerRepresentativeTree.Tree.leaf 3238 representative_3238) (QuarticIntegerRepresentativeTree.Tree.leaf 3239 representative_3239)))) (QuarticIntegerRepresentativeTree.Tree.branch 3244 (QuarticIntegerRepresentativeTree.Tree.branch 3242 (QuarticIntegerRepresentativeTree.Tree.branch 3241 (QuarticIntegerRepresentativeTree.Tree.leaf 3240 representative_3240) (QuarticIntegerRepresentativeTree.Tree.leaf 3241 representative_3241)) (QuarticIntegerRepresentativeTree.Tree.branch 3243 (QuarticIntegerRepresentativeTree.Tree.leaf 3242 representative_3242) (QuarticIntegerRepresentativeTree.Tree.leaf 3243 representative_3243))) (QuarticIntegerRepresentativeTree.Tree.branch 3246 (QuarticIntegerRepresentativeTree.Tree.branch 3245 (QuarticIntegerRepresentativeTree.Tree.leaf 3244 representative_3244) (QuarticIntegerRepresentativeTree.Tree.leaf 3245 representative_3245)) (QuarticIntegerRepresentativeTree.Tree.branch 3247 (QuarticIntegerRepresentativeTree.Tree.leaf 3246 representative_3246) (QuarticIntegerRepresentativeTree.Tree.leaf 3247 representative_3247))))) (QuarticIntegerRepresentativeTree.Tree.branch 3256 (QuarticIntegerRepresentativeTree.Tree.branch 3252 (QuarticIntegerRepresentativeTree.Tree.branch 3250 (QuarticIntegerRepresentativeTree.Tree.branch 3249 (QuarticIntegerRepresentativeTree.Tree.leaf 3248 representative_3248) (QuarticIntegerRepresentativeTree.Tree.leaf 3249 representative_3249)) (QuarticIntegerRepresentativeTree.Tree.branch 3251 (QuarticIntegerRepresentativeTree.Tree.leaf 3250 representative_3250) (QuarticIntegerRepresentativeTree.Tree.leaf 3251 representative_3251))) (QuarticIntegerRepresentativeTree.Tree.branch 3254 (QuarticIntegerRepresentativeTree.Tree.branch 3253 (QuarticIntegerRepresentativeTree.Tree.leaf 3252 representative_3252) (QuarticIntegerRepresentativeTree.Tree.leaf 3253 representative_3253)) (QuarticIntegerRepresentativeTree.Tree.branch 3255 (QuarticIntegerRepresentativeTree.Tree.leaf 3254 representative_3254) (QuarticIntegerRepresentativeTree.Tree.leaf 3255 representative_3255)))) (QuarticIntegerRepresentativeTree.Tree.branch 3260 (QuarticIntegerRepresentativeTree.Tree.branch 3258 (QuarticIntegerRepresentativeTree.Tree.branch 3257 (QuarticIntegerRepresentativeTree.Tree.leaf 3256 representative_3256) (QuarticIntegerRepresentativeTree.Tree.leaf 3257 representative_3257)) (QuarticIntegerRepresentativeTree.Tree.branch 3259 (QuarticIntegerRepresentativeTree.Tree.leaf 3258 representative_3258) (QuarticIntegerRepresentativeTree.Tree.leaf 3259 representative_3259))) (QuarticIntegerRepresentativeTree.Tree.branch 3262 (QuarticIntegerRepresentativeTree.Tree.branch 3261 (QuarticIntegerRepresentativeTree.Tree.leaf 3260 representative_3260) (QuarticIntegerRepresentativeTree.Tree.leaf 3261 representative_3261)) (QuarticIntegerRepresentativeTree.Tree.branch 3263 (QuarticIntegerRepresentativeTree.Tree.leaf 3262 representative_3262) (QuarticIntegerRepresentativeTree.Tree.leaf 3263 representative_3263)))))))
theorem accepted_050 : All validRep tree_050 := ⟨⟨⟨⟨⟨⟨coefficient_3200,coefficient_3201⟩,⟨coefficient_3202,coefficient_3203⟩⟩,⟨⟨coefficient_3204,coefficient_3205⟩,⟨coefficient_3206,coefficient_3207⟩⟩⟩,⟨⟨⟨coefficient_3208,coefficient_3209⟩,⟨coefficient_3210,coefficient_3211⟩⟩,⟨⟨coefficient_3212,coefficient_3213⟩,⟨coefficient_3214,coefficient_3215⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3216,coefficient_3217⟩,⟨coefficient_3218,coefficient_3219⟩⟩,⟨⟨coefficient_3220,coefficient_3221⟩,⟨coefficient_3222,coefficient_3223⟩⟩⟩,⟨⟨⟨coefficient_3224,coefficient_3225⟩,⟨coefficient_3226,coefficient_3227⟩⟩,⟨⟨coefficient_3228,coefficient_3229⟩,⟨coefficient_3230,coefficient_3231⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3232,coefficient_3233⟩,⟨coefficient_3234,coefficient_3235⟩⟩,⟨⟨coefficient_3236,coefficient_3237⟩,⟨coefficient_3238,coefficient_3239⟩⟩⟩,⟨⟨⟨coefficient_3240,coefficient_3241⟩,⟨coefficient_3242,coefficient_3243⟩⟩,⟨⟨coefficient_3244,coefficient_3245⟩,⟨coefficient_3246,coefficient_3247⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3248,coefficient_3249⟩,⟨coefficient_3250,coefficient_3251⟩⟩,⟨⟨coefficient_3252,coefficient_3253⟩,⟨coefficient_3254,coefficient_3255⟩⟩⟩,⟨⟨⟨coefficient_3256,coefficient_3257⟩,⟨coefficient_3258,coefficient_3259⟩⟩,⟨⟨coefficient_3260,coefficient_3261⟩,⟨coefficient_3262,coefficient_3263⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

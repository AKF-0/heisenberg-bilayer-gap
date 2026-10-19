import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3264 : Rep := ⟨![0,12,1,37],462⟩
def representative_3265 : Rep := ⟨![0,12,1,38],462⟩
def representative_3266 : Rep := ⟨![0,12,1,39],462⟩
def representative_3267 : Rep := ⟨![0,12,1,43],462⟩
def representative_3268 : Rep := ⟨![0,12,1,44],462⟩
def representative_3269 : Rep := ⟨![0,12,1,45],462⟩
def representative_3270 : Rep := ⟨![0,12,1,46],462⟩
def representative_3271 : Rep := ⟨![0,12,1,47],462⟩
def representative_3272 : Rep := ⟨![0,12,1,51],462⟩
def representative_3273 : Rep := ⟨![0,12,1,52],462⟩
def representative_3274 : Rep := ⟨![0,12,1,53],462⟩
def representative_3275 : Rep := ⟨![0,12,1,54],462⟩
def representative_3276 : Rep := ⟨![0,12,1,55],462⟩
def representative_3277 : Rep := ⟨![0,12,1,61],462⟩
def representative_3278 : Rep := ⟨![0,12,2,14],462⟩
def representative_3279 : Rep := ⟨![0,12,2,16],462⟩
def representative_3280 : Rep := ⟨![0,12,2,20],462⟩
def representative_3281 : Rep := ⟨![0,12,2,21],462⟩
def representative_3282 : Rep := ⟨![0,12,2,22],462⟩
def representative_3283 : Rep := ⟨![0,12,2,23],462⟩
def representative_3284 : Rep := ⟨![0,12,2,24],462⟩
def representative_3285 : Rep := ⟨![0,12,2,28],462⟩
def representative_3286 : Rep := ⟨![0,12,2,29],462⟩
def representative_3287 : Rep := ⟨![0,12,2,30],462⟩
def representative_3288 : Rep := ⟨![0,12,2,31],462⟩
def representative_3289 : Rep := ⟨![0,12,2,32],462⟩
def representative_3290 : Rep := ⟨![0,12,2,33],462⟩
def representative_3291 : Rep := ⟨![0,12,2,35],462⟩
def representative_3292 : Rep := ⟨![0,12,2,36],462⟩
def representative_3293 : Rep := ⟨![0,12,2,37],462⟩
def representative_3294 : Rep := ⟨![0,12,2,38],462⟩
def representative_3295 : Rep := ⟨![0,12,2,39],462⟩
def representative_3296 : Rep := ⟨![0,12,2,40],462⟩
def representative_3297 : Rep := ⟨![0,12,2,44],462⟩
def representative_3298 : Rep := ⟨![0,12,2,45],462⟩
def representative_3299 : Rep := ⟨![0,12,2,46],462⟩
def representative_3300 : Rep := ⟨![0,12,2,47],462⟩
def representative_3301 : Rep := ⟨![0,12,2,48],462⟩
def representative_3302 : Rep := ⟨![0,12,2,52],462⟩
def representative_3303 : Rep := ⟨![0,12,2,53],462⟩
def representative_3304 : Rep := ⟨![0,12,2,54],462⟩
def representative_3305 : Rep := ⟨![0,12,2,55],462⟩
def representative_3306 : Rep := ⟨![0,12,2,62],462⟩
def representative_3307 : Rep := ⟨![0,12,3,15],462⟩
def representative_3308 : Rep := ⟨![0,12,3,16],462⟩
def representative_3309 : Rep := ⟨![0,12,3,17],462⟩
def representative_3310 : Rep := ⟨![0,12,3,21],462⟩
def representative_3311 : Rep := ⟨![0,12,3,22],462⟩
def representative_3312 : Rep := ⟨![0,12,3,23],462⟩
def representative_3313 : Rep := ⟨![0,12,3,24],462⟩
def representative_3314 : Rep := ⟨![0,12,3,25],462⟩
def representative_3315 : Rep := ⟨![0,12,3,29],462⟩
def representative_3316 : Rep := ⟨![0,12,3,30],462⟩
def representative_3317 : Rep := ⟨![0,12,3,31],462⟩
def representative_3318 : Rep := ⟨![0,12,3,32],462⟩
def representative_3319 : Rep := ⟨![0,12,3,33],462⟩
def representative_3320 : Rep := ⟨![0,12,3,34],462⟩
def representative_3321 : Rep := ⟨![0,12,3,36],462⟩
def representative_3322 : Rep := ⟨![0,12,3,37],462⟩
def representative_3323 : Rep := ⟨![0,12,3,38],462⟩
def representative_3324 : Rep := ⟨![0,12,3,39],462⟩
def representative_3325 : Rep := ⟨![0,12,3,40],462⟩
def representative_3326 : Rep := ⟨![0,12,3,41],462⟩
def representative_3327 : Rep := ⟨![0,12,3,45],462⟩
theorem coefficient_3264 : validRep representative_3264 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3264)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3265 : validRep representative_3265 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3265)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3266 : validRep representative_3266 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3266)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3267 : validRep representative_3267 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3267)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3268 : validRep representative_3268 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3268)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3269 : validRep representative_3269 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3269)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3270 : validRep representative_3270 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3270)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3271 : validRep representative_3271 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3271)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3272 : validRep representative_3272 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3272)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3273 : validRep representative_3273 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3273)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3274 : validRep representative_3274 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3274)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3275 : validRep representative_3275 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3275)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3276 : validRep representative_3276 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3276)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3277 : validRep representative_3277 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3277)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3278 : validRep representative_3278 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3278)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3279 : validRep representative_3279 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3279)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3280 : validRep representative_3280 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3280)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3281 : validRep representative_3281 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3281)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3282 : validRep representative_3282 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3282)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3283 : validRep representative_3283 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3283)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3284 : validRep representative_3284 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3284)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3285 : validRep representative_3285 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3285)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3286 : validRep representative_3286 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3286)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3287 : validRep representative_3287 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3287)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3288 : validRep representative_3288 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3288)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3289 : validRep representative_3289 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3289)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3290 : validRep representative_3290 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3290)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3291 : validRep representative_3291 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3291)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3292 : validRep representative_3292 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3292)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3293 : validRep representative_3293 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3293)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3294 : validRep representative_3294 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3294)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3295 : validRep representative_3295 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3295)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3296 : validRep representative_3296 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3296)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3297 : validRep representative_3297 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3297)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3298 : validRep representative_3298 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3298)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3299 : validRep representative_3299 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3299)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3300 : validRep representative_3300 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3300)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3301 : validRep representative_3301 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3301)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3302 : validRep representative_3302 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3302)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3303 : validRep representative_3303 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3303)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3304 : validRep representative_3304 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3304)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3305 : validRep representative_3305 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3305)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3306 : validRep representative_3306 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3306)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3307 : validRep representative_3307 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3307)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3308 : validRep representative_3308 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3308)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3309 : validRep representative_3309 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3309)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3310 : validRep representative_3310 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3310)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3311 : validRep representative_3311 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3311)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3312 : validRep representative_3312 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3312)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3313 : validRep representative_3313 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3313)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3314 : validRep representative_3314 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3314)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3315 : validRep representative_3315 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3315)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3316 : validRep representative_3316 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3316)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3317 : validRep representative_3317 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3317)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3318 : validRep representative_3318 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3318)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3319 : validRep representative_3319 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3319)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3320 : validRep representative_3320 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3320)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3321 : validRep representative_3321 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3321)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3322 : validRep representative_3322 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3322)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3323 : validRep representative_3323 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3323)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3324 : validRep representative_3324 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3324)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3325 : validRep representative_3325 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3325)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3326 : validRep representative_3326 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3326)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3327 : validRep representative_3327 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3327)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_051 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3296 (QuarticIntegerRepresentativeTree.Tree.branch 3280 (QuarticIntegerRepresentativeTree.Tree.branch 3272 (QuarticIntegerRepresentativeTree.Tree.branch 3268 (QuarticIntegerRepresentativeTree.Tree.branch 3266 (QuarticIntegerRepresentativeTree.Tree.branch 3265 (QuarticIntegerRepresentativeTree.Tree.leaf 3264 representative_3264) (QuarticIntegerRepresentativeTree.Tree.leaf 3265 representative_3265)) (QuarticIntegerRepresentativeTree.Tree.branch 3267 (QuarticIntegerRepresentativeTree.Tree.leaf 3266 representative_3266) (QuarticIntegerRepresentativeTree.Tree.leaf 3267 representative_3267))) (QuarticIntegerRepresentativeTree.Tree.branch 3270 (QuarticIntegerRepresentativeTree.Tree.branch 3269 (QuarticIntegerRepresentativeTree.Tree.leaf 3268 representative_3268) (QuarticIntegerRepresentativeTree.Tree.leaf 3269 representative_3269)) (QuarticIntegerRepresentativeTree.Tree.branch 3271 (QuarticIntegerRepresentativeTree.Tree.leaf 3270 representative_3270) (QuarticIntegerRepresentativeTree.Tree.leaf 3271 representative_3271)))) (QuarticIntegerRepresentativeTree.Tree.branch 3276 (QuarticIntegerRepresentativeTree.Tree.branch 3274 (QuarticIntegerRepresentativeTree.Tree.branch 3273 (QuarticIntegerRepresentativeTree.Tree.leaf 3272 representative_3272) (QuarticIntegerRepresentativeTree.Tree.leaf 3273 representative_3273)) (QuarticIntegerRepresentativeTree.Tree.branch 3275 (QuarticIntegerRepresentativeTree.Tree.leaf 3274 representative_3274) (QuarticIntegerRepresentativeTree.Tree.leaf 3275 representative_3275))) (QuarticIntegerRepresentativeTree.Tree.branch 3278 (QuarticIntegerRepresentativeTree.Tree.branch 3277 (QuarticIntegerRepresentativeTree.Tree.leaf 3276 representative_3276) (QuarticIntegerRepresentativeTree.Tree.leaf 3277 representative_3277)) (QuarticIntegerRepresentativeTree.Tree.branch 3279 (QuarticIntegerRepresentativeTree.Tree.leaf 3278 representative_3278) (QuarticIntegerRepresentativeTree.Tree.leaf 3279 representative_3279))))) (QuarticIntegerRepresentativeTree.Tree.branch 3288 (QuarticIntegerRepresentativeTree.Tree.branch 3284 (QuarticIntegerRepresentativeTree.Tree.branch 3282 (QuarticIntegerRepresentativeTree.Tree.branch 3281 (QuarticIntegerRepresentativeTree.Tree.leaf 3280 representative_3280) (QuarticIntegerRepresentativeTree.Tree.leaf 3281 representative_3281)) (QuarticIntegerRepresentativeTree.Tree.branch 3283 (QuarticIntegerRepresentativeTree.Tree.leaf 3282 representative_3282) (QuarticIntegerRepresentativeTree.Tree.leaf 3283 representative_3283))) (QuarticIntegerRepresentativeTree.Tree.branch 3286 (QuarticIntegerRepresentativeTree.Tree.branch 3285 (QuarticIntegerRepresentativeTree.Tree.leaf 3284 representative_3284) (QuarticIntegerRepresentativeTree.Tree.leaf 3285 representative_3285)) (QuarticIntegerRepresentativeTree.Tree.branch 3287 (QuarticIntegerRepresentativeTree.Tree.leaf 3286 representative_3286) (QuarticIntegerRepresentativeTree.Tree.leaf 3287 representative_3287)))) (QuarticIntegerRepresentativeTree.Tree.branch 3292 (QuarticIntegerRepresentativeTree.Tree.branch 3290 (QuarticIntegerRepresentativeTree.Tree.branch 3289 (QuarticIntegerRepresentativeTree.Tree.leaf 3288 representative_3288) (QuarticIntegerRepresentativeTree.Tree.leaf 3289 representative_3289)) (QuarticIntegerRepresentativeTree.Tree.branch 3291 (QuarticIntegerRepresentativeTree.Tree.leaf 3290 representative_3290) (QuarticIntegerRepresentativeTree.Tree.leaf 3291 representative_3291))) (QuarticIntegerRepresentativeTree.Tree.branch 3294 (QuarticIntegerRepresentativeTree.Tree.branch 3293 (QuarticIntegerRepresentativeTree.Tree.leaf 3292 representative_3292) (QuarticIntegerRepresentativeTree.Tree.leaf 3293 representative_3293)) (QuarticIntegerRepresentativeTree.Tree.branch 3295 (QuarticIntegerRepresentativeTree.Tree.leaf 3294 representative_3294) (QuarticIntegerRepresentativeTree.Tree.leaf 3295 representative_3295)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3312 (QuarticIntegerRepresentativeTree.Tree.branch 3304 (QuarticIntegerRepresentativeTree.Tree.branch 3300 (QuarticIntegerRepresentativeTree.Tree.branch 3298 (QuarticIntegerRepresentativeTree.Tree.branch 3297 (QuarticIntegerRepresentativeTree.Tree.leaf 3296 representative_3296) (QuarticIntegerRepresentativeTree.Tree.leaf 3297 representative_3297)) (QuarticIntegerRepresentativeTree.Tree.branch 3299 (QuarticIntegerRepresentativeTree.Tree.leaf 3298 representative_3298) (QuarticIntegerRepresentativeTree.Tree.leaf 3299 representative_3299))) (QuarticIntegerRepresentativeTree.Tree.branch 3302 (QuarticIntegerRepresentativeTree.Tree.branch 3301 (QuarticIntegerRepresentativeTree.Tree.leaf 3300 representative_3300) (QuarticIntegerRepresentativeTree.Tree.leaf 3301 representative_3301)) (QuarticIntegerRepresentativeTree.Tree.branch 3303 (QuarticIntegerRepresentativeTree.Tree.leaf 3302 representative_3302) (QuarticIntegerRepresentativeTree.Tree.leaf 3303 representative_3303)))) (QuarticIntegerRepresentativeTree.Tree.branch 3308 (QuarticIntegerRepresentativeTree.Tree.branch 3306 (QuarticIntegerRepresentativeTree.Tree.branch 3305 (QuarticIntegerRepresentativeTree.Tree.leaf 3304 representative_3304) (QuarticIntegerRepresentativeTree.Tree.leaf 3305 representative_3305)) (QuarticIntegerRepresentativeTree.Tree.branch 3307 (QuarticIntegerRepresentativeTree.Tree.leaf 3306 representative_3306) (QuarticIntegerRepresentativeTree.Tree.leaf 3307 representative_3307))) (QuarticIntegerRepresentativeTree.Tree.branch 3310 (QuarticIntegerRepresentativeTree.Tree.branch 3309 (QuarticIntegerRepresentativeTree.Tree.leaf 3308 representative_3308) (QuarticIntegerRepresentativeTree.Tree.leaf 3309 representative_3309)) (QuarticIntegerRepresentativeTree.Tree.branch 3311 (QuarticIntegerRepresentativeTree.Tree.leaf 3310 representative_3310) (QuarticIntegerRepresentativeTree.Tree.leaf 3311 representative_3311))))) (QuarticIntegerRepresentativeTree.Tree.branch 3320 (QuarticIntegerRepresentativeTree.Tree.branch 3316 (QuarticIntegerRepresentativeTree.Tree.branch 3314 (QuarticIntegerRepresentativeTree.Tree.branch 3313 (QuarticIntegerRepresentativeTree.Tree.leaf 3312 representative_3312) (QuarticIntegerRepresentativeTree.Tree.leaf 3313 representative_3313)) (QuarticIntegerRepresentativeTree.Tree.branch 3315 (QuarticIntegerRepresentativeTree.Tree.leaf 3314 representative_3314) (QuarticIntegerRepresentativeTree.Tree.leaf 3315 representative_3315))) (QuarticIntegerRepresentativeTree.Tree.branch 3318 (QuarticIntegerRepresentativeTree.Tree.branch 3317 (QuarticIntegerRepresentativeTree.Tree.leaf 3316 representative_3316) (QuarticIntegerRepresentativeTree.Tree.leaf 3317 representative_3317)) (QuarticIntegerRepresentativeTree.Tree.branch 3319 (QuarticIntegerRepresentativeTree.Tree.leaf 3318 representative_3318) (QuarticIntegerRepresentativeTree.Tree.leaf 3319 representative_3319)))) (QuarticIntegerRepresentativeTree.Tree.branch 3324 (QuarticIntegerRepresentativeTree.Tree.branch 3322 (QuarticIntegerRepresentativeTree.Tree.branch 3321 (QuarticIntegerRepresentativeTree.Tree.leaf 3320 representative_3320) (QuarticIntegerRepresentativeTree.Tree.leaf 3321 representative_3321)) (QuarticIntegerRepresentativeTree.Tree.branch 3323 (QuarticIntegerRepresentativeTree.Tree.leaf 3322 representative_3322) (QuarticIntegerRepresentativeTree.Tree.leaf 3323 representative_3323))) (QuarticIntegerRepresentativeTree.Tree.branch 3326 (QuarticIntegerRepresentativeTree.Tree.branch 3325 (QuarticIntegerRepresentativeTree.Tree.leaf 3324 representative_3324) (QuarticIntegerRepresentativeTree.Tree.leaf 3325 representative_3325)) (QuarticIntegerRepresentativeTree.Tree.branch 3327 (QuarticIntegerRepresentativeTree.Tree.leaf 3326 representative_3326) (QuarticIntegerRepresentativeTree.Tree.leaf 3327 representative_3327)))))))
theorem accepted_051 : All validRep tree_051 := ⟨⟨⟨⟨⟨⟨coefficient_3264,coefficient_3265⟩,⟨coefficient_3266,coefficient_3267⟩⟩,⟨⟨coefficient_3268,coefficient_3269⟩,⟨coefficient_3270,coefficient_3271⟩⟩⟩,⟨⟨⟨coefficient_3272,coefficient_3273⟩,⟨coefficient_3274,coefficient_3275⟩⟩,⟨⟨coefficient_3276,coefficient_3277⟩,⟨coefficient_3278,coefficient_3279⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3280,coefficient_3281⟩,⟨coefficient_3282,coefficient_3283⟩⟩,⟨⟨coefficient_3284,coefficient_3285⟩,⟨coefficient_3286,coefficient_3287⟩⟩⟩,⟨⟨⟨coefficient_3288,coefficient_3289⟩,⟨coefficient_3290,coefficient_3291⟩⟩,⟨⟨coefficient_3292,coefficient_3293⟩,⟨coefficient_3294,coefficient_3295⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3296,coefficient_3297⟩,⟨coefficient_3298,coefficient_3299⟩⟩,⟨⟨coefficient_3300,coefficient_3301⟩,⟨coefficient_3302,coefficient_3303⟩⟩⟩,⟨⟨⟨coefficient_3304,coefficient_3305⟩,⟨coefficient_3306,coefficient_3307⟩⟩,⟨⟨coefficient_3308,coefficient_3309⟩,⟨coefficient_3310,coefficient_3311⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3312,coefficient_3313⟩,⟨coefficient_3314,coefficient_3315⟩⟩,⟨⟨coefficient_3316,coefficient_3317⟩,⟨coefficient_3318,coefficient_3319⟩⟩⟩,⟨⟨⟨coefficient_3320,coefficient_3321⟩,⟨coefficient_3322,coefficient_3323⟩⟩,⟨⟨coefficient_3324,coefficient_3325⟩,⟨coefficient_3326,coefficient_3327⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

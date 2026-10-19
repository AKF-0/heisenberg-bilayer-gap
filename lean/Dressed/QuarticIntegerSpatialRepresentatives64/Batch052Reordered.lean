import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3328 : Rep := ⟨![0,12,3,46],462⟩
def representative_3329 : Rep := ⟨![0,12,3,47],462⟩
def representative_3330 : Rep := ⟨![0,12,3,48],462⟩
def representative_3331 : Rep := ⟨![0,12,3,49],462⟩
def representative_3332 : Rep := ⟨![0,12,3,53],462⟩
def representative_3333 : Rep := ⟨![0,12,3,54],462⟩
def representative_3334 : Rep := ⟨![0,12,3,55],462⟩
def representative_3335 : Rep := ⟨![0,12,3,63],462⟩
def representative_3336 : Rep := ⟨![0,12,4,8],462⟩
def representative_3337 : Rep := ⟨![0,12,4,16],462⟩
def representative_3338 : Rep := ⟨![0,12,4,17],462⟩
def representative_3339 : Rep := ⟨![0,12,4,18],462⟩
def representative_3340 : Rep := ⟨![0,12,4,24],462⟩
def representative_3341 : Rep := ⟨![0,12,4,25],462⟩
def representative_3342 : Rep := ⟨![0,12,4,26],462⟩
def representative_3343 : Rep := ⟨![0,12,4,32],462⟩
def representative_3344 : Rep := ⟨![0,12,4,33],462⟩
def representative_3345 : Rep := ⟨![0,12,4,34],462⟩
def representative_3346 : Rep := ⟨![0,12,4,40],462⟩
def representative_3347 : Rep := ⟨![0,12,4,41],462⟩
def representative_3348 : Rep := ⟨![0,12,4,42],462⟩
def representative_3349 : Rep := ⟨![0,12,4,48],462⟩
def representative_3350 : Rep := ⟨![0,12,4,49],462⟩
def representative_3351 : Rep := ⟨![0,12,4,50],462⟩
def representative_3352 : Rep := ⟨![0,12,4,56],462⟩
def representative_3353 : Rep := ⟨![0,12,16,28],462⟩
def representative_3354 : Rep := ⟨![0,12,16,34],462⟩
def representative_3355 : Rep := ⟨![0,12,16,35],462⟩
def representative_3356 : Rep := ⟨![0,12,16,36],462⟩
def representative_3357 : Rep := ⟨![0,12,16,42],462⟩
def representative_3358 : Rep := ⟨![0,12,16,43],462⟩
def representative_3359 : Rep := ⟨![0,12,16,44],462⟩
def representative_3360 : Rep := ⟨![0,12,16,50],462⟩
def representative_3361 : Rep := ⟨![0,12,16,51],462⟩
def representative_3362 : Rep := ⟨![0,12,16,52],462⟩
def representative_3363 : Rep := ⟨![0,12,16,58],462⟩
def representative_3364 : Rep := ⟨![0,12,16,59],462⟩
def representative_3365 : Rep := ⟨![0,12,16,60],462⟩
def representative_3366 : Rep := ⟨![0,12,17,29],462⟩
def representative_3367 : Rep := ⟨![0,12,17,35],462⟩
def representative_3368 : Rep := ⟨![0,12,17,36],462⟩
def representative_3369 : Rep := ⟨![0,12,17,37],462⟩
def representative_3370 : Rep := ⟨![0,12,17,38],462⟩
def representative_3371 : Rep := ⟨![0,12,17,39],462⟩
def representative_3372 : Rep := ⟨![0,12,17,43],462⟩
def representative_3373 : Rep := ⟨![0,12,17,44],462⟩
def representative_3374 : Rep := ⟨![0,12,17,45],462⟩
def representative_3375 : Rep := ⟨![0,12,17,46],462⟩
def representative_3376 : Rep := ⟨![0,12,17,47],462⟩
def representative_3377 : Rep := ⟨![0,12,17,50],462⟩
def representative_3378 : Rep := ⟨![0,12,17,51],462⟩
def representative_3379 : Rep := ⟨![0,12,17,52],462⟩
def representative_3380 : Rep := ⟨![0,12,17,53],462⟩
def representative_3381 : Rep := ⟨![0,12,17,54],462⟩
def representative_3382 : Rep := ⟨![0,12,17,55],462⟩
def representative_3383 : Rep := ⟨![0,12,17,59],462⟩
def representative_3384 : Rep := ⟨![0,12,17,61],462⟩
def representative_3385 : Rep := ⟨![0,12,17,62],462⟩
def representative_3386 : Rep := ⟨![0,12,17,63],462⟩
def representative_3387 : Rep := ⟨![0,12,18,30],462⟩
def representative_3388 : Rep := ⟨![0,12,18,32],462⟩
def representative_3389 : Rep := ⟨![0,12,18,36],462⟩
def representative_3390 : Rep := ⟨![0,12,18,37],462⟩
def representative_3391 : Rep := ⟨![0,12,18,38],462⟩
theorem coefficient_3328 : validRep representative_3328 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3328)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3329 : validRep representative_3329 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3329)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3330 : validRep representative_3330 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3330)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3331 : validRep representative_3331 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3331)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3332 : validRep representative_3332 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3332)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3333 : validRep representative_3333 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3333)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3334 : validRep representative_3334 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3334)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3335 : validRep representative_3335 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3335)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3336 : validRep representative_3336 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3336)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3337 : validRep representative_3337 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3337)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3338 : validRep representative_3338 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3338)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3339 : validRep representative_3339 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3339)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3340 : validRep representative_3340 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3340)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3341 : validRep representative_3341 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3341)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3342 : validRep representative_3342 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3342)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3343 : validRep representative_3343 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3343)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3344 : validRep representative_3344 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3344)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3345 : validRep representative_3345 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3345)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3346 : validRep representative_3346 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3346)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3347 : validRep representative_3347 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3347)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3348 : validRep representative_3348 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3348)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3349 : validRep representative_3349 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3349)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3350 : validRep representative_3350 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3350)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3351 : validRep representative_3351 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3351)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3352 : validRep representative_3352 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3352)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3353 : validRep representative_3353 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3353)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3354 : validRep representative_3354 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3354)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3355 : validRep representative_3355 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3355)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3356 : validRep representative_3356 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3356)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3357 : validRep representative_3357 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3357)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3358 : validRep representative_3358 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3358)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3359 : validRep representative_3359 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3359)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3360 : validRep representative_3360 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3360)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3361 : validRep representative_3361 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3361)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3362 : validRep representative_3362 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3362)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3363 : validRep representative_3363 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3363)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3364 : validRep representative_3364 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3364)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3365 : validRep representative_3365 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3365)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3366 : validRep representative_3366 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3366)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3367 : validRep representative_3367 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3367)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3368 : validRep representative_3368 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3368)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3369 : validRep representative_3369 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3369)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3370 : validRep representative_3370 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3370)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3371 : validRep representative_3371 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3371)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3372 : validRep representative_3372 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3372)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3373 : validRep representative_3373 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3373)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3374 : validRep representative_3374 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3374)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3375 : validRep representative_3375 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3375)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3376 : validRep representative_3376 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3376)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3377 : validRep representative_3377 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3377)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3378 : validRep representative_3378 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3378)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3379 : validRep representative_3379 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3379)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3380 : validRep representative_3380 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3380)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3381 : validRep representative_3381 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3381)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3382 : validRep representative_3382 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3382)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3383 : validRep representative_3383 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3383)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3384 : validRep representative_3384 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3384)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3385 : validRep representative_3385 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3385)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3386 : validRep representative_3386 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3386)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3387 : validRep representative_3387 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3387)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3388 : validRep representative_3388 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3388)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3389 : validRep representative_3389 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3389)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3390 : validRep representative_3390 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3390)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3391 : validRep representative_3391 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3391)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_052 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3360 (QuarticIntegerRepresentativeTree.Tree.branch 3344 (QuarticIntegerRepresentativeTree.Tree.branch 3336 (QuarticIntegerRepresentativeTree.Tree.branch 3332 (QuarticIntegerRepresentativeTree.Tree.branch 3330 (QuarticIntegerRepresentativeTree.Tree.branch 3329 (QuarticIntegerRepresentativeTree.Tree.leaf 3328 representative_3328) (QuarticIntegerRepresentativeTree.Tree.leaf 3329 representative_3329)) (QuarticIntegerRepresentativeTree.Tree.branch 3331 (QuarticIntegerRepresentativeTree.Tree.leaf 3330 representative_3330) (QuarticIntegerRepresentativeTree.Tree.leaf 3331 representative_3331))) (QuarticIntegerRepresentativeTree.Tree.branch 3334 (QuarticIntegerRepresentativeTree.Tree.branch 3333 (QuarticIntegerRepresentativeTree.Tree.leaf 3332 representative_3332) (QuarticIntegerRepresentativeTree.Tree.leaf 3333 representative_3333)) (QuarticIntegerRepresentativeTree.Tree.branch 3335 (QuarticIntegerRepresentativeTree.Tree.leaf 3334 representative_3334) (QuarticIntegerRepresentativeTree.Tree.leaf 3335 representative_3335)))) (QuarticIntegerRepresentativeTree.Tree.branch 3340 (QuarticIntegerRepresentativeTree.Tree.branch 3338 (QuarticIntegerRepresentativeTree.Tree.branch 3337 (QuarticIntegerRepresentativeTree.Tree.leaf 3336 representative_3336) (QuarticIntegerRepresentativeTree.Tree.leaf 3337 representative_3337)) (QuarticIntegerRepresentativeTree.Tree.branch 3339 (QuarticIntegerRepresentativeTree.Tree.leaf 3338 representative_3338) (QuarticIntegerRepresentativeTree.Tree.leaf 3339 representative_3339))) (QuarticIntegerRepresentativeTree.Tree.branch 3342 (QuarticIntegerRepresentativeTree.Tree.branch 3341 (QuarticIntegerRepresentativeTree.Tree.leaf 3340 representative_3340) (QuarticIntegerRepresentativeTree.Tree.leaf 3341 representative_3341)) (QuarticIntegerRepresentativeTree.Tree.branch 3343 (QuarticIntegerRepresentativeTree.Tree.leaf 3342 representative_3342) (QuarticIntegerRepresentativeTree.Tree.leaf 3343 representative_3343))))) (QuarticIntegerRepresentativeTree.Tree.branch 3352 (QuarticIntegerRepresentativeTree.Tree.branch 3348 (QuarticIntegerRepresentativeTree.Tree.branch 3346 (QuarticIntegerRepresentativeTree.Tree.branch 3345 (QuarticIntegerRepresentativeTree.Tree.leaf 3344 representative_3344) (QuarticIntegerRepresentativeTree.Tree.leaf 3345 representative_3345)) (QuarticIntegerRepresentativeTree.Tree.branch 3347 (QuarticIntegerRepresentativeTree.Tree.leaf 3346 representative_3346) (QuarticIntegerRepresentativeTree.Tree.leaf 3347 representative_3347))) (QuarticIntegerRepresentativeTree.Tree.branch 3350 (QuarticIntegerRepresentativeTree.Tree.branch 3349 (QuarticIntegerRepresentativeTree.Tree.leaf 3348 representative_3348) (QuarticIntegerRepresentativeTree.Tree.leaf 3349 representative_3349)) (QuarticIntegerRepresentativeTree.Tree.branch 3351 (QuarticIntegerRepresentativeTree.Tree.leaf 3350 representative_3350) (QuarticIntegerRepresentativeTree.Tree.leaf 3351 representative_3351)))) (QuarticIntegerRepresentativeTree.Tree.branch 3356 (QuarticIntegerRepresentativeTree.Tree.branch 3354 (QuarticIntegerRepresentativeTree.Tree.branch 3353 (QuarticIntegerRepresentativeTree.Tree.leaf 3352 representative_3352) (QuarticIntegerRepresentativeTree.Tree.leaf 3353 representative_3353)) (QuarticIntegerRepresentativeTree.Tree.branch 3355 (QuarticIntegerRepresentativeTree.Tree.leaf 3354 representative_3354) (QuarticIntegerRepresentativeTree.Tree.leaf 3355 representative_3355))) (QuarticIntegerRepresentativeTree.Tree.branch 3358 (QuarticIntegerRepresentativeTree.Tree.branch 3357 (QuarticIntegerRepresentativeTree.Tree.leaf 3356 representative_3356) (QuarticIntegerRepresentativeTree.Tree.leaf 3357 representative_3357)) (QuarticIntegerRepresentativeTree.Tree.branch 3359 (QuarticIntegerRepresentativeTree.Tree.leaf 3358 representative_3358) (QuarticIntegerRepresentativeTree.Tree.leaf 3359 representative_3359)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3376 (QuarticIntegerRepresentativeTree.Tree.branch 3368 (QuarticIntegerRepresentativeTree.Tree.branch 3364 (QuarticIntegerRepresentativeTree.Tree.branch 3362 (QuarticIntegerRepresentativeTree.Tree.branch 3361 (QuarticIntegerRepresentativeTree.Tree.leaf 3360 representative_3360) (QuarticIntegerRepresentativeTree.Tree.leaf 3361 representative_3361)) (QuarticIntegerRepresentativeTree.Tree.branch 3363 (QuarticIntegerRepresentativeTree.Tree.leaf 3362 representative_3362) (QuarticIntegerRepresentativeTree.Tree.leaf 3363 representative_3363))) (QuarticIntegerRepresentativeTree.Tree.branch 3366 (QuarticIntegerRepresentativeTree.Tree.branch 3365 (QuarticIntegerRepresentativeTree.Tree.leaf 3364 representative_3364) (QuarticIntegerRepresentativeTree.Tree.leaf 3365 representative_3365)) (QuarticIntegerRepresentativeTree.Tree.branch 3367 (QuarticIntegerRepresentativeTree.Tree.leaf 3366 representative_3366) (QuarticIntegerRepresentativeTree.Tree.leaf 3367 representative_3367)))) (QuarticIntegerRepresentativeTree.Tree.branch 3372 (QuarticIntegerRepresentativeTree.Tree.branch 3370 (QuarticIntegerRepresentativeTree.Tree.branch 3369 (QuarticIntegerRepresentativeTree.Tree.leaf 3368 representative_3368) (QuarticIntegerRepresentativeTree.Tree.leaf 3369 representative_3369)) (QuarticIntegerRepresentativeTree.Tree.branch 3371 (QuarticIntegerRepresentativeTree.Tree.leaf 3370 representative_3370) (QuarticIntegerRepresentativeTree.Tree.leaf 3371 representative_3371))) (QuarticIntegerRepresentativeTree.Tree.branch 3374 (QuarticIntegerRepresentativeTree.Tree.branch 3373 (QuarticIntegerRepresentativeTree.Tree.leaf 3372 representative_3372) (QuarticIntegerRepresentativeTree.Tree.leaf 3373 representative_3373)) (QuarticIntegerRepresentativeTree.Tree.branch 3375 (QuarticIntegerRepresentativeTree.Tree.leaf 3374 representative_3374) (QuarticIntegerRepresentativeTree.Tree.leaf 3375 representative_3375))))) (QuarticIntegerRepresentativeTree.Tree.branch 3384 (QuarticIntegerRepresentativeTree.Tree.branch 3380 (QuarticIntegerRepresentativeTree.Tree.branch 3378 (QuarticIntegerRepresentativeTree.Tree.branch 3377 (QuarticIntegerRepresentativeTree.Tree.leaf 3376 representative_3376) (QuarticIntegerRepresentativeTree.Tree.leaf 3377 representative_3377)) (QuarticIntegerRepresentativeTree.Tree.branch 3379 (QuarticIntegerRepresentativeTree.Tree.leaf 3378 representative_3378) (QuarticIntegerRepresentativeTree.Tree.leaf 3379 representative_3379))) (QuarticIntegerRepresentativeTree.Tree.branch 3382 (QuarticIntegerRepresentativeTree.Tree.branch 3381 (QuarticIntegerRepresentativeTree.Tree.leaf 3380 representative_3380) (QuarticIntegerRepresentativeTree.Tree.leaf 3381 representative_3381)) (QuarticIntegerRepresentativeTree.Tree.branch 3383 (QuarticIntegerRepresentativeTree.Tree.leaf 3382 representative_3382) (QuarticIntegerRepresentativeTree.Tree.leaf 3383 representative_3383)))) (QuarticIntegerRepresentativeTree.Tree.branch 3388 (QuarticIntegerRepresentativeTree.Tree.branch 3386 (QuarticIntegerRepresentativeTree.Tree.branch 3385 (QuarticIntegerRepresentativeTree.Tree.leaf 3384 representative_3384) (QuarticIntegerRepresentativeTree.Tree.leaf 3385 representative_3385)) (QuarticIntegerRepresentativeTree.Tree.branch 3387 (QuarticIntegerRepresentativeTree.Tree.leaf 3386 representative_3386) (QuarticIntegerRepresentativeTree.Tree.leaf 3387 representative_3387))) (QuarticIntegerRepresentativeTree.Tree.branch 3390 (QuarticIntegerRepresentativeTree.Tree.branch 3389 (QuarticIntegerRepresentativeTree.Tree.leaf 3388 representative_3388) (QuarticIntegerRepresentativeTree.Tree.leaf 3389 representative_3389)) (QuarticIntegerRepresentativeTree.Tree.branch 3391 (QuarticIntegerRepresentativeTree.Tree.leaf 3390 representative_3390) (QuarticIntegerRepresentativeTree.Tree.leaf 3391 representative_3391)))))))
theorem accepted_052 : All validRep tree_052 := ⟨⟨⟨⟨⟨⟨coefficient_3328,coefficient_3329⟩,⟨coefficient_3330,coefficient_3331⟩⟩,⟨⟨coefficient_3332,coefficient_3333⟩,⟨coefficient_3334,coefficient_3335⟩⟩⟩,⟨⟨⟨coefficient_3336,coefficient_3337⟩,⟨coefficient_3338,coefficient_3339⟩⟩,⟨⟨coefficient_3340,coefficient_3341⟩,⟨coefficient_3342,coefficient_3343⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3344,coefficient_3345⟩,⟨coefficient_3346,coefficient_3347⟩⟩,⟨⟨coefficient_3348,coefficient_3349⟩,⟨coefficient_3350,coefficient_3351⟩⟩⟩,⟨⟨⟨coefficient_3352,coefficient_3353⟩,⟨coefficient_3354,coefficient_3355⟩⟩,⟨⟨coefficient_3356,coefficient_3357⟩,⟨coefficient_3358,coefficient_3359⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3360,coefficient_3361⟩,⟨coefficient_3362,coefficient_3363⟩⟩,⟨⟨coefficient_3364,coefficient_3365⟩,⟨coefficient_3366,coefficient_3367⟩⟩⟩,⟨⟨⟨coefficient_3368,coefficient_3369⟩,⟨coefficient_3370,coefficient_3371⟩⟩,⟨⟨coefficient_3372,coefficient_3373⟩,⟨coefficient_3374,coefficient_3375⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3376,coefficient_3377⟩,⟨coefficient_3378,coefficient_3379⟩⟩,⟨⟨coefficient_3380,coefficient_3381⟩,⟨coefficient_3382,coefficient_3383⟩⟩⟩,⟨⟨⟨coefficient_3384,coefficient_3385⟩,⟨coefficient_3386,coefficient_3387⟩⟩,⟨⟨coefficient_3388,coefficient_3389⟩,⟨coefficient_3390,coefficient_3391⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

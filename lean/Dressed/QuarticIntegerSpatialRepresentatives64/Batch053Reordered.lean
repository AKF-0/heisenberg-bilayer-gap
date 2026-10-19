import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3392 : Rep := ⟨![0,12,18,39],462⟩
def representative_3393 : Rep := ⟨![0,12,18,40],462⟩
def representative_3394 : Rep := ⟨![0,12,18,44],462⟩
def representative_3395 : Rep := ⟨![0,12,18,45],462⟩
def representative_3396 : Rep := ⟨![0,12,18,46],462⟩
def representative_3397 : Rep := ⟨![0,12,18,47],462⟩
def representative_3398 : Rep := ⟨![0,12,18,48],462⟩
def representative_3399 : Rep := ⟨![0,12,18,49],462⟩
def representative_3400 : Rep := ⟨![0,12,18,52],462⟩
def representative_3401 : Rep := ⟨![0,12,18,53],462⟩
def representative_3402 : Rep := ⟨![0,12,18,54],462⟩
def representative_3403 : Rep := ⟨![0,12,18,55],462⟩
def representative_3404 : Rep := ⟨![0,12,18,56],462⟩
def representative_3405 : Rep := ⟨![0,12,18,62],462⟩
def representative_3406 : Rep := ⟨![0,12,18,63],462⟩
def representative_3407 : Rep := ⟨![0,12,19,31],462⟩
def representative_3408 : Rep := ⟨![0,12,19,32],462⟩
def representative_3409 : Rep := ⟨![0,12,19,33],462⟩
def representative_3410 : Rep := ⟨![0,12,19,37],462⟩
def representative_3411 : Rep := ⟨![0,12,19,38],462⟩
def representative_3412 : Rep := ⟨![0,12,19,39],462⟩
def representative_3413 : Rep := ⟨![0,12,19,40],462⟩
def representative_3414 : Rep := ⟨![0,12,19,41],462⟩
def representative_3415 : Rep := ⟨![0,12,19,45],462⟩
def representative_3416 : Rep := ⟨![0,12,19,46],462⟩
def representative_3417 : Rep := ⟨![0,12,19,47],462⟩
def representative_3418 : Rep := ⟨![0,12,19,48],462⟩
def representative_3419 : Rep := ⟨![0,12,19,49],462⟩
def representative_3420 : Rep := ⟨![0,12,19,50],462⟩
def representative_3421 : Rep := ⟨![0,12,19,53],462⟩
def representative_3422 : Rep := ⟨![0,12,19,54],462⟩
def representative_3423 : Rep := ⟨![0,12,19,55],462⟩
def representative_3424 : Rep := ⟨![0,12,19,56],462⟩
def representative_3425 : Rep := ⟨![0,12,19,57],462⟩
def representative_3426 : Rep := ⟨![0,12,19,63],462⟩
def representative_3427 : Rep := ⟨![0,12,20,24],462⟩
def representative_3428 : Rep := ⟨![0,12,20,32],462⟩
def representative_3429 : Rep := ⟨![0,12,20,33],462⟩
def representative_3430 : Rep := ⟨![0,12,20,34],462⟩
def representative_3431 : Rep := ⟨![0,12,20,40],462⟩
def representative_3432 : Rep := ⟨![0,12,20,41],462⟩
def representative_3433 : Rep := ⟨![0,12,20,42],462⟩
def representative_3434 : Rep := ⟨![0,12,20,48],462⟩
def representative_3435 : Rep := ⟨![0,12,20,49],462⟩
def representative_3436 : Rep := ⟨![0,12,20,50],462⟩
def representative_3437 : Rep := ⟨![0,12,20,56],462⟩
def representative_3438 : Rep := ⟨![0,12,24,36],462⟩
def representative_3439 : Rep := ⟨![0,12,24,42],462⟩
def representative_3440 : Rep := ⟨![0,12,24,43],462⟩
def representative_3441 : Rep := ⟨![0,12,24,44],462⟩
def representative_3442 : Rep := ⟨![0,12,24,50],462⟩
def representative_3443 : Rep := ⟨![0,12,24,51],462⟩
def representative_3444 : Rep := ⟨![0,12,24,52],462⟩
def representative_3445 : Rep := ⟨![0,12,25,37],462⟩
def representative_3446 : Rep := ⟨![0,12,25,43],462⟩
def representative_3447 : Rep := ⟨![0,12,25,44],462⟩
def representative_3448 : Rep := ⟨![0,12,25,45],462⟩
def representative_3449 : Rep := ⟨![0,12,25,46],462⟩
def representative_3450 : Rep := ⟨![0,12,25,47],462⟩
def representative_3451 : Rep := ⟨![0,12,25,51],462⟩
def representative_3452 : Rep := ⟨![0,12,25,53],462⟩
def representative_3453 : Rep := ⟨![0,12,25,54],462⟩
def representative_3454 : Rep := ⟨![0,12,25,55],462⟩
def representative_3455 : Rep := ⟨![0,12,26,38],462⟩
theorem coefficient_3392 : validRep representative_3392 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3392)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3393 : validRep representative_3393 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3393)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3394 : validRep representative_3394 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3394)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3395 : validRep representative_3395 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3395)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3396 : validRep representative_3396 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3396)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3397 : validRep representative_3397 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3397)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3398 : validRep representative_3398 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3398)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3399 : validRep representative_3399 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3399)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3400 : validRep representative_3400 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3400)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3401 : validRep representative_3401 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3401)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3402 : validRep representative_3402 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3402)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3403 : validRep representative_3403 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3403)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3404 : validRep representative_3404 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3404)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3405 : validRep representative_3405 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3405)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3406 : validRep representative_3406 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3406)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3407 : validRep representative_3407 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3407)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3408 : validRep representative_3408 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3408)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3409 : validRep representative_3409 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3409)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3410 : validRep representative_3410 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3410)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3411 : validRep representative_3411 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3411)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3412 : validRep representative_3412 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3412)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3413 : validRep representative_3413 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3413)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3414 : validRep representative_3414 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3414)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3415 : validRep representative_3415 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3415)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3416 : validRep representative_3416 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3416)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3417 : validRep representative_3417 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3417)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3418 : validRep representative_3418 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3418)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3419 : validRep representative_3419 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3419)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3420 : validRep representative_3420 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3420)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3421 : validRep representative_3421 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3421)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3422 : validRep representative_3422 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3422)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3423 : validRep representative_3423 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3423)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3424 : validRep representative_3424 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3424)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3425 : validRep representative_3425 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3425)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3426 : validRep representative_3426 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3426)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3427 : validRep representative_3427 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3427)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3428 : validRep representative_3428 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3428)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3429 : validRep representative_3429 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3429)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3430 : validRep representative_3430 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3430)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3431 : validRep representative_3431 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3431)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3432 : validRep representative_3432 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3432)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3433 : validRep representative_3433 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3433)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3434 : validRep representative_3434 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3434)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3435 : validRep representative_3435 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3435)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3436 : validRep representative_3436 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3436)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3437 : validRep representative_3437 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3437)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3438 : validRep representative_3438 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3438)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3439 : validRep representative_3439 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3439)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3440 : validRep representative_3440 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3440)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3441 : validRep representative_3441 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3441)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3442 : validRep representative_3442 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3442)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3443 : validRep representative_3443 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3443)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3444 : validRep representative_3444 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3444)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3445 : validRep representative_3445 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3445)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3446 : validRep representative_3446 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3446)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3447 : validRep representative_3447 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3447)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3448 : validRep representative_3448 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3448)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3449 : validRep representative_3449 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3449)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3450 : validRep representative_3450 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3450)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3451 : validRep representative_3451 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3451)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3452 : validRep representative_3452 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3452)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3453 : validRep representative_3453 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3453)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3454 : validRep representative_3454 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3454)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3455 : validRep representative_3455 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3455)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_053 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3424 (QuarticIntegerRepresentativeTree.Tree.branch 3408 (QuarticIntegerRepresentativeTree.Tree.branch 3400 (QuarticIntegerRepresentativeTree.Tree.branch 3396 (QuarticIntegerRepresentativeTree.Tree.branch 3394 (QuarticIntegerRepresentativeTree.Tree.branch 3393 (QuarticIntegerRepresentativeTree.Tree.leaf 3392 representative_3392) (QuarticIntegerRepresentativeTree.Tree.leaf 3393 representative_3393)) (QuarticIntegerRepresentativeTree.Tree.branch 3395 (QuarticIntegerRepresentativeTree.Tree.leaf 3394 representative_3394) (QuarticIntegerRepresentativeTree.Tree.leaf 3395 representative_3395))) (QuarticIntegerRepresentativeTree.Tree.branch 3398 (QuarticIntegerRepresentativeTree.Tree.branch 3397 (QuarticIntegerRepresentativeTree.Tree.leaf 3396 representative_3396) (QuarticIntegerRepresentativeTree.Tree.leaf 3397 representative_3397)) (QuarticIntegerRepresentativeTree.Tree.branch 3399 (QuarticIntegerRepresentativeTree.Tree.leaf 3398 representative_3398) (QuarticIntegerRepresentativeTree.Tree.leaf 3399 representative_3399)))) (QuarticIntegerRepresentativeTree.Tree.branch 3404 (QuarticIntegerRepresentativeTree.Tree.branch 3402 (QuarticIntegerRepresentativeTree.Tree.branch 3401 (QuarticIntegerRepresentativeTree.Tree.leaf 3400 representative_3400) (QuarticIntegerRepresentativeTree.Tree.leaf 3401 representative_3401)) (QuarticIntegerRepresentativeTree.Tree.branch 3403 (QuarticIntegerRepresentativeTree.Tree.leaf 3402 representative_3402) (QuarticIntegerRepresentativeTree.Tree.leaf 3403 representative_3403))) (QuarticIntegerRepresentativeTree.Tree.branch 3406 (QuarticIntegerRepresentativeTree.Tree.branch 3405 (QuarticIntegerRepresentativeTree.Tree.leaf 3404 representative_3404) (QuarticIntegerRepresentativeTree.Tree.leaf 3405 representative_3405)) (QuarticIntegerRepresentativeTree.Tree.branch 3407 (QuarticIntegerRepresentativeTree.Tree.leaf 3406 representative_3406) (QuarticIntegerRepresentativeTree.Tree.leaf 3407 representative_3407))))) (QuarticIntegerRepresentativeTree.Tree.branch 3416 (QuarticIntegerRepresentativeTree.Tree.branch 3412 (QuarticIntegerRepresentativeTree.Tree.branch 3410 (QuarticIntegerRepresentativeTree.Tree.branch 3409 (QuarticIntegerRepresentativeTree.Tree.leaf 3408 representative_3408) (QuarticIntegerRepresentativeTree.Tree.leaf 3409 representative_3409)) (QuarticIntegerRepresentativeTree.Tree.branch 3411 (QuarticIntegerRepresentativeTree.Tree.leaf 3410 representative_3410) (QuarticIntegerRepresentativeTree.Tree.leaf 3411 representative_3411))) (QuarticIntegerRepresentativeTree.Tree.branch 3414 (QuarticIntegerRepresentativeTree.Tree.branch 3413 (QuarticIntegerRepresentativeTree.Tree.leaf 3412 representative_3412) (QuarticIntegerRepresentativeTree.Tree.leaf 3413 representative_3413)) (QuarticIntegerRepresentativeTree.Tree.branch 3415 (QuarticIntegerRepresentativeTree.Tree.leaf 3414 representative_3414) (QuarticIntegerRepresentativeTree.Tree.leaf 3415 representative_3415)))) (QuarticIntegerRepresentativeTree.Tree.branch 3420 (QuarticIntegerRepresentativeTree.Tree.branch 3418 (QuarticIntegerRepresentativeTree.Tree.branch 3417 (QuarticIntegerRepresentativeTree.Tree.leaf 3416 representative_3416) (QuarticIntegerRepresentativeTree.Tree.leaf 3417 representative_3417)) (QuarticIntegerRepresentativeTree.Tree.branch 3419 (QuarticIntegerRepresentativeTree.Tree.leaf 3418 representative_3418) (QuarticIntegerRepresentativeTree.Tree.leaf 3419 representative_3419))) (QuarticIntegerRepresentativeTree.Tree.branch 3422 (QuarticIntegerRepresentativeTree.Tree.branch 3421 (QuarticIntegerRepresentativeTree.Tree.leaf 3420 representative_3420) (QuarticIntegerRepresentativeTree.Tree.leaf 3421 representative_3421)) (QuarticIntegerRepresentativeTree.Tree.branch 3423 (QuarticIntegerRepresentativeTree.Tree.leaf 3422 representative_3422) (QuarticIntegerRepresentativeTree.Tree.leaf 3423 representative_3423)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3440 (QuarticIntegerRepresentativeTree.Tree.branch 3432 (QuarticIntegerRepresentativeTree.Tree.branch 3428 (QuarticIntegerRepresentativeTree.Tree.branch 3426 (QuarticIntegerRepresentativeTree.Tree.branch 3425 (QuarticIntegerRepresentativeTree.Tree.leaf 3424 representative_3424) (QuarticIntegerRepresentativeTree.Tree.leaf 3425 representative_3425)) (QuarticIntegerRepresentativeTree.Tree.branch 3427 (QuarticIntegerRepresentativeTree.Tree.leaf 3426 representative_3426) (QuarticIntegerRepresentativeTree.Tree.leaf 3427 representative_3427))) (QuarticIntegerRepresentativeTree.Tree.branch 3430 (QuarticIntegerRepresentativeTree.Tree.branch 3429 (QuarticIntegerRepresentativeTree.Tree.leaf 3428 representative_3428) (QuarticIntegerRepresentativeTree.Tree.leaf 3429 representative_3429)) (QuarticIntegerRepresentativeTree.Tree.branch 3431 (QuarticIntegerRepresentativeTree.Tree.leaf 3430 representative_3430) (QuarticIntegerRepresentativeTree.Tree.leaf 3431 representative_3431)))) (QuarticIntegerRepresentativeTree.Tree.branch 3436 (QuarticIntegerRepresentativeTree.Tree.branch 3434 (QuarticIntegerRepresentativeTree.Tree.branch 3433 (QuarticIntegerRepresentativeTree.Tree.leaf 3432 representative_3432) (QuarticIntegerRepresentativeTree.Tree.leaf 3433 representative_3433)) (QuarticIntegerRepresentativeTree.Tree.branch 3435 (QuarticIntegerRepresentativeTree.Tree.leaf 3434 representative_3434) (QuarticIntegerRepresentativeTree.Tree.leaf 3435 representative_3435))) (QuarticIntegerRepresentativeTree.Tree.branch 3438 (QuarticIntegerRepresentativeTree.Tree.branch 3437 (QuarticIntegerRepresentativeTree.Tree.leaf 3436 representative_3436) (QuarticIntegerRepresentativeTree.Tree.leaf 3437 representative_3437)) (QuarticIntegerRepresentativeTree.Tree.branch 3439 (QuarticIntegerRepresentativeTree.Tree.leaf 3438 representative_3438) (QuarticIntegerRepresentativeTree.Tree.leaf 3439 representative_3439))))) (QuarticIntegerRepresentativeTree.Tree.branch 3448 (QuarticIntegerRepresentativeTree.Tree.branch 3444 (QuarticIntegerRepresentativeTree.Tree.branch 3442 (QuarticIntegerRepresentativeTree.Tree.branch 3441 (QuarticIntegerRepresentativeTree.Tree.leaf 3440 representative_3440) (QuarticIntegerRepresentativeTree.Tree.leaf 3441 representative_3441)) (QuarticIntegerRepresentativeTree.Tree.branch 3443 (QuarticIntegerRepresentativeTree.Tree.leaf 3442 representative_3442) (QuarticIntegerRepresentativeTree.Tree.leaf 3443 representative_3443))) (QuarticIntegerRepresentativeTree.Tree.branch 3446 (QuarticIntegerRepresentativeTree.Tree.branch 3445 (QuarticIntegerRepresentativeTree.Tree.leaf 3444 representative_3444) (QuarticIntegerRepresentativeTree.Tree.leaf 3445 representative_3445)) (QuarticIntegerRepresentativeTree.Tree.branch 3447 (QuarticIntegerRepresentativeTree.Tree.leaf 3446 representative_3446) (QuarticIntegerRepresentativeTree.Tree.leaf 3447 representative_3447)))) (QuarticIntegerRepresentativeTree.Tree.branch 3452 (QuarticIntegerRepresentativeTree.Tree.branch 3450 (QuarticIntegerRepresentativeTree.Tree.branch 3449 (QuarticIntegerRepresentativeTree.Tree.leaf 3448 representative_3448) (QuarticIntegerRepresentativeTree.Tree.leaf 3449 representative_3449)) (QuarticIntegerRepresentativeTree.Tree.branch 3451 (QuarticIntegerRepresentativeTree.Tree.leaf 3450 representative_3450) (QuarticIntegerRepresentativeTree.Tree.leaf 3451 representative_3451))) (QuarticIntegerRepresentativeTree.Tree.branch 3454 (QuarticIntegerRepresentativeTree.Tree.branch 3453 (QuarticIntegerRepresentativeTree.Tree.leaf 3452 representative_3452) (QuarticIntegerRepresentativeTree.Tree.leaf 3453 representative_3453)) (QuarticIntegerRepresentativeTree.Tree.branch 3455 (QuarticIntegerRepresentativeTree.Tree.leaf 3454 representative_3454) (QuarticIntegerRepresentativeTree.Tree.leaf 3455 representative_3455)))))))
theorem accepted_053 : All validRep tree_053 := ⟨⟨⟨⟨⟨⟨coefficient_3392,coefficient_3393⟩,⟨coefficient_3394,coefficient_3395⟩⟩,⟨⟨coefficient_3396,coefficient_3397⟩,⟨coefficient_3398,coefficient_3399⟩⟩⟩,⟨⟨⟨coefficient_3400,coefficient_3401⟩,⟨coefficient_3402,coefficient_3403⟩⟩,⟨⟨coefficient_3404,coefficient_3405⟩,⟨coefficient_3406,coefficient_3407⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3408,coefficient_3409⟩,⟨coefficient_3410,coefficient_3411⟩⟩,⟨⟨coefficient_3412,coefficient_3413⟩,⟨coefficient_3414,coefficient_3415⟩⟩⟩,⟨⟨⟨coefficient_3416,coefficient_3417⟩,⟨coefficient_3418,coefficient_3419⟩⟩,⟨⟨coefficient_3420,coefficient_3421⟩,⟨coefficient_3422,coefficient_3423⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3424,coefficient_3425⟩,⟨coefficient_3426,coefficient_3427⟩⟩,⟨⟨coefficient_3428,coefficient_3429⟩,⟨coefficient_3430,coefficient_3431⟩⟩⟩,⟨⟨⟨coefficient_3432,coefficient_3433⟩,⟨coefficient_3434,coefficient_3435⟩⟩,⟨⟨coefficient_3436,coefficient_3437⟩,⟨coefficient_3438,coefficient_3439⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3440,coefficient_3441⟩,⟨coefficient_3442,coefficient_3443⟩⟩,⟨⟨coefficient_3444,coefficient_3445⟩,⟨coefficient_3446,coefficient_3447⟩⟩⟩,⟨⟨⟨coefficient_3448,coefficient_3449⟩,⟨coefficient_3450,coefficient_3451⟩⟩,⟨⟨coefficient_3452,coefficient_3453⟩,⟨coefficient_3454,coefficient_3455⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

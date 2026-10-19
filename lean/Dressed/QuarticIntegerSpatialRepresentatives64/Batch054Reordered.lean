import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3456 : Rep := ⟨![0,12,26,40],462⟩
def representative_3457 : Rep := ⟨![0,12,26,44],462⟩
def representative_3458 : Rep := ⟨![0,12,26,45],462⟩
def representative_3459 : Rep := ⟨![0,12,26,46],462⟩
def representative_3460 : Rep := ⟨![0,12,26,47],462⟩
def representative_3461 : Rep := ⟨![0,12,26,48],462⟩
def representative_3462 : Rep := ⟨![0,12,26,54],462⟩
def representative_3463 : Rep := ⟨![0,12,26,55],462⟩
def representative_3464 : Rep := ⟨![0,12,27,39],462⟩
def representative_3465 : Rep := ⟨![0,12,27,40],462⟩
def representative_3466 : Rep := ⟨![0,12,27,41],462⟩
def representative_3467 : Rep := ⟨![0,12,27,45],462⟩
def representative_3468 : Rep := ⟨![0,12,27,46],462⟩
def representative_3469 : Rep := ⟨![0,12,27,47],462⟩
def representative_3470 : Rep := ⟨![0,12,27,48],462⟩
def representative_3471 : Rep := ⟨![0,12,27,49],462⟩
def representative_3472 : Rep := ⟨![0,12,27,55],462⟩
def representative_3473 : Rep := ⟨![0,12,28,32],462⟩
def representative_3474 : Rep := ⟨![0,12,28,40],462⟩
def representative_3475 : Rep := ⟨![0,12,28,41],462⟩
def representative_3476 : Rep := ⟨![0,12,28,42],462⟩
def representative_3477 : Rep := ⟨![0,12,28,48],462⟩
def representative_3478 : Rep := ⟨![0,12,32,44],462⟩
def representative_3479 : Rep := ⟨![0,12,33,45],462⟩
def representative_3480 : Rep := ⟨![0,12,34,46],462⟩
def representative_3481 : Rep := ⟨![0,12,35,47],462⟩
def representative_3482 : Rep := ⟨![0,12,36,40],462⟩
def representative_3483 : Rep := ⟨![0,18,1,19],462⟩
def representative_3484 : Rep := ⟨![0,18,1,20],462⟩
def representative_3485 : Rep := ⟨![0,18,1,21],462⟩
def representative_3486 : Rep := ⟨![0,18,1,22],462⟩
def representative_3487 : Rep := ⟨![0,18,1,23],11⟩
def representative_3488 : Rep := ⟨![0,18,1,27],462⟩
def representative_3489 : Rep := ⟨![0,18,1,28],462⟩
def representative_3490 : Rep := ⟨![0,18,1,29],462⟩
def representative_3491 : Rep := ⟨![0,18,1,30],462⟩
def representative_3492 : Rep := ⟨![0,18,1,31],462⟩
def representative_3493 : Rep := ⟨![0,18,1,35],462⟩
def representative_3494 : Rep := ⟨![0,18,1,36],462⟩
def representative_3495 : Rep := ⟨![0,18,1,37],462⟩
def representative_3496 : Rep := ⟨![0,18,1,38],462⟩
def representative_3497 : Rep := ⟨![0,18,1,39],462⟩
def representative_3498 : Rep := ⟨![0,18,1,43],462⟩
def representative_3499 : Rep := ⟨![0,18,1,44],462⟩
def representative_3500 : Rep := ⟨![0,18,1,45],462⟩
def representative_3501 : Rep := ⟨![0,18,1,46],462⟩
def representative_3502 : Rep := ⟨![0,18,1,47],462⟩
def representative_3503 : Rep := ⟨![0,18,1,51],462⟩
def representative_3504 : Rep := ⟨![0,18,1,52],462⟩
def representative_3505 : Rep := ⟨![0,18,1,53],462⟩
def representative_3506 : Rep := ⟨![0,18,1,54],462⟩
def representative_3507 : Rep := ⟨![0,18,1,55],11⟩
def representative_3508 : Rep := ⟨![0,18,2,16],462⟩
def representative_3509 : Rep := ⟨![0,18,2,20],462⟩
def representative_3510 : Rep := ⟨![0,18,2,21],462⟩
def representative_3511 : Rep := ⟨![0,18,2,22],462⟩
def representative_3512 : Rep := ⟨![0,18,2,23],462⟩
def representative_3513 : Rep := ⟨![0,18,2,28],462⟩
def representative_3514 : Rep := ⟨![0,18,2,29],462⟩
def representative_3515 : Rep := ⟨![0,18,2,30],462⟩
def representative_3516 : Rep := ⟨![0,18,2,31],462⟩
def representative_3517 : Rep := ⟨![0,18,2,36],462⟩
def representative_3518 : Rep := ⟨![0,18,2,37],462⟩
def representative_3519 : Rep := ⟨![0,18,2,38],462⟩
theorem coefficient_3456 : validRep representative_3456 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3456)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3457 : validRep representative_3457 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3457)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3458 : validRep representative_3458 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3458)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3459 : validRep representative_3459 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3459)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3460 : validRep representative_3460 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3460)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3461 : validRep representative_3461 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3461)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3462 : validRep representative_3462 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3462)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3463 : validRep representative_3463 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3463)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3464 : validRep representative_3464 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3464)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3465 : validRep representative_3465 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3465)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3466 : validRep representative_3466 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3466)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3467 : validRep representative_3467 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3467)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3468 : validRep representative_3468 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3468)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3469 : validRep representative_3469 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3469)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3470 : validRep representative_3470 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3470)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3471 : validRep representative_3471 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3471)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3472 : validRep representative_3472 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3472)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3473 : validRep representative_3473 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3473)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3474 : validRep representative_3474 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3474)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3475 : validRep representative_3475 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3475)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3476 : validRep representative_3476 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3476)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3477 : validRep representative_3477 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3477)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3478 : validRep representative_3478 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3478)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3479 : validRep representative_3479 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3479)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3480 : validRep representative_3480 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3480)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3481 : validRep representative_3481 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3481)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3482 : validRep representative_3482 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3482)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3483 : validRep representative_3483 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3483)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3484 : validRep representative_3484 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3484)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3485 : validRep representative_3485 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3485)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3486 : validRep representative_3486 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3486)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3487 : validRep representative_3487 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3487)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_3488 : validRep representative_3488 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3488)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3489 : validRep representative_3489 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3489)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3490 : validRep representative_3490 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3490)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3491 : validRep representative_3491 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3491)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3492 : validRep representative_3492 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3492)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3493 : validRep representative_3493 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3493)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3494 : validRep representative_3494 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3494)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3495 : validRep representative_3495 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3495)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3496 : validRep representative_3496 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3496)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3497 : validRep representative_3497 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3497)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3498 : validRep representative_3498 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3498)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3499 : validRep representative_3499 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3499)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3500 : validRep representative_3500 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3500)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3501 : validRep representative_3501 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3501)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3502 : validRep representative_3502 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3502)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3503 : validRep representative_3503 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3503)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3504 : validRep representative_3504 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3504)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3505 : validRep representative_3505 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3505)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3506 : validRep representative_3506 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3506)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3507 : validRep representative_3507 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3507)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_3508 : validRep representative_3508 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3508)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3509 : validRep representative_3509 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3509)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3510 : validRep representative_3510 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3510)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3511 : validRep representative_3511 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3511)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3512 : validRep representative_3512 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3512)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3513 : validRep representative_3513 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3513)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3514 : validRep representative_3514 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3514)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3515 : validRep representative_3515 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3515)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3516 : validRep representative_3516 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3516)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3517 : validRep representative_3517 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3517)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3518 : validRep representative_3518 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3518)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3519 : validRep representative_3519 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3519)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_054 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3488 (QuarticIntegerRepresentativeTree.Tree.branch 3472 (QuarticIntegerRepresentativeTree.Tree.branch 3464 (QuarticIntegerRepresentativeTree.Tree.branch 3460 (QuarticIntegerRepresentativeTree.Tree.branch 3458 (QuarticIntegerRepresentativeTree.Tree.branch 3457 (QuarticIntegerRepresentativeTree.Tree.leaf 3456 representative_3456) (QuarticIntegerRepresentativeTree.Tree.leaf 3457 representative_3457)) (QuarticIntegerRepresentativeTree.Tree.branch 3459 (QuarticIntegerRepresentativeTree.Tree.leaf 3458 representative_3458) (QuarticIntegerRepresentativeTree.Tree.leaf 3459 representative_3459))) (QuarticIntegerRepresentativeTree.Tree.branch 3462 (QuarticIntegerRepresentativeTree.Tree.branch 3461 (QuarticIntegerRepresentativeTree.Tree.leaf 3460 representative_3460) (QuarticIntegerRepresentativeTree.Tree.leaf 3461 representative_3461)) (QuarticIntegerRepresentativeTree.Tree.branch 3463 (QuarticIntegerRepresentativeTree.Tree.leaf 3462 representative_3462) (QuarticIntegerRepresentativeTree.Tree.leaf 3463 representative_3463)))) (QuarticIntegerRepresentativeTree.Tree.branch 3468 (QuarticIntegerRepresentativeTree.Tree.branch 3466 (QuarticIntegerRepresentativeTree.Tree.branch 3465 (QuarticIntegerRepresentativeTree.Tree.leaf 3464 representative_3464) (QuarticIntegerRepresentativeTree.Tree.leaf 3465 representative_3465)) (QuarticIntegerRepresentativeTree.Tree.branch 3467 (QuarticIntegerRepresentativeTree.Tree.leaf 3466 representative_3466) (QuarticIntegerRepresentativeTree.Tree.leaf 3467 representative_3467))) (QuarticIntegerRepresentativeTree.Tree.branch 3470 (QuarticIntegerRepresentativeTree.Tree.branch 3469 (QuarticIntegerRepresentativeTree.Tree.leaf 3468 representative_3468) (QuarticIntegerRepresentativeTree.Tree.leaf 3469 representative_3469)) (QuarticIntegerRepresentativeTree.Tree.branch 3471 (QuarticIntegerRepresentativeTree.Tree.leaf 3470 representative_3470) (QuarticIntegerRepresentativeTree.Tree.leaf 3471 representative_3471))))) (QuarticIntegerRepresentativeTree.Tree.branch 3480 (QuarticIntegerRepresentativeTree.Tree.branch 3476 (QuarticIntegerRepresentativeTree.Tree.branch 3474 (QuarticIntegerRepresentativeTree.Tree.branch 3473 (QuarticIntegerRepresentativeTree.Tree.leaf 3472 representative_3472) (QuarticIntegerRepresentativeTree.Tree.leaf 3473 representative_3473)) (QuarticIntegerRepresentativeTree.Tree.branch 3475 (QuarticIntegerRepresentativeTree.Tree.leaf 3474 representative_3474) (QuarticIntegerRepresentativeTree.Tree.leaf 3475 representative_3475))) (QuarticIntegerRepresentativeTree.Tree.branch 3478 (QuarticIntegerRepresentativeTree.Tree.branch 3477 (QuarticIntegerRepresentativeTree.Tree.leaf 3476 representative_3476) (QuarticIntegerRepresentativeTree.Tree.leaf 3477 representative_3477)) (QuarticIntegerRepresentativeTree.Tree.branch 3479 (QuarticIntegerRepresentativeTree.Tree.leaf 3478 representative_3478) (QuarticIntegerRepresentativeTree.Tree.leaf 3479 representative_3479)))) (QuarticIntegerRepresentativeTree.Tree.branch 3484 (QuarticIntegerRepresentativeTree.Tree.branch 3482 (QuarticIntegerRepresentativeTree.Tree.branch 3481 (QuarticIntegerRepresentativeTree.Tree.leaf 3480 representative_3480) (QuarticIntegerRepresentativeTree.Tree.leaf 3481 representative_3481)) (QuarticIntegerRepresentativeTree.Tree.branch 3483 (QuarticIntegerRepresentativeTree.Tree.leaf 3482 representative_3482) (QuarticIntegerRepresentativeTree.Tree.leaf 3483 representative_3483))) (QuarticIntegerRepresentativeTree.Tree.branch 3486 (QuarticIntegerRepresentativeTree.Tree.branch 3485 (QuarticIntegerRepresentativeTree.Tree.leaf 3484 representative_3484) (QuarticIntegerRepresentativeTree.Tree.leaf 3485 representative_3485)) (QuarticIntegerRepresentativeTree.Tree.branch 3487 (QuarticIntegerRepresentativeTree.Tree.leaf 3486 representative_3486) (QuarticIntegerRepresentativeTree.Tree.leaf 3487 representative_3487)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3504 (QuarticIntegerRepresentativeTree.Tree.branch 3496 (QuarticIntegerRepresentativeTree.Tree.branch 3492 (QuarticIntegerRepresentativeTree.Tree.branch 3490 (QuarticIntegerRepresentativeTree.Tree.branch 3489 (QuarticIntegerRepresentativeTree.Tree.leaf 3488 representative_3488) (QuarticIntegerRepresentativeTree.Tree.leaf 3489 representative_3489)) (QuarticIntegerRepresentativeTree.Tree.branch 3491 (QuarticIntegerRepresentativeTree.Tree.leaf 3490 representative_3490) (QuarticIntegerRepresentativeTree.Tree.leaf 3491 representative_3491))) (QuarticIntegerRepresentativeTree.Tree.branch 3494 (QuarticIntegerRepresentativeTree.Tree.branch 3493 (QuarticIntegerRepresentativeTree.Tree.leaf 3492 representative_3492) (QuarticIntegerRepresentativeTree.Tree.leaf 3493 representative_3493)) (QuarticIntegerRepresentativeTree.Tree.branch 3495 (QuarticIntegerRepresentativeTree.Tree.leaf 3494 representative_3494) (QuarticIntegerRepresentativeTree.Tree.leaf 3495 representative_3495)))) (QuarticIntegerRepresentativeTree.Tree.branch 3500 (QuarticIntegerRepresentativeTree.Tree.branch 3498 (QuarticIntegerRepresentativeTree.Tree.branch 3497 (QuarticIntegerRepresentativeTree.Tree.leaf 3496 representative_3496) (QuarticIntegerRepresentativeTree.Tree.leaf 3497 representative_3497)) (QuarticIntegerRepresentativeTree.Tree.branch 3499 (QuarticIntegerRepresentativeTree.Tree.leaf 3498 representative_3498) (QuarticIntegerRepresentativeTree.Tree.leaf 3499 representative_3499))) (QuarticIntegerRepresentativeTree.Tree.branch 3502 (QuarticIntegerRepresentativeTree.Tree.branch 3501 (QuarticIntegerRepresentativeTree.Tree.leaf 3500 representative_3500) (QuarticIntegerRepresentativeTree.Tree.leaf 3501 representative_3501)) (QuarticIntegerRepresentativeTree.Tree.branch 3503 (QuarticIntegerRepresentativeTree.Tree.leaf 3502 representative_3502) (QuarticIntegerRepresentativeTree.Tree.leaf 3503 representative_3503))))) (QuarticIntegerRepresentativeTree.Tree.branch 3512 (QuarticIntegerRepresentativeTree.Tree.branch 3508 (QuarticIntegerRepresentativeTree.Tree.branch 3506 (QuarticIntegerRepresentativeTree.Tree.branch 3505 (QuarticIntegerRepresentativeTree.Tree.leaf 3504 representative_3504) (QuarticIntegerRepresentativeTree.Tree.leaf 3505 representative_3505)) (QuarticIntegerRepresentativeTree.Tree.branch 3507 (QuarticIntegerRepresentativeTree.Tree.leaf 3506 representative_3506) (QuarticIntegerRepresentativeTree.Tree.leaf 3507 representative_3507))) (QuarticIntegerRepresentativeTree.Tree.branch 3510 (QuarticIntegerRepresentativeTree.Tree.branch 3509 (QuarticIntegerRepresentativeTree.Tree.leaf 3508 representative_3508) (QuarticIntegerRepresentativeTree.Tree.leaf 3509 representative_3509)) (QuarticIntegerRepresentativeTree.Tree.branch 3511 (QuarticIntegerRepresentativeTree.Tree.leaf 3510 representative_3510) (QuarticIntegerRepresentativeTree.Tree.leaf 3511 representative_3511)))) (QuarticIntegerRepresentativeTree.Tree.branch 3516 (QuarticIntegerRepresentativeTree.Tree.branch 3514 (QuarticIntegerRepresentativeTree.Tree.branch 3513 (QuarticIntegerRepresentativeTree.Tree.leaf 3512 representative_3512) (QuarticIntegerRepresentativeTree.Tree.leaf 3513 representative_3513)) (QuarticIntegerRepresentativeTree.Tree.branch 3515 (QuarticIntegerRepresentativeTree.Tree.leaf 3514 representative_3514) (QuarticIntegerRepresentativeTree.Tree.leaf 3515 representative_3515))) (QuarticIntegerRepresentativeTree.Tree.branch 3518 (QuarticIntegerRepresentativeTree.Tree.branch 3517 (QuarticIntegerRepresentativeTree.Tree.leaf 3516 representative_3516) (QuarticIntegerRepresentativeTree.Tree.leaf 3517 representative_3517)) (QuarticIntegerRepresentativeTree.Tree.branch 3519 (QuarticIntegerRepresentativeTree.Tree.leaf 3518 representative_3518) (QuarticIntegerRepresentativeTree.Tree.leaf 3519 representative_3519)))))))
theorem accepted_054 : All validRep tree_054 := ⟨⟨⟨⟨⟨⟨coefficient_3456,coefficient_3457⟩,⟨coefficient_3458,coefficient_3459⟩⟩,⟨⟨coefficient_3460,coefficient_3461⟩,⟨coefficient_3462,coefficient_3463⟩⟩⟩,⟨⟨⟨coefficient_3464,coefficient_3465⟩,⟨coefficient_3466,coefficient_3467⟩⟩,⟨⟨coefficient_3468,coefficient_3469⟩,⟨coefficient_3470,coefficient_3471⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3472,coefficient_3473⟩,⟨coefficient_3474,coefficient_3475⟩⟩,⟨⟨coefficient_3476,coefficient_3477⟩,⟨coefficient_3478,coefficient_3479⟩⟩⟩,⟨⟨⟨coefficient_3480,coefficient_3481⟩,⟨coefficient_3482,coefficient_3483⟩⟩,⟨⟨coefficient_3484,coefficient_3485⟩,⟨coefficient_3486,coefficient_3487⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3488,coefficient_3489⟩,⟨coefficient_3490,coefficient_3491⟩⟩,⟨⟨coefficient_3492,coefficient_3493⟩,⟨coefficient_3494,coefficient_3495⟩⟩⟩,⟨⟨⟨coefficient_3496,coefficient_3497⟩,⟨coefficient_3498,coefficient_3499⟩⟩,⟨⟨coefficient_3500,coefficient_3501⟩,⟨coefficient_3502,coefficient_3503⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3504,coefficient_3505⟩,⟨coefficient_3506,coefficient_3507⟩⟩,⟨⟨coefficient_3508,coefficient_3509⟩,⟨coefficient_3510,coefficient_3511⟩⟩⟩,⟨⟨⟨coefficient_3512,coefficient_3513⟩,⟨coefficient_3514,coefficient_3515⟩⟩,⟨⟨coefficient_3516,coefficient_3517⟩,⟨coefficient_3518,coefficient_3519⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

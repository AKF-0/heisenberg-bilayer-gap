import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3520 : Rep := ⟨![0,18,2,44],462⟩
def representative_3521 : Rep := ⟨![0,18,2,45],462⟩
def representative_3522 : Rep := ⟨![0,18,2,52],462⟩
def representative_3523 : Rep := ⟨![0,18,3,21],462⟩
def representative_3524 : Rep := ⟨![0,18,3,22],462⟩
def representative_3525 : Rep := ⟨![0,18,3,23],462⟩
def representative_3526 : Rep := ⟨![0,18,3,24],462⟩
def representative_3527 : Rep := ⟨![0,18,3,25],462⟩
def representative_3528 : Rep := ⟨![0,18,3,29],462⟩
def representative_3529 : Rep := ⟨![0,18,3,30],462⟩
def representative_3530 : Rep := ⟨![0,18,3,31],462⟩
def representative_3531 : Rep := ⟨![0,18,3,32],462⟩
def representative_3532 : Rep := ⟨![0,18,3,33],462⟩
def representative_3533 : Rep := ⟨![0,18,3,37],462⟩
def representative_3534 : Rep := ⟨![0,18,3,38],462⟩
def representative_3535 : Rep := ⟨![0,18,3,39],462⟩
def representative_3536 : Rep := ⟨![0,18,3,40],462⟩
def representative_3537 : Rep := ⟨![0,18,3,41],462⟩
def representative_3538 : Rep := ⟨![0,18,3,45],462⟩
def representative_3539 : Rep := ⟨![0,18,3,46],462⟩
def representative_3540 : Rep := ⟨![0,18,3,47],462⟩
def representative_3541 : Rep := ⟨![0,18,3,48],462⟩
def representative_3542 : Rep := ⟨![0,18,3,49],462⟩
def representative_3543 : Rep := ⟨![0,18,3,53],462⟩
def representative_3544 : Rep := ⟨![0,18,3,54],462⟩
def representative_3545 : Rep := ⟨![0,18,3,55],462⟩
def representative_3546 : Rep := ⟨![0,18,4,22],462⟩
def representative_3547 : Rep := ⟨![0,18,4,25],462⟩
def representative_3548 : Rep := ⟨![0,18,4,26],462⟩
def representative_3549 : Rep := ⟨![0,18,4,30],462⟩
def representative_3550 : Rep := ⟨![0,18,4,31],462⟩
def representative_3551 : Rep := ⟨![0,18,4,32],462⟩
def representative_3552 : Rep := ⟨![0,18,4,33],462⟩
def representative_3553 : Rep := ⟨![0,18,4,34],462⟩
def representative_3554 : Rep := ⟨![0,18,4,38],462⟩
def representative_3555 : Rep := ⟨![0,18,4,39],462⟩
def representative_3556 : Rep := ⟨![0,18,4,40],462⟩
def representative_3557 : Rep := ⟨![0,18,4,41],462⟩
def representative_3558 : Rep := ⟨![0,18,4,42],462⟩
def representative_3559 : Rep := ⟨![0,18,4,46],462⟩
def representative_3560 : Rep := ⟨![0,18,4,47],462⟩
def representative_3561 : Rep := ⟨![0,18,4,48],462⟩
def representative_3562 : Rep := ⟨![0,18,4,49],462⟩
def representative_3563 : Rep := ⟨![0,18,4,50],462⟩
def representative_3564 : Rep := ⟨![0,18,4,54],462⟩
def representative_3565 : Rep := ⟨![0,18,4,55],462⟩
def representative_3566 : Rep := ⟨![0,18,5,19],462⟩
def representative_3567 : Rep := ⟨![0,18,5,25],462⟩
def representative_3568 : Rep := ⟨![0,18,5,26],462⟩
def representative_3569 : Rep := ⟨![0,18,5,27],462⟩
def representative_3570 : Rep := ⟨![0,18,5,31],462⟩
def representative_3571 : Rep := ⟨![0,18,5,33],462⟩
def representative_3572 : Rep := ⟨![0,18,5,34],462⟩
def representative_3573 : Rep := ⟨![0,18,5,35],462⟩
def representative_3574 : Rep := ⟨![0,18,5,39],462⟩
def representative_3575 : Rep := ⟨![0,18,5,40],462⟩
def representative_3576 : Rep := ⟨![0,18,5,41],462⟩
def representative_3577 : Rep := ⟨![0,18,5,42],462⟩
def representative_3578 : Rep := ⟨![0,18,5,43],462⟩
def representative_3579 : Rep := ⟨![0,18,5,47],462⟩
def representative_3580 : Rep := ⟨![0,18,5,48],462⟩
def representative_3581 : Rep := ⟨![0,18,5,49],462⟩
def representative_3582 : Rep := ⟨![0,18,5,51],462⟩
def representative_3583 : Rep := ⟨![0,18,6,19],462⟩
theorem coefficient_3520 : validRep representative_3520 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3520)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3521 : validRep representative_3521 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3521)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3522 : validRep representative_3522 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3522)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3523 : validRep representative_3523 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3523)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3524 : validRep representative_3524 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3524)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3525 : validRep representative_3525 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3525)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3526 : validRep representative_3526 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3526)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3527 : validRep representative_3527 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3527)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3528 : validRep representative_3528 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3528)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3529 : validRep representative_3529 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3529)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3530 : validRep representative_3530 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3530)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3531 : validRep representative_3531 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3531)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3532 : validRep representative_3532 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3532)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3533 : validRep representative_3533 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3533)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3534 : validRep representative_3534 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3534)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3535 : validRep representative_3535 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3535)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3536 : validRep representative_3536 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3536)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3537 : validRep representative_3537 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3537)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3538 : validRep representative_3538 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3538)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3539 : validRep representative_3539 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3539)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3540 : validRep representative_3540 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3540)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3541 : validRep representative_3541 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3541)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3542 : validRep representative_3542 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3542)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3543 : validRep representative_3543 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3543)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3544 : validRep representative_3544 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3544)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3545 : validRep representative_3545 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3545)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3546 : validRep representative_3546 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3546)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3547 : validRep representative_3547 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3547)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3548 : validRep representative_3548 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3548)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3549 : validRep representative_3549 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3549)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3550 : validRep representative_3550 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3550)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3551 : validRep representative_3551 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3551)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3552 : validRep representative_3552 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3552)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3553 : validRep representative_3553 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3553)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3554 : validRep representative_3554 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3554)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3555 : validRep representative_3555 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3555)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3556 : validRep representative_3556 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3556)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3557 : validRep representative_3557 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3557)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3558 : validRep representative_3558 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3558)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3559 : validRep representative_3559 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3559)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3560 : validRep representative_3560 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3560)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3561 : validRep representative_3561 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3561)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3562 : validRep representative_3562 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3562)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3563 : validRep representative_3563 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3563)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3564 : validRep representative_3564 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3564)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3565 : validRep representative_3565 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3565)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3566 : validRep representative_3566 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3566)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3567 : validRep representative_3567 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3567)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3568 : validRep representative_3568 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3568)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3569 : validRep representative_3569 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3569)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3570 : validRep representative_3570 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3570)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3571 : validRep representative_3571 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3571)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3572 : validRep representative_3572 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3572)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3573 : validRep representative_3573 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3573)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3574 : validRep representative_3574 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3574)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3575 : validRep representative_3575 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3575)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3576 : validRep representative_3576 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3576)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3577 : validRep representative_3577 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3577)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3578 : validRep representative_3578 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3578)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3579 : validRep representative_3579 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3579)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3580 : validRep representative_3580 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3580)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3581 : validRep representative_3581 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3581)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3582 : validRep representative_3582 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3582)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3583 : validRep representative_3583 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3583)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_055 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3552 (QuarticIntegerRepresentativeTree.Tree.branch 3536 (QuarticIntegerRepresentativeTree.Tree.branch 3528 (QuarticIntegerRepresentativeTree.Tree.branch 3524 (QuarticIntegerRepresentativeTree.Tree.branch 3522 (QuarticIntegerRepresentativeTree.Tree.branch 3521 (QuarticIntegerRepresentativeTree.Tree.leaf 3520 representative_3520) (QuarticIntegerRepresentativeTree.Tree.leaf 3521 representative_3521)) (QuarticIntegerRepresentativeTree.Tree.branch 3523 (QuarticIntegerRepresentativeTree.Tree.leaf 3522 representative_3522) (QuarticIntegerRepresentativeTree.Tree.leaf 3523 representative_3523))) (QuarticIntegerRepresentativeTree.Tree.branch 3526 (QuarticIntegerRepresentativeTree.Tree.branch 3525 (QuarticIntegerRepresentativeTree.Tree.leaf 3524 representative_3524) (QuarticIntegerRepresentativeTree.Tree.leaf 3525 representative_3525)) (QuarticIntegerRepresentativeTree.Tree.branch 3527 (QuarticIntegerRepresentativeTree.Tree.leaf 3526 representative_3526) (QuarticIntegerRepresentativeTree.Tree.leaf 3527 representative_3527)))) (QuarticIntegerRepresentativeTree.Tree.branch 3532 (QuarticIntegerRepresentativeTree.Tree.branch 3530 (QuarticIntegerRepresentativeTree.Tree.branch 3529 (QuarticIntegerRepresentativeTree.Tree.leaf 3528 representative_3528) (QuarticIntegerRepresentativeTree.Tree.leaf 3529 representative_3529)) (QuarticIntegerRepresentativeTree.Tree.branch 3531 (QuarticIntegerRepresentativeTree.Tree.leaf 3530 representative_3530) (QuarticIntegerRepresentativeTree.Tree.leaf 3531 representative_3531))) (QuarticIntegerRepresentativeTree.Tree.branch 3534 (QuarticIntegerRepresentativeTree.Tree.branch 3533 (QuarticIntegerRepresentativeTree.Tree.leaf 3532 representative_3532) (QuarticIntegerRepresentativeTree.Tree.leaf 3533 representative_3533)) (QuarticIntegerRepresentativeTree.Tree.branch 3535 (QuarticIntegerRepresentativeTree.Tree.leaf 3534 representative_3534) (QuarticIntegerRepresentativeTree.Tree.leaf 3535 representative_3535))))) (QuarticIntegerRepresentativeTree.Tree.branch 3544 (QuarticIntegerRepresentativeTree.Tree.branch 3540 (QuarticIntegerRepresentativeTree.Tree.branch 3538 (QuarticIntegerRepresentativeTree.Tree.branch 3537 (QuarticIntegerRepresentativeTree.Tree.leaf 3536 representative_3536) (QuarticIntegerRepresentativeTree.Tree.leaf 3537 representative_3537)) (QuarticIntegerRepresentativeTree.Tree.branch 3539 (QuarticIntegerRepresentativeTree.Tree.leaf 3538 representative_3538) (QuarticIntegerRepresentativeTree.Tree.leaf 3539 representative_3539))) (QuarticIntegerRepresentativeTree.Tree.branch 3542 (QuarticIntegerRepresentativeTree.Tree.branch 3541 (QuarticIntegerRepresentativeTree.Tree.leaf 3540 representative_3540) (QuarticIntegerRepresentativeTree.Tree.leaf 3541 representative_3541)) (QuarticIntegerRepresentativeTree.Tree.branch 3543 (QuarticIntegerRepresentativeTree.Tree.leaf 3542 representative_3542) (QuarticIntegerRepresentativeTree.Tree.leaf 3543 representative_3543)))) (QuarticIntegerRepresentativeTree.Tree.branch 3548 (QuarticIntegerRepresentativeTree.Tree.branch 3546 (QuarticIntegerRepresentativeTree.Tree.branch 3545 (QuarticIntegerRepresentativeTree.Tree.leaf 3544 representative_3544) (QuarticIntegerRepresentativeTree.Tree.leaf 3545 representative_3545)) (QuarticIntegerRepresentativeTree.Tree.branch 3547 (QuarticIntegerRepresentativeTree.Tree.leaf 3546 representative_3546) (QuarticIntegerRepresentativeTree.Tree.leaf 3547 representative_3547))) (QuarticIntegerRepresentativeTree.Tree.branch 3550 (QuarticIntegerRepresentativeTree.Tree.branch 3549 (QuarticIntegerRepresentativeTree.Tree.leaf 3548 representative_3548) (QuarticIntegerRepresentativeTree.Tree.leaf 3549 representative_3549)) (QuarticIntegerRepresentativeTree.Tree.branch 3551 (QuarticIntegerRepresentativeTree.Tree.leaf 3550 representative_3550) (QuarticIntegerRepresentativeTree.Tree.leaf 3551 representative_3551)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3568 (QuarticIntegerRepresentativeTree.Tree.branch 3560 (QuarticIntegerRepresentativeTree.Tree.branch 3556 (QuarticIntegerRepresentativeTree.Tree.branch 3554 (QuarticIntegerRepresentativeTree.Tree.branch 3553 (QuarticIntegerRepresentativeTree.Tree.leaf 3552 representative_3552) (QuarticIntegerRepresentativeTree.Tree.leaf 3553 representative_3553)) (QuarticIntegerRepresentativeTree.Tree.branch 3555 (QuarticIntegerRepresentativeTree.Tree.leaf 3554 representative_3554) (QuarticIntegerRepresentativeTree.Tree.leaf 3555 representative_3555))) (QuarticIntegerRepresentativeTree.Tree.branch 3558 (QuarticIntegerRepresentativeTree.Tree.branch 3557 (QuarticIntegerRepresentativeTree.Tree.leaf 3556 representative_3556) (QuarticIntegerRepresentativeTree.Tree.leaf 3557 representative_3557)) (QuarticIntegerRepresentativeTree.Tree.branch 3559 (QuarticIntegerRepresentativeTree.Tree.leaf 3558 representative_3558) (QuarticIntegerRepresentativeTree.Tree.leaf 3559 representative_3559)))) (QuarticIntegerRepresentativeTree.Tree.branch 3564 (QuarticIntegerRepresentativeTree.Tree.branch 3562 (QuarticIntegerRepresentativeTree.Tree.branch 3561 (QuarticIntegerRepresentativeTree.Tree.leaf 3560 representative_3560) (QuarticIntegerRepresentativeTree.Tree.leaf 3561 representative_3561)) (QuarticIntegerRepresentativeTree.Tree.branch 3563 (QuarticIntegerRepresentativeTree.Tree.leaf 3562 representative_3562) (QuarticIntegerRepresentativeTree.Tree.leaf 3563 representative_3563))) (QuarticIntegerRepresentativeTree.Tree.branch 3566 (QuarticIntegerRepresentativeTree.Tree.branch 3565 (QuarticIntegerRepresentativeTree.Tree.leaf 3564 representative_3564) (QuarticIntegerRepresentativeTree.Tree.leaf 3565 representative_3565)) (QuarticIntegerRepresentativeTree.Tree.branch 3567 (QuarticIntegerRepresentativeTree.Tree.leaf 3566 representative_3566) (QuarticIntegerRepresentativeTree.Tree.leaf 3567 representative_3567))))) (QuarticIntegerRepresentativeTree.Tree.branch 3576 (QuarticIntegerRepresentativeTree.Tree.branch 3572 (QuarticIntegerRepresentativeTree.Tree.branch 3570 (QuarticIntegerRepresentativeTree.Tree.branch 3569 (QuarticIntegerRepresentativeTree.Tree.leaf 3568 representative_3568) (QuarticIntegerRepresentativeTree.Tree.leaf 3569 representative_3569)) (QuarticIntegerRepresentativeTree.Tree.branch 3571 (QuarticIntegerRepresentativeTree.Tree.leaf 3570 representative_3570) (QuarticIntegerRepresentativeTree.Tree.leaf 3571 representative_3571))) (QuarticIntegerRepresentativeTree.Tree.branch 3574 (QuarticIntegerRepresentativeTree.Tree.branch 3573 (QuarticIntegerRepresentativeTree.Tree.leaf 3572 representative_3572) (QuarticIntegerRepresentativeTree.Tree.leaf 3573 representative_3573)) (QuarticIntegerRepresentativeTree.Tree.branch 3575 (QuarticIntegerRepresentativeTree.Tree.leaf 3574 representative_3574) (QuarticIntegerRepresentativeTree.Tree.leaf 3575 representative_3575)))) (QuarticIntegerRepresentativeTree.Tree.branch 3580 (QuarticIntegerRepresentativeTree.Tree.branch 3578 (QuarticIntegerRepresentativeTree.Tree.branch 3577 (QuarticIntegerRepresentativeTree.Tree.leaf 3576 representative_3576) (QuarticIntegerRepresentativeTree.Tree.leaf 3577 representative_3577)) (QuarticIntegerRepresentativeTree.Tree.branch 3579 (QuarticIntegerRepresentativeTree.Tree.leaf 3578 representative_3578) (QuarticIntegerRepresentativeTree.Tree.leaf 3579 representative_3579))) (QuarticIntegerRepresentativeTree.Tree.branch 3582 (QuarticIntegerRepresentativeTree.Tree.branch 3581 (QuarticIntegerRepresentativeTree.Tree.leaf 3580 representative_3580) (QuarticIntegerRepresentativeTree.Tree.leaf 3581 representative_3581)) (QuarticIntegerRepresentativeTree.Tree.branch 3583 (QuarticIntegerRepresentativeTree.Tree.leaf 3582 representative_3582) (QuarticIntegerRepresentativeTree.Tree.leaf 3583 representative_3583)))))))
theorem accepted_055 : All validRep tree_055 := ⟨⟨⟨⟨⟨⟨coefficient_3520,coefficient_3521⟩,⟨coefficient_3522,coefficient_3523⟩⟩,⟨⟨coefficient_3524,coefficient_3525⟩,⟨coefficient_3526,coefficient_3527⟩⟩⟩,⟨⟨⟨coefficient_3528,coefficient_3529⟩,⟨coefficient_3530,coefficient_3531⟩⟩,⟨⟨coefficient_3532,coefficient_3533⟩,⟨coefficient_3534,coefficient_3535⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3536,coefficient_3537⟩,⟨coefficient_3538,coefficient_3539⟩⟩,⟨⟨coefficient_3540,coefficient_3541⟩,⟨coefficient_3542,coefficient_3543⟩⟩⟩,⟨⟨⟨coefficient_3544,coefficient_3545⟩,⟨coefficient_3546,coefficient_3547⟩⟩,⟨⟨coefficient_3548,coefficient_3549⟩,⟨coefficient_3550,coefficient_3551⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3552,coefficient_3553⟩,⟨coefficient_3554,coefficient_3555⟩⟩,⟨⟨coefficient_3556,coefficient_3557⟩,⟨coefficient_3558,coefficient_3559⟩⟩⟩,⟨⟨⟨coefficient_3560,coefficient_3561⟩,⟨coefficient_3562,coefficient_3563⟩⟩,⟨⟨coefficient_3564,coefficient_3565⟩,⟨coefficient_3566,coefficient_3567⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3568,coefficient_3569⟩,⟨coefficient_3570,coefficient_3571⟩⟩,⟨⟨coefficient_3572,coefficient_3573⟩,⟨coefficient_3574,coefficient_3575⟩⟩⟩,⟨⟨⟨coefficient_3576,coefficient_3577⟩,⟨coefficient_3578,coefficient_3579⟩⟩,⟨⟨coefficient_3580,coefficient_3581⟩,⟨coefficient_3582,coefficient_3583⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

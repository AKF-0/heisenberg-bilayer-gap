import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3584 : Rep := ⟨![0,18,6,20],462⟩
def representative_3585 : Rep := ⟨![0,18,6,25],462⟩
def representative_3586 : Rep := ⟨![0,18,6,26],462⟩
def representative_3587 : Rep := ⟨![0,18,6,27],462⟩
def representative_3588 : Rep := ⟨![0,18,6,28],462⟩
def representative_3589 : Rep := ⟨![0,18,6,33],462⟩
def representative_3590 : Rep := ⟨![0,18,6,34],462⟩
def representative_3591 : Rep := ⟨![0,18,6,35],462⟩
def representative_3592 : Rep := ⟨![0,18,6,36],462⟩
def representative_3593 : Rep := ⟨![0,18,6,41],462⟩
def representative_3594 : Rep := ⟨![0,18,6,43],462⟩
def representative_3595 : Rep := ⟨![0,18,6,44],462⟩
def representative_3596 : Rep := ⟨![0,18,6,49],462⟩
def representative_3597 : Rep := ⟨![0,18,6,51],462⟩
def representative_3598 : Rep := ⟨![0,18,6,52],462⟩
def representative_3599 : Rep := ⟨![0,18,7,19],462⟩
def representative_3600 : Rep := ⟨![0,18,7,25],462⟩
def representative_3601 : Rep := ⟨![0,18,7,26],462⟩
def representative_3602 : Rep := ⟨![0,18,7,27],462⟩
def representative_3603 : Rep := ⟨![0,18,7,28],462⟩
def representative_3604 : Rep := ⟨![0,18,7,29],462⟩
def representative_3605 : Rep := ⟨![0,18,7,33],462⟩
def representative_3606 : Rep := ⟨![0,18,7,35],462⟩
def representative_3607 : Rep := ⟨![0,18,7,36],462⟩
def representative_3608 : Rep := ⟨![0,18,7,37],462⟩
def representative_3609 : Rep := ⟨![0,18,7,41],462⟩
def representative_3610 : Rep := ⟨![0,18,7,43],462⟩
def representative_3611 : Rep := ⟨![0,18,7,44],462⟩
def representative_3612 : Rep := ⟨![0,18,7,45],462⟩
def representative_3613 : Rep := ⟨![0,18,7,51],462⟩
def representative_3614 : Rep := ⟨![0,18,7,52],462⟩
def representative_3615 : Rep := ⟨![0,18,7,53],462⟩
def representative_3616 : Rep := ⟨![0,18,9,27],462⟩
def representative_3617 : Rep := ⟨![0,18,9,28],462⟩
def representative_3618 : Rep := ⟨![0,18,9,29],462⟩
def representative_3619 : Rep := ⟨![0,18,9,30],462⟩
def representative_3620 : Rep := ⟨![0,18,9,31],462⟩
def representative_3621 : Rep := ⟨![0,18,9,36],462⟩
def representative_3622 : Rep := ⟨![0,18,9,37],462⟩
def representative_3623 : Rep := ⟨![0,18,9,38],462⟩
def representative_3624 : Rep := ⟨![0,18,9,45],462⟩
def representative_3625 : Rep := ⟨![0,18,11,29],462⟩
def representative_3626 : Rep := ⟨![0,18,11,30],462⟩
def representative_3627 : Rep := ⟨![0,18,11,31],462⟩
def representative_3628 : Rep := ⟨![0,18,11,33],462⟩
def representative_3629 : Rep := ⟨![0,18,11,37],462⟩
def representative_3630 : Rep := ⟨![0,18,11,38],462⟩
def representative_3631 : Rep := ⟨![0,18,11,39],462⟩
def representative_3632 : Rep := ⟨![0,18,11,41],462⟩
def representative_3633 : Rep := ⟨![0,18,11,45],462⟩
def representative_3634 : Rep := ⟨![0,18,11,46],462⟩
def representative_3635 : Rep := ⟨![0,18,11,47],462⟩
def representative_3636 : Rep := ⟨![0,18,11,49],462⟩
def representative_3637 : Rep := ⟨![0,18,11,53],462⟩
def representative_3638 : Rep := ⟨![0,18,11,54],462⟩
def representative_3639 : Rep := ⟨![0,18,11,55],462⟩
def representative_3640 : Rep := ⟨![0,18,11,57],462⟩
def representative_3641 : Rep := ⟨![0,18,11,61],462⟩
def representative_3642 : Rep := ⟨![0,18,11,62],462⟩
def representative_3643 : Rep := ⟨![0,18,11,63],462⟩
def representative_3644 : Rep := ⟨![0,18,12,30],462⟩
def representative_3645 : Rep := ⟨![0,18,12,31],462⟩
def representative_3646 : Rep := ⟨![0,18,12,33],462⟩
def representative_3647 : Rep := ⟨![0,18,12,38],462⟩
theorem coefficient_3584 : validRep representative_3584 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3584)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3585 : validRep representative_3585 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3585)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3586 : validRep representative_3586 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3586)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3587 : validRep representative_3587 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3587)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3588 : validRep representative_3588 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3588)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3589 : validRep representative_3589 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3589)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3590 : validRep representative_3590 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3590)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3591 : validRep representative_3591 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3591)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3592 : validRep representative_3592 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3592)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3593 : validRep representative_3593 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3593)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3594 : validRep representative_3594 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3594)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3595 : validRep representative_3595 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3595)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3596 : validRep representative_3596 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3596)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3597 : validRep representative_3597 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3597)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3598 : validRep representative_3598 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3598)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3599 : validRep representative_3599 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3599)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3600 : validRep representative_3600 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3600)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3601 : validRep representative_3601 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3601)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3602 : validRep representative_3602 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3602)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3603 : validRep representative_3603 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3603)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3604 : validRep representative_3604 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3604)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3605 : validRep representative_3605 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3605)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3606 : validRep representative_3606 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3606)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3607 : validRep representative_3607 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3607)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3608 : validRep representative_3608 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3608)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3609 : validRep representative_3609 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3609)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3610 : validRep representative_3610 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3610)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3611 : validRep representative_3611 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3611)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3612 : validRep representative_3612 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3612)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3613 : validRep representative_3613 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3613)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3614 : validRep representative_3614 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3614)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3615 : validRep representative_3615 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3615)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3616 : validRep representative_3616 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3616)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3617 : validRep representative_3617 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3617)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3618 : validRep representative_3618 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3618)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3619 : validRep representative_3619 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3619)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3620 : validRep representative_3620 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3620)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3621 : validRep representative_3621 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3621)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3622 : validRep representative_3622 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3622)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3623 : validRep representative_3623 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3623)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3624 : validRep representative_3624 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3624)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3625 : validRep representative_3625 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3625)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3626 : validRep representative_3626 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3626)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3627 : validRep representative_3627 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3627)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3628 : validRep representative_3628 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3628)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3629 : validRep representative_3629 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3629)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3630 : validRep representative_3630 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3630)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3631 : validRep representative_3631 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3631)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3632 : validRep representative_3632 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3632)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3633 : validRep representative_3633 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3633)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3634 : validRep representative_3634 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3634)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3635 : validRep representative_3635 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3635)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3636 : validRep representative_3636 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3636)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3637 : validRep representative_3637 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3637)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3638 : validRep representative_3638 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3638)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3639 : validRep representative_3639 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3639)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3640 : validRep representative_3640 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3640)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3641 : validRep representative_3641 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3641)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3642 : validRep representative_3642 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3642)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3643 : validRep representative_3643 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3643)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3644 : validRep representative_3644 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3644)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3645 : validRep representative_3645 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3645)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3646 : validRep representative_3646 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3646)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3647 : validRep representative_3647 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3647)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_056 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3616 (QuarticIntegerRepresentativeTree.Tree.branch 3600 (QuarticIntegerRepresentativeTree.Tree.branch 3592 (QuarticIntegerRepresentativeTree.Tree.branch 3588 (QuarticIntegerRepresentativeTree.Tree.branch 3586 (QuarticIntegerRepresentativeTree.Tree.branch 3585 (QuarticIntegerRepresentativeTree.Tree.leaf 3584 representative_3584) (QuarticIntegerRepresentativeTree.Tree.leaf 3585 representative_3585)) (QuarticIntegerRepresentativeTree.Tree.branch 3587 (QuarticIntegerRepresentativeTree.Tree.leaf 3586 representative_3586) (QuarticIntegerRepresentativeTree.Tree.leaf 3587 representative_3587))) (QuarticIntegerRepresentativeTree.Tree.branch 3590 (QuarticIntegerRepresentativeTree.Tree.branch 3589 (QuarticIntegerRepresentativeTree.Tree.leaf 3588 representative_3588) (QuarticIntegerRepresentativeTree.Tree.leaf 3589 representative_3589)) (QuarticIntegerRepresentativeTree.Tree.branch 3591 (QuarticIntegerRepresentativeTree.Tree.leaf 3590 representative_3590) (QuarticIntegerRepresentativeTree.Tree.leaf 3591 representative_3591)))) (QuarticIntegerRepresentativeTree.Tree.branch 3596 (QuarticIntegerRepresentativeTree.Tree.branch 3594 (QuarticIntegerRepresentativeTree.Tree.branch 3593 (QuarticIntegerRepresentativeTree.Tree.leaf 3592 representative_3592) (QuarticIntegerRepresentativeTree.Tree.leaf 3593 representative_3593)) (QuarticIntegerRepresentativeTree.Tree.branch 3595 (QuarticIntegerRepresentativeTree.Tree.leaf 3594 representative_3594) (QuarticIntegerRepresentativeTree.Tree.leaf 3595 representative_3595))) (QuarticIntegerRepresentativeTree.Tree.branch 3598 (QuarticIntegerRepresentativeTree.Tree.branch 3597 (QuarticIntegerRepresentativeTree.Tree.leaf 3596 representative_3596) (QuarticIntegerRepresentativeTree.Tree.leaf 3597 representative_3597)) (QuarticIntegerRepresentativeTree.Tree.branch 3599 (QuarticIntegerRepresentativeTree.Tree.leaf 3598 representative_3598) (QuarticIntegerRepresentativeTree.Tree.leaf 3599 representative_3599))))) (QuarticIntegerRepresentativeTree.Tree.branch 3608 (QuarticIntegerRepresentativeTree.Tree.branch 3604 (QuarticIntegerRepresentativeTree.Tree.branch 3602 (QuarticIntegerRepresentativeTree.Tree.branch 3601 (QuarticIntegerRepresentativeTree.Tree.leaf 3600 representative_3600) (QuarticIntegerRepresentativeTree.Tree.leaf 3601 representative_3601)) (QuarticIntegerRepresentativeTree.Tree.branch 3603 (QuarticIntegerRepresentativeTree.Tree.leaf 3602 representative_3602) (QuarticIntegerRepresentativeTree.Tree.leaf 3603 representative_3603))) (QuarticIntegerRepresentativeTree.Tree.branch 3606 (QuarticIntegerRepresentativeTree.Tree.branch 3605 (QuarticIntegerRepresentativeTree.Tree.leaf 3604 representative_3604) (QuarticIntegerRepresentativeTree.Tree.leaf 3605 representative_3605)) (QuarticIntegerRepresentativeTree.Tree.branch 3607 (QuarticIntegerRepresentativeTree.Tree.leaf 3606 representative_3606) (QuarticIntegerRepresentativeTree.Tree.leaf 3607 representative_3607)))) (QuarticIntegerRepresentativeTree.Tree.branch 3612 (QuarticIntegerRepresentativeTree.Tree.branch 3610 (QuarticIntegerRepresentativeTree.Tree.branch 3609 (QuarticIntegerRepresentativeTree.Tree.leaf 3608 representative_3608) (QuarticIntegerRepresentativeTree.Tree.leaf 3609 representative_3609)) (QuarticIntegerRepresentativeTree.Tree.branch 3611 (QuarticIntegerRepresentativeTree.Tree.leaf 3610 representative_3610) (QuarticIntegerRepresentativeTree.Tree.leaf 3611 representative_3611))) (QuarticIntegerRepresentativeTree.Tree.branch 3614 (QuarticIntegerRepresentativeTree.Tree.branch 3613 (QuarticIntegerRepresentativeTree.Tree.leaf 3612 representative_3612) (QuarticIntegerRepresentativeTree.Tree.leaf 3613 representative_3613)) (QuarticIntegerRepresentativeTree.Tree.branch 3615 (QuarticIntegerRepresentativeTree.Tree.leaf 3614 representative_3614) (QuarticIntegerRepresentativeTree.Tree.leaf 3615 representative_3615)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3632 (QuarticIntegerRepresentativeTree.Tree.branch 3624 (QuarticIntegerRepresentativeTree.Tree.branch 3620 (QuarticIntegerRepresentativeTree.Tree.branch 3618 (QuarticIntegerRepresentativeTree.Tree.branch 3617 (QuarticIntegerRepresentativeTree.Tree.leaf 3616 representative_3616) (QuarticIntegerRepresentativeTree.Tree.leaf 3617 representative_3617)) (QuarticIntegerRepresentativeTree.Tree.branch 3619 (QuarticIntegerRepresentativeTree.Tree.leaf 3618 representative_3618) (QuarticIntegerRepresentativeTree.Tree.leaf 3619 representative_3619))) (QuarticIntegerRepresentativeTree.Tree.branch 3622 (QuarticIntegerRepresentativeTree.Tree.branch 3621 (QuarticIntegerRepresentativeTree.Tree.leaf 3620 representative_3620) (QuarticIntegerRepresentativeTree.Tree.leaf 3621 representative_3621)) (QuarticIntegerRepresentativeTree.Tree.branch 3623 (QuarticIntegerRepresentativeTree.Tree.leaf 3622 representative_3622) (QuarticIntegerRepresentativeTree.Tree.leaf 3623 representative_3623)))) (QuarticIntegerRepresentativeTree.Tree.branch 3628 (QuarticIntegerRepresentativeTree.Tree.branch 3626 (QuarticIntegerRepresentativeTree.Tree.branch 3625 (QuarticIntegerRepresentativeTree.Tree.leaf 3624 representative_3624) (QuarticIntegerRepresentativeTree.Tree.leaf 3625 representative_3625)) (QuarticIntegerRepresentativeTree.Tree.branch 3627 (QuarticIntegerRepresentativeTree.Tree.leaf 3626 representative_3626) (QuarticIntegerRepresentativeTree.Tree.leaf 3627 representative_3627))) (QuarticIntegerRepresentativeTree.Tree.branch 3630 (QuarticIntegerRepresentativeTree.Tree.branch 3629 (QuarticIntegerRepresentativeTree.Tree.leaf 3628 representative_3628) (QuarticIntegerRepresentativeTree.Tree.leaf 3629 representative_3629)) (QuarticIntegerRepresentativeTree.Tree.branch 3631 (QuarticIntegerRepresentativeTree.Tree.leaf 3630 representative_3630) (QuarticIntegerRepresentativeTree.Tree.leaf 3631 representative_3631))))) (QuarticIntegerRepresentativeTree.Tree.branch 3640 (QuarticIntegerRepresentativeTree.Tree.branch 3636 (QuarticIntegerRepresentativeTree.Tree.branch 3634 (QuarticIntegerRepresentativeTree.Tree.branch 3633 (QuarticIntegerRepresentativeTree.Tree.leaf 3632 representative_3632) (QuarticIntegerRepresentativeTree.Tree.leaf 3633 representative_3633)) (QuarticIntegerRepresentativeTree.Tree.branch 3635 (QuarticIntegerRepresentativeTree.Tree.leaf 3634 representative_3634) (QuarticIntegerRepresentativeTree.Tree.leaf 3635 representative_3635))) (QuarticIntegerRepresentativeTree.Tree.branch 3638 (QuarticIntegerRepresentativeTree.Tree.branch 3637 (QuarticIntegerRepresentativeTree.Tree.leaf 3636 representative_3636) (QuarticIntegerRepresentativeTree.Tree.leaf 3637 representative_3637)) (QuarticIntegerRepresentativeTree.Tree.branch 3639 (QuarticIntegerRepresentativeTree.Tree.leaf 3638 representative_3638) (QuarticIntegerRepresentativeTree.Tree.leaf 3639 representative_3639)))) (QuarticIntegerRepresentativeTree.Tree.branch 3644 (QuarticIntegerRepresentativeTree.Tree.branch 3642 (QuarticIntegerRepresentativeTree.Tree.branch 3641 (QuarticIntegerRepresentativeTree.Tree.leaf 3640 representative_3640) (QuarticIntegerRepresentativeTree.Tree.leaf 3641 representative_3641)) (QuarticIntegerRepresentativeTree.Tree.branch 3643 (QuarticIntegerRepresentativeTree.Tree.leaf 3642 representative_3642) (QuarticIntegerRepresentativeTree.Tree.leaf 3643 representative_3643))) (QuarticIntegerRepresentativeTree.Tree.branch 3646 (QuarticIntegerRepresentativeTree.Tree.branch 3645 (QuarticIntegerRepresentativeTree.Tree.leaf 3644 representative_3644) (QuarticIntegerRepresentativeTree.Tree.leaf 3645 representative_3645)) (QuarticIntegerRepresentativeTree.Tree.branch 3647 (QuarticIntegerRepresentativeTree.Tree.leaf 3646 representative_3646) (QuarticIntegerRepresentativeTree.Tree.leaf 3647 representative_3647)))))))
theorem accepted_056 : All validRep tree_056 := ⟨⟨⟨⟨⟨⟨coefficient_3584,coefficient_3585⟩,⟨coefficient_3586,coefficient_3587⟩⟩,⟨⟨coefficient_3588,coefficient_3589⟩,⟨coefficient_3590,coefficient_3591⟩⟩⟩,⟨⟨⟨coefficient_3592,coefficient_3593⟩,⟨coefficient_3594,coefficient_3595⟩⟩,⟨⟨coefficient_3596,coefficient_3597⟩,⟨coefficient_3598,coefficient_3599⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3600,coefficient_3601⟩,⟨coefficient_3602,coefficient_3603⟩⟩,⟨⟨coefficient_3604,coefficient_3605⟩,⟨coefficient_3606,coefficient_3607⟩⟩⟩,⟨⟨⟨coefficient_3608,coefficient_3609⟩,⟨coefficient_3610,coefficient_3611⟩⟩,⟨⟨coefficient_3612,coefficient_3613⟩,⟨coefficient_3614,coefficient_3615⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3616,coefficient_3617⟩,⟨coefficient_3618,coefficient_3619⟩⟩,⟨⟨coefficient_3620,coefficient_3621⟩,⟨coefficient_3622,coefficient_3623⟩⟩⟩,⟨⟨⟨coefficient_3624,coefficient_3625⟩,⟨coefficient_3626,coefficient_3627⟩⟩,⟨⟨coefficient_3628,coefficient_3629⟩,⟨coefficient_3630,coefficient_3631⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3632,coefficient_3633⟩,⟨coefficient_3634,coefficient_3635⟩⟩,⟨⟨coefficient_3636,coefficient_3637⟩,⟨coefficient_3638,coefficient_3639⟩⟩⟩,⟨⟨⟨coefficient_3640,coefficient_3641⟩,⟨coefficient_3642,coefficient_3643⟩⟩,⟨⟨coefficient_3644,coefficient_3645⟩,⟨coefficient_3646,coefficient_3647⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

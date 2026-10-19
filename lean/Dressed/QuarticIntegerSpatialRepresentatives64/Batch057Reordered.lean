import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3648 : Rep := ⟨![0,18,12,39],462⟩
def representative_3649 : Rep := ⟨![0,18,12,41],462⟩
def representative_3650 : Rep := ⟨![0,18,12,46],462⟩
def representative_3651 : Rep := ⟨![0,18,12,47],462⟩
def representative_3652 : Rep := ⟨![0,18,12,49],462⟩
def representative_3653 : Rep := ⟨![0,18,12,54],462⟩
def representative_3654 : Rep := ⟨![0,18,12,55],462⟩
def representative_3655 : Rep := ⟨![0,18,12,62],462⟩
def representative_3656 : Rep := ⟨![0,18,12,63],462⟩
def representative_3657 : Rep := ⟨![0,18,13,31],462⟩
def representative_3658 : Rep := ⟨![0,18,13,35],462⟩
def representative_3659 : Rep := ⟨![0,18,13,39],462⟩
def representative_3660 : Rep := ⟨![0,18,13,41],462⟩
def representative_3661 : Rep := ⟨![0,18,13,43],462⟩
def representative_3662 : Rep := ⟨![0,18,27,45],462⟩
def representative_3663 : Rep := ⟨![0,18,27,46],462⟩
def representative_3664 : Rep := ⟨![0,18,27,47],462⟩
def representative_3665 : Rep := ⟨![0,18,27,54],462⟩
def representative_3666 : Rep := ⟨![0,18,27,55],462⟩
def representative_3667 : Rep := ⟨![0,18,27,63],462⟩
def representative_3668 : Rep := ⟨![0,18,28,46],462⟩
def representative_3669 : Rep := ⟨![0,18,28,47],462⟩
def representative_3670 : Rep := ⟨![0,18,28,54],462⟩
def representative_3671 : Rep := ⟨![0,18,28,55],462⟩
def representative_3672 : Rep := ⟨![0,18,28,62],462⟩
def representative_3673 : Rep := ⟨![0,18,29,43],462⟩
def representative_3674 : Rep := ⟨![0,18,29,47],462⟩
def representative_3675 : Rep := ⟨![0,18,29,51],462⟩
def representative_3676 : Rep := ⟨![0,18,29,59],462⟩
def representative_3677 : Rep := ⟨![0,18,30,44],462⟩
def representative_3678 : Rep := ⟨![0,18,30,51],462⟩
def representative_3679 : Rep := ⟨![0,18,30,52],462⟩
def representative_3680 : Rep := ⟨![0,18,30,59],462⟩
def representative_3681 : Rep := ⟨![0,18,30,60],462⟩
def representative_3682 : Rep := ⟨![0,18,31,44],462⟩
def representative_3683 : Rep := ⟨![0,18,31,52],462⟩
def representative_3684 : Rep := ⟨![0,18,31,59],462⟩
def representative_3685 : Rep := ⟨![0,18,36,54],462⟩
def representative_3686 : Rep := ⟨![0,18,38,52],462⟩
def representative_3687 : Rep := ⟨![0,19,1,20],462⟩
def representative_3688 : Rep := ⟨![0,19,1,21],462⟩
def representative_3689 : Rep := ⟨![0,19,1,22],462⟩
def representative_3690 : Rep := ⟨![0,19,1,27],462⟩
def representative_3691 : Rep := ⟨![0,19,1,28],462⟩
def representative_3692 : Rep := ⟨![0,19,1,29],462⟩
def representative_3693 : Rep := ⟨![0,19,1,30],462⟩
def representative_3694 : Rep := ⟨![0,19,1,31],462⟩
def representative_3695 : Rep := ⟨![0,19,1,35],462⟩
def representative_3696 : Rep := ⟨![0,19,1,36],462⟩
def representative_3697 : Rep := ⟨![0,19,1,37],462⟩
def representative_3698 : Rep := ⟨![0,19,1,38],462⟩
def representative_3699 : Rep := ⟨![0,19,1,39],462⟩
def representative_3700 : Rep := ⟨![0,19,1,43],462⟩
def representative_3701 : Rep := ⟨![0,19,1,44],462⟩
def representative_3702 : Rep := ⟨![0,19,1,45],462⟩
def representative_3703 : Rep := ⟨![0,19,1,46],462⟩
def representative_3704 : Rep := ⟨![0,19,1,47],462⟩
def representative_3705 : Rep := ⟨![0,19,1,52],462⟩
def representative_3706 : Rep := ⟨![0,19,1,53],462⟩
def representative_3707 : Rep := ⟨![0,19,1,54],462⟩
def representative_3708 : Rep := ⟨![0,19,2,21],462⟩
def representative_3709 : Rep := ⟨![0,19,2,22],462⟩
def representative_3710 : Rep := ⟨![0,19,2,23],462⟩
def representative_3711 : Rep := ⟨![0,19,2,24],462⟩
theorem coefficient_3648 : validRep representative_3648 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3648)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3649 : validRep representative_3649 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3649)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3650 : validRep representative_3650 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3650)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3651 : validRep representative_3651 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3651)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3652 : validRep representative_3652 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3652)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3653 : validRep representative_3653 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3653)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3654 : validRep representative_3654 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3654)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3655 : validRep representative_3655 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3655)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3656 : validRep representative_3656 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3656)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3657 : validRep representative_3657 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3657)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3658 : validRep representative_3658 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3658)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3659 : validRep representative_3659 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3659)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3660 : validRep representative_3660 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3660)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3661 : validRep representative_3661 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3661)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3662 : validRep representative_3662 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3662)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3663 : validRep representative_3663 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3663)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3664 : validRep representative_3664 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3664)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3665 : validRep representative_3665 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3665)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3666 : validRep representative_3666 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3666)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3667 : validRep representative_3667 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3667)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3668 : validRep representative_3668 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3668)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3669 : validRep representative_3669 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3669)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3670 : validRep representative_3670 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3670)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3671 : validRep representative_3671 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3671)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3672 : validRep representative_3672 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3672)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3673 : validRep representative_3673 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3673)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3674 : validRep representative_3674 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3674)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3675 : validRep representative_3675 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3675)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3676 : validRep representative_3676 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3676)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3677 : validRep representative_3677 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3677)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3678 : validRep representative_3678 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3678)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3679 : validRep representative_3679 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3679)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3680 : validRep representative_3680 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3680)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3681 : validRep representative_3681 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3681)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3682 : validRep representative_3682 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3682)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3683 : validRep representative_3683 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3683)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3684 : validRep representative_3684 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3684)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3685 : validRep representative_3685 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3685)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3686 : validRep representative_3686 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3686)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3687 : validRep representative_3687 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3687)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3688 : validRep representative_3688 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3688)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3689 : validRep representative_3689 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3689)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3690 : validRep representative_3690 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3690)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3691 : validRep representative_3691 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3691)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3692 : validRep representative_3692 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3692)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3693 : validRep representative_3693 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3693)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3694 : validRep representative_3694 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3694)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3695 : validRep representative_3695 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3695)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3696 : validRep representative_3696 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3696)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3697 : validRep representative_3697 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3697)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3698 : validRep representative_3698 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3698)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3699 : validRep representative_3699 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3699)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3700 : validRep representative_3700 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3700)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3701 : validRep representative_3701 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3701)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3702 : validRep representative_3702 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3702)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3703 : validRep representative_3703 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3703)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3704 : validRep representative_3704 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3704)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3705 : validRep representative_3705 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3705)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3706 : validRep representative_3706 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3706)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3707 : validRep representative_3707 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3707)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3708 : validRep representative_3708 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3708)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3709 : validRep representative_3709 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3709)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3710 : validRep representative_3710 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3710)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3711 : validRep representative_3711 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3711)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_057 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3680 (QuarticIntegerRepresentativeTree.Tree.branch 3664 (QuarticIntegerRepresentativeTree.Tree.branch 3656 (QuarticIntegerRepresentativeTree.Tree.branch 3652 (QuarticIntegerRepresentativeTree.Tree.branch 3650 (QuarticIntegerRepresentativeTree.Tree.branch 3649 (QuarticIntegerRepresentativeTree.Tree.leaf 3648 representative_3648) (QuarticIntegerRepresentativeTree.Tree.leaf 3649 representative_3649)) (QuarticIntegerRepresentativeTree.Tree.branch 3651 (QuarticIntegerRepresentativeTree.Tree.leaf 3650 representative_3650) (QuarticIntegerRepresentativeTree.Tree.leaf 3651 representative_3651))) (QuarticIntegerRepresentativeTree.Tree.branch 3654 (QuarticIntegerRepresentativeTree.Tree.branch 3653 (QuarticIntegerRepresentativeTree.Tree.leaf 3652 representative_3652) (QuarticIntegerRepresentativeTree.Tree.leaf 3653 representative_3653)) (QuarticIntegerRepresentativeTree.Tree.branch 3655 (QuarticIntegerRepresentativeTree.Tree.leaf 3654 representative_3654) (QuarticIntegerRepresentativeTree.Tree.leaf 3655 representative_3655)))) (QuarticIntegerRepresentativeTree.Tree.branch 3660 (QuarticIntegerRepresentativeTree.Tree.branch 3658 (QuarticIntegerRepresentativeTree.Tree.branch 3657 (QuarticIntegerRepresentativeTree.Tree.leaf 3656 representative_3656) (QuarticIntegerRepresentativeTree.Tree.leaf 3657 representative_3657)) (QuarticIntegerRepresentativeTree.Tree.branch 3659 (QuarticIntegerRepresentativeTree.Tree.leaf 3658 representative_3658) (QuarticIntegerRepresentativeTree.Tree.leaf 3659 representative_3659))) (QuarticIntegerRepresentativeTree.Tree.branch 3662 (QuarticIntegerRepresentativeTree.Tree.branch 3661 (QuarticIntegerRepresentativeTree.Tree.leaf 3660 representative_3660) (QuarticIntegerRepresentativeTree.Tree.leaf 3661 representative_3661)) (QuarticIntegerRepresentativeTree.Tree.branch 3663 (QuarticIntegerRepresentativeTree.Tree.leaf 3662 representative_3662) (QuarticIntegerRepresentativeTree.Tree.leaf 3663 representative_3663))))) (QuarticIntegerRepresentativeTree.Tree.branch 3672 (QuarticIntegerRepresentativeTree.Tree.branch 3668 (QuarticIntegerRepresentativeTree.Tree.branch 3666 (QuarticIntegerRepresentativeTree.Tree.branch 3665 (QuarticIntegerRepresentativeTree.Tree.leaf 3664 representative_3664) (QuarticIntegerRepresentativeTree.Tree.leaf 3665 representative_3665)) (QuarticIntegerRepresentativeTree.Tree.branch 3667 (QuarticIntegerRepresentativeTree.Tree.leaf 3666 representative_3666) (QuarticIntegerRepresentativeTree.Tree.leaf 3667 representative_3667))) (QuarticIntegerRepresentativeTree.Tree.branch 3670 (QuarticIntegerRepresentativeTree.Tree.branch 3669 (QuarticIntegerRepresentativeTree.Tree.leaf 3668 representative_3668) (QuarticIntegerRepresentativeTree.Tree.leaf 3669 representative_3669)) (QuarticIntegerRepresentativeTree.Tree.branch 3671 (QuarticIntegerRepresentativeTree.Tree.leaf 3670 representative_3670) (QuarticIntegerRepresentativeTree.Tree.leaf 3671 representative_3671)))) (QuarticIntegerRepresentativeTree.Tree.branch 3676 (QuarticIntegerRepresentativeTree.Tree.branch 3674 (QuarticIntegerRepresentativeTree.Tree.branch 3673 (QuarticIntegerRepresentativeTree.Tree.leaf 3672 representative_3672) (QuarticIntegerRepresentativeTree.Tree.leaf 3673 representative_3673)) (QuarticIntegerRepresentativeTree.Tree.branch 3675 (QuarticIntegerRepresentativeTree.Tree.leaf 3674 representative_3674) (QuarticIntegerRepresentativeTree.Tree.leaf 3675 representative_3675))) (QuarticIntegerRepresentativeTree.Tree.branch 3678 (QuarticIntegerRepresentativeTree.Tree.branch 3677 (QuarticIntegerRepresentativeTree.Tree.leaf 3676 representative_3676) (QuarticIntegerRepresentativeTree.Tree.leaf 3677 representative_3677)) (QuarticIntegerRepresentativeTree.Tree.branch 3679 (QuarticIntegerRepresentativeTree.Tree.leaf 3678 representative_3678) (QuarticIntegerRepresentativeTree.Tree.leaf 3679 representative_3679)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3696 (QuarticIntegerRepresentativeTree.Tree.branch 3688 (QuarticIntegerRepresentativeTree.Tree.branch 3684 (QuarticIntegerRepresentativeTree.Tree.branch 3682 (QuarticIntegerRepresentativeTree.Tree.branch 3681 (QuarticIntegerRepresentativeTree.Tree.leaf 3680 representative_3680) (QuarticIntegerRepresentativeTree.Tree.leaf 3681 representative_3681)) (QuarticIntegerRepresentativeTree.Tree.branch 3683 (QuarticIntegerRepresentativeTree.Tree.leaf 3682 representative_3682) (QuarticIntegerRepresentativeTree.Tree.leaf 3683 representative_3683))) (QuarticIntegerRepresentativeTree.Tree.branch 3686 (QuarticIntegerRepresentativeTree.Tree.branch 3685 (QuarticIntegerRepresentativeTree.Tree.leaf 3684 representative_3684) (QuarticIntegerRepresentativeTree.Tree.leaf 3685 representative_3685)) (QuarticIntegerRepresentativeTree.Tree.branch 3687 (QuarticIntegerRepresentativeTree.Tree.leaf 3686 representative_3686) (QuarticIntegerRepresentativeTree.Tree.leaf 3687 representative_3687)))) (QuarticIntegerRepresentativeTree.Tree.branch 3692 (QuarticIntegerRepresentativeTree.Tree.branch 3690 (QuarticIntegerRepresentativeTree.Tree.branch 3689 (QuarticIntegerRepresentativeTree.Tree.leaf 3688 representative_3688) (QuarticIntegerRepresentativeTree.Tree.leaf 3689 representative_3689)) (QuarticIntegerRepresentativeTree.Tree.branch 3691 (QuarticIntegerRepresentativeTree.Tree.leaf 3690 representative_3690) (QuarticIntegerRepresentativeTree.Tree.leaf 3691 representative_3691))) (QuarticIntegerRepresentativeTree.Tree.branch 3694 (QuarticIntegerRepresentativeTree.Tree.branch 3693 (QuarticIntegerRepresentativeTree.Tree.leaf 3692 representative_3692) (QuarticIntegerRepresentativeTree.Tree.leaf 3693 representative_3693)) (QuarticIntegerRepresentativeTree.Tree.branch 3695 (QuarticIntegerRepresentativeTree.Tree.leaf 3694 representative_3694) (QuarticIntegerRepresentativeTree.Tree.leaf 3695 representative_3695))))) (QuarticIntegerRepresentativeTree.Tree.branch 3704 (QuarticIntegerRepresentativeTree.Tree.branch 3700 (QuarticIntegerRepresentativeTree.Tree.branch 3698 (QuarticIntegerRepresentativeTree.Tree.branch 3697 (QuarticIntegerRepresentativeTree.Tree.leaf 3696 representative_3696) (QuarticIntegerRepresentativeTree.Tree.leaf 3697 representative_3697)) (QuarticIntegerRepresentativeTree.Tree.branch 3699 (QuarticIntegerRepresentativeTree.Tree.leaf 3698 representative_3698) (QuarticIntegerRepresentativeTree.Tree.leaf 3699 representative_3699))) (QuarticIntegerRepresentativeTree.Tree.branch 3702 (QuarticIntegerRepresentativeTree.Tree.branch 3701 (QuarticIntegerRepresentativeTree.Tree.leaf 3700 representative_3700) (QuarticIntegerRepresentativeTree.Tree.leaf 3701 representative_3701)) (QuarticIntegerRepresentativeTree.Tree.branch 3703 (QuarticIntegerRepresentativeTree.Tree.leaf 3702 representative_3702) (QuarticIntegerRepresentativeTree.Tree.leaf 3703 representative_3703)))) (QuarticIntegerRepresentativeTree.Tree.branch 3708 (QuarticIntegerRepresentativeTree.Tree.branch 3706 (QuarticIntegerRepresentativeTree.Tree.branch 3705 (QuarticIntegerRepresentativeTree.Tree.leaf 3704 representative_3704) (QuarticIntegerRepresentativeTree.Tree.leaf 3705 representative_3705)) (QuarticIntegerRepresentativeTree.Tree.branch 3707 (QuarticIntegerRepresentativeTree.Tree.leaf 3706 representative_3706) (QuarticIntegerRepresentativeTree.Tree.leaf 3707 representative_3707))) (QuarticIntegerRepresentativeTree.Tree.branch 3710 (QuarticIntegerRepresentativeTree.Tree.branch 3709 (QuarticIntegerRepresentativeTree.Tree.leaf 3708 representative_3708) (QuarticIntegerRepresentativeTree.Tree.leaf 3709 representative_3709)) (QuarticIntegerRepresentativeTree.Tree.branch 3711 (QuarticIntegerRepresentativeTree.Tree.leaf 3710 representative_3710) (QuarticIntegerRepresentativeTree.Tree.leaf 3711 representative_3711)))))))
theorem accepted_057 : All validRep tree_057 := ⟨⟨⟨⟨⟨⟨coefficient_3648,coefficient_3649⟩,⟨coefficient_3650,coefficient_3651⟩⟩,⟨⟨coefficient_3652,coefficient_3653⟩,⟨coefficient_3654,coefficient_3655⟩⟩⟩,⟨⟨⟨coefficient_3656,coefficient_3657⟩,⟨coefficient_3658,coefficient_3659⟩⟩,⟨⟨coefficient_3660,coefficient_3661⟩,⟨coefficient_3662,coefficient_3663⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3664,coefficient_3665⟩,⟨coefficient_3666,coefficient_3667⟩⟩,⟨⟨coefficient_3668,coefficient_3669⟩,⟨coefficient_3670,coefficient_3671⟩⟩⟩,⟨⟨⟨coefficient_3672,coefficient_3673⟩,⟨coefficient_3674,coefficient_3675⟩⟩,⟨⟨coefficient_3676,coefficient_3677⟩,⟨coefficient_3678,coefficient_3679⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3680,coefficient_3681⟩,⟨coefficient_3682,coefficient_3683⟩⟩,⟨⟨coefficient_3684,coefficient_3685⟩,⟨coefficient_3686,coefficient_3687⟩⟩⟩,⟨⟨⟨coefficient_3688,coefficient_3689⟩,⟨coefficient_3690,coefficient_3691⟩⟩,⟨⟨coefficient_3692,coefficient_3693⟩,⟨coefficient_3694,coefficient_3695⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3696,coefficient_3697⟩,⟨coefficient_3698,coefficient_3699⟩⟩,⟨⟨coefficient_3700,coefficient_3701⟩,⟨coefficient_3702,coefficient_3703⟩⟩⟩,⟨⟨⟨coefficient_3704,coefficient_3705⟩,⟨coefficient_3706,coefficient_3707⟩⟩,⟨⟨coefficient_3708,coefficient_3709⟩,⟨coefficient_3710,coefficient_3711⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

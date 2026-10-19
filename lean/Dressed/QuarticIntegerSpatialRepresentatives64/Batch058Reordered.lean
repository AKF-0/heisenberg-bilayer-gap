import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3712 : Rep := ⟨![0,19,2,28],462⟩
def representative_3713 : Rep := ⟨![0,19,2,29],462⟩
def representative_3714 : Rep := ⟨![0,19,2,30],462⟩
def representative_3715 : Rep := ⟨![0,19,2,31],462⟩
def representative_3716 : Rep := ⟨![0,19,2,32],462⟩
def representative_3717 : Rep := ⟨![0,19,2,36],462⟩
def representative_3718 : Rep := ⟨![0,19,2,37],462⟩
def representative_3719 : Rep := ⟨![0,19,2,38],462⟩
def representative_3720 : Rep := ⟨![0,19,2,39],462⟩
def representative_3721 : Rep := ⟨![0,19,2,40],462⟩
def representative_3722 : Rep := ⟨![0,19,2,44],462⟩
def representative_3723 : Rep := ⟨![0,19,2,45],462⟩
def representative_3724 : Rep := ⟨![0,19,2,46],462⟩
def representative_3725 : Rep := ⟨![0,19,2,47],462⟩
def representative_3726 : Rep := ⟨![0,19,2,53],462⟩
def representative_3727 : Rep := ⟨![0,19,2,54],462⟩
def representative_3728 : Rep := ⟨![0,19,2,55],462⟩
def representative_3729 : Rep := ⟨![0,19,3,16],462⟩
def representative_3730 : Rep := ⟨![0,19,3,22],462⟩
def representative_3731 : Rep := ⟨![0,19,3,23],462⟩
def representative_3732 : Rep := ⟨![0,19,3,24],462⟩
def representative_3733 : Rep := ⟨![0,19,3,30],462⟩
def representative_3734 : Rep := ⟨![0,19,3,31],462⟩
def representative_3735 : Rep := ⟨![0,19,3,32],462⟩
def representative_3736 : Rep := ⟨![0,19,3,33],462⟩
def representative_3737 : Rep := ⟨![0,19,3,37],462⟩
def representative_3738 : Rep := ⟨![0,19,3,38],462⟩
def representative_3739 : Rep := ⟨![0,19,3,39],462⟩
def representative_3740 : Rep := ⟨![0,19,3,40],462⟩
def representative_3741 : Rep := ⟨![0,19,3,41],462⟩
def representative_3742 : Rep := ⟨![0,19,3,45],462⟩
def representative_3743 : Rep := ⟨![0,19,3,46],462⟩
def representative_3744 : Rep := ⟨![0,19,3,47],462⟩
def representative_3745 : Rep := ⟨![0,19,3,48],462⟩
def representative_3746 : Rep := ⟨![0,19,3,54],462⟩
def representative_3747 : Rep := ⟨![0,19,3,55],462⟩
def representative_3748 : Rep := ⟨![0,19,4,23],462⟩
def representative_3749 : Rep := ⟨![0,19,4,24],462⟩
def representative_3750 : Rep := ⟨![0,19,4,25],462⟩
def representative_3751 : Rep := ⟨![0,19,4,26],462⟩
def representative_3752 : Rep := ⟨![0,19,4,30],462⟩
def representative_3753 : Rep := ⟨![0,19,4,31],462⟩
def representative_3754 : Rep := ⟨![0,19,4,32],462⟩
def representative_3755 : Rep := ⟨![0,19,4,33],462⟩
def representative_3756 : Rep := ⟨![0,19,4,34],462⟩
def representative_3757 : Rep := ⟨![0,19,4,38],462⟩
def representative_3758 : Rep := ⟨![0,19,4,39],462⟩
def representative_3759 : Rep := ⟨![0,19,4,40],462⟩
def representative_3760 : Rep := ⟨![0,19,4,41],462⟩
def representative_3761 : Rep := ⟨![0,19,4,42],462⟩
def representative_3762 : Rep := ⟨![0,19,4,46],462⟩
def representative_3763 : Rep := ⟨![0,19,4,47],462⟩
def representative_3764 : Rep := ⟨![0,19,4,48],462⟩
def representative_3765 : Rep := ⟨![0,19,4,49],462⟩
def representative_3766 : Rep := ⟨![0,19,4,55],462⟩
def representative_3767 : Rep := ⟨![0,19,5,24],462⟩
def representative_3768 : Rep := ⟨![0,19,5,25],462⟩
def representative_3769 : Rep := ⟨![0,19,5,26],462⟩
def representative_3770 : Rep := ⟨![0,19,5,31],462⟩
def representative_3771 : Rep := ⟨![0,19,5,32],462⟩
def representative_3772 : Rep := ⟨![0,19,5,33],462⟩
def representative_3773 : Rep := ⟨![0,19,5,34],462⟩
def representative_3774 : Rep := ⟨![0,19,5,35],462⟩
def representative_3775 : Rep := ⟨![0,19,5,39],462⟩
theorem coefficient_3712 : validRep representative_3712 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3712)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3713 : validRep representative_3713 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3713)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3714 : validRep representative_3714 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3714)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3715 : validRep representative_3715 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3715)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3716 : validRep representative_3716 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3716)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3717 : validRep representative_3717 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3717)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3718 : validRep representative_3718 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3718)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3719 : validRep representative_3719 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3719)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3720 : validRep representative_3720 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3720)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3721 : validRep representative_3721 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3721)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3722 : validRep representative_3722 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3722)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3723 : validRep representative_3723 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3723)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3724 : validRep representative_3724 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3724)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3725 : validRep representative_3725 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3725)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3726 : validRep representative_3726 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3726)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3727 : validRep representative_3727 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3727)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3728 : validRep representative_3728 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3728)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3729 : validRep representative_3729 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3729)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3730 : validRep representative_3730 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3730)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3731 : validRep representative_3731 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3731)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3732 : validRep representative_3732 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3732)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3733 : validRep representative_3733 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3733)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3734 : validRep representative_3734 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3734)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3735 : validRep representative_3735 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3735)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3736 : validRep representative_3736 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3736)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3737 : validRep representative_3737 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3737)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3738 : validRep representative_3738 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3738)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3739 : validRep representative_3739 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3739)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3740 : validRep representative_3740 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3740)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3741 : validRep representative_3741 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3741)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3742 : validRep representative_3742 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3742)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3743 : validRep representative_3743 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3743)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3744 : validRep representative_3744 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3744)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3745 : validRep representative_3745 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3745)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3746 : validRep representative_3746 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3746)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3747 : validRep representative_3747 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3747)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3748 : validRep representative_3748 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3748)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3749 : validRep representative_3749 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3749)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3750 : validRep representative_3750 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3750)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3751 : validRep representative_3751 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3751)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3752 : validRep representative_3752 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3752)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3753 : validRep representative_3753 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3753)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3754 : validRep representative_3754 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3754)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3755 : validRep representative_3755 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3755)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3756 : validRep representative_3756 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3756)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3757 : validRep representative_3757 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3757)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3758 : validRep representative_3758 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3758)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3759 : validRep representative_3759 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3759)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3760 : validRep representative_3760 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3760)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3761 : validRep representative_3761 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3761)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3762 : validRep representative_3762 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3762)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3763 : validRep representative_3763 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3763)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3764 : validRep representative_3764 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3764)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3765 : validRep representative_3765 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3765)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3766 : validRep representative_3766 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3766)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3767 : validRep representative_3767 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3767)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3768 : validRep representative_3768 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3768)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3769 : validRep representative_3769 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3769)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3770 : validRep representative_3770 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3770)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3771 : validRep representative_3771 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3771)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3772 : validRep representative_3772 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3772)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3773 : validRep representative_3773 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3773)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3774 : validRep representative_3774 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3774)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3775 : validRep representative_3775 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3775)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_058 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3744 (QuarticIntegerRepresentativeTree.Tree.branch 3728 (QuarticIntegerRepresentativeTree.Tree.branch 3720 (QuarticIntegerRepresentativeTree.Tree.branch 3716 (QuarticIntegerRepresentativeTree.Tree.branch 3714 (QuarticIntegerRepresentativeTree.Tree.branch 3713 (QuarticIntegerRepresentativeTree.Tree.leaf 3712 representative_3712) (QuarticIntegerRepresentativeTree.Tree.leaf 3713 representative_3713)) (QuarticIntegerRepresentativeTree.Tree.branch 3715 (QuarticIntegerRepresentativeTree.Tree.leaf 3714 representative_3714) (QuarticIntegerRepresentativeTree.Tree.leaf 3715 representative_3715))) (QuarticIntegerRepresentativeTree.Tree.branch 3718 (QuarticIntegerRepresentativeTree.Tree.branch 3717 (QuarticIntegerRepresentativeTree.Tree.leaf 3716 representative_3716) (QuarticIntegerRepresentativeTree.Tree.leaf 3717 representative_3717)) (QuarticIntegerRepresentativeTree.Tree.branch 3719 (QuarticIntegerRepresentativeTree.Tree.leaf 3718 representative_3718) (QuarticIntegerRepresentativeTree.Tree.leaf 3719 representative_3719)))) (QuarticIntegerRepresentativeTree.Tree.branch 3724 (QuarticIntegerRepresentativeTree.Tree.branch 3722 (QuarticIntegerRepresentativeTree.Tree.branch 3721 (QuarticIntegerRepresentativeTree.Tree.leaf 3720 representative_3720) (QuarticIntegerRepresentativeTree.Tree.leaf 3721 representative_3721)) (QuarticIntegerRepresentativeTree.Tree.branch 3723 (QuarticIntegerRepresentativeTree.Tree.leaf 3722 representative_3722) (QuarticIntegerRepresentativeTree.Tree.leaf 3723 representative_3723))) (QuarticIntegerRepresentativeTree.Tree.branch 3726 (QuarticIntegerRepresentativeTree.Tree.branch 3725 (QuarticIntegerRepresentativeTree.Tree.leaf 3724 representative_3724) (QuarticIntegerRepresentativeTree.Tree.leaf 3725 representative_3725)) (QuarticIntegerRepresentativeTree.Tree.branch 3727 (QuarticIntegerRepresentativeTree.Tree.leaf 3726 representative_3726) (QuarticIntegerRepresentativeTree.Tree.leaf 3727 representative_3727))))) (QuarticIntegerRepresentativeTree.Tree.branch 3736 (QuarticIntegerRepresentativeTree.Tree.branch 3732 (QuarticIntegerRepresentativeTree.Tree.branch 3730 (QuarticIntegerRepresentativeTree.Tree.branch 3729 (QuarticIntegerRepresentativeTree.Tree.leaf 3728 representative_3728) (QuarticIntegerRepresentativeTree.Tree.leaf 3729 representative_3729)) (QuarticIntegerRepresentativeTree.Tree.branch 3731 (QuarticIntegerRepresentativeTree.Tree.leaf 3730 representative_3730) (QuarticIntegerRepresentativeTree.Tree.leaf 3731 representative_3731))) (QuarticIntegerRepresentativeTree.Tree.branch 3734 (QuarticIntegerRepresentativeTree.Tree.branch 3733 (QuarticIntegerRepresentativeTree.Tree.leaf 3732 representative_3732) (QuarticIntegerRepresentativeTree.Tree.leaf 3733 representative_3733)) (QuarticIntegerRepresentativeTree.Tree.branch 3735 (QuarticIntegerRepresentativeTree.Tree.leaf 3734 representative_3734) (QuarticIntegerRepresentativeTree.Tree.leaf 3735 representative_3735)))) (QuarticIntegerRepresentativeTree.Tree.branch 3740 (QuarticIntegerRepresentativeTree.Tree.branch 3738 (QuarticIntegerRepresentativeTree.Tree.branch 3737 (QuarticIntegerRepresentativeTree.Tree.leaf 3736 representative_3736) (QuarticIntegerRepresentativeTree.Tree.leaf 3737 representative_3737)) (QuarticIntegerRepresentativeTree.Tree.branch 3739 (QuarticIntegerRepresentativeTree.Tree.leaf 3738 representative_3738) (QuarticIntegerRepresentativeTree.Tree.leaf 3739 representative_3739))) (QuarticIntegerRepresentativeTree.Tree.branch 3742 (QuarticIntegerRepresentativeTree.Tree.branch 3741 (QuarticIntegerRepresentativeTree.Tree.leaf 3740 representative_3740) (QuarticIntegerRepresentativeTree.Tree.leaf 3741 representative_3741)) (QuarticIntegerRepresentativeTree.Tree.branch 3743 (QuarticIntegerRepresentativeTree.Tree.leaf 3742 representative_3742) (QuarticIntegerRepresentativeTree.Tree.leaf 3743 representative_3743)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3760 (QuarticIntegerRepresentativeTree.Tree.branch 3752 (QuarticIntegerRepresentativeTree.Tree.branch 3748 (QuarticIntegerRepresentativeTree.Tree.branch 3746 (QuarticIntegerRepresentativeTree.Tree.branch 3745 (QuarticIntegerRepresentativeTree.Tree.leaf 3744 representative_3744) (QuarticIntegerRepresentativeTree.Tree.leaf 3745 representative_3745)) (QuarticIntegerRepresentativeTree.Tree.branch 3747 (QuarticIntegerRepresentativeTree.Tree.leaf 3746 representative_3746) (QuarticIntegerRepresentativeTree.Tree.leaf 3747 representative_3747))) (QuarticIntegerRepresentativeTree.Tree.branch 3750 (QuarticIntegerRepresentativeTree.Tree.branch 3749 (QuarticIntegerRepresentativeTree.Tree.leaf 3748 representative_3748) (QuarticIntegerRepresentativeTree.Tree.leaf 3749 representative_3749)) (QuarticIntegerRepresentativeTree.Tree.branch 3751 (QuarticIntegerRepresentativeTree.Tree.leaf 3750 representative_3750) (QuarticIntegerRepresentativeTree.Tree.leaf 3751 representative_3751)))) (QuarticIntegerRepresentativeTree.Tree.branch 3756 (QuarticIntegerRepresentativeTree.Tree.branch 3754 (QuarticIntegerRepresentativeTree.Tree.branch 3753 (QuarticIntegerRepresentativeTree.Tree.leaf 3752 representative_3752) (QuarticIntegerRepresentativeTree.Tree.leaf 3753 representative_3753)) (QuarticIntegerRepresentativeTree.Tree.branch 3755 (QuarticIntegerRepresentativeTree.Tree.leaf 3754 representative_3754) (QuarticIntegerRepresentativeTree.Tree.leaf 3755 representative_3755))) (QuarticIntegerRepresentativeTree.Tree.branch 3758 (QuarticIntegerRepresentativeTree.Tree.branch 3757 (QuarticIntegerRepresentativeTree.Tree.leaf 3756 representative_3756) (QuarticIntegerRepresentativeTree.Tree.leaf 3757 representative_3757)) (QuarticIntegerRepresentativeTree.Tree.branch 3759 (QuarticIntegerRepresentativeTree.Tree.leaf 3758 representative_3758) (QuarticIntegerRepresentativeTree.Tree.leaf 3759 representative_3759))))) (QuarticIntegerRepresentativeTree.Tree.branch 3768 (QuarticIntegerRepresentativeTree.Tree.branch 3764 (QuarticIntegerRepresentativeTree.Tree.branch 3762 (QuarticIntegerRepresentativeTree.Tree.branch 3761 (QuarticIntegerRepresentativeTree.Tree.leaf 3760 representative_3760) (QuarticIntegerRepresentativeTree.Tree.leaf 3761 representative_3761)) (QuarticIntegerRepresentativeTree.Tree.branch 3763 (QuarticIntegerRepresentativeTree.Tree.leaf 3762 representative_3762) (QuarticIntegerRepresentativeTree.Tree.leaf 3763 representative_3763))) (QuarticIntegerRepresentativeTree.Tree.branch 3766 (QuarticIntegerRepresentativeTree.Tree.branch 3765 (QuarticIntegerRepresentativeTree.Tree.leaf 3764 representative_3764) (QuarticIntegerRepresentativeTree.Tree.leaf 3765 representative_3765)) (QuarticIntegerRepresentativeTree.Tree.branch 3767 (QuarticIntegerRepresentativeTree.Tree.leaf 3766 representative_3766) (QuarticIntegerRepresentativeTree.Tree.leaf 3767 representative_3767)))) (QuarticIntegerRepresentativeTree.Tree.branch 3772 (QuarticIntegerRepresentativeTree.Tree.branch 3770 (QuarticIntegerRepresentativeTree.Tree.branch 3769 (QuarticIntegerRepresentativeTree.Tree.leaf 3768 representative_3768) (QuarticIntegerRepresentativeTree.Tree.leaf 3769 representative_3769)) (QuarticIntegerRepresentativeTree.Tree.branch 3771 (QuarticIntegerRepresentativeTree.Tree.leaf 3770 representative_3770) (QuarticIntegerRepresentativeTree.Tree.leaf 3771 representative_3771))) (QuarticIntegerRepresentativeTree.Tree.branch 3774 (QuarticIntegerRepresentativeTree.Tree.branch 3773 (QuarticIntegerRepresentativeTree.Tree.leaf 3772 representative_3772) (QuarticIntegerRepresentativeTree.Tree.leaf 3773 representative_3773)) (QuarticIntegerRepresentativeTree.Tree.branch 3775 (QuarticIntegerRepresentativeTree.Tree.leaf 3774 representative_3774) (QuarticIntegerRepresentativeTree.Tree.leaf 3775 representative_3775)))))))
theorem accepted_058 : All validRep tree_058 := ⟨⟨⟨⟨⟨⟨coefficient_3712,coefficient_3713⟩,⟨coefficient_3714,coefficient_3715⟩⟩,⟨⟨coefficient_3716,coefficient_3717⟩,⟨coefficient_3718,coefficient_3719⟩⟩⟩,⟨⟨⟨coefficient_3720,coefficient_3721⟩,⟨coefficient_3722,coefficient_3723⟩⟩,⟨⟨coefficient_3724,coefficient_3725⟩,⟨coefficient_3726,coefficient_3727⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3728,coefficient_3729⟩,⟨coefficient_3730,coefficient_3731⟩⟩,⟨⟨coefficient_3732,coefficient_3733⟩,⟨coefficient_3734,coefficient_3735⟩⟩⟩,⟨⟨⟨coefficient_3736,coefficient_3737⟩,⟨coefficient_3738,coefficient_3739⟩⟩,⟨⟨coefficient_3740,coefficient_3741⟩,⟨coefficient_3742,coefficient_3743⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3744,coefficient_3745⟩,⟨coefficient_3746,coefficient_3747⟩⟩,⟨⟨coefficient_3748,coefficient_3749⟩,⟨coefficient_3750,coefficient_3751⟩⟩⟩,⟨⟨⟨coefficient_3752,coefficient_3753⟩,⟨coefficient_3754,coefficient_3755⟩⟩,⟨⟨coefficient_3756,coefficient_3757⟩,⟨coefficient_3758,coefficient_3759⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3760,coefficient_3761⟩,⟨coefficient_3762,coefficient_3763⟩⟩,⟨⟨coefficient_3764,coefficient_3765⟩,⟨coefficient_3766,coefficient_3767⟩⟩⟩,⟨⟨⟨coefficient_3768,coefficient_3769⟩,⟨coefficient_3770,coefficient_3771⟩⟩,⟨⟨coefficient_3772,coefficient_3773⟩,⟨coefficient_3774,coefficient_3775⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

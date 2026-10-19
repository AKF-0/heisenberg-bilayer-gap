import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3776 : Rep := ⟨![0,19,5,40],462⟩
def representative_3777 : Rep := ⟨![0,19,5,41],462⟩
def representative_3778 : Rep := ⟨![0,19,5,42],462⟩
def representative_3779 : Rep := ⟨![0,19,5,43],462⟩
def representative_3780 : Rep := ⟨![0,19,5,47],462⟩
def representative_3781 : Rep := ⟨![0,19,5,49],462⟩
def representative_3782 : Rep := ⟨![0,19,5,50],462⟩
def representative_3783 : Rep := ⟨![0,19,6,25],462⟩
def representative_3784 : Rep := ⟨![0,19,6,26],462⟩
def representative_3785 : Rep := ⟨![0,19,6,27],462⟩
def representative_3786 : Rep := ⟨![0,19,6,28],462⟩
def representative_3787 : Rep := ⟨![0,19,6,32],462⟩
def representative_3788 : Rep := ⟨![0,19,6,33],462⟩
def representative_3789 : Rep := ⟨![0,19,6,34],462⟩
def representative_3790 : Rep := ⟨![0,19,6,35],462⟩
def representative_3791 : Rep := ⟨![0,19,6,36],462⟩
def representative_3792 : Rep := ⟨![0,19,6,41],462⟩
def representative_3793 : Rep := ⟨![0,19,6,42],462⟩
def representative_3794 : Rep := ⟨![0,19,6,43],462⟩
def representative_3795 : Rep := ⟨![0,19,6,44],462⟩
def representative_3796 : Rep := ⟨![0,19,6,50],462⟩
def representative_3797 : Rep := ⟨![0,19,6,51],462⟩
def representative_3798 : Rep := ⟨![0,19,7,20],462⟩
def representative_3799 : Rep := ⟨![0,19,7,25],462⟩
def representative_3800 : Rep := ⟨![0,19,7,26],462⟩
def representative_3801 : Rep := ⟨![0,19,7,27],462⟩
def representative_3802 : Rep := ⟨![0,19,7,28],462⟩
def representative_3803 : Rep := ⟨![0,19,7,29],462⟩
def representative_3804 : Rep := ⟨![0,19,7,33],462⟩
def representative_3805 : Rep := ⟨![0,19,7,34],462⟩
def representative_3806 : Rep := ⟨![0,19,7,35],462⟩
def representative_3807 : Rep := ⟨![0,19,7,36],462⟩
def representative_3808 : Rep := ⟨![0,19,7,37],462⟩
def representative_3809 : Rep := ⟨![0,19,7,41],462⟩
def representative_3810 : Rep := ⟨![0,19,7,42],462⟩
def representative_3811 : Rep := ⟨![0,19,7,43],462⟩
def representative_3812 : Rep := ⟨![0,19,7,44],462⟩
def representative_3813 : Rep := ⟨![0,19,7,45],462⟩
def representative_3814 : Rep := ⟨![0,19,7,51],462⟩
def representative_3815 : Rep := ⟨![0,19,7,52],462⟩
def representative_3816 : Rep := ⟨![0,19,8,27],462⟩
def representative_3817 : Rep := ⟨![0,19,8,28],462⟩
def representative_3818 : Rep := ⟨![0,19,8,29],462⟩
def representative_3819 : Rep := ⟨![0,19,8,35],462⟩
def representative_3820 : Rep := ⟨![0,19,8,36],462⟩
def representative_3821 : Rep := ⟨![0,19,8,37],462⟩
def representative_3822 : Rep := ⟨![0,19,8,42],462⟩
def representative_3823 : Rep := ⟨![0,19,8,43],462⟩
def representative_3824 : Rep := ⟨![0,19,8,44],462⟩
def representative_3825 : Rep := ⟨![0,19,8,45],462⟩
def representative_3826 : Rep := ⟨![0,19,8,46],462⟩
def representative_3827 : Rep := ⟨![0,19,8,51],462⟩
def representative_3828 : Rep := ⟨![0,19,8,52],462⟩
def representative_3829 : Rep := ⟨![0,19,8,53],462⟩
def representative_3830 : Rep := ⟨![0,19,8,59],462⟩
def representative_3831 : Rep := ⟨![0,19,8,60],462⟩
def representative_3832 : Rep := ⟨![0,19,8,61],462⟩
def representative_3833 : Rep := ⟨![0,19,9,28],462⟩
def representative_3834 : Rep := ⟨![0,19,9,29],462⟩
def representative_3835 : Rep := ⟨![0,19,9,30],462⟩
def representative_3836 : Rep := ⟨![0,19,9,36],462⟩
def representative_3837 : Rep := ⟨![0,19,9,37],462⟩
def representative_3838 : Rep := ⟨![0,19,9,38],462⟩
def representative_3839 : Rep := ⟨![0,19,9,39],462⟩
theorem coefficient_3776 : validRep representative_3776 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3776)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3777 : validRep representative_3777 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3777)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3778 : validRep representative_3778 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3778)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3779 : validRep representative_3779 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3779)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3780 : validRep representative_3780 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3780)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3781 : validRep representative_3781 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3781)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3782 : validRep representative_3782 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3782)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3783 : validRep representative_3783 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3783)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3784 : validRep representative_3784 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3784)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3785 : validRep representative_3785 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3785)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3786 : validRep representative_3786 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3786)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3787 : validRep representative_3787 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3787)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3788 : validRep representative_3788 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3788)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3789 : validRep representative_3789 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3789)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3790 : validRep representative_3790 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3790)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3791 : validRep representative_3791 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3791)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3792 : validRep representative_3792 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3792)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3793 : validRep representative_3793 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3793)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3794 : validRep representative_3794 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3794)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3795 : validRep representative_3795 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3795)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3796 : validRep representative_3796 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3796)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3797 : validRep representative_3797 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3797)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3798 : validRep representative_3798 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3798)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3799 : validRep representative_3799 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3799)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3800 : validRep representative_3800 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3800)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3801 : validRep representative_3801 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3801)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3802 : validRep representative_3802 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3802)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3803 : validRep representative_3803 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3803)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3804 : validRep representative_3804 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3804)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3805 : validRep representative_3805 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3805)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3806 : validRep representative_3806 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3806)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3807 : validRep representative_3807 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3807)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3808 : validRep representative_3808 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3808)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3809 : validRep representative_3809 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3809)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3810 : validRep representative_3810 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3810)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3811 : validRep representative_3811 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3811)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3812 : validRep representative_3812 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3812)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3813 : validRep representative_3813 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3813)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3814 : validRep representative_3814 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3814)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3815 : validRep representative_3815 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3815)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3816 : validRep representative_3816 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3816)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3817 : validRep representative_3817 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3817)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3818 : validRep representative_3818 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3818)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3819 : validRep representative_3819 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3819)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3820 : validRep representative_3820 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3820)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3821 : validRep representative_3821 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3821)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3822 : validRep representative_3822 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3822)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3823 : validRep representative_3823 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3823)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3824 : validRep representative_3824 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3824)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3825 : validRep representative_3825 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3825)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3826 : validRep representative_3826 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3826)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3827 : validRep representative_3827 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3827)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3828 : validRep representative_3828 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3828)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3829 : validRep representative_3829 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3829)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3830 : validRep representative_3830 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3830)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3831 : validRep representative_3831 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3831)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3832 : validRep representative_3832 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3832)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3833 : validRep representative_3833 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3833)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3834 : validRep representative_3834 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3834)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3835 : validRep representative_3835 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3835)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3836 : validRep representative_3836 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3836)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3837 : validRep representative_3837 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3837)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3838 : validRep representative_3838 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3838)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3839 : validRep representative_3839 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3839)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_059 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3808 (QuarticIntegerRepresentativeTree.Tree.branch 3792 (QuarticIntegerRepresentativeTree.Tree.branch 3784 (QuarticIntegerRepresentativeTree.Tree.branch 3780 (QuarticIntegerRepresentativeTree.Tree.branch 3778 (QuarticIntegerRepresentativeTree.Tree.branch 3777 (QuarticIntegerRepresentativeTree.Tree.leaf 3776 representative_3776) (QuarticIntegerRepresentativeTree.Tree.leaf 3777 representative_3777)) (QuarticIntegerRepresentativeTree.Tree.branch 3779 (QuarticIntegerRepresentativeTree.Tree.leaf 3778 representative_3778) (QuarticIntegerRepresentativeTree.Tree.leaf 3779 representative_3779))) (QuarticIntegerRepresentativeTree.Tree.branch 3782 (QuarticIntegerRepresentativeTree.Tree.branch 3781 (QuarticIntegerRepresentativeTree.Tree.leaf 3780 representative_3780) (QuarticIntegerRepresentativeTree.Tree.leaf 3781 representative_3781)) (QuarticIntegerRepresentativeTree.Tree.branch 3783 (QuarticIntegerRepresentativeTree.Tree.leaf 3782 representative_3782) (QuarticIntegerRepresentativeTree.Tree.leaf 3783 representative_3783)))) (QuarticIntegerRepresentativeTree.Tree.branch 3788 (QuarticIntegerRepresentativeTree.Tree.branch 3786 (QuarticIntegerRepresentativeTree.Tree.branch 3785 (QuarticIntegerRepresentativeTree.Tree.leaf 3784 representative_3784) (QuarticIntegerRepresentativeTree.Tree.leaf 3785 representative_3785)) (QuarticIntegerRepresentativeTree.Tree.branch 3787 (QuarticIntegerRepresentativeTree.Tree.leaf 3786 representative_3786) (QuarticIntegerRepresentativeTree.Tree.leaf 3787 representative_3787))) (QuarticIntegerRepresentativeTree.Tree.branch 3790 (QuarticIntegerRepresentativeTree.Tree.branch 3789 (QuarticIntegerRepresentativeTree.Tree.leaf 3788 representative_3788) (QuarticIntegerRepresentativeTree.Tree.leaf 3789 representative_3789)) (QuarticIntegerRepresentativeTree.Tree.branch 3791 (QuarticIntegerRepresentativeTree.Tree.leaf 3790 representative_3790) (QuarticIntegerRepresentativeTree.Tree.leaf 3791 representative_3791))))) (QuarticIntegerRepresentativeTree.Tree.branch 3800 (QuarticIntegerRepresentativeTree.Tree.branch 3796 (QuarticIntegerRepresentativeTree.Tree.branch 3794 (QuarticIntegerRepresentativeTree.Tree.branch 3793 (QuarticIntegerRepresentativeTree.Tree.leaf 3792 representative_3792) (QuarticIntegerRepresentativeTree.Tree.leaf 3793 representative_3793)) (QuarticIntegerRepresentativeTree.Tree.branch 3795 (QuarticIntegerRepresentativeTree.Tree.leaf 3794 representative_3794) (QuarticIntegerRepresentativeTree.Tree.leaf 3795 representative_3795))) (QuarticIntegerRepresentativeTree.Tree.branch 3798 (QuarticIntegerRepresentativeTree.Tree.branch 3797 (QuarticIntegerRepresentativeTree.Tree.leaf 3796 representative_3796) (QuarticIntegerRepresentativeTree.Tree.leaf 3797 representative_3797)) (QuarticIntegerRepresentativeTree.Tree.branch 3799 (QuarticIntegerRepresentativeTree.Tree.leaf 3798 representative_3798) (QuarticIntegerRepresentativeTree.Tree.leaf 3799 representative_3799)))) (QuarticIntegerRepresentativeTree.Tree.branch 3804 (QuarticIntegerRepresentativeTree.Tree.branch 3802 (QuarticIntegerRepresentativeTree.Tree.branch 3801 (QuarticIntegerRepresentativeTree.Tree.leaf 3800 representative_3800) (QuarticIntegerRepresentativeTree.Tree.leaf 3801 representative_3801)) (QuarticIntegerRepresentativeTree.Tree.branch 3803 (QuarticIntegerRepresentativeTree.Tree.leaf 3802 representative_3802) (QuarticIntegerRepresentativeTree.Tree.leaf 3803 representative_3803))) (QuarticIntegerRepresentativeTree.Tree.branch 3806 (QuarticIntegerRepresentativeTree.Tree.branch 3805 (QuarticIntegerRepresentativeTree.Tree.leaf 3804 representative_3804) (QuarticIntegerRepresentativeTree.Tree.leaf 3805 representative_3805)) (QuarticIntegerRepresentativeTree.Tree.branch 3807 (QuarticIntegerRepresentativeTree.Tree.leaf 3806 representative_3806) (QuarticIntegerRepresentativeTree.Tree.leaf 3807 representative_3807)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3824 (QuarticIntegerRepresentativeTree.Tree.branch 3816 (QuarticIntegerRepresentativeTree.Tree.branch 3812 (QuarticIntegerRepresentativeTree.Tree.branch 3810 (QuarticIntegerRepresentativeTree.Tree.branch 3809 (QuarticIntegerRepresentativeTree.Tree.leaf 3808 representative_3808) (QuarticIntegerRepresentativeTree.Tree.leaf 3809 representative_3809)) (QuarticIntegerRepresentativeTree.Tree.branch 3811 (QuarticIntegerRepresentativeTree.Tree.leaf 3810 representative_3810) (QuarticIntegerRepresentativeTree.Tree.leaf 3811 representative_3811))) (QuarticIntegerRepresentativeTree.Tree.branch 3814 (QuarticIntegerRepresentativeTree.Tree.branch 3813 (QuarticIntegerRepresentativeTree.Tree.leaf 3812 representative_3812) (QuarticIntegerRepresentativeTree.Tree.leaf 3813 representative_3813)) (QuarticIntegerRepresentativeTree.Tree.branch 3815 (QuarticIntegerRepresentativeTree.Tree.leaf 3814 representative_3814) (QuarticIntegerRepresentativeTree.Tree.leaf 3815 representative_3815)))) (QuarticIntegerRepresentativeTree.Tree.branch 3820 (QuarticIntegerRepresentativeTree.Tree.branch 3818 (QuarticIntegerRepresentativeTree.Tree.branch 3817 (QuarticIntegerRepresentativeTree.Tree.leaf 3816 representative_3816) (QuarticIntegerRepresentativeTree.Tree.leaf 3817 representative_3817)) (QuarticIntegerRepresentativeTree.Tree.branch 3819 (QuarticIntegerRepresentativeTree.Tree.leaf 3818 representative_3818) (QuarticIntegerRepresentativeTree.Tree.leaf 3819 representative_3819))) (QuarticIntegerRepresentativeTree.Tree.branch 3822 (QuarticIntegerRepresentativeTree.Tree.branch 3821 (QuarticIntegerRepresentativeTree.Tree.leaf 3820 representative_3820) (QuarticIntegerRepresentativeTree.Tree.leaf 3821 representative_3821)) (QuarticIntegerRepresentativeTree.Tree.branch 3823 (QuarticIntegerRepresentativeTree.Tree.leaf 3822 representative_3822) (QuarticIntegerRepresentativeTree.Tree.leaf 3823 representative_3823))))) (QuarticIntegerRepresentativeTree.Tree.branch 3832 (QuarticIntegerRepresentativeTree.Tree.branch 3828 (QuarticIntegerRepresentativeTree.Tree.branch 3826 (QuarticIntegerRepresentativeTree.Tree.branch 3825 (QuarticIntegerRepresentativeTree.Tree.leaf 3824 representative_3824) (QuarticIntegerRepresentativeTree.Tree.leaf 3825 representative_3825)) (QuarticIntegerRepresentativeTree.Tree.branch 3827 (QuarticIntegerRepresentativeTree.Tree.leaf 3826 representative_3826) (QuarticIntegerRepresentativeTree.Tree.leaf 3827 representative_3827))) (QuarticIntegerRepresentativeTree.Tree.branch 3830 (QuarticIntegerRepresentativeTree.Tree.branch 3829 (QuarticIntegerRepresentativeTree.Tree.leaf 3828 representative_3828) (QuarticIntegerRepresentativeTree.Tree.leaf 3829 representative_3829)) (QuarticIntegerRepresentativeTree.Tree.branch 3831 (QuarticIntegerRepresentativeTree.Tree.leaf 3830 representative_3830) (QuarticIntegerRepresentativeTree.Tree.leaf 3831 representative_3831)))) (QuarticIntegerRepresentativeTree.Tree.branch 3836 (QuarticIntegerRepresentativeTree.Tree.branch 3834 (QuarticIntegerRepresentativeTree.Tree.branch 3833 (QuarticIntegerRepresentativeTree.Tree.leaf 3832 representative_3832) (QuarticIntegerRepresentativeTree.Tree.leaf 3833 representative_3833)) (QuarticIntegerRepresentativeTree.Tree.branch 3835 (QuarticIntegerRepresentativeTree.Tree.leaf 3834 representative_3834) (QuarticIntegerRepresentativeTree.Tree.leaf 3835 representative_3835))) (QuarticIntegerRepresentativeTree.Tree.branch 3838 (QuarticIntegerRepresentativeTree.Tree.branch 3837 (QuarticIntegerRepresentativeTree.Tree.leaf 3836 representative_3836) (QuarticIntegerRepresentativeTree.Tree.leaf 3837 representative_3837)) (QuarticIntegerRepresentativeTree.Tree.branch 3839 (QuarticIntegerRepresentativeTree.Tree.leaf 3838 representative_3838) (QuarticIntegerRepresentativeTree.Tree.leaf 3839 representative_3839)))))))
theorem accepted_059 : All validRep tree_059 := ⟨⟨⟨⟨⟨⟨coefficient_3776,coefficient_3777⟩,⟨coefficient_3778,coefficient_3779⟩⟩,⟨⟨coefficient_3780,coefficient_3781⟩,⟨coefficient_3782,coefficient_3783⟩⟩⟩,⟨⟨⟨coefficient_3784,coefficient_3785⟩,⟨coefficient_3786,coefficient_3787⟩⟩,⟨⟨coefficient_3788,coefficient_3789⟩,⟨coefficient_3790,coefficient_3791⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3792,coefficient_3793⟩,⟨coefficient_3794,coefficient_3795⟩⟩,⟨⟨coefficient_3796,coefficient_3797⟩,⟨coefficient_3798,coefficient_3799⟩⟩⟩,⟨⟨⟨coefficient_3800,coefficient_3801⟩,⟨coefficient_3802,coefficient_3803⟩⟩,⟨⟨coefficient_3804,coefficient_3805⟩,⟨coefficient_3806,coefficient_3807⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3808,coefficient_3809⟩,⟨coefficient_3810,coefficient_3811⟩⟩,⟨⟨coefficient_3812,coefficient_3813⟩,⟨coefficient_3814,coefficient_3815⟩⟩⟩,⟨⟨⟨coefficient_3816,coefficient_3817⟩,⟨coefficient_3818,coefficient_3819⟩⟩,⟨⟨coefficient_3820,coefficient_3821⟩,⟨coefficient_3822,coefficient_3823⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3824,coefficient_3825⟩,⟨coefficient_3826,coefficient_3827⟩⟩,⟨⟨coefficient_3828,coefficient_3829⟩,⟨coefficient_3830,coefficient_3831⟩⟩⟩,⟨⟨⟨coefficient_3832,coefficient_3833⟩,⟨coefficient_3834,coefficient_3835⟩⟩,⟨⟨coefficient_3836,coefficient_3837⟩,⟨coefficient_3838,coefficient_3839⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3840 : Rep := ⟨![0,19,9,43],462⟩
def representative_3841 : Rep := ⟨![0,19,9,44],462⟩
def representative_3842 : Rep := ⟨![0,19,9,45],462⟩
def representative_3843 : Rep := ⟨![0,19,9,46],462⟩
def representative_3844 : Rep := ⟨![0,19,9,47],462⟩
def representative_3845 : Rep := ⟨![0,19,9,52],462⟩
def representative_3846 : Rep := ⟨![0,19,9,53],462⟩
def representative_3847 : Rep := ⟨![0,19,9,54],462⟩
def representative_3848 : Rep := ⟨![0,19,9,55],462⟩
def representative_3849 : Rep := ⟨![0,19,9,60],462⟩
def representative_3850 : Rep := ⟨![0,19,9,61],462⟩
def representative_3851 : Rep := ⟨![0,19,9,62],462⟩
def representative_3852 : Rep := ⟨![0,19,12,24],462⟩
def representative_3853 : Rep := ⟨![0,19,12,31],462⟩
def representative_3854 : Rep := ⟨![0,19,12,32],462⟩
def representative_3855 : Rep := ⟨![0,19,12,33],462⟩
def representative_3856 : Rep := ⟨![0,19,12,38],462⟩
def representative_3857 : Rep := ⟨![0,19,12,39],462⟩
def representative_3858 : Rep := ⟨![0,19,12,40],462⟩
def representative_3859 : Rep := ⟨![0,19,12,41],462⟩
def representative_3860 : Rep := ⟨![0,19,12,42],462⟩
def representative_3861 : Rep := ⟨![0,19,12,46],462⟩
def representative_3862 : Rep := ⟨![0,19,12,47],462⟩
def representative_3863 : Rep := ⟨![0,19,12,48],462⟩
def representative_3864 : Rep := ⟨![0,19,12,49],462⟩
def representative_3865 : Rep := ⟨![0,19,12,50],462⟩
def representative_3866 : Rep := ⟨![0,19,12,54],462⟩
def representative_3867 : Rep := ⟨![0,19,12,55],462⟩
def representative_3868 : Rep := ⟨![0,19,12,56],462⟩
def representative_3869 : Rep := ⟨![0,19,12,57],462⟩
def representative_3870 : Rep := ⟨![0,19,12,63],462⟩
def representative_3871 : Rep := ⟨![0,19,13,24],462⟩
def representative_3872 : Rep := ⟨![0,19,13,25],462⟩
def representative_3873 : Rep := ⟨![0,19,13,32],462⟩
def representative_3874 : Rep := ⟨![0,19,13,33],462⟩
def representative_3875 : Rep := ⟨![0,19,13,34],462⟩
def representative_3876 : Rep := ⟨![0,19,13,39],462⟩
def representative_3877 : Rep := ⟨![0,19,13,40],462⟩
def representative_3878 : Rep := ⟨![0,19,13,41],462⟩
def representative_3879 : Rep := ⟨![0,19,13,42],462⟩
def representative_3880 : Rep := ⟨![0,19,13,43],462⟩
def representative_3881 : Rep := ⟨![0,19,13,47],462⟩
def representative_3882 : Rep := ⟨![0,19,13,48],462⟩
def representative_3883 : Rep := ⟨![0,19,13,49],462⟩
def representative_3884 : Rep := ⟨![0,19,13,50],462⟩
def representative_3885 : Rep := ⟨![0,19,13,55],462⟩
def representative_3886 : Rep := ⟨![0,19,13,57],462⟩
def representative_3887 : Rep := ⟨![0,19,13,58],462⟩
def representative_3888 : Rep := ⟨![0,19,24,43],462⟩
def representative_3889 : Rep := ⟨![0,19,24,44],462⟩
def representative_3890 : Rep := ⟨![0,19,24,45],462⟩
def representative_3891 : Rep := ⟨![0,19,24,51],462⟩
def representative_3892 : Rep := ⟨![0,19,24,52],462⟩
def representative_3893 : Rep := ⟨![0,19,24,53],462⟩
def representative_3894 : Rep := ⟨![0,19,24,58],462⟩
def representative_3895 : Rep := ⟨![0,19,24,59],462⟩
def representative_3896 : Rep := ⟨![0,19,24,60],462⟩
def representative_3897 : Rep := ⟨![0,19,24,61],462⟩
def representative_3898 : Rep := ⟨![0,19,24,62],462⟩
def representative_3899 : Rep := ⟨![0,19,25,44],462⟩
def representative_3900 : Rep := ⟨![0,19,25,45],462⟩
def representative_3901 : Rep := ⟨![0,19,25,46],462⟩
def representative_3902 : Rep := ⟨![0,19,25,52],462⟩
def representative_3903 : Rep := ⟨![0,19,25,53],462⟩
theorem coefficient_3840 : validRep representative_3840 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3840)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3841 : validRep representative_3841 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3841)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3842 : validRep representative_3842 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3842)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3843 : validRep representative_3843 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3843)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3844 : validRep representative_3844 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3844)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3845 : validRep representative_3845 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3845)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3846 : validRep representative_3846 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3846)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3847 : validRep representative_3847 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3847)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3848 : validRep representative_3848 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3848)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3849 : validRep representative_3849 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3849)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3850 : validRep representative_3850 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3850)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3851 : validRep representative_3851 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3851)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3852 : validRep representative_3852 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3852)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3853 : validRep representative_3853 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3853)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3854 : validRep representative_3854 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3854)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3855 : validRep representative_3855 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3855)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3856 : validRep representative_3856 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3856)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3857 : validRep representative_3857 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3857)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3858 : validRep representative_3858 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3858)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3859 : validRep representative_3859 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3859)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3860 : validRep representative_3860 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3860)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3861 : validRep representative_3861 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3861)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3862 : validRep representative_3862 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3862)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3863 : validRep representative_3863 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3863)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3864 : validRep representative_3864 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3864)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3865 : validRep representative_3865 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3865)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3866 : validRep representative_3866 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3866)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3867 : validRep representative_3867 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3867)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3868 : validRep representative_3868 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3868)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3869 : validRep representative_3869 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3869)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3870 : validRep representative_3870 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3870)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3871 : validRep representative_3871 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3871)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3872 : validRep representative_3872 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3872)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3873 : validRep representative_3873 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3873)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3874 : validRep representative_3874 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3874)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3875 : validRep representative_3875 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3875)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3876 : validRep representative_3876 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3876)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3877 : validRep representative_3877 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3877)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3878 : validRep representative_3878 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3878)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3879 : validRep representative_3879 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3879)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3880 : validRep representative_3880 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3880)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3881 : validRep representative_3881 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3881)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3882 : validRep representative_3882 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3882)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3883 : validRep representative_3883 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3883)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3884 : validRep representative_3884 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3884)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3885 : validRep representative_3885 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3885)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3886 : validRep representative_3886 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3886)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3887 : validRep representative_3887 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3887)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3888 : validRep representative_3888 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3888)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3889 : validRep representative_3889 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3889)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3890 : validRep representative_3890 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3890)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3891 : validRep representative_3891 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3891)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3892 : validRep representative_3892 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3892)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3893 : validRep representative_3893 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3893)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3894 : validRep representative_3894 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3894)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3895 : validRep representative_3895 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3895)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3896 : validRep representative_3896 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3896)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3897 : validRep representative_3897 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3897)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3898 : validRep representative_3898 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3898)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3899 : validRep representative_3899 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3899)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3900 : validRep representative_3900 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3900)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3901 : validRep representative_3901 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3901)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3902 : validRep representative_3902 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3902)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3903 : validRep representative_3903 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3903)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_060 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3872 (QuarticIntegerRepresentativeTree.Tree.branch 3856 (QuarticIntegerRepresentativeTree.Tree.branch 3848 (QuarticIntegerRepresentativeTree.Tree.branch 3844 (QuarticIntegerRepresentativeTree.Tree.branch 3842 (QuarticIntegerRepresentativeTree.Tree.branch 3841 (QuarticIntegerRepresentativeTree.Tree.leaf 3840 representative_3840) (QuarticIntegerRepresentativeTree.Tree.leaf 3841 representative_3841)) (QuarticIntegerRepresentativeTree.Tree.branch 3843 (QuarticIntegerRepresentativeTree.Tree.leaf 3842 representative_3842) (QuarticIntegerRepresentativeTree.Tree.leaf 3843 representative_3843))) (QuarticIntegerRepresentativeTree.Tree.branch 3846 (QuarticIntegerRepresentativeTree.Tree.branch 3845 (QuarticIntegerRepresentativeTree.Tree.leaf 3844 representative_3844) (QuarticIntegerRepresentativeTree.Tree.leaf 3845 representative_3845)) (QuarticIntegerRepresentativeTree.Tree.branch 3847 (QuarticIntegerRepresentativeTree.Tree.leaf 3846 representative_3846) (QuarticIntegerRepresentativeTree.Tree.leaf 3847 representative_3847)))) (QuarticIntegerRepresentativeTree.Tree.branch 3852 (QuarticIntegerRepresentativeTree.Tree.branch 3850 (QuarticIntegerRepresentativeTree.Tree.branch 3849 (QuarticIntegerRepresentativeTree.Tree.leaf 3848 representative_3848) (QuarticIntegerRepresentativeTree.Tree.leaf 3849 representative_3849)) (QuarticIntegerRepresentativeTree.Tree.branch 3851 (QuarticIntegerRepresentativeTree.Tree.leaf 3850 representative_3850) (QuarticIntegerRepresentativeTree.Tree.leaf 3851 representative_3851))) (QuarticIntegerRepresentativeTree.Tree.branch 3854 (QuarticIntegerRepresentativeTree.Tree.branch 3853 (QuarticIntegerRepresentativeTree.Tree.leaf 3852 representative_3852) (QuarticIntegerRepresentativeTree.Tree.leaf 3853 representative_3853)) (QuarticIntegerRepresentativeTree.Tree.branch 3855 (QuarticIntegerRepresentativeTree.Tree.leaf 3854 representative_3854) (QuarticIntegerRepresentativeTree.Tree.leaf 3855 representative_3855))))) (QuarticIntegerRepresentativeTree.Tree.branch 3864 (QuarticIntegerRepresentativeTree.Tree.branch 3860 (QuarticIntegerRepresentativeTree.Tree.branch 3858 (QuarticIntegerRepresentativeTree.Tree.branch 3857 (QuarticIntegerRepresentativeTree.Tree.leaf 3856 representative_3856) (QuarticIntegerRepresentativeTree.Tree.leaf 3857 representative_3857)) (QuarticIntegerRepresentativeTree.Tree.branch 3859 (QuarticIntegerRepresentativeTree.Tree.leaf 3858 representative_3858) (QuarticIntegerRepresentativeTree.Tree.leaf 3859 representative_3859))) (QuarticIntegerRepresentativeTree.Tree.branch 3862 (QuarticIntegerRepresentativeTree.Tree.branch 3861 (QuarticIntegerRepresentativeTree.Tree.leaf 3860 representative_3860) (QuarticIntegerRepresentativeTree.Tree.leaf 3861 representative_3861)) (QuarticIntegerRepresentativeTree.Tree.branch 3863 (QuarticIntegerRepresentativeTree.Tree.leaf 3862 representative_3862) (QuarticIntegerRepresentativeTree.Tree.leaf 3863 representative_3863)))) (QuarticIntegerRepresentativeTree.Tree.branch 3868 (QuarticIntegerRepresentativeTree.Tree.branch 3866 (QuarticIntegerRepresentativeTree.Tree.branch 3865 (QuarticIntegerRepresentativeTree.Tree.leaf 3864 representative_3864) (QuarticIntegerRepresentativeTree.Tree.leaf 3865 representative_3865)) (QuarticIntegerRepresentativeTree.Tree.branch 3867 (QuarticIntegerRepresentativeTree.Tree.leaf 3866 representative_3866) (QuarticIntegerRepresentativeTree.Tree.leaf 3867 representative_3867))) (QuarticIntegerRepresentativeTree.Tree.branch 3870 (QuarticIntegerRepresentativeTree.Tree.branch 3869 (QuarticIntegerRepresentativeTree.Tree.leaf 3868 representative_3868) (QuarticIntegerRepresentativeTree.Tree.leaf 3869 representative_3869)) (QuarticIntegerRepresentativeTree.Tree.branch 3871 (QuarticIntegerRepresentativeTree.Tree.leaf 3870 representative_3870) (QuarticIntegerRepresentativeTree.Tree.leaf 3871 representative_3871)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3888 (QuarticIntegerRepresentativeTree.Tree.branch 3880 (QuarticIntegerRepresentativeTree.Tree.branch 3876 (QuarticIntegerRepresentativeTree.Tree.branch 3874 (QuarticIntegerRepresentativeTree.Tree.branch 3873 (QuarticIntegerRepresentativeTree.Tree.leaf 3872 representative_3872) (QuarticIntegerRepresentativeTree.Tree.leaf 3873 representative_3873)) (QuarticIntegerRepresentativeTree.Tree.branch 3875 (QuarticIntegerRepresentativeTree.Tree.leaf 3874 representative_3874) (QuarticIntegerRepresentativeTree.Tree.leaf 3875 representative_3875))) (QuarticIntegerRepresentativeTree.Tree.branch 3878 (QuarticIntegerRepresentativeTree.Tree.branch 3877 (QuarticIntegerRepresentativeTree.Tree.leaf 3876 representative_3876) (QuarticIntegerRepresentativeTree.Tree.leaf 3877 representative_3877)) (QuarticIntegerRepresentativeTree.Tree.branch 3879 (QuarticIntegerRepresentativeTree.Tree.leaf 3878 representative_3878) (QuarticIntegerRepresentativeTree.Tree.leaf 3879 representative_3879)))) (QuarticIntegerRepresentativeTree.Tree.branch 3884 (QuarticIntegerRepresentativeTree.Tree.branch 3882 (QuarticIntegerRepresentativeTree.Tree.branch 3881 (QuarticIntegerRepresentativeTree.Tree.leaf 3880 representative_3880) (QuarticIntegerRepresentativeTree.Tree.leaf 3881 representative_3881)) (QuarticIntegerRepresentativeTree.Tree.branch 3883 (QuarticIntegerRepresentativeTree.Tree.leaf 3882 representative_3882) (QuarticIntegerRepresentativeTree.Tree.leaf 3883 representative_3883))) (QuarticIntegerRepresentativeTree.Tree.branch 3886 (QuarticIntegerRepresentativeTree.Tree.branch 3885 (QuarticIntegerRepresentativeTree.Tree.leaf 3884 representative_3884) (QuarticIntegerRepresentativeTree.Tree.leaf 3885 representative_3885)) (QuarticIntegerRepresentativeTree.Tree.branch 3887 (QuarticIntegerRepresentativeTree.Tree.leaf 3886 representative_3886) (QuarticIntegerRepresentativeTree.Tree.leaf 3887 representative_3887))))) (QuarticIntegerRepresentativeTree.Tree.branch 3896 (QuarticIntegerRepresentativeTree.Tree.branch 3892 (QuarticIntegerRepresentativeTree.Tree.branch 3890 (QuarticIntegerRepresentativeTree.Tree.branch 3889 (QuarticIntegerRepresentativeTree.Tree.leaf 3888 representative_3888) (QuarticIntegerRepresentativeTree.Tree.leaf 3889 representative_3889)) (QuarticIntegerRepresentativeTree.Tree.branch 3891 (QuarticIntegerRepresentativeTree.Tree.leaf 3890 representative_3890) (QuarticIntegerRepresentativeTree.Tree.leaf 3891 representative_3891))) (QuarticIntegerRepresentativeTree.Tree.branch 3894 (QuarticIntegerRepresentativeTree.Tree.branch 3893 (QuarticIntegerRepresentativeTree.Tree.leaf 3892 representative_3892) (QuarticIntegerRepresentativeTree.Tree.leaf 3893 representative_3893)) (QuarticIntegerRepresentativeTree.Tree.branch 3895 (QuarticIntegerRepresentativeTree.Tree.leaf 3894 representative_3894) (QuarticIntegerRepresentativeTree.Tree.leaf 3895 representative_3895)))) (QuarticIntegerRepresentativeTree.Tree.branch 3900 (QuarticIntegerRepresentativeTree.Tree.branch 3898 (QuarticIntegerRepresentativeTree.Tree.branch 3897 (QuarticIntegerRepresentativeTree.Tree.leaf 3896 representative_3896) (QuarticIntegerRepresentativeTree.Tree.leaf 3897 representative_3897)) (QuarticIntegerRepresentativeTree.Tree.branch 3899 (QuarticIntegerRepresentativeTree.Tree.leaf 3898 representative_3898) (QuarticIntegerRepresentativeTree.Tree.leaf 3899 representative_3899))) (QuarticIntegerRepresentativeTree.Tree.branch 3902 (QuarticIntegerRepresentativeTree.Tree.branch 3901 (QuarticIntegerRepresentativeTree.Tree.leaf 3900 representative_3900) (QuarticIntegerRepresentativeTree.Tree.leaf 3901 representative_3901)) (QuarticIntegerRepresentativeTree.Tree.branch 3903 (QuarticIntegerRepresentativeTree.Tree.leaf 3902 representative_3902) (QuarticIntegerRepresentativeTree.Tree.leaf 3903 representative_3903)))))))
theorem accepted_060 : All validRep tree_060 := ⟨⟨⟨⟨⟨⟨coefficient_3840,coefficient_3841⟩,⟨coefficient_3842,coefficient_3843⟩⟩,⟨⟨coefficient_3844,coefficient_3845⟩,⟨coefficient_3846,coefficient_3847⟩⟩⟩,⟨⟨⟨coefficient_3848,coefficient_3849⟩,⟨coefficient_3850,coefficient_3851⟩⟩,⟨⟨coefficient_3852,coefficient_3853⟩,⟨coefficient_3854,coefficient_3855⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3856,coefficient_3857⟩,⟨coefficient_3858,coefficient_3859⟩⟩,⟨⟨coefficient_3860,coefficient_3861⟩,⟨coefficient_3862,coefficient_3863⟩⟩⟩,⟨⟨⟨coefficient_3864,coefficient_3865⟩,⟨coefficient_3866,coefficient_3867⟩⟩,⟨⟨coefficient_3868,coefficient_3869⟩,⟨coefficient_3870,coefficient_3871⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3872,coefficient_3873⟩,⟨coefficient_3874,coefficient_3875⟩⟩,⟨⟨coefficient_3876,coefficient_3877⟩,⟨coefficient_3878,coefficient_3879⟩⟩⟩,⟨⟨⟨coefficient_3880,coefficient_3881⟩,⟨coefficient_3882,coefficient_3883⟩⟩,⟨⟨coefficient_3884,coefficient_3885⟩,⟨coefficient_3886,coefficient_3887⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3888,coefficient_3889⟩,⟨coefficient_3890,coefficient_3891⟩⟩,⟨⟨coefficient_3892,coefficient_3893⟩,⟨coefficient_3894,coefficient_3895⟩⟩⟩,⟨⟨⟨coefficient_3896,coefficient_3897⟩,⟨coefficient_3898,coefficient_3899⟩⟩,⟨⟨coefficient_3900,coefficient_3901⟩,⟨coefficient_3902,coefficient_3903⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

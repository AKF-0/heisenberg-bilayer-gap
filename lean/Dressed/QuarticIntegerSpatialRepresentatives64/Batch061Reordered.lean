import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3904 : Rep := ⟨![0,19,25,54],462⟩
def representative_3905 : Rep := ⟨![0,19,25,60],462⟩
def representative_3906 : Rep := ⟨![0,19,25,61],462⟩
def representative_3907 : Rep := ⟨![0,19,25,62],462⟩
def representative_3908 : Rep := ⟨![0,19,25,63],462⟩
def representative_3909 : Rep := ⟨![0,19,26,45],462⟩
def representative_3910 : Rep := ⟨![0,19,26,46],462⟩
def representative_3911 : Rep := ⟨![0,19,26,47],462⟩
def representative_3912 : Rep := ⟨![0,19,26,53],462⟩
def representative_3913 : Rep := ⟨![0,19,26,54],462⟩
def representative_3914 : Rep := ⟨![0,19,26,55],462⟩
def representative_3915 : Rep := ⟨![0,19,26,56],462⟩
def representative_3916 : Rep := ⟨![0,19,26,60],462⟩
def representative_3917 : Rep := ⟨![0,19,26,61],462⟩
def representative_3918 : Rep := ⟨![0,19,26,62],462⟩
def representative_3919 : Rep := ⟨![0,19,26,63],462⟩
def representative_3920 : Rep := ⟨![0,19,27,40],462⟩
def representative_3921 : Rep := ⟨![0,19,27,46],462⟩
def representative_3922 : Rep := ⟨![0,19,27,47],462⟩
def representative_3923 : Rep := ⟨![0,19,27,48],462⟩
def representative_3924 : Rep := ⟨![0,19,27,54],462⟩
def representative_3925 : Rep := ⟨![0,19,27,55],462⟩
def representative_3926 : Rep := ⟨![0,19,27,56],462⟩
def representative_3927 : Rep := ⟨![0,19,27,61],462⟩
def representative_3928 : Rep := ⟨![0,19,27,62],462⟩
def representative_3929 : Rep := ⟨![0,19,27,63],462⟩
def representative_3930 : Rep := ⟨![0,19,28,40],462⟩
def representative_3931 : Rep := ⟨![0,19,28,47],462⟩
def representative_3932 : Rep := ⟨![0,19,28,48],462⟩
def representative_3933 : Rep := ⟨![0,19,28,49],462⟩
def representative_3934 : Rep := ⟨![0,19,28,54],462⟩
def representative_3935 : Rep := ⟨![0,19,28,55],462⟩
def representative_3936 : Rep := ⟨![0,19,28,62],462⟩
def representative_3937 : Rep := ⟨![0,19,28,63],462⟩
def representative_3938 : Rep := ⟨![0,19,29,40],462⟩
def representative_3939 : Rep := ⟨![0,19,29,41],462⟩
def representative_3940 : Rep := ⟨![0,19,29,48],462⟩
def representative_3941 : Rep := ⟨![0,19,29,49],462⟩
def representative_3942 : Rep := ⟨![0,19,29,50],462⟩
def representative_3943 : Rep := ⟨![0,19,29,55],462⟩
def representative_3944 : Rep := ⟨![0,19,30,41],462⟩
def representative_3945 : Rep := ⟨![0,19,30,42],462⟩
def representative_3946 : Rep := ⟨![0,19,30,49],462⟩
def representative_3947 : Rep := ⟨![0,19,30,50],462⟩
def representative_3948 : Rep := ⟨![0,19,30,51],462⟩
def representative_3949 : Rep := ⟨![0,19,30,52],462⟩
def representative_3950 : Rep := ⟨![0,19,30,60],462⟩
def representative_3951 : Rep := ⟨![0,19,31,42],462⟩
def representative_3952 : Rep := ⟨![0,19,31,43],462⟩
def representative_3953 : Rep := ⟨![0,19,31,44],462⟩
def representative_3954 : Rep := ⟨![0,19,31,50],462⟩
def representative_3955 : Rep := ⟨![0,19,31,51],462⟩
def representative_3956 : Rep := ⟨![0,19,31,52],462⟩
def representative_3957 : Rep := ⟨![0,19,31,60],462⟩
def representative_3958 : Rep := ⟨![0,19,32,51],462⟩
def representative_3959 : Rep := ⟨![0,19,32,52],462⟩
def representative_3960 : Rep := ⟨![0,19,32,53],462⟩
def representative_3961 : Rep := ⟨![0,19,33,52],462⟩
def representative_3962 : Rep := ⟨![0,19,33,53],462⟩
def representative_3963 : Rep := ⟨![0,19,33,54],462⟩
def representative_3964 : Rep := ⟨![0,19,34,53],462⟩
def representative_3965 : Rep := ⟨![0,19,34,54],462⟩
def representative_3966 : Rep := ⟨![0,19,34,55],462⟩
def representative_3967 : Rep := ⟨![0,19,35,48],462⟩
theorem coefficient_3904 : validRep representative_3904 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3904)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3905 : validRep representative_3905 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3905)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3906 : validRep representative_3906 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3906)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3907 : validRep representative_3907 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3907)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3908 : validRep representative_3908 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3908)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3909 : validRep representative_3909 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3909)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3910 : validRep representative_3910 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3910)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3911 : validRep representative_3911 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3911)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3912 : validRep representative_3912 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3912)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3913 : validRep representative_3913 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3913)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3914 : validRep representative_3914 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3914)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3915 : validRep representative_3915 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3915)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3916 : validRep representative_3916 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3916)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3917 : validRep representative_3917 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3917)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3918 : validRep representative_3918 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3918)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3919 : validRep representative_3919 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3919)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3920 : validRep representative_3920 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3920)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3921 : validRep representative_3921 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3921)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3922 : validRep representative_3922 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3922)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3923 : validRep representative_3923 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3923)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3924 : validRep representative_3924 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3924)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3925 : validRep representative_3925 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3925)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3926 : validRep representative_3926 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3926)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3927 : validRep representative_3927 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3927)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3928 : validRep representative_3928 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3928)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3929 : validRep representative_3929 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3929)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3930 : validRep representative_3930 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3930)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3931 : validRep representative_3931 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3931)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3932 : validRep representative_3932 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3932)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3933 : validRep representative_3933 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3933)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3934 : validRep representative_3934 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3934)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3935 : validRep representative_3935 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3935)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3936 : validRep representative_3936 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3936)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3937 : validRep representative_3937 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3937)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3938 : validRep representative_3938 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3938)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3939 : validRep representative_3939 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3939)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3940 : validRep representative_3940 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3940)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3941 : validRep representative_3941 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3941)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3942 : validRep representative_3942 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3942)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3943 : validRep representative_3943 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3943)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3944 : validRep representative_3944 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3944)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3945 : validRep representative_3945 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3945)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3946 : validRep representative_3946 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3946)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3947 : validRep representative_3947 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3947)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3948 : validRep representative_3948 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3948)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3949 : validRep representative_3949 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3949)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3950 : validRep representative_3950 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3950)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3951 : validRep representative_3951 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3951)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3952 : validRep representative_3952 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3952)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3953 : validRep representative_3953 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3953)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3954 : validRep representative_3954 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3954)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3955 : validRep representative_3955 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3955)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3956 : validRep representative_3956 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3956)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3957 : validRep representative_3957 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3957)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3958 : validRep representative_3958 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3958)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3959 : validRep representative_3959 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3959)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3960 : validRep representative_3960 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3960)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3961 : validRep representative_3961 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3961)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3962 : validRep representative_3962 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3962)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3963 : validRep representative_3963 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3963)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3964 : validRep representative_3964 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3964)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3965 : validRep representative_3965 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3965)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3966 : validRep representative_3966 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3966)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3967 : validRep representative_3967 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3967)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_061 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 3936 (QuarticIntegerRepresentativeTree.Tree.branch 3920 (QuarticIntegerRepresentativeTree.Tree.branch 3912 (QuarticIntegerRepresentativeTree.Tree.branch 3908 (QuarticIntegerRepresentativeTree.Tree.branch 3906 (QuarticIntegerRepresentativeTree.Tree.branch 3905 (QuarticIntegerRepresentativeTree.Tree.leaf 3904 representative_3904) (QuarticIntegerRepresentativeTree.Tree.leaf 3905 representative_3905)) (QuarticIntegerRepresentativeTree.Tree.branch 3907 (QuarticIntegerRepresentativeTree.Tree.leaf 3906 representative_3906) (QuarticIntegerRepresentativeTree.Tree.leaf 3907 representative_3907))) (QuarticIntegerRepresentativeTree.Tree.branch 3910 (QuarticIntegerRepresentativeTree.Tree.branch 3909 (QuarticIntegerRepresentativeTree.Tree.leaf 3908 representative_3908) (QuarticIntegerRepresentativeTree.Tree.leaf 3909 representative_3909)) (QuarticIntegerRepresentativeTree.Tree.branch 3911 (QuarticIntegerRepresentativeTree.Tree.leaf 3910 representative_3910) (QuarticIntegerRepresentativeTree.Tree.leaf 3911 representative_3911)))) (QuarticIntegerRepresentativeTree.Tree.branch 3916 (QuarticIntegerRepresentativeTree.Tree.branch 3914 (QuarticIntegerRepresentativeTree.Tree.branch 3913 (QuarticIntegerRepresentativeTree.Tree.leaf 3912 representative_3912) (QuarticIntegerRepresentativeTree.Tree.leaf 3913 representative_3913)) (QuarticIntegerRepresentativeTree.Tree.branch 3915 (QuarticIntegerRepresentativeTree.Tree.leaf 3914 representative_3914) (QuarticIntegerRepresentativeTree.Tree.leaf 3915 representative_3915))) (QuarticIntegerRepresentativeTree.Tree.branch 3918 (QuarticIntegerRepresentativeTree.Tree.branch 3917 (QuarticIntegerRepresentativeTree.Tree.leaf 3916 representative_3916) (QuarticIntegerRepresentativeTree.Tree.leaf 3917 representative_3917)) (QuarticIntegerRepresentativeTree.Tree.branch 3919 (QuarticIntegerRepresentativeTree.Tree.leaf 3918 representative_3918) (QuarticIntegerRepresentativeTree.Tree.leaf 3919 representative_3919))))) (QuarticIntegerRepresentativeTree.Tree.branch 3928 (QuarticIntegerRepresentativeTree.Tree.branch 3924 (QuarticIntegerRepresentativeTree.Tree.branch 3922 (QuarticIntegerRepresentativeTree.Tree.branch 3921 (QuarticIntegerRepresentativeTree.Tree.leaf 3920 representative_3920) (QuarticIntegerRepresentativeTree.Tree.leaf 3921 representative_3921)) (QuarticIntegerRepresentativeTree.Tree.branch 3923 (QuarticIntegerRepresentativeTree.Tree.leaf 3922 representative_3922) (QuarticIntegerRepresentativeTree.Tree.leaf 3923 representative_3923))) (QuarticIntegerRepresentativeTree.Tree.branch 3926 (QuarticIntegerRepresentativeTree.Tree.branch 3925 (QuarticIntegerRepresentativeTree.Tree.leaf 3924 representative_3924) (QuarticIntegerRepresentativeTree.Tree.leaf 3925 representative_3925)) (QuarticIntegerRepresentativeTree.Tree.branch 3927 (QuarticIntegerRepresentativeTree.Tree.leaf 3926 representative_3926) (QuarticIntegerRepresentativeTree.Tree.leaf 3927 representative_3927)))) (QuarticIntegerRepresentativeTree.Tree.branch 3932 (QuarticIntegerRepresentativeTree.Tree.branch 3930 (QuarticIntegerRepresentativeTree.Tree.branch 3929 (QuarticIntegerRepresentativeTree.Tree.leaf 3928 representative_3928) (QuarticIntegerRepresentativeTree.Tree.leaf 3929 representative_3929)) (QuarticIntegerRepresentativeTree.Tree.branch 3931 (QuarticIntegerRepresentativeTree.Tree.leaf 3930 representative_3930) (QuarticIntegerRepresentativeTree.Tree.leaf 3931 representative_3931))) (QuarticIntegerRepresentativeTree.Tree.branch 3934 (QuarticIntegerRepresentativeTree.Tree.branch 3933 (QuarticIntegerRepresentativeTree.Tree.leaf 3932 representative_3932) (QuarticIntegerRepresentativeTree.Tree.leaf 3933 representative_3933)) (QuarticIntegerRepresentativeTree.Tree.branch 3935 (QuarticIntegerRepresentativeTree.Tree.leaf 3934 representative_3934) (QuarticIntegerRepresentativeTree.Tree.leaf 3935 representative_3935)))))) (QuarticIntegerRepresentativeTree.Tree.branch 3952 (QuarticIntegerRepresentativeTree.Tree.branch 3944 (QuarticIntegerRepresentativeTree.Tree.branch 3940 (QuarticIntegerRepresentativeTree.Tree.branch 3938 (QuarticIntegerRepresentativeTree.Tree.branch 3937 (QuarticIntegerRepresentativeTree.Tree.leaf 3936 representative_3936) (QuarticIntegerRepresentativeTree.Tree.leaf 3937 representative_3937)) (QuarticIntegerRepresentativeTree.Tree.branch 3939 (QuarticIntegerRepresentativeTree.Tree.leaf 3938 representative_3938) (QuarticIntegerRepresentativeTree.Tree.leaf 3939 representative_3939))) (QuarticIntegerRepresentativeTree.Tree.branch 3942 (QuarticIntegerRepresentativeTree.Tree.branch 3941 (QuarticIntegerRepresentativeTree.Tree.leaf 3940 representative_3940) (QuarticIntegerRepresentativeTree.Tree.leaf 3941 representative_3941)) (QuarticIntegerRepresentativeTree.Tree.branch 3943 (QuarticIntegerRepresentativeTree.Tree.leaf 3942 representative_3942) (QuarticIntegerRepresentativeTree.Tree.leaf 3943 representative_3943)))) (QuarticIntegerRepresentativeTree.Tree.branch 3948 (QuarticIntegerRepresentativeTree.Tree.branch 3946 (QuarticIntegerRepresentativeTree.Tree.branch 3945 (QuarticIntegerRepresentativeTree.Tree.leaf 3944 representative_3944) (QuarticIntegerRepresentativeTree.Tree.leaf 3945 representative_3945)) (QuarticIntegerRepresentativeTree.Tree.branch 3947 (QuarticIntegerRepresentativeTree.Tree.leaf 3946 representative_3946) (QuarticIntegerRepresentativeTree.Tree.leaf 3947 representative_3947))) (QuarticIntegerRepresentativeTree.Tree.branch 3950 (QuarticIntegerRepresentativeTree.Tree.branch 3949 (QuarticIntegerRepresentativeTree.Tree.leaf 3948 representative_3948) (QuarticIntegerRepresentativeTree.Tree.leaf 3949 representative_3949)) (QuarticIntegerRepresentativeTree.Tree.branch 3951 (QuarticIntegerRepresentativeTree.Tree.leaf 3950 representative_3950) (QuarticIntegerRepresentativeTree.Tree.leaf 3951 representative_3951))))) (QuarticIntegerRepresentativeTree.Tree.branch 3960 (QuarticIntegerRepresentativeTree.Tree.branch 3956 (QuarticIntegerRepresentativeTree.Tree.branch 3954 (QuarticIntegerRepresentativeTree.Tree.branch 3953 (QuarticIntegerRepresentativeTree.Tree.leaf 3952 representative_3952) (QuarticIntegerRepresentativeTree.Tree.leaf 3953 representative_3953)) (QuarticIntegerRepresentativeTree.Tree.branch 3955 (QuarticIntegerRepresentativeTree.Tree.leaf 3954 representative_3954) (QuarticIntegerRepresentativeTree.Tree.leaf 3955 representative_3955))) (QuarticIntegerRepresentativeTree.Tree.branch 3958 (QuarticIntegerRepresentativeTree.Tree.branch 3957 (QuarticIntegerRepresentativeTree.Tree.leaf 3956 representative_3956) (QuarticIntegerRepresentativeTree.Tree.leaf 3957 representative_3957)) (QuarticIntegerRepresentativeTree.Tree.branch 3959 (QuarticIntegerRepresentativeTree.Tree.leaf 3958 representative_3958) (QuarticIntegerRepresentativeTree.Tree.leaf 3959 representative_3959)))) (QuarticIntegerRepresentativeTree.Tree.branch 3964 (QuarticIntegerRepresentativeTree.Tree.branch 3962 (QuarticIntegerRepresentativeTree.Tree.branch 3961 (QuarticIntegerRepresentativeTree.Tree.leaf 3960 representative_3960) (QuarticIntegerRepresentativeTree.Tree.leaf 3961 representative_3961)) (QuarticIntegerRepresentativeTree.Tree.branch 3963 (QuarticIntegerRepresentativeTree.Tree.leaf 3962 representative_3962) (QuarticIntegerRepresentativeTree.Tree.leaf 3963 representative_3963))) (QuarticIntegerRepresentativeTree.Tree.branch 3966 (QuarticIntegerRepresentativeTree.Tree.branch 3965 (QuarticIntegerRepresentativeTree.Tree.leaf 3964 representative_3964) (QuarticIntegerRepresentativeTree.Tree.leaf 3965 representative_3965)) (QuarticIntegerRepresentativeTree.Tree.branch 3967 (QuarticIntegerRepresentativeTree.Tree.leaf 3966 representative_3966) (QuarticIntegerRepresentativeTree.Tree.leaf 3967 representative_3967)))))))
theorem accepted_061 : All validRep tree_061 := ⟨⟨⟨⟨⟨⟨coefficient_3904,coefficient_3905⟩,⟨coefficient_3906,coefficient_3907⟩⟩,⟨⟨coefficient_3908,coefficient_3909⟩,⟨coefficient_3910,coefficient_3911⟩⟩⟩,⟨⟨⟨coefficient_3912,coefficient_3913⟩,⟨coefficient_3914,coefficient_3915⟩⟩,⟨⟨coefficient_3916,coefficient_3917⟩,⟨coefficient_3918,coefficient_3919⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3920,coefficient_3921⟩,⟨coefficient_3922,coefficient_3923⟩⟩,⟨⟨coefficient_3924,coefficient_3925⟩,⟨coefficient_3926,coefficient_3927⟩⟩⟩,⟨⟨⟨coefficient_3928,coefficient_3929⟩,⟨coefficient_3930,coefficient_3931⟩⟩,⟨⟨coefficient_3932,coefficient_3933⟩,⟨coefficient_3934,coefficient_3935⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_3936,coefficient_3937⟩,⟨coefficient_3938,coefficient_3939⟩⟩,⟨⟨coefficient_3940,coefficient_3941⟩,⟨coefficient_3942,coefficient_3943⟩⟩⟩,⟨⟨⟨coefficient_3944,coefficient_3945⟩,⟨coefficient_3946,coefficient_3947⟩⟩,⟨⟨coefficient_3948,coefficient_3949⟩,⟨coefficient_3950,coefficient_3951⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3952,coefficient_3953⟩,⟨coefficient_3954,coefficient_3955⟩⟩,⟨⟨coefficient_3956,coefficient_3957⟩,⟨coefficient_3958,coefficient_3959⟩⟩⟩,⟨⟨⟨coefficient_3960,coefficient_3961⟩,⟨coefficient_3962,coefficient_3963⟩⟩,⟨⟨coefficient_3964,coefficient_3965⟩,⟨coefficient_3966,coefficient_3967⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

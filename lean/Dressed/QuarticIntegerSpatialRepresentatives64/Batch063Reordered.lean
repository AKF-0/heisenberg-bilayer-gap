import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_4032 : Rep := ⟨![0,20,9,44],462⟩
def representative_4033 : Rep := ⟨![0,20,9,45],462⟩
def representative_4034 : Rep := ⟨![0,20,9,46],462⟩
def representative_4035 : Rep := ⟨![0,20,9,47],462⟩
def representative_4036 : Rep := ⟨![0,20,9,52],462⟩
def representative_4037 : Rep := ⟨![0,20,9,53],462⟩
def representative_4038 : Rep := ⟨![0,20,9,54],462⟩
def representative_4039 : Rep := ⟨![0,20,9,61],462⟩
def representative_4040 : Rep := ⟨![0,20,10,30],462⟩
def representative_4041 : Rep := ⟨![0,20,10,37],462⟩
def representative_4042 : Rep := ⟨![0,20,10,38],462⟩
def representative_4043 : Rep := ⟨![0,20,10,39],462⟩
def representative_4044 : Rep := ⟨![0,20,10,45],462⟩
def representative_4045 : Rep := ⟨![0,20,10,46],462⟩
def representative_4046 : Rep := ⟨![0,20,24,44],462⟩
def representative_4047 : Rep := ⟨![0,20,24,51],462⟩
def representative_4048 : Rep := ⟨![0,20,24,52],462⟩
def representative_4049 : Rep := ⟨![0,20,24,59],462⟩
def representative_4050 : Rep := ⟨![0,20,24,60],462⟩
def representative_4051 : Rep := ⟨![0,20,25,45],462⟩
def representative_4052 : Rep := ⟨![0,20,25,52],462⟩
def representative_4053 : Rep := ⟨![0,20,25,53],462⟩
def representative_4054 : Rep := ⟨![0,20,25,54],462⟩
def representative_4055 : Rep := ⟨![0,20,25,59],462⟩
def representative_4056 : Rep := ⟨![0,20,25,61],462⟩
def representative_4057 : Rep := ⟨![0,20,25,62],462⟩
def representative_4058 : Rep := ⟨![0,20,26,46],462⟩
def representative_4059 : Rep := ⟨![0,20,26,53],462⟩
def representative_4060 : Rep := ⟨![0,20,26,54],462⟩
def representative_4061 : Rep := ⟨![0,20,26,55],462⟩
def representative_4062 : Rep := ⟨![0,20,26,62],462⟩
def representative_4063 : Rep := ⟨![0,20,26,63],462⟩
def representative_4064 : Rep := ⟨![0,20,27,47],462⟩
def representative_4065 : Rep := ⟨![0,20,27,48],462⟩
def representative_4066 : Rep := ⟨![0,20,27,54],462⟩
def representative_4067 : Rep := ⟨![0,20,27,55],462⟩
def representative_4068 : Rep := ⟨![0,20,27,56],462⟩
def representative_4069 : Rep := ⟨![0,20,27,57],462⟩
def representative_4070 : Rep := ⟨![0,20,27,63],462⟩
def representative_4071 : Rep := ⟨![0,20,28,40],462⟩
def representative_4072 : Rep := ⟨![0,20,28,48],462⟩
def representative_4073 : Rep := ⟨![0,20,28,49],462⟩
def representative_4074 : Rep := ⟨![0,20,28,56],462⟩
def representative_4075 : Rep := ⟨![0,20,32,52],462⟩
def representative_4076 : Rep := ⟨![0,20,33,53],462⟩
def representative_4077 : Rep := ⟨![0,20,34,54],462⟩
def representative_4078 : Rep := ⟨![0,20,35,55],462⟩
def representative_4079 : Rep := ⟨![0,20,36,48],462⟩
def representative_4080 : Rep := ⟨![0,27,1,28],462⟩
def representative_4081 : Rep := ⟨![0,27,1,29],462⟩
def representative_4082 : Rep := ⟨![0,27,1,30],462⟩
def representative_4083 : Rep := ⟨![0,27,1,36],462⟩
def representative_4084 : Rep := ⟨![0,27,1,37],462⟩
def representative_4085 : Rep := ⟨![0,27,1,38],462⟩
def representative_4086 : Rep := ⟨![0,27,1,44],462⟩
def representative_4087 : Rep := ⟨![0,27,1,45],462⟩
def representative_4088 : Rep := ⟨![0,27,1,46],462⟩
def representative_4089 : Rep := ⟨![0,27,2,29],462⟩
def representative_4090 : Rep := ⟨![0,27,2,30],462⟩
def representative_4091 : Rep := ⟨![0,27,2,31],462⟩
def representative_4092 : Rep := ⟨![0,27,2,37],462⟩
def representative_4093 : Rep := ⟨![0,27,2,38],462⟩
def representative_4094 : Rep := ⟨![0,27,2,39],462⟩
def representative_4095 : Rep := ⟨![0,27,2,45],462⟩
theorem coefficient_4032 : validRep representative_4032 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4032)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4033 : validRep representative_4033 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4033)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4034 : validRep representative_4034 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4034)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4035 : validRep representative_4035 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4035)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4036 : validRep representative_4036 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4036)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4037 : validRep representative_4037 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4037)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4038 : validRep representative_4038 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4038)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4039 : validRep representative_4039 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4039)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4040 : validRep representative_4040 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4040)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4041 : validRep representative_4041 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4041)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4042 : validRep representative_4042 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4042)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4043 : validRep representative_4043 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4043)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4044 : validRep representative_4044 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4044)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4045 : validRep representative_4045 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4045)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4046 : validRep representative_4046 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4046)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4047 : validRep representative_4047 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4047)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4048 : validRep representative_4048 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4048)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4049 : validRep representative_4049 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4049)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4050 : validRep representative_4050 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4050)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4051 : validRep representative_4051 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4051)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4052 : validRep representative_4052 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4052)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4053 : validRep representative_4053 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4053)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4054 : validRep representative_4054 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4054)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4055 : validRep representative_4055 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4055)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4056 : validRep representative_4056 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4056)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4057 : validRep representative_4057 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4057)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4058 : validRep representative_4058 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4058)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4059 : validRep representative_4059 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4059)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4060 : validRep representative_4060 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4060)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4061 : validRep representative_4061 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4061)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4062 : validRep representative_4062 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4062)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4063 : validRep representative_4063 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4063)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4064 : validRep representative_4064 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4064)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4065 : validRep representative_4065 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4065)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4066 : validRep representative_4066 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4066)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4067 : validRep representative_4067 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4067)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4068 : validRep representative_4068 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4068)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4069 : validRep representative_4069 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4069)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4070 : validRep representative_4070 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4070)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4071 : validRep representative_4071 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4071)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4072 : validRep representative_4072 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4072)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4073 : validRep representative_4073 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4073)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4074 : validRep representative_4074 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4074)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4075 : validRep representative_4075 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4075)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4076 : validRep representative_4076 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4076)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4077 : validRep representative_4077 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4077)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4078 : validRep representative_4078 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4078)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4079 : validRep representative_4079 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4079)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4080 : validRep representative_4080 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4080)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4081 : validRep representative_4081 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4081)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4082 : validRep representative_4082 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4082)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4083 : validRep representative_4083 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4083)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4084 : validRep representative_4084 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4084)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4085 : validRep representative_4085 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4085)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4086 : validRep representative_4086 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4086)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4087 : validRep representative_4087 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4087)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4088 : validRep representative_4088 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4088)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4089 : validRep representative_4089 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4089)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4090 : validRep representative_4090 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4090)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4091 : validRep representative_4091 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4091)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4092 : validRep representative_4092 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4092)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4093 : validRep representative_4093 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4093)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4094 : validRep representative_4094 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4094)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4095 : validRep representative_4095 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4095)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_063 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 4064 (QuarticIntegerRepresentativeTree.Tree.branch 4048 (QuarticIntegerRepresentativeTree.Tree.branch 4040 (QuarticIntegerRepresentativeTree.Tree.branch 4036 (QuarticIntegerRepresentativeTree.Tree.branch 4034 (QuarticIntegerRepresentativeTree.Tree.branch 4033 (QuarticIntegerRepresentativeTree.Tree.leaf 4032 representative_4032) (QuarticIntegerRepresentativeTree.Tree.leaf 4033 representative_4033)) (QuarticIntegerRepresentativeTree.Tree.branch 4035 (QuarticIntegerRepresentativeTree.Tree.leaf 4034 representative_4034) (QuarticIntegerRepresentativeTree.Tree.leaf 4035 representative_4035))) (QuarticIntegerRepresentativeTree.Tree.branch 4038 (QuarticIntegerRepresentativeTree.Tree.branch 4037 (QuarticIntegerRepresentativeTree.Tree.leaf 4036 representative_4036) (QuarticIntegerRepresentativeTree.Tree.leaf 4037 representative_4037)) (QuarticIntegerRepresentativeTree.Tree.branch 4039 (QuarticIntegerRepresentativeTree.Tree.leaf 4038 representative_4038) (QuarticIntegerRepresentativeTree.Tree.leaf 4039 representative_4039)))) (QuarticIntegerRepresentativeTree.Tree.branch 4044 (QuarticIntegerRepresentativeTree.Tree.branch 4042 (QuarticIntegerRepresentativeTree.Tree.branch 4041 (QuarticIntegerRepresentativeTree.Tree.leaf 4040 representative_4040) (QuarticIntegerRepresentativeTree.Tree.leaf 4041 representative_4041)) (QuarticIntegerRepresentativeTree.Tree.branch 4043 (QuarticIntegerRepresentativeTree.Tree.leaf 4042 representative_4042) (QuarticIntegerRepresentativeTree.Tree.leaf 4043 representative_4043))) (QuarticIntegerRepresentativeTree.Tree.branch 4046 (QuarticIntegerRepresentativeTree.Tree.branch 4045 (QuarticIntegerRepresentativeTree.Tree.leaf 4044 representative_4044) (QuarticIntegerRepresentativeTree.Tree.leaf 4045 representative_4045)) (QuarticIntegerRepresentativeTree.Tree.branch 4047 (QuarticIntegerRepresentativeTree.Tree.leaf 4046 representative_4046) (QuarticIntegerRepresentativeTree.Tree.leaf 4047 representative_4047))))) (QuarticIntegerRepresentativeTree.Tree.branch 4056 (QuarticIntegerRepresentativeTree.Tree.branch 4052 (QuarticIntegerRepresentativeTree.Tree.branch 4050 (QuarticIntegerRepresentativeTree.Tree.branch 4049 (QuarticIntegerRepresentativeTree.Tree.leaf 4048 representative_4048) (QuarticIntegerRepresentativeTree.Tree.leaf 4049 representative_4049)) (QuarticIntegerRepresentativeTree.Tree.branch 4051 (QuarticIntegerRepresentativeTree.Tree.leaf 4050 representative_4050) (QuarticIntegerRepresentativeTree.Tree.leaf 4051 representative_4051))) (QuarticIntegerRepresentativeTree.Tree.branch 4054 (QuarticIntegerRepresentativeTree.Tree.branch 4053 (QuarticIntegerRepresentativeTree.Tree.leaf 4052 representative_4052) (QuarticIntegerRepresentativeTree.Tree.leaf 4053 representative_4053)) (QuarticIntegerRepresentativeTree.Tree.branch 4055 (QuarticIntegerRepresentativeTree.Tree.leaf 4054 representative_4054) (QuarticIntegerRepresentativeTree.Tree.leaf 4055 representative_4055)))) (QuarticIntegerRepresentativeTree.Tree.branch 4060 (QuarticIntegerRepresentativeTree.Tree.branch 4058 (QuarticIntegerRepresentativeTree.Tree.branch 4057 (QuarticIntegerRepresentativeTree.Tree.leaf 4056 representative_4056) (QuarticIntegerRepresentativeTree.Tree.leaf 4057 representative_4057)) (QuarticIntegerRepresentativeTree.Tree.branch 4059 (QuarticIntegerRepresentativeTree.Tree.leaf 4058 representative_4058) (QuarticIntegerRepresentativeTree.Tree.leaf 4059 representative_4059))) (QuarticIntegerRepresentativeTree.Tree.branch 4062 (QuarticIntegerRepresentativeTree.Tree.branch 4061 (QuarticIntegerRepresentativeTree.Tree.leaf 4060 representative_4060) (QuarticIntegerRepresentativeTree.Tree.leaf 4061 representative_4061)) (QuarticIntegerRepresentativeTree.Tree.branch 4063 (QuarticIntegerRepresentativeTree.Tree.leaf 4062 representative_4062) (QuarticIntegerRepresentativeTree.Tree.leaf 4063 representative_4063)))))) (QuarticIntegerRepresentativeTree.Tree.branch 4080 (QuarticIntegerRepresentativeTree.Tree.branch 4072 (QuarticIntegerRepresentativeTree.Tree.branch 4068 (QuarticIntegerRepresentativeTree.Tree.branch 4066 (QuarticIntegerRepresentativeTree.Tree.branch 4065 (QuarticIntegerRepresentativeTree.Tree.leaf 4064 representative_4064) (QuarticIntegerRepresentativeTree.Tree.leaf 4065 representative_4065)) (QuarticIntegerRepresentativeTree.Tree.branch 4067 (QuarticIntegerRepresentativeTree.Tree.leaf 4066 representative_4066) (QuarticIntegerRepresentativeTree.Tree.leaf 4067 representative_4067))) (QuarticIntegerRepresentativeTree.Tree.branch 4070 (QuarticIntegerRepresentativeTree.Tree.branch 4069 (QuarticIntegerRepresentativeTree.Tree.leaf 4068 representative_4068) (QuarticIntegerRepresentativeTree.Tree.leaf 4069 representative_4069)) (QuarticIntegerRepresentativeTree.Tree.branch 4071 (QuarticIntegerRepresentativeTree.Tree.leaf 4070 representative_4070) (QuarticIntegerRepresentativeTree.Tree.leaf 4071 representative_4071)))) (QuarticIntegerRepresentativeTree.Tree.branch 4076 (QuarticIntegerRepresentativeTree.Tree.branch 4074 (QuarticIntegerRepresentativeTree.Tree.branch 4073 (QuarticIntegerRepresentativeTree.Tree.leaf 4072 representative_4072) (QuarticIntegerRepresentativeTree.Tree.leaf 4073 representative_4073)) (QuarticIntegerRepresentativeTree.Tree.branch 4075 (QuarticIntegerRepresentativeTree.Tree.leaf 4074 representative_4074) (QuarticIntegerRepresentativeTree.Tree.leaf 4075 representative_4075))) (QuarticIntegerRepresentativeTree.Tree.branch 4078 (QuarticIntegerRepresentativeTree.Tree.branch 4077 (QuarticIntegerRepresentativeTree.Tree.leaf 4076 representative_4076) (QuarticIntegerRepresentativeTree.Tree.leaf 4077 representative_4077)) (QuarticIntegerRepresentativeTree.Tree.branch 4079 (QuarticIntegerRepresentativeTree.Tree.leaf 4078 representative_4078) (QuarticIntegerRepresentativeTree.Tree.leaf 4079 representative_4079))))) (QuarticIntegerRepresentativeTree.Tree.branch 4088 (QuarticIntegerRepresentativeTree.Tree.branch 4084 (QuarticIntegerRepresentativeTree.Tree.branch 4082 (QuarticIntegerRepresentativeTree.Tree.branch 4081 (QuarticIntegerRepresentativeTree.Tree.leaf 4080 representative_4080) (QuarticIntegerRepresentativeTree.Tree.leaf 4081 representative_4081)) (QuarticIntegerRepresentativeTree.Tree.branch 4083 (QuarticIntegerRepresentativeTree.Tree.leaf 4082 representative_4082) (QuarticIntegerRepresentativeTree.Tree.leaf 4083 representative_4083))) (QuarticIntegerRepresentativeTree.Tree.branch 4086 (QuarticIntegerRepresentativeTree.Tree.branch 4085 (QuarticIntegerRepresentativeTree.Tree.leaf 4084 representative_4084) (QuarticIntegerRepresentativeTree.Tree.leaf 4085 representative_4085)) (QuarticIntegerRepresentativeTree.Tree.branch 4087 (QuarticIntegerRepresentativeTree.Tree.leaf 4086 representative_4086) (QuarticIntegerRepresentativeTree.Tree.leaf 4087 representative_4087)))) (QuarticIntegerRepresentativeTree.Tree.branch 4092 (QuarticIntegerRepresentativeTree.Tree.branch 4090 (QuarticIntegerRepresentativeTree.Tree.branch 4089 (QuarticIntegerRepresentativeTree.Tree.leaf 4088 representative_4088) (QuarticIntegerRepresentativeTree.Tree.leaf 4089 representative_4089)) (QuarticIntegerRepresentativeTree.Tree.branch 4091 (QuarticIntegerRepresentativeTree.Tree.leaf 4090 representative_4090) (QuarticIntegerRepresentativeTree.Tree.leaf 4091 representative_4091))) (QuarticIntegerRepresentativeTree.Tree.branch 4094 (QuarticIntegerRepresentativeTree.Tree.branch 4093 (QuarticIntegerRepresentativeTree.Tree.leaf 4092 representative_4092) (QuarticIntegerRepresentativeTree.Tree.leaf 4093 representative_4093)) (QuarticIntegerRepresentativeTree.Tree.branch 4095 (QuarticIntegerRepresentativeTree.Tree.leaf 4094 representative_4094) (QuarticIntegerRepresentativeTree.Tree.leaf 4095 representative_4095)))))))
theorem accepted_063 : All validRep tree_063 := ⟨⟨⟨⟨⟨⟨coefficient_4032,coefficient_4033⟩,⟨coefficient_4034,coefficient_4035⟩⟩,⟨⟨coefficient_4036,coefficient_4037⟩,⟨coefficient_4038,coefficient_4039⟩⟩⟩,⟨⟨⟨coefficient_4040,coefficient_4041⟩,⟨coefficient_4042,coefficient_4043⟩⟩,⟨⟨coefficient_4044,coefficient_4045⟩,⟨coefficient_4046,coefficient_4047⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4048,coefficient_4049⟩,⟨coefficient_4050,coefficient_4051⟩⟩,⟨⟨coefficient_4052,coefficient_4053⟩,⟨coefficient_4054,coefficient_4055⟩⟩⟩,⟨⟨⟨coefficient_4056,coefficient_4057⟩,⟨coefficient_4058,coefficient_4059⟩⟩,⟨⟨coefficient_4060,coefficient_4061⟩,⟨coefficient_4062,coefficient_4063⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_4064,coefficient_4065⟩,⟨coefficient_4066,coefficient_4067⟩⟩,⟨⟨coefficient_4068,coefficient_4069⟩,⟨coefficient_4070,coefficient_4071⟩⟩⟩,⟨⟨⟨coefficient_4072,coefficient_4073⟩,⟨coefficient_4074,coefficient_4075⟩⟩,⟨⟨coefficient_4076,coefficient_4077⟩,⟨coefficient_4078,coefficient_4079⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4080,coefficient_4081⟩,⟨coefficient_4082,coefficient_4083⟩⟩,⟨⟨coefficient_4084,coefficient_4085⟩,⟨coefficient_4086,coefficient_4087⟩⟩⟩,⟨⟨⟨coefficient_4088,coefficient_4089⟩,⟨coefficient_4090,coefficient_4091⟩⟩,⟨⟨coefficient_4092,coefficient_4093⟩,⟨coefficient_4094,coefficient_4095⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

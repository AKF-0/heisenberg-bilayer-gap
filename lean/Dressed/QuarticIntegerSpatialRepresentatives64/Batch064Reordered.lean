import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_4096 : Rep := ⟨![0,27,2,46],462⟩
def representative_4097 : Rep := ⟨![0,27,2,47],462⟩
def representative_4098 : Rep := ⟨![0,27,3,24],462⟩
def representative_4099 : Rep := ⟨![0,27,3,30],462⟩
def representative_4100 : Rep := ⟨![0,27,3,31],462⟩
def representative_4101 : Rep := ⟨![0,27,3,38],462⟩
def representative_4102 : Rep := ⟨![0,27,3,39],462⟩
def representative_4103 : Rep := ⟨![0,27,3,46],462⟩
def representative_4104 : Rep := ⟨![0,27,4,31],462⟩
def representative_4105 : Rep := ⟨![0,27,4,32],462⟩
def representative_4106 : Rep := ⟨![0,27,4,33],462⟩
def representative_4107 : Rep := ⟨![0,27,4,39],462⟩
def representative_4108 : Rep := ⟨![0,27,4,40],462⟩
def representative_4109 : Rep := ⟨![0,27,4,41],462⟩
def representative_4110 : Rep := ⟨![0,27,4,47],462⟩
def representative_4111 : Rep := ⟨![0,27,5,33],462⟩
def representative_4112 : Rep := ⟨![0,27,5,34],462⟩
def representative_4113 : Rep := ⟨![0,27,5,41],462⟩
def representative_4114 : Rep := ⟨![0,27,5,42],462⟩
def representative_4115 : Rep := ⟨![0,27,6,33],462⟩
def representative_4116 : Rep := ⟨![0,27,6,34],462⟩
def representative_4117 : Rep := ⟨![0,27,6,35],462⟩
def representative_4118 : Rep := ⟨![0,27,6,42],462⟩
def representative_4119 : Rep := ⟨![0,27,6,43],462⟩
def representative_4120 : Rep := ⟨![0,27,7,28],462⟩
def representative_4121 : Rep := ⟨![0,27,7,34],462⟩
def representative_4122 : Rep := ⟨![0,27,7,35],462⟩
def representative_4123 : Rep := ⟨![0,27,7,36],462⟩
def representative_4124 : Rep := ⟨![0,27,7,44],462⟩
def representative_4125 : Rep := ⟨![0,27,9,36],462⟩
def representative_4126 : Rep := ⟨![0,27,9,37],462⟩
def representative_4127 : Rep := ⟨![0,27,9,38],462⟩
def representative_4128 : Rep := ⟨![0,27,9,45],462⟩
def representative_4129 : Rep := ⟨![0,27,9,46],462⟩
def representative_4130 : Rep := ⟨![0,27,9,54],462⟩
def representative_4131 : Rep := ⟨![0,27,10,37],462⟩
def representative_4132 : Rep := ⟨![0,27,10,38],462⟩
def representative_4133 : Rep := ⟨![0,27,10,39],462⟩
def representative_4134 : Rep := ⟨![0,27,10,45],462⟩
def representative_4135 : Rep := ⟨![0,27,10,46],462⟩
def representative_4136 : Rep := ⟨![0,27,10,53],462⟩
def representative_4137 : Rep := ⟨![0,27,12,39],462⟩
def representative_4138 : Rep := ⟨![0,27,12,41],462⟩
def representative_4139 : Rep := ⟨![0,27,12,47],462⟩
def representative_4140 : Rep := ⟨![0,27,12,49],462⟩
def representative_4141 : Rep := ⟨![0,27,12,55],462⟩
def representative_4142 : Rep := ⟨![0,27,13,41],462⟩
def representative_4143 : Rep := ⟨![0,27,13,42],462⟩
def representative_4144 : Rep := ⟨![0,27,13,49],462⟩
def representative_4145 : Rep := ⟨![0,27,13,50],462⟩
def representative_4146 : Rep := ⟨![0,27,14,34],462⟩
def representative_4147 : Rep := ⟨![0,27,14,42],462⟩
def representative_4148 : Rep := ⟨![0,27,15,34],462⟩
def representative_4149 : Rep := ⟨![0,27,15,36],462⟩
def representative_4150 : Rep := ⟨![0,27,15,44],462⟩
def representative_4151 : Rep := ⟨![0,27,15,52],462⟩
def representative_4152 : Rep := ⟨![0,27,36,63],462⟩
def representative_4153 : Rep := ⟨![0,27,39,60],462⟩
def representative_4154 : Rep := ⟨![0,28,1,29],462⟩
def representative_4155 : Rep := ⟨![0,28,1,36],462⟩
def representative_4156 : Rep := ⟨![0,28,1,37],462⟩
def representative_4157 : Rep := ⟨![0,28,1,38],462⟩
def representative_4158 : Rep := ⟨![0,28,1,45],462⟩
def representative_4159 : Rep := ⟨![0,28,2,30],462⟩
theorem coefficient_4096 : validRep representative_4096 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4096)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4097 : validRep representative_4097 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4097)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4098 : validRep representative_4098 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4098)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4099 : validRep representative_4099 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4099)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4100 : validRep representative_4100 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4100)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4101 : validRep representative_4101 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4101)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4102 : validRep representative_4102 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4102)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4103 : validRep representative_4103 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4103)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4104 : validRep representative_4104 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4104)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4105 : validRep representative_4105 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4105)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4106 : validRep representative_4106 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4106)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4107 : validRep representative_4107 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4107)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4108 : validRep representative_4108 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4108)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4109 : validRep representative_4109 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4109)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4110 : validRep representative_4110 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4110)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4111 : validRep representative_4111 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4111)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4112 : validRep representative_4112 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4112)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4113 : validRep representative_4113 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4113)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4114 : validRep representative_4114 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4114)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4115 : validRep representative_4115 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4115)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4116 : validRep representative_4116 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4116)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4117 : validRep representative_4117 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4117)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4118 : validRep representative_4118 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4118)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4119 : validRep representative_4119 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4119)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4120 : validRep representative_4120 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4120)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4121 : validRep representative_4121 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4121)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4122 : validRep representative_4122 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4122)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4123 : validRep representative_4123 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4123)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4124 : validRep representative_4124 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4124)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4125 : validRep representative_4125 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4125)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4126 : validRep representative_4126 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4126)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4127 : validRep representative_4127 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4127)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4128 : validRep representative_4128 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4128)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4129 : validRep representative_4129 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4129)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4130 : validRep representative_4130 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4130)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4131 : validRep representative_4131 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4131)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4132 : validRep representative_4132 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4132)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4133 : validRep representative_4133 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4133)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4134 : validRep representative_4134 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4134)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4135 : validRep representative_4135 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4135)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4136 : validRep representative_4136 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4136)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4137 : validRep representative_4137 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4137)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4138 : validRep representative_4138 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4138)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4139 : validRep representative_4139 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4139)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4140 : validRep representative_4140 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4140)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4141 : validRep representative_4141 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4141)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4142 : validRep representative_4142 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4142)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4143 : validRep representative_4143 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4143)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4144 : validRep representative_4144 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4144)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4145 : validRep representative_4145 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4145)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4146 : validRep representative_4146 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4146)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4147 : validRep representative_4147 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4147)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4148 : validRep representative_4148 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4148)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4149 : validRep representative_4149 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4149)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4150 : validRep representative_4150 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4150)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4151 : validRep representative_4151 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4151)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4152 : validRep representative_4152 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4152)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4153 : validRep representative_4153 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4153)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4154 : validRep representative_4154 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4154)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4155 : validRep representative_4155 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4155)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4156 : validRep representative_4156 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4156)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4157 : validRep representative_4157 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4157)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4158 : validRep representative_4158 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4158)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4159 : validRep representative_4159 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4159)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_064 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 4128 (QuarticIntegerRepresentativeTree.Tree.branch 4112 (QuarticIntegerRepresentativeTree.Tree.branch 4104 (QuarticIntegerRepresentativeTree.Tree.branch 4100 (QuarticIntegerRepresentativeTree.Tree.branch 4098 (QuarticIntegerRepresentativeTree.Tree.branch 4097 (QuarticIntegerRepresentativeTree.Tree.leaf 4096 representative_4096) (QuarticIntegerRepresentativeTree.Tree.leaf 4097 representative_4097)) (QuarticIntegerRepresentativeTree.Tree.branch 4099 (QuarticIntegerRepresentativeTree.Tree.leaf 4098 representative_4098) (QuarticIntegerRepresentativeTree.Tree.leaf 4099 representative_4099))) (QuarticIntegerRepresentativeTree.Tree.branch 4102 (QuarticIntegerRepresentativeTree.Tree.branch 4101 (QuarticIntegerRepresentativeTree.Tree.leaf 4100 representative_4100) (QuarticIntegerRepresentativeTree.Tree.leaf 4101 representative_4101)) (QuarticIntegerRepresentativeTree.Tree.branch 4103 (QuarticIntegerRepresentativeTree.Tree.leaf 4102 representative_4102) (QuarticIntegerRepresentativeTree.Tree.leaf 4103 representative_4103)))) (QuarticIntegerRepresentativeTree.Tree.branch 4108 (QuarticIntegerRepresentativeTree.Tree.branch 4106 (QuarticIntegerRepresentativeTree.Tree.branch 4105 (QuarticIntegerRepresentativeTree.Tree.leaf 4104 representative_4104) (QuarticIntegerRepresentativeTree.Tree.leaf 4105 representative_4105)) (QuarticIntegerRepresentativeTree.Tree.branch 4107 (QuarticIntegerRepresentativeTree.Tree.leaf 4106 representative_4106) (QuarticIntegerRepresentativeTree.Tree.leaf 4107 representative_4107))) (QuarticIntegerRepresentativeTree.Tree.branch 4110 (QuarticIntegerRepresentativeTree.Tree.branch 4109 (QuarticIntegerRepresentativeTree.Tree.leaf 4108 representative_4108) (QuarticIntegerRepresentativeTree.Tree.leaf 4109 representative_4109)) (QuarticIntegerRepresentativeTree.Tree.branch 4111 (QuarticIntegerRepresentativeTree.Tree.leaf 4110 representative_4110) (QuarticIntegerRepresentativeTree.Tree.leaf 4111 representative_4111))))) (QuarticIntegerRepresentativeTree.Tree.branch 4120 (QuarticIntegerRepresentativeTree.Tree.branch 4116 (QuarticIntegerRepresentativeTree.Tree.branch 4114 (QuarticIntegerRepresentativeTree.Tree.branch 4113 (QuarticIntegerRepresentativeTree.Tree.leaf 4112 representative_4112) (QuarticIntegerRepresentativeTree.Tree.leaf 4113 representative_4113)) (QuarticIntegerRepresentativeTree.Tree.branch 4115 (QuarticIntegerRepresentativeTree.Tree.leaf 4114 representative_4114) (QuarticIntegerRepresentativeTree.Tree.leaf 4115 representative_4115))) (QuarticIntegerRepresentativeTree.Tree.branch 4118 (QuarticIntegerRepresentativeTree.Tree.branch 4117 (QuarticIntegerRepresentativeTree.Tree.leaf 4116 representative_4116) (QuarticIntegerRepresentativeTree.Tree.leaf 4117 representative_4117)) (QuarticIntegerRepresentativeTree.Tree.branch 4119 (QuarticIntegerRepresentativeTree.Tree.leaf 4118 representative_4118) (QuarticIntegerRepresentativeTree.Tree.leaf 4119 representative_4119)))) (QuarticIntegerRepresentativeTree.Tree.branch 4124 (QuarticIntegerRepresentativeTree.Tree.branch 4122 (QuarticIntegerRepresentativeTree.Tree.branch 4121 (QuarticIntegerRepresentativeTree.Tree.leaf 4120 representative_4120) (QuarticIntegerRepresentativeTree.Tree.leaf 4121 representative_4121)) (QuarticIntegerRepresentativeTree.Tree.branch 4123 (QuarticIntegerRepresentativeTree.Tree.leaf 4122 representative_4122) (QuarticIntegerRepresentativeTree.Tree.leaf 4123 representative_4123))) (QuarticIntegerRepresentativeTree.Tree.branch 4126 (QuarticIntegerRepresentativeTree.Tree.branch 4125 (QuarticIntegerRepresentativeTree.Tree.leaf 4124 representative_4124) (QuarticIntegerRepresentativeTree.Tree.leaf 4125 representative_4125)) (QuarticIntegerRepresentativeTree.Tree.branch 4127 (QuarticIntegerRepresentativeTree.Tree.leaf 4126 representative_4126) (QuarticIntegerRepresentativeTree.Tree.leaf 4127 representative_4127)))))) (QuarticIntegerRepresentativeTree.Tree.branch 4144 (QuarticIntegerRepresentativeTree.Tree.branch 4136 (QuarticIntegerRepresentativeTree.Tree.branch 4132 (QuarticIntegerRepresentativeTree.Tree.branch 4130 (QuarticIntegerRepresentativeTree.Tree.branch 4129 (QuarticIntegerRepresentativeTree.Tree.leaf 4128 representative_4128) (QuarticIntegerRepresentativeTree.Tree.leaf 4129 representative_4129)) (QuarticIntegerRepresentativeTree.Tree.branch 4131 (QuarticIntegerRepresentativeTree.Tree.leaf 4130 representative_4130) (QuarticIntegerRepresentativeTree.Tree.leaf 4131 representative_4131))) (QuarticIntegerRepresentativeTree.Tree.branch 4134 (QuarticIntegerRepresentativeTree.Tree.branch 4133 (QuarticIntegerRepresentativeTree.Tree.leaf 4132 representative_4132) (QuarticIntegerRepresentativeTree.Tree.leaf 4133 representative_4133)) (QuarticIntegerRepresentativeTree.Tree.branch 4135 (QuarticIntegerRepresentativeTree.Tree.leaf 4134 representative_4134) (QuarticIntegerRepresentativeTree.Tree.leaf 4135 representative_4135)))) (QuarticIntegerRepresentativeTree.Tree.branch 4140 (QuarticIntegerRepresentativeTree.Tree.branch 4138 (QuarticIntegerRepresentativeTree.Tree.branch 4137 (QuarticIntegerRepresentativeTree.Tree.leaf 4136 representative_4136) (QuarticIntegerRepresentativeTree.Tree.leaf 4137 representative_4137)) (QuarticIntegerRepresentativeTree.Tree.branch 4139 (QuarticIntegerRepresentativeTree.Tree.leaf 4138 representative_4138) (QuarticIntegerRepresentativeTree.Tree.leaf 4139 representative_4139))) (QuarticIntegerRepresentativeTree.Tree.branch 4142 (QuarticIntegerRepresentativeTree.Tree.branch 4141 (QuarticIntegerRepresentativeTree.Tree.leaf 4140 representative_4140) (QuarticIntegerRepresentativeTree.Tree.leaf 4141 representative_4141)) (QuarticIntegerRepresentativeTree.Tree.branch 4143 (QuarticIntegerRepresentativeTree.Tree.leaf 4142 representative_4142) (QuarticIntegerRepresentativeTree.Tree.leaf 4143 representative_4143))))) (QuarticIntegerRepresentativeTree.Tree.branch 4152 (QuarticIntegerRepresentativeTree.Tree.branch 4148 (QuarticIntegerRepresentativeTree.Tree.branch 4146 (QuarticIntegerRepresentativeTree.Tree.branch 4145 (QuarticIntegerRepresentativeTree.Tree.leaf 4144 representative_4144) (QuarticIntegerRepresentativeTree.Tree.leaf 4145 representative_4145)) (QuarticIntegerRepresentativeTree.Tree.branch 4147 (QuarticIntegerRepresentativeTree.Tree.leaf 4146 representative_4146) (QuarticIntegerRepresentativeTree.Tree.leaf 4147 representative_4147))) (QuarticIntegerRepresentativeTree.Tree.branch 4150 (QuarticIntegerRepresentativeTree.Tree.branch 4149 (QuarticIntegerRepresentativeTree.Tree.leaf 4148 representative_4148) (QuarticIntegerRepresentativeTree.Tree.leaf 4149 representative_4149)) (QuarticIntegerRepresentativeTree.Tree.branch 4151 (QuarticIntegerRepresentativeTree.Tree.leaf 4150 representative_4150) (QuarticIntegerRepresentativeTree.Tree.leaf 4151 representative_4151)))) (QuarticIntegerRepresentativeTree.Tree.branch 4156 (QuarticIntegerRepresentativeTree.Tree.branch 4154 (QuarticIntegerRepresentativeTree.Tree.branch 4153 (QuarticIntegerRepresentativeTree.Tree.leaf 4152 representative_4152) (QuarticIntegerRepresentativeTree.Tree.leaf 4153 representative_4153)) (QuarticIntegerRepresentativeTree.Tree.branch 4155 (QuarticIntegerRepresentativeTree.Tree.leaf 4154 representative_4154) (QuarticIntegerRepresentativeTree.Tree.leaf 4155 representative_4155))) (QuarticIntegerRepresentativeTree.Tree.branch 4158 (QuarticIntegerRepresentativeTree.Tree.branch 4157 (QuarticIntegerRepresentativeTree.Tree.leaf 4156 representative_4156) (QuarticIntegerRepresentativeTree.Tree.leaf 4157 representative_4157)) (QuarticIntegerRepresentativeTree.Tree.branch 4159 (QuarticIntegerRepresentativeTree.Tree.leaf 4158 representative_4158) (QuarticIntegerRepresentativeTree.Tree.leaf 4159 representative_4159)))))))
theorem accepted_064 : All validRep tree_064 := ⟨⟨⟨⟨⟨⟨coefficient_4096,coefficient_4097⟩,⟨coefficient_4098,coefficient_4099⟩⟩,⟨⟨coefficient_4100,coefficient_4101⟩,⟨coefficient_4102,coefficient_4103⟩⟩⟩,⟨⟨⟨coefficient_4104,coefficient_4105⟩,⟨coefficient_4106,coefficient_4107⟩⟩,⟨⟨coefficient_4108,coefficient_4109⟩,⟨coefficient_4110,coefficient_4111⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4112,coefficient_4113⟩,⟨coefficient_4114,coefficient_4115⟩⟩,⟨⟨coefficient_4116,coefficient_4117⟩,⟨coefficient_4118,coefficient_4119⟩⟩⟩,⟨⟨⟨coefficient_4120,coefficient_4121⟩,⟨coefficient_4122,coefficient_4123⟩⟩,⟨⟨coefficient_4124,coefficient_4125⟩,⟨coefficient_4126,coefficient_4127⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_4128,coefficient_4129⟩,⟨coefficient_4130,coefficient_4131⟩⟩,⟨⟨coefficient_4132,coefficient_4133⟩,⟨coefficient_4134,coefficient_4135⟩⟩⟩,⟨⟨⟨coefficient_4136,coefficient_4137⟩,⟨coefficient_4138,coefficient_4139⟩⟩,⟨⟨coefficient_4140,coefficient_4141⟩,⟨coefficient_4142,coefficient_4143⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4144,coefficient_4145⟩,⟨coefficient_4146,coefficient_4147⟩⟩,⟨⟨coefficient_4148,coefficient_4149⟩,⟨coefficient_4150,coefficient_4151⟩⟩⟩,⟨⟨⟨coefficient_4152,coefficient_4153⟩,⟨coefficient_4154,coefficient_4155⟩⟩,⟨⟨coefficient_4156,coefficient_4157⟩,⟨coefficient_4158,coefficient_4159⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

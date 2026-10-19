import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_4160 : Rep := ⟨![0,28,2,37],462⟩
def representative_4161 : Rep := ⟨![0,28,2,38],462⟩
def representative_4162 : Rep := ⟨![0,28,2,39],462⟩
def representative_4163 : Rep := ⟨![0,28,2,46],462⟩
def representative_4164 : Rep := ⟨![0,28,3,31],462⟩
def representative_4165 : Rep := ⟨![0,28,3,32],462⟩
def representative_4166 : Rep := ⟨![0,28,3,38],462⟩
def representative_4167 : Rep := ⟨![0,28,3,39],462⟩
def representative_4168 : Rep := ⟨![0,28,3,47],462⟩
def representative_4169 : Rep := ⟨![0,28,4,24],462⟩
def representative_4170 : Rep := ⟨![0,28,4,32],462⟩
def representative_4171 : Rep := ⟨![0,28,4,40],462⟩
def representative_4172 : Rep := ⟨![0,28,8,36],462⟩
def representative_4173 : Rep := ⟨![0,28,8,44],462⟩
def representative_4174 : Rep := ⟨![0,28,8,52],462⟩
def representative_4175 : Rep := ⟨![0,28,9,37],462⟩
def representative_4176 : Rep := ⟨![0,28,9,45],462⟩
def representative_4177 : Rep := ⟨![0,28,9,46],462⟩
def representative_4178 : Rep := ⟨![0,28,9,53],462⟩
def representative_4179 : Rep := ⟨![0,28,10,38],462⟩
def representative_4180 : Rep := ⟨![0,28,10,45],462⟩
def representative_4181 : Rep := ⟨![0,28,10,46],462⟩
def representative_4182 : Rep := ⟨![0,28,10,47],462⟩
def representative_4183 : Rep := ⟨![0,28,10,54],462⟩
def representative_4184 : Rep := ⟨![0,28,11,39],462⟩
def representative_4185 : Rep := ⟨![0,28,11,47],462⟩
def representative_4186 : Rep := ⟨![0,28,11,55],462⟩
def representative_4187 : Rep := ⟨![0,28,12,32],462⟩
def representative_4188 : Rep := ⟨![0,28,12,40],462⟩
def representative_4189 : Rep := ⟨![0,28,12,48],462⟩
def representative_4190 : Rep := ⟨![0,28,32,60],462⟩
def representative_4191 : Rep := ⟨![0,28,33,61],462⟩
def representative_4192 : Rep := ⟨![0,28,34,62],462⟩
def representative_4193 : Rep := ⟨![0,28,35,63],462⟩
def representative_4194 : Rep := ⟨![0,28,36,56],462⟩
def representative_4195 : Rep := ⟨![0,36,1,37],462⟩
def representative_4196 : Rep := ⟨![0,36,2,38],462⟩
def representative_4197 : Rep := ⟨![0,36,3,39],462⟩
def representative_4198 : Rep := ⟨![0,36,4,32],462⟩
def representative_4199 : Rep := ⟨![0,36,9,45],462⟩
def representative_4200 : Rep := ⟨![0,36,10,46],462⟩
def representative_4201 : Rep := ⟨![0,36,11,47],462⟩
def representative_4202 : Rep := ⟨![0,36,18,54],462⟩
theorem coefficient_4160 : validRep representative_4160 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4160)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4161 : validRep representative_4161 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4161)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4162 : validRep representative_4162 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4162)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4163 : validRep representative_4163 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4163)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4164 : validRep representative_4164 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4164)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4165 : validRep representative_4165 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4165)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4166 : validRep representative_4166 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4166)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4167 : validRep representative_4167 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4167)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4168 : validRep representative_4168 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4168)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4169 : validRep representative_4169 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4169)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4170 : validRep representative_4170 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4170)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4171 : validRep representative_4171 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4171)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4172 : validRep representative_4172 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4172)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4173 : validRep representative_4173 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4173)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4174 : validRep representative_4174 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4174)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4175 : validRep representative_4175 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4175)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4176 : validRep representative_4176 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4176)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4177 : validRep representative_4177 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4177)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4178 : validRep representative_4178 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4178)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4179 : validRep representative_4179 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4179)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4180 : validRep representative_4180 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4180)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4181 : validRep representative_4181 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4181)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4182 : validRep representative_4182 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4182)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4183 : validRep representative_4183 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4183)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4184 : validRep representative_4184 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4184)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4185 : validRep representative_4185 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4185)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4186 : validRep representative_4186 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4186)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4187 : validRep representative_4187 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4187)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4188 : validRep representative_4188 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4188)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4189 : validRep representative_4189 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4189)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4190 : validRep representative_4190 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4190)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4191 : validRep representative_4191 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4191)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4192 : validRep representative_4192 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4192)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4193 : validRep representative_4193 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4193)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4194 : validRep representative_4194 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4194)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4195 : validRep representative_4195 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4195)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4196 : validRep representative_4196 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4196)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4197 : validRep representative_4197 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4197)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4198 : validRep representative_4198 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4198)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4199 : validRep representative_4199 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4199)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4200 : validRep representative_4200 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4200)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4201 : validRep representative_4201 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4201)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4202 : validRep representative_4202 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4202)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_065 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 4181 (QuarticIntegerRepresentativeTree.Tree.branch 4170 (QuarticIntegerRepresentativeTree.Tree.branch 4165 (QuarticIntegerRepresentativeTree.Tree.branch 4162 (QuarticIntegerRepresentativeTree.Tree.branch 4161 (QuarticIntegerRepresentativeTree.Tree.leaf 4160 representative_4160) (QuarticIntegerRepresentativeTree.Tree.leaf 4161 representative_4161)) (QuarticIntegerRepresentativeTree.Tree.branch 4163 (QuarticIntegerRepresentativeTree.Tree.leaf 4162 representative_4162) (QuarticIntegerRepresentativeTree.Tree.branch 4164 (QuarticIntegerRepresentativeTree.Tree.leaf 4163 representative_4163) (QuarticIntegerRepresentativeTree.Tree.leaf 4164 representative_4164)))) (QuarticIntegerRepresentativeTree.Tree.branch 4167 (QuarticIntegerRepresentativeTree.Tree.branch 4166 (QuarticIntegerRepresentativeTree.Tree.leaf 4165 representative_4165) (QuarticIntegerRepresentativeTree.Tree.leaf 4166 representative_4166)) (QuarticIntegerRepresentativeTree.Tree.branch 4168 (QuarticIntegerRepresentativeTree.Tree.leaf 4167 representative_4167) (QuarticIntegerRepresentativeTree.Tree.branch 4169 (QuarticIntegerRepresentativeTree.Tree.leaf 4168 representative_4168) (QuarticIntegerRepresentativeTree.Tree.leaf 4169 representative_4169))))) (QuarticIntegerRepresentativeTree.Tree.branch 4175 (QuarticIntegerRepresentativeTree.Tree.branch 4172 (QuarticIntegerRepresentativeTree.Tree.branch 4171 (QuarticIntegerRepresentativeTree.Tree.leaf 4170 representative_4170) (QuarticIntegerRepresentativeTree.Tree.leaf 4171 representative_4171)) (QuarticIntegerRepresentativeTree.Tree.branch 4173 (QuarticIntegerRepresentativeTree.Tree.leaf 4172 representative_4172) (QuarticIntegerRepresentativeTree.Tree.branch 4174 (QuarticIntegerRepresentativeTree.Tree.leaf 4173 representative_4173) (QuarticIntegerRepresentativeTree.Tree.leaf 4174 representative_4174)))) (QuarticIntegerRepresentativeTree.Tree.branch 4178 (QuarticIntegerRepresentativeTree.Tree.branch 4176 (QuarticIntegerRepresentativeTree.Tree.leaf 4175 representative_4175) (QuarticIntegerRepresentativeTree.Tree.branch 4177 (QuarticIntegerRepresentativeTree.Tree.leaf 4176 representative_4176) (QuarticIntegerRepresentativeTree.Tree.leaf 4177 representative_4177))) (QuarticIntegerRepresentativeTree.Tree.branch 4179 (QuarticIntegerRepresentativeTree.Tree.leaf 4178 representative_4178) (QuarticIntegerRepresentativeTree.Tree.branch 4180 (QuarticIntegerRepresentativeTree.Tree.leaf 4179 representative_4179) (QuarticIntegerRepresentativeTree.Tree.leaf 4180 representative_4180)))))) (QuarticIntegerRepresentativeTree.Tree.branch 4192 (QuarticIntegerRepresentativeTree.Tree.branch 4186 (QuarticIntegerRepresentativeTree.Tree.branch 4183 (QuarticIntegerRepresentativeTree.Tree.branch 4182 (QuarticIntegerRepresentativeTree.Tree.leaf 4181 representative_4181) (QuarticIntegerRepresentativeTree.Tree.leaf 4182 representative_4182)) (QuarticIntegerRepresentativeTree.Tree.branch 4184 (QuarticIntegerRepresentativeTree.Tree.leaf 4183 representative_4183) (QuarticIntegerRepresentativeTree.Tree.branch 4185 (QuarticIntegerRepresentativeTree.Tree.leaf 4184 representative_4184) (QuarticIntegerRepresentativeTree.Tree.leaf 4185 representative_4185)))) (QuarticIntegerRepresentativeTree.Tree.branch 4189 (QuarticIntegerRepresentativeTree.Tree.branch 4187 (QuarticIntegerRepresentativeTree.Tree.leaf 4186 representative_4186) (QuarticIntegerRepresentativeTree.Tree.branch 4188 (QuarticIntegerRepresentativeTree.Tree.leaf 4187 representative_4187) (QuarticIntegerRepresentativeTree.Tree.leaf 4188 representative_4188))) (QuarticIntegerRepresentativeTree.Tree.branch 4190 (QuarticIntegerRepresentativeTree.Tree.leaf 4189 representative_4189) (QuarticIntegerRepresentativeTree.Tree.branch 4191 (QuarticIntegerRepresentativeTree.Tree.leaf 4190 representative_4190) (QuarticIntegerRepresentativeTree.Tree.leaf 4191 representative_4191))))) (QuarticIntegerRepresentativeTree.Tree.branch 4197 (QuarticIntegerRepresentativeTree.Tree.branch 4194 (QuarticIntegerRepresentativeTree.Tree.branch 4193 (QuarticIntegerRepresentativeTree.Tree.leaf 4192 representative_4192) (QuarticIntegerRepresentativeTree.Tree.leaf 4193 representative_4193)) (QuarticIntegerRepresentativeTree.Tree.branch 4195 (QuarticIntegerRepresentativeTree.Tree.leaf 4194 representative_4194) (QuarticIntegerRepresentativeTree.Tree.branch 4196 (QuarticIntegerRepresentativeTree.Tree.leaf 4195 representative_4195) (QuarticIntegerRepresentativeTree.Tree.leaf 4196 representative_4196)))) (QuarticIntegerRepresentativeTree.Tree.branch 4200 (QuarticIntegerRepresentativeTree.Tree.branch 4198 (QuarticIntegerRepresentativeTree.Tree.leaf 4197 representative_4197) (QuarticIntegerRepresentativeTree.Tree.branch 4199 (QuarticIntegerRepresentativeTree.Tree.leaf 4198 representative_4198) (QuarticIntegerRepresentativeTree.Tree.leaf 4199 representative_4199))) (QuarticIntegerRepresentativeTree.Tree.branch 4201 (QuarticIntegerRepresentativeTree.Tree.leaf 4200 representative_4200) (QuarticIntegerRepresentativeTree.Tree.branch 4202 (QuarticIntegerRepresentativeTree.Tree.leaf 4201 representative_4201) (QuarticIntegerRepresentativeTree.Tree.leaf 4202 representative_4202)))))))
theorem accepted_065 : All validRep tree_065 := ⟨⟨⟨⟨⟨coefficient_4160,coefficient_4161⟩,⟨coefficient_4162,⟨coefficient_4163,coefficient_4164⟩⟩⟩,⟨⟨coefficient_4165,coefficient_4166⟩,⟨coefficient_4167,⟨coefficient_4168,coefficient_4169⟩⟩⟩⟩,⟨⟨⟨coefficient_4170,coefficient_4171⟩,⟨coefficient_4172,⟨coefficient_4173,coefficient_4174⟩⟩⟩,⟨⟨coefficient_4175,⟨coefficient_4176,coefficient_4177⟩⟩,⟨coefficient_4178,⟨coefficient_4179,coefficient_4180⟩⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4181,coefficient_4182⟩,⟨coefficient_4183,⟨coefficient_4184,coefficient_4185⟩⟩⟩,⟨⟨coefficient_4186,⟨coefficient_4187,coefficient_4188⟩⟩,⟨coefficient_4189,⟨coefficient_4190,coefficient_4191⟩⟩⟩⟩,⟨⟨⟨coefficient_4192,coefficient_4193⟩,⟨coefficient_4194,⟨coefficient_4195,coefficient_4196⟩⟩⟩,⟨⟨coefficient_4197,⟨coefficient_4198,coefficient_4199⟩⟩,⟨coefficient_4200,⟨coefficient_4201,coefficient_4202⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

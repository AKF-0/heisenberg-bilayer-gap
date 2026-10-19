import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_3968 : Rep := ⟨![0,19,35,54],462⟩
def representative_3969 : Rep := ⟨![0,19,35,55],462⟩
def representative_3970 : Rep := ⟨![0,19,36,55],462⟩
def representative_3971 : Rep := ⟨![0,19,39,52],462⟩
def representative_3972 : Rep := ⟨![0,20,1,21],462⟩
def representative_3973 : Rep := ⟨![0,20,1,28],462⟩
def representative_3974 : Rep := ⟨![0,20,1,29],462⟩
def representative_3975 : Rep := ⟨![0,20,1,30],462⟩
def representative_3976 : Rep := ⟨![0,20,1,35],462⟩
def representative_3977 : Rep := ⟨![0,20,1,36],462⟩
def representative_3978 : Rep := ⟨![0,20,1,37],462⟩
def representative_3979 : Rep := ⟨![0,20,1,38],462⟩
def representative_3980 : Rep := ⟨![0,20,1,39],462⟩
def representative_3981 : Rep := ⟨![0,20,1,44],462⟩
def representative_3982 : Rep := ⟨![0,20,1,45],462⟩
def representative_3983 : Rep := ⟨![0,20,1,46],462⟩
def representative_3984 : Rep := ⟨![0,20,1,53],462⟩
def representative_3985 : Rep := ⟨![0,20,2,22],462⟩
def representative_3986 : Rep := ⟨![0,20,2,29],462⟩
def representative_3987 : Rep := ⟨![0,20,2,30],462⟩
def representative_3988 : Rep := ⟨![0,20,2,31],462⟩
def representative_3989 : Rep := ⟨![0,20,2,32],462⟩
def representative_3990 : Rep := ⟨![0,20,2,36],462⟩
def representative_3991 : Rep := ⟨![0,20,2,37],462⟩
def representative_3992 : Rep := ⟨![0,20,2,38],462⟩
def representative_3993 : Rep := ⟨![0,20,2,39],462⟩
def representative_3994 : Rep := ⟨![0,20,2,45],462⟩
def representative_3995 : Rep := ⟨![0,20,2,46],462⟩
def representative_3996 : Rep := ⟨![0,20,2,47],462⟩
def representative_3997 : Rep := ⟨![0,20,2,54],462⟩
def representative_3998 : Rep := ⟨![0,20,3,23],462⟩
def representative_3999 : Rep := ⟨![0,20,3,24],462⟩
def representative_4000 : Rep := ⟨![0,20,3,30],462⟩
def representative_4001 : Rep := ⟨![0,20,3,31],462⟩
def representative_4002 : Rep := ⟨![0,20,3,32],462⟩
def representative_4003 : Rep := ⟨![0,20,3,33],462⟩
def representative_4004 : Rep := ⟨![0,20,3,37],462⟩
def representative_4005 : Rep := ⟨![0,20,3,38],462⟩
def representative_4006 : Rep := ⟨![0,20,3,39],462⟩
def representative_4007 : Rep := ⟨![0,20,3,40],462⟩
def representative_4008 : Rep := ⟨![0,20,3,46],462⟩
def representative_4009 : Rep := ⟨![0,20,3,47],462⟩
def representative_4010 : Rep := ⟨![0,20,3,55],462⟩
def representative_4011 : Rep := ⟨![0,20,4,16],462⟩
def representative_4012 : Rep := ⟨![0,20,4,24],462⟩
def representative_4013 : Rep := ⟨![0,20,4,25],462⟩
def representative_4014 : Rep := ⟨![0,20,4,32],462⟩
def representative_4015 : Rep := ⟨![0,20,4,33],462⟩
def representative_4016 : Rep := ⟨![0,20,4,40],462⟩
def representative_4017 : Rep := ⟨![0,20,4,41],462⟩
def representative_4018 : Rep := ⟨![0,20,4,48],462⟩
def representative_4019 : Rep := ⟨![0,20,8,28],462⟩
def representative_4020 : Rep := ⟨![0,20,8,35],462⟩
def representative_4021 : Rep := ⟨![0,20,8,36],462⟩
def representative_4022 : Rep := ⟨![0,20,8,43],462⟩
def representative_4023 : Rep := ⟨![0,20,8,44],462⟩
def representative_4024 : Rep := ⟨![0,20,8,51],462⟩
def representative_4025 : Rep := ⟨![0,20,8,52],462⟩
def representative_4026 : Rep := ⟨![0,20,8,60],462⟩
def representative_4027 : Rep := ⟨![0,20,9,29],462⟩
def representative_4028 : Rep := ⟨![0,20,9,36],462⟩
def representative_4029 : Rep := ⟨![0,20,9,37],462⟩
def representative_4030 : Rep := ⟨![0,20,9,38],462⟩
def representative_4031 : Rep := ⟨![0,20,9,43],462⟩
theorem coefficient_3968 : validRep representative_3968 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3968)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3969 : validRep representative_3969 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3969)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3970 : validRep representative_3970 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3970)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3971 : validRep representative_3971 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3971)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3972 : validRep representative_3972 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3972)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3973 : validRep representative_3973 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3973)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3974 : validRep representative_3974 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3974)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3975 : validRep representative_3975 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3975)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3976 : validRep representative_3976 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3976)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3977 : validRep representative_3977 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3977)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3978 : validRep representative_3978 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3978)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3979 : validRep representative_3979 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3979)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3980 : validRep representative_3980 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3980)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3981 : validRep representative_3981 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3981)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3982 : validRep representative_3982 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3982)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3983 : validRep representative_3983 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3983)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3984 : validRep representative_3984 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3984)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3985 : validRep representative_3985 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3985)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3986 : validRep representative_3986 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3986)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3987 : validRep representative_3987 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3987)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3988 : validRep representative_3988 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3988)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3989 : validRep representative_3989 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3989)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3990 : validRep representative_3990 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3990)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3991 : validRep representative_3991 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3991)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3992 : validRep representative_3992 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3992)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3993 : validRep representative_3993 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3993)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3994 : validRep representative_3994 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3994)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3995 : validRep representative_3995 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3995)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3996 : validRep representative_3996 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3996)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3997 : validRep representative_3997 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3997)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3998 : validRep representative_3998 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3998)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3999 : validRep representative_3999 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3999)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4000 : validRep representative_4000 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4000)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4001 : validRep representative_4001 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4001)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4002 : validRep representative_4002 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4002)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4003 : validRep representative_4003 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4003)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4004 : validRep representative_4004 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4004)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4005 : validRep representative_4005 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4005)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4006 : validRep representative_4006 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4006)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4007 : validRep representative_4007 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4007)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4008 : validRep representative_4008 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4008)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4009 : validRep representative_4009 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4009)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4010 : validRep representative_4010 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4010)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4011 : validRep representative_4011 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4011)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4012 : validRep representative_4012 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4012)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4013 : validRep representative_4013 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4013)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4014 : validRep representative_4014 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4014)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4015 : validRep representative_4015 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4015)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4016 : validRep representative_4016 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4016)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4017 : validRep representative_4017 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4017)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4018 : validRep representative_4018 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4018)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4019 : validRep representative_4019 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4019)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4020 : validRep representative_4020 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4020)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4021 : validRep representative_4021 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4021)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4022 : validRep representative_4022 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4022)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4023 : validRep representative_4023 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4023)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4024 : validRep representative_4024 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4024)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4025 : validRep representative_4025 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4025)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4026 : validRep representative_4026 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4026)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4027 : validRep representative_4027 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4027)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4028 : validRep representative_4028 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4028)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4029 : validRep representative_4029 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4029)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4030 : validRep representative_4030 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4030)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_4031 : validRep representative_4031 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4031)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_062 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 4000 (QuarticIntegerRepresentativeTree.Tree.branch 3984 (QuarticIntegerRepresentativeTree.Tree.branch 3976 (QuarticIntegerRepresentativeTree.Tree.branch 3972 (QuarticIntegerRepresentativeTree.Tree.branch 3970 (QuarticIntegerRepresentativeTree.Tree.branch 3969 (QuarticIntegerRepresentativeTree.Tree.leaf 3968 representative_3968) (QuarticIntegerRepresentativeTree.Tree.leaf 3969 representative_3969)) (QuarticIntegerRepresentativeTree.Tree.branch 3971 (QuarticIntegerRepresentativeTree.Tree.leaf 3970 representative_3970) (QuarticIntegerRepresentativeTree.Tree.leaf 3971 representative_3971))) (QuarticIntegerRepresentativeTree.Tree.branch 3974 (QuarticIntegerRepresentativeTree.Tree.branch 3973 (QuarticIntegerRepresentativeTree.Tree.leaf 3972 representative_3972) (QuarticIntegerRepresentativeTree.Tree.leaf 3973 representative_3973)) (QuarticIntegerRepresentativeTree.Tree.branch 3975 (QuarticIntegerRepresentativeTree.Tree.leaf 3974 representative_3974) (QuarticIntegerRepresentativeTree.Tree.leaf 3975 representative_3975)))) (QuarticIntegerRepresentativeTree.Tree.branch 3980 (QuarticIntegerRepresentativeTree.Tree.branch 3978 (QuarticIntegerRepresentativeTree.Tree.branch 3977 (QuarticIntegerRepresentativeTree.Tree.leaf 3976 representative_3976) (QuarticIntegerRepresentativeTree.Tree.leaf 3977 representative_3977)) (QuarticIntegerRepresentativeTree.Tree.branch 3979 (QuarticIntegerRepresentativeTree.Tree.leaf 3978 representative_3978) (QuarticIntegerRepresentativeTree.Tree.leaf 3979 representative_3979))) (QuarticIntegerRepresentativeTree.Tree.branch 3982 (QuarticIntegerRepresentativeTree.Tree.branch 3981 (QuarticIntegerRepresentativeTree.Tree.leaf 3980 representative_3980) (QuarticIntegerRepresentativeTree.Tree.leaf 3981 representative_3981)) (QuarticIntegerRepresentativeTree.Tree.branch 3983 (QuarticIntegerRepresentativeTree.Tree.leaf 3982 representative_3982) (QuarticIntegerRepresentativeTree.Tree.leaf 3983 representative_3983))))) (QuarticIntegerRepresentativeTree.Tree.branch 3992 (QuarticIntegerRepresentativeTree.Tree.branch 3988 (QuarticIntegerRepresentativeTree.Tree.branch 3986 (QuarticIntegerRepresentativeTree.Tree.branch 3985 (QuarticIntegerRepresentativeTree.Tree.leaf 3984 representative_3984) (QuarticIntegerRepresentativeTree.Tree.leaf 3985 representative_3985)) (QuarticIntegerRepresentativeTree.Tree.branch 3987 (QuarticIntegerRepresentativeTree.Tree.leaf 3986 representative_3986) (QuarticIntegerRepresentativeTree.Tree.leaf 3987 representative_3987))) (QuarticIntegerRepresentativeTree.Tree.branch 3990 (QuarticIntegerRepresentativeTree.Tree.branch 3989 (QuarticIntegerRepresentativeTree.Tree.leaf 3988 representative_3988) (QuarticIntegerRepresentativeTree.Tree.leaf 3989 representative_3989)) (QuarticIntegerRepresentativeTree.Tree.branch 3991 (QuarticIntegerRepresentativeTree.Tree.leaf 3990 representative_3990) (QuarticIntegerRepresentativeTree.Tree.leaf 3991 representative_3991)))) (QuarticIntegerRepresentativeTree.Tree.branch 3996 (QuarticIntegerRepresentativeTree.Tree.branch 3994 (QuarticIntegerRepresentativeTree.Tree.branch 3993 (QuarticIntegerRepresentativeTree.Tree.leaf 3992 representative_3992) (QuarticIntegerRepresentativeTree.Tree.leaf 3993 representative_3993)) (QuarticIntegerRepresentativeTree.Tree.branch 3995 (QuarticIntegerRepresentativeTree.Tree.leaf 3994 representative_3994) (QuarticIntegerRepresentativeTree.Tree.leaf 3995 representative_3995))) (QuarticIntegerRepresentativeTree.Tree.branch 3998 (QuarticIntegerRepresentativeTree.Tree.branch 3997 (QuarticIntegerRepresentativeTree.Tree.leaf 3996 representative_3996) (QuarticIntegerRepresentativeTree.Tree.leaf 3997 representative_3997)) (QuarticIntegerRepresentativeTree.Tree.branch 3999 (QuarticIntegerRepresentativeTree.Tree.leaf 3998 representative_3998) (QuarticIntegerRepresentativeTree.Tree.leaf 3999 representative_3999)))))) (QuarticIntegerRepresentativeTree.Tree.branch 4016 (QuarticIntegerRepresentativeTree.Tree.branch 4008 (QuarticIntegerRepresentativeTree.Tree.branch 4004 (QuarticIntegerRepresentativeTree.Tree.branch 4002 (QuarticIntegerRepresentativeTree.Tree.branch 4001 (QuarticIntegerRepresentativeTree.Tree.leaf 4000 representative_4000) (QuarticIntegerRepresentativeTree.Tree.leaf 4001 representative_4001)) (QuarticIntegerRepresentativeTree.Tree.branch 4003 (QuarticIntegerRepresentativeTree.Tree.leaf 4002 representative_4002) (QuarticIntegerRepresentativeTree.Tree.leaf 4003 representative_4003))) (QuarticIntegerRepresentativeTree.Tree.branch 4006 (QuarticIntegerRepresentativeTree.Tree.branch 4005 (QuarticIntegerRepresentativeTree.Tree.leaf 4004 representative_4004) (QuarticIntegerRepresentativeTree.Tree.leaf 4005 representative_4005)) (QuarticIntegerRepresentativeTree.Tree.branch 4007 (QuarticIntegerRepresentativeTree.Tree.leaf 4006 representative_4006) (QuarticIntegerRepresentativeTree.Tree.leaf 4007 representative_4007)))) (QuarticIntegerRepresentativeTree.Tree.branch 4012 (QuarticIntegerRepresentativeTree.Tree.branch 4010 (QuarticIntegerRepresentativeTree.Tree.branch 4009 (QuarticIntegerRepresentativeTree.Tree.leaf 4008 representative_4008) (QuarticIntegerRepresentativeTree.Tree.leaf 4009 representative_4009)) (QuarticIntegerRepresentativeTree.Tree.branch 4011 (QuarticIntegerRepresentativeTree.Tree.leaf 4010 representative_4010) (QuarticIntegerRepresentativeTree.Tree.leaf 4011 representative_4011))) (QuarticIntegerRepresentativeTree.Tree.branch 4014 (QuarticIntegerRepresentativeTree.Tree.branch 4013 (QuarticIntegerRepresentativeTree.Tree.leaf 4012 representative_4012) (QuarticIntegerRepresentativeTree.Tree.leaf 4013 representative_4013)) (QuarticIntegerRepresentativeTree.Tree.branch 4015 (QuarticIntegerRepresentativeTree.Tree.leaf 4014 representative_4014) (QuarticIntegerRepresentativeTree.Tree.leaf 4015 representative_4015))))) (QuarticIntegerRepresentativeTree.Tree.branch 4024 (QuarticIntegerRepresentativeTree.Tree.branch 4020 (QuarticIntegerRepresentativeTree.Tree.branch 4018 (QuarticIntegerRepresentativeTree.Tree.branch 4017 (QuarticIntegerRepresentativeTree.Tree.leaf 4016 representative_4016) (QuarticIntegerRepresentativeTree.Tree.leaf 4017 representative_4017)) (QuarticIntegerRepresentativeTree.Tree.branch 4019 (QuarticIntegerRepresentativeTree.Tree.leaf 4018 representative_4018) (QuarticIntegerRepresentativeTree.Tree.leaf 4019 representative_4019))) (QuarticIntegerRepresentativeTree.Tree.branch 4022 (QuarticIntegerRepresentativeTree.Tree.branch 4021 (QuarticIntegerRepresentativeTree.Tree.leaf 4020 representative_4020) (QuarticIntegerRepresentativeTree.Tree.leaf 4021 representative_4021)) (QuarticIntegerRepresentativeTree.Tree.branch 4023 (QuarticIntegerRepresentativeTree.Tree.leaf 4022 representative_4022) (QuarticIntegerRepresentativeTree.Tree.leaf 4023 representative_4023)))) (QuarticIntegerRepresentativeTree.Tree.branch 4028 (QuarticIntegerRepresentativeTree.Tree.branch 4026 (QuarticIntegerRepresentativeTree.Tree.branch 4025 (QuarticIntegerRepresentativeTree.Tree.leaf 4024 representative_4024) (QuarticIntegerRepresentativeTree.Tree.leaf 4025 representative_4025)) (QuarticIntegerRepresentativeTree.Tree.branch 4027 (QuarticIntegerRepresentativeTree.Tree.leaf 4026 representative_4026) (QuarticIntegerRepresentativeTree.Tree.leaf 4027 representative_4027))) (QuarticIntegerRepresentativeTree.Tree.branch 4030 (QuarticIntegerRepresentativeTree.Tree.branch 4029 (QuarticIntegerRepresentativeTree.Tree.leaf 4028 representative_4028) (QuarticIntegerRepresentativeTree.Tree.leaf 4029 representative_4029)) (QuarticIntegerRepresentativeTree.Tree.branch 4031 (QuarticIntegerRepresentativeTree.Tree.leaf 4030 representative_4030) (QuarticIntegerRepresentativeTree.Tree.leaf 4031 representative_4031)))))))
theorem accepted_062 : All validRep tree_062 := ⟨⟨⟨⟨⟨⟨coefficient_3968,coefficient_3969⟩,⟨coefficient_3970,coefficient_3971⟩⟩,⟨⟨coefficient_3972,coefficient_3973⟩,⟨coefficient_3974,coefficient_3975⟩⟩⟩,⟨⟨⟨coefficient_3976,coefficient_3977⟩,⟨coefficient_3978,coefficient_3979⟩⟩,⟨⟨coefficient_3980,coefficient_3981⟩,⟨coefficient_3982,coefficient_3983⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_3984,coefficient_3985⟩,⟨coefficient_3986,coefficient_3987⟩⟩,⟨⟨coefficient_3988,coefficient_3989⟩,⟨coefficient_3990,coefficient_3991⟩⟩⟩,⟨⟨⟨coefficient_3992,coefficient_3993⟩,⟨coefficient_3994,coefficient_3995⟩⟩,⟨⟨coefficient_3996,coefficient_3997⟩,⟨coefficient_3998,coefficient_3999⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_4000,coefficient_4001⟩,⟨coefficient_4002,coefficient_4003⟩⟩,⟨⟨coefficient_4004,coefficient_4005⟩,⟨coefficient_4006,coefficient_4007⟩⟩⟩,⟨⟨⟨coefficient_4008,coefficient_4009⟩,⟨coefficient_4010,coefficient_4011⟩⟩,⟨⟨coefficient_4012,coefficient_4013⟩,⟨coefficient_4014,coefficient_4015⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_4016,coefficient_4017⟩,⟨coefficient_4018,coefficient_4019⟩⟩,⟨⟨coefficient_4020,coefficient_4021⟩,⟨coefficient_4022,coefficient_4023⟩⟩⟩,⟨⟨⟨coefficient_4024,coefficient_4025⟩,⟨coefficient_4026,coefficient_4027⟩⟩,⟨⟨coefficient_4028,coefficient_4029⟩,⟨coefficient_4030,coefficient_4031⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

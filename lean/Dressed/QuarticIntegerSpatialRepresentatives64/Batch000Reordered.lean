import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_0 : Rep := ⟨![0,1,2,3],441⟩
def representative_1 : Rep := ⟨![0,1,2,4],80⟩
def representative_2 : Rep := ⟨![0,1,2,5],70⟩
def representative_3 : Rep := ⟨![0,1,2,6],446⟩
def representative_4 : Rep := ⟨![0,1,2,7],21⟩
def representative_5 : Rep := ⟨![0,1,2,8],22⟩
def representative_6 : Rep := ⟨![0,1,2,9],19⟩
def representative_7 : Rep := ⟨![0,1,2,10],450⟩
def representative_8 : Rep := ⟨![0,1,2,11],47⟩
def representative_9 : Rep := ⟨![0,1,2,12],95⟩
def representative_10 : Rep := ⟨![0,1,2,13],193⟩
def representative_11 : Rep := ⟨![0,1,2,14],41⟩
def representative_12 : Rep := ⟨![0,1,2,15],453⟩
def representative_13 : Rep := ⟨![0,1,2,16],444⟩
def representative_14 : Rep := ⟨![0,1,2,17],447⟩
def representative_15 : Rep := ⟨![0,1,2,18],37⟩
def representative_16 : Rep := ⟨![0,1,2,19],181⟩
def representative_17 : Rep := ⟨![0,1,2,20],462⟩
def representative_18 : Rep := ⟨![0,1,2,21],462⟩
def representative_19 : Rep := ⟨![0,1,2,22],180⟩
def representative_20 : Rep := ⟨![0,1,2,23],42⟩
def representative_21 : Rep := ⟨![0,1,2,24],72⟩
def representative_22 : Rep := ⟨![0,1,2,25],65⟩
def representative_23 : Rep := ⟨![0,1,2,26],336⟩
def representative_24 : Rep := ⟨![0,1,2,27],462⟩
def representative_25 : Rep := ⟨![0,1,2,28],462⟩
def representative_26 : Rep := ⟨![0,1,2,29],462⟩
def representative_27 : Rep := ⟨![0,1,2,30],462⟩
def representative_28 : Rep := ⟨![0,1,2,31],193⟩
def representative_29 : Rep := ⟨![0,1,2,32],208⟩
def representative_30 : Rep := ⟨![0,1,2,33],337⟩
def representative_31 : Rep := ⟨![0,1,2,34],462⟩
def representative_32 : Rep := ⟨![0,1,2,35],462⟩
def representative_33 : Rep := ⟨![0,1,2,36],462⟩
def representative_34 : Rep := ⟨![0,1,2,37],462⟩
def representative_35 : Rep := ⟨![0,1,2,38],462⟩
def representative_36 : Rep := ⟨![0,1,2,39],462⟩
def representative_37 : Rep := ⟨![0,1,3,4],355⟩
def representative_38 : Rep := ⟨![0,1,3,5],335⟩
def representative_39 : Rep := ⟨![0,1,3,6],75⟩
def representative_40 : Rep := ⟨![0,1,3,8],445⟩
def representative_41 : Rep := ⟨![0,1,3,9],449⟩
def representative_42 : Rep := ⟨![0,1,3,10],57⟩
def representative_43 : Rep := ⟨![0,1,3,11],384⟩
def representative_44 : Rep := ⟨![0,1,3,12],166⟩
def representative_45 : Rep := ⟨![0,1,3,13],277⟩
def representative_46 : Rep := ⟨![0,1,3,14],371⟩
def representative_47 : Rep := ⟨![0,1,3,15],58⟩
def representative_48 : Rep := ⟨![0,1,3,16],77⟩
def representative_49 : Rep := ⟨![0,1,3,17],76⟩
def representative_50 : Rep := ⟨![0,1,3,18],363⟩
def representative_51 : Rep := ⟨![0,1,3,19],164⟩
def representative_52 : Rep := ⟨![0,1,3,20],266⟩
def representative_53 : Rep := ⟨![0,1,3,21],462⟩
def representative_54 : Rep := ⟨![0,1,3,22],269⟩
def representative_55 : Rep := ⟨![0,1,3,23],370⟩
def representative_56 : Rep := ⟨![0,1,3,24],334⟩
def representative_57 : Rep := ⟨![0,1,3,25],330⟩
def representative_58 : Rep := ⟨![0,1,3,26],193⟩
def representative_59 : Rep := ⟨![0,1,3,27],256⟩
def representative_60 : Rep := ⟨![0,1,3,28],462⟩
def representative_61 : Rep := ⟨![0,1,3,29],462⟩
def representative_62 : Rep := ⟨![0,1,3,30],462⟩
def representative_63 : Rep := ⟨![0,1,3,31],263⟩
theorem coefficient_0 : validRep representative_0 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_0)=dictionary64.getD 441 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_441]
  decide +kernel
theorem coefficient_1 : validRep representative_1 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1)=dictionary64.getD 80 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_80]
  decide +kernel
theorem coefficient_2 : validRep representative_2 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2)=dictionary64.getD 70 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_70]
  decide +kernel
theorem coefficient_3 : validRep representative_3 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3)=dictionary64.getD 446 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_446]
  decide +kernel
theorem coefficient_4 : validRep representative_4 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_4)=dictionary64.getD 21 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_21]
  decide +kernel
theorem coefficient_5 : validRep representative_5 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_5)=dictionary64.getD 22 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_22]
  decide +kernel
theorem coefficient_6 : validRep representative_6 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_6)=dictionary64.getD 19 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_19]
  decide +kernel
theorem coefficient_7 : validRep representative_7 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_7)=dictionary64.getD 450 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_450]
  decide +kernel
theorem coefficient_8 : validRep representative_8 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_8)=dictionary64.getD 47 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_47]
  decide +kernel
theorem coefficient_9 : validRep representative_9 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_9)=dictionary64.getD 95 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_95]
  decide +kernel
theorem coefficient_10 : validRep representative_10 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_10)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_11 : validRep representative_11 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_11)=dictionary64.getD 41 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_12 : validRep representative_12 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_12)=dictionary64.getD 453 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_453]
  decide +kernel
theorem coefficient_13 : validRep representative_13 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_13)=dictionary64.getD 444 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_444]
  decide +kernel
theorem coefficient_14 : validRep representative_14 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_14)=dictionary64.getD 447 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_447]
  decide +kernel
theorem coefficient_15 : validRep representative_15 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_15)=dictionary64.getD 37 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_37]
  decide +kernel
theorem coefficient_16 : validRep representative_16 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_16)=dictionary64.getD 181 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_181]
  decide +kernel
theorem coefficient_17 : validRep representative_17 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_17)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_18 : validRep representative_18 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_18)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_19 : validRep representative_19 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_19)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_20 : validRep representative_20 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_20)=dictionary64.getD 42 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_42]
  decide +kernel
theorem coefficient_21 : validRep representative_21 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_21)=dictionary64.getD 72 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_72]
  decide +kernel
theorem coefficient_22 : validRep representative_22 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_22)=dictionary64.getD 65 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_65]
  decide +kernel
theorem coefficient_23 : validRep representative_23 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_23)=dictionary64.getD 336 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_336]
  decide +kernel
theorem coefficient_24 : validRep representative_24 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_24)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_25 : validRep representative_25 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_25)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_26 : validRep representative_26 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_26)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_27 : validRep representative_27 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_27)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_28 : validRep representative_28 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_28)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_29 : validRep representative_29 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_29)=dictionary64.getD 208 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_208]
  decide +kernel
theorem coefficient_30 : validRep representative_30 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_30)=dictionary64.getD 337 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_337]
  decide +kernel
theorem coefficient_31 : validRep representative_31 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_31)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_32 : validRep representative_32 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_32)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_33 : validRep representative_33 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_33)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_34 : validRep representative_34 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_34)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_35 : validRep representative_35 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_35)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_36 : validRep representative_36 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_36)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_37 : validRep representative_37 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_37)=dictionary64.getD 355 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_355]
  decide +kernel
theorem coefficient_38 : validRep representative_38 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_38)=dictionary64.getD 335 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_335]
  decide +kernel
theorem coefficient_39 : validRep representative_39 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_39)=dictionary64.getD 75 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_75]
  decide +kernel
theorem coefficient_40 : validRep representative_40 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_40)=dictionary64.getD 445 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_445]
  decide +kernel
theorem coefficient_41 : validRep representative_41 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_41)=dictionary64.getD 449 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_449]
  decide +kernel
theorem coefficient_42 : validRep representative_42 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_42)=dictionary64.getD 57 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_57]
  decide +kernel
theorem coefficient_43 : validRep representative_43 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_43)=dictionary64.getD 384 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_384]
  decide +kernel
theorem coefficient_44 : validRep representative_44 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_44)=dictionary64.getD 166 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_166]
  decide +kernel
theorem coefficient_45 : validRep representative_45 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_45)=dictionary64.getD 277 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_277]
  decide +kernel
theorem coefficient_46 : validRep representative_46 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_46)=dictionary64.getD 371 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_371]
  decide +kernel
theorem coefficient_47 : validRep representative_47 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_47)=dictionary64.getD 58 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_58]
  decide +kernel
theorem coefficient_48 : validRep representative_48 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_48)=dictionary64.getD 77 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_77]
  decide +kernel
theorem coefficient_49 : validRep representative_49 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_49)=dictionary64.getD 76 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_76]
  decide +kernel
theorem coefficient_50 : validRep representative_50 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_50)=dictionary64.getD 363 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_363]
  decide +kernel
theorem coefficient_51 : validRep representative_51 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_51)=dictionary64.getD 164 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_164]
  decide +kernel
theorem coefficient_52 : validRep representative_52 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_52)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_53 : validRep representative_53 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_53)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_54 : validRep representative_54 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_54)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_55 : validRep representative_55 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_55)=dictionary64.getD 370 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_370]
  decide +kernel
theorem coefficient_56 : validRep representative_56 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_56)=dictionary64.getD 334 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_334]
  decide +kernel
theorem coefficient_57 : validRep representative_57 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_57)=dictionary64.getD 330 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_330]
  decide +kernel
theorem coefficient_58 : validRep representative_58 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_58)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_59 : validRep representative_59 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_59)=dictionary64.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_60 : validRep representative_60 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_60)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_61 : validRep representative_61 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_61)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_62 : validRep representative_62 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_62)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_63 : validRep representative_63 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_63)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
def tree_000 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 32 (QuarticIntegerRepresentativeTree.Tree.branch 16 (QuarticIntegerRepresentativeTree.Tree.branch 8 (QuarticIntegerRepresentativeTree.Tree.branch 4 (QuarticIntegerRepresentativeTree.Tree.branch 2 (QuarticIntegerRepresentativeTree.Tree.branch 1 (QuarticIntegerRepresentativeTree.Tree.leaf 0 representative_0) (QuarticIntegerRepresentativeTree.Tree.leaf 1 representative_1)) (QuarticIntegerRepresentativeTree.Tree.branch 3 (QuarticIntegerRepresentativeTree.Tree.leaf 2 representative_2) (QuarticIntegerRepresentativeTree.Tree.leaf 3 representative_3))) (QuarticIntegerRepresentativeTree.Tree.branch 6 (QuarticIntegerRepresentativeTree.Tree.branch 5 (QuarticIntegerRepresentativeTree.Tree.leaf 4 representative_4) (QuarticIntegerRepresentativeTree.Tree.leaf 5 representative_5)) (QuarticIntegerRepresentativeTree.Tree.branch 7 (QuarticIntegerRepresentativeTree.Tree.leaf 6 representative_6) (QuarticIntegerRepresentativeTree.Tree.leaf 7 representative_7)))) (QuarticIntegerRepresentativeTree.Tree.branch 12 (QuarticIntegerRepresentativeTree.Tree.branch 10 (QuarticIntegerRepresentativeTree.Tree.branch 9 (QuarticIntegerRepresentativeTree.Tree.leaf 8 representative_8) (QuarticIntegerRepresentativeTree.Tree.leaf 9 representative_9)) (QuarticIntegerRepresentativeTree.Tree.branch 11 (QuarticIntegerRepresentativeTree.Tree.leaf 10 representative_10) (QuarticIntegerRepresentativeTree.Tree.leaf 11 representative_11))) (QuarticIntegerRepresentativeTree.Tree.branch 14 (QuarticIntegerRepresentativeTree.Tree.branch 13 (QuarticIntegerRepresentativeTree.Tree.leaf 12 representative_12) (QuarticIntegerRepresentativeTree.Tree.leaf 13 representative_13)) (QuarticIntegerRepresentativeTree.Tree.branch 15 (QuarticIntegerRepresentativeTree.Tree.leaf 14 representative_14) (QuarticIntegerRepresentativeTree.Tree.leaf 15 representative_15))))) (QuarticIntegerRepresentativeTree.Tree.branch 24 (QuarticIntegerRepresentativeTree.Tree.branch 20 (QuarticIntegerRepresentativeTree.Tree.branch 18 (QuarticIntegerRepresentativeTree.Tree.branch 17 (QuarticIntegerRepresentativeTree.Tree.leaf 16 representative_16) (QuarticIntegerRepresentativeTree.Tree.leaf 17 representative_17)) (QuarticIntegerRepresentativeTree.Tree.branch 19 (QuarticIntegerRepresentativeTree.Tree.leaf 18 representative_18) (QuarticIntegerRepresentativeTree.Tree.leaf 19 representative_19))) (QuarticIntegerRepresentativeTree.Tree.branch 22 (QuarticIntegerRepresentativeTree.Tree.branch 21 (QuarticIntegerRepresentativeTree.Tree.leaf 20 representative_20) (QuarticIntegerRepresentativeTree.Tree.leaf 21 representative_21)) (QuarticIntegerRepresentativeTree.Tree.branch 23 (QuarticIntegerRepresentativeTree.Tree.leaf 22 representative_22) (QuarticIntegerRepresentativeTree.Tree.leaf 23 representative_23)))) (QuarticIntegerRepresentativeTree.Tree.branch 28 (QuarticIntegerRepresentativeTree.Tree.branch 26 (QuarticIntegerRepresentativeTree.Tree.branch 25 (QuarticIntegerRepresentativeTree.Tree.leaf 24 representative_24) (QuarticIntegerRepresentativeTree.Tree.leaf 25 representative_25)) (QuarticIntegerRepresentativeTree.Tree.branch 27 (QuarticIntegerRepresentativeTree.Tree.leaf 26 representative_26) (QuarticIntegerRepresentativeTree.Tree.leaf 27 representative_27))) (QuarticIntegerRepresentativeTree.Tree.branch 30 (QuarticIntegerRepresentativeTree.Tree.branch 29 (QuarticIntegerRepresentativeTree.Tree.leaf 28 representative_28) (QuarticIntegerRepresentativeTree.Tree.leaf 29 representative_29)) (QuarticIntegerRepresentativeTree.Tree.branch 31 (QuarticIntegerRepresentativeTree.Tree.leaf 30 representative_30) (QuarticIntegerRepresentativeTree.Tree.leaf 31 representative_31)))))) (QuarticIntegerRepresentativeTree.Tree.branch 48 (QuarticIntegerRepresentativeTree.Tree.branch 40 (QuarticIntegerRepresentativeTree.Tree.branch 36 (QuarticIntegerRepresentativeTree.Tree.branch 34 (QuarticIntegerRepresentativeTree.Tree.branch 33 (QuarticIntegerRepresentativeTree.Tree.leaf 32 representative_32) (QuarticIntegerRepresentativeTree.Tree.leaf 33 representative_33)) (QuarticIntegerRepresentativeTree.Tree.branch 35 (QuarticIntegerRepresentativeTree.Tree.leaf 34 representative_34) (QuarticIntegerRepresentativeTree.Tree.leaf 35 representative_35))) (QuarticIntegerRepresentativeTree.Tree.branch 38 (QuarticIntegerRepresentativeTree.Tree.branch 37 (QuarticIntegerRepresentativeTree.Tree.leaf 36 representative_36) (QuarticIntegerRepresentativeTree.Tree.leaf 37 representative_37)) (QuarticIntegerRepresentativeTree.Tree.branch 39 (QuarticIntegerRepresentativeTree.Tree.leaf 38 representative_38) (QuarticIntegerRepresentativeTree.Tree.leaf 39 representative_39)))) (QuarticIntegerRepresentativeTree.Tree.branch 44 (QuarticIntegerRepresentativeTree.Tree.branch 42 (QuarticIntegerRepresentativeTree.Tree.branch 41 (QuarticIntegerRepresentativeTree.Tree.leaf 40 representative_40) (QuarticIntegerRepresentativeTree.Tree.leaf 41 representative_41)) (QuarticIntegerRepresentativeTree.Tree.branch 43 (QuarticIntegerRepresentativeTree.Tree.leaf 42 representative_42) (QuarticIntegerRepresentativeTree.Tree.leaf 43 representative_43))) (QuarticIntegerRepresentativeTree.Tree.branch 46 (QuarticIntegerRepresentativeTree.Tree.branch 45 (QuarticIntegerRepresentativeTree.Tree.leaf 44 representative_44) (QuarticIntegerRepresentativeTree.Tree.leaf 45 representative_45)) (QuarticIntegerRepresentativeTree.Tree.branch 47 (QuarticIntegerRepresentativeTree.Tree.leaf 46 representative_46) (QuarticIntegerRepresentativeTree.Tree.leaf 47 representative_47))))) (QuarticIntegerRepresentativeTree.Tree.branch 56 (QuarticIntegerRepresentativeTree.Tree.branch 52 (QuarticIntegerRepresentativeTree.Tree.branch 50 (QuarticIntegerRepresentativeTree.Tree.branch 49 (QuarticIntegerRepresentativeTree.Tree.leaf 48 representative_48) (QuarticIntegerRepresentativeTree.Tree.leaf 49 representative_49)) (QuarticIntegerRepresentativeTree.Tree.branch 51 (QuarticIntegerRepresentativeTree.Tree.leaf 50 representative_50) (QuarticIntegerRepresentativeTree.Tree.leaf 51 representative_51))) (QuarticIntegerRepresentativeTree.Tree.branch 54 (QuarticIntegerRepresentativeTree.Tree.branch 53 (QuarticIntegerRepresentativeTree.Tree.leaf 52 representative_52) (QuarticIntegerRepresentativeTree.Tree.leaf 53 representative_53)) (QuarticIntegerRepresentativeTree.Tree.branch 55 (QuarticIntegerRepresentativeTree.Tree.leaf 54 representative_54) (QuarticIntegerRepresentativeTree.Tree.leaf 55 representative_55)))) (QuarticIntegerRepresentativeTree.Tree.branch 60 (QuarticIntegerRepresentativeTree.Tree.branch 58 (QuarticIntegerRepresentativeTree.Tree.branch 57 (QuarticIntegerRepresentativeTree.Tree.leaf 56 representative_56) (QuarticIntegerRepresentativeTree.Tree.leaf 57 representative_57)) (QuarticIntegerRepresentativeTree.Tree.branch 59 (QuarticIntegerRepresentativeTree.Tree.leaf 58 representative_58) (QuarticIntegerRepresentativeTree.Tree.leaf 59 representative_59))) (QuarticIntegerRepresentativeTree.Tree.branch 62 (QuarticIntegerRepresentativeTree.Tree.branch 61 (QuarticIntegerRepresentativeTree.Tree.leaf 60 representative_60) (QuarticIntegerRepresentativeTree.Tree.leaf 61 representative_61)) (QuarticIntegerRepresentativeTree.Tree.branch 63 (QuarticIntegerRepresentativeTree.Tree.leaf 62 representative_62) (QuarticIntegerRepresentativeTree.Tree.leaf 63 representative_63)))))))
theorem accepted_000 : All validRep tree_000 := ⟨⟨⟨⟨⟨⟨coefficient_0,coefficient_1⟩,⟨coefficient_2,coefficient_3⟩⟩,⟨⟨coefficient_4,coefficient_5⟩,⟨coefficient_6,coefficient_7⟩⟩⟩,⟨⟨⟨coefficient_8,coefficient_9⟩,⟨coefficient_10,coefficient_11⟩⟩,⟨⟨coefficient_12,coefficient_13⟩,⟨coefficient_14,coefficient_15⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_16,coefficient_17⟩,⟨coefficient_18,coefficient_19⟩⟩,⟨⟨coefficient_20,coefficient_21⟩,⟨coefficient_22,coefficient_23⟩⟩⟩,⟨⟨⟨coefficient_24,coefficient_25⟩,⟨coefficient_26,coefficient_27⟩⟩,⟨⟨coefficient_28,coefficient_29⟩,⟨coefficient_30,coefficient_31⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_32,coefficient_33⟩,⟨coefficient_34,coefficient_35⟩⟩,⟨⟨coefficient_36,coefficient_37⟩,⟨coefficient_38,coefficient_39⟩⟩⟩,⟨⟨⟨coefficient_40,coefficient_41⟩,⟨coefficient_42,coefficient_43⟩⟩,⟨⟨coefficient_44,coefficient_45⟩,⟨coefficient_46,coefficient_47⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_48,coefficient_49⟩,⟨coefficient_50,coefficient_51⟩⟩,⟨⟨coefficient_52,coefficient_53⟩,⟨coefficient_54,coefficient_55⟩⟩⟩,⟨⟨⟨coefficient_56,coefficient_57⟩,⟨coefficient_58,coefficient_59⟩⟩,⟨⟨coefficient_60,coefficient_61⟩,⟨coefficient_62,coefficient_63⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

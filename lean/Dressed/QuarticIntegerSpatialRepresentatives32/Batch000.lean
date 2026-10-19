import Dressed.QuarticIntegerSpatialRepresentatives32.Base
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_0 : Rep := ⟨![0,1,2,3],26⟩
theorem coefficient_0 : validRep representative_0 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_0)=dictionary32.getD 26 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_26]
  decide +kernel
def representative_1 : Rep := ⟨![0,1,2,4],31⟩
theorem coefficient_1 : validRep representative_1 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1)=dictionary32.getD 31 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_31]
  decide +kernel
def representative_2 : Rep := ⟨![0,1,2,5],21⟩
theorem coefficient_2 : validRep representative_2 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_2)=dictionary32.getD 21 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_21]
  decide +kernel
def representative_3 : Rep := ⟨![0,1,2,6],497⟩
theorem coefficient_3 : validRep representative_3 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_3)=dictionary32.getD 497 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_497]
  decide +kernel
def representative_4 : Rep := ⟨![0,1,2,7],483⟩
theorem coefficient_4 : validRep representative_4 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_4)=dictionary32.getD 483 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_483]
  decide +kernel
def representative_5 : Rep := ⟨![0,1,2,8],476⟩
theorem coefficient_5 : validRep representative_5 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_5)=dictionary32.getD 476 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_476]
  decide +kernel
def representative_6 : Rep := ⟨![0,1,2,9],480⟩
theorem coefficient_6 : validRep representative_6 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_6)=dictionary32.getD 480 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_480]
  decide +kernel
def representative_7 : Rep := ⟨![0,1,2,10],56⟩
theorem coefficient_7 : validRep representative_7 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_7)=dictionary32.getD 56 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_56]
  decide +kernel
def representative_8 : Rep := ⟨![0,1,2,11],71⟩
theorem coefficient_8 : validRep representative_8 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_8)=dictionary32.getD 71 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_71]
  decide +kernel
def representative_9 : Rep := ⟨![0,1,2,12],100⟩
theorem coefficient_9 : validRep representative_9 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_9)=dictionary32.getD 100 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_100]
  decide +kernel
def representative_10 : Rep := ⟨![0,1,2,13],94⟩
theorem coefficient_10 : validRep representative_10 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_10)=dictionary32.getD 94 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_94]
  decide +kernel
def representative_11 : Rep := ⟨![0,1,2,14],369⟩
theorem coefficient_11 : validRep representative_11 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_11)=dictionary32.getD 369 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_369]
  decide +kernel
def representative_12 : Rep := ⟨![0,1,2,15],210⟩
theorem coefficient_12 : validRep representative_12 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_12)=dictionary32.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_210]
  decide +kernel
def representative_13 : Rep := ⟨![0,1,2,16],234⟩
theorem coefficient_13 : validRep representative_13 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_13)=dictionary32.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_234]
  decide +kernel
def representative_14 : Rep := ⟨![0,1,2,17],353⟩
theorem coefficient_14 : validRep representative_14 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_14)=dictionary32.getD 353 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_353]
  decide +kernel
def representative_15 : Rep := ⟨![0,1,2,18],508⟩
theorem coefficient_15 : validRep representative_15 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_15)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def representative_16 : Rep := ⟨![0,1,2,19],508⟩
theorem coefficient_16 : validRep representative_16 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_16)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def representative_17 : Rep := ⟨![0,1,4,5],27⟩
theorem coefficient_17 : validRep representative_17 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_17)=dictionary32.getD 27 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_27]
  decide +kernel
def representative_18 : Rep := ⟨![0,1,4,6],482⟩
theorem coefficient_18 : validRep representative_18 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_18)=dictionary32.getD 482 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_482]
  decide +kernel
def representative_19 : Rep := ⟨![0,1,4,7],496⟩
theorem coefficient_19 : validRep representative_19 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_19)=dictionary32.getD 496 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_496]
  decide +kernel
def representative_20 : Rep := ⟨![0,1,4,8],487⟩
theorem coefficient_20 : validRep representative_20 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_20)=dictionary32.getD 487 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_487]
  decide +kernel
def representative_21 : Rep := ⟨![0,1,4,9],474⟩
theorem coefficient_21 : validRep representative_21 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_21)=dictionary32.getD 474 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_474]
  decide +kernel
def representative_22 : Rep := ⟨![0,1,4,10],72⟩
theorem coefficient_22 : validRep representative_22 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_22)=dictionary32.getD 72 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_72]
  decide +kernel
def representative_23 : Rep := ⟨![0,1,4,11],51⟩
theorem coefficient_23 : validRep representative_23 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_23)=dictionary32.getD 51 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_51]
  decide +kernel
def representative_24 : Rep := ⟨![0,1,4,12],84⟩
theorem coefficient_24 : validRep representative_24 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_24)=dictionary32.getD 84 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_84]
  decide +kernel
def representative_25 : Rep := ⟨![0,1,4,13],102⟩
theorem coefficient_25 : validRep representative_25 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_25)=dictionary32.getD 102 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_102]
  decide +kernel
def representative_26 : Rep := ⟨![0,1,4,14],210⟩
theorem coefficient_26 : validRep representative_26 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_26)=dictionary32.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_210]
  decide +kernel
def representative_27 : Rep := ⟨![0,1,4,15],391⟩
theorem coefficient_27 : validRep representative_27 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_27)=dictionary32.getD 391 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_391]
  decide +kernel
def representative_28 : Rep := ⟨![0,1,4,16],355⟩
theorem coefficient_28 : validRep representative_28 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_28)=dictionary32.getD 355 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_355]
  decide +kernel
def representative_29 : Rep := ⟨![0,1,4,17],234⟩
theorem coefficient_29 : validRep representative_29 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_29)=dictionary32.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_234]
  decide +kernel
def representative_30 : Rep := ⟨![0,1,4,18],508⟩
theorem coefficient_30 : validRep representative_30 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_30)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def representative_31 : Rep := ⟨![0,1,4,19],508⟩
theorem coefficient_31 : validRep representative_31 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_31)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def representative_32 : Rep := ⟨![0,1,4,20],95⟩
theorem coefficient_32 : validRep representative_32 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_32)=dictionary32.getD 95 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_95]
  decide +kernel
def representative_33 : Rep := ⟨![0,1,4,21],101⟩
theorem coefficient_33 : validRep representative_33 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_33)=dictionary32.getD 101 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_101]
  decide +kernel
def representative_34 : Rep := ⟨![0,1,4,22],210⟩
theorem coefficient_34 : validRep representative_34 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_34)=dictionary32.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_210]
  decide +kernel
def representative_35 : Rep := ⟨![0,1,4,23],367⟩
theorem coefficient_35 : validRep representative_35 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_35)=dictionary32.getD 367 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_367]
  decide +kernel
def representative_36 : Rep := ⟨![0,1,4,24],479⟩
theorem coefficient_36 : validRep representative_36 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_36)=dictionary32.getD 479 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_479]
  decide +kernel
def representative_37 : Rep := ⟨![0,1,4,25],475⟩
theorem coefficient_37 : validRep representative_37 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_37)=dictionary32.getD 475 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_475]
  decide +kernel
def representative_38 : Rep := ⟨![0,1,4,26],70⟩
theorem coefficient_38 : validRep representative_38 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_38)=dictionary32.getD 70 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_70]
  decide +kernel
def representative_39 : Rep := ⟨![0,1,4,27],58⟩
theorem coefficient_39 : validRep representative_39 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_39)=dictionary32.getD 58 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_58]
  decide +kernel
def representative_40 : Rep := ⟨![0,1,4,28],23⟩
theorem coefficient_40 : validRep representative_40 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_40)=dictionary32.getD 23 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_23]
  decide +kernel
def representative_41 : Rep := ⟨![0,1,4,29],32⟩
theorem coefficient_41 : validRep representative_41 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_41)=dictionary32.getD 32 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_32]
  decide +kernel
def representative_42 : Rep := ⟨![0,1,4,30],485⟩
theorem coefficient_42 : validRep representative_42 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_42)=dictionary32.getD 485 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_485]
  decide +kernel
def representative_43 : Rep := ⟨![0,1,4,31],494⟩
theorem coefficient_43 : validRep representative_43 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_43)=dictionary32.getD 494 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_494]
  decide +kernel
def representative_44 : Rep := ⟨![0,1,6,7],46⟩
theorem coefficient_44 : validRep representative_44 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_44)=dictionary32.getD 46 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_46]
  decide +kernel
def representative_45 : Rep := ⟨![0,1,6,8],91⟩
theorem coefficient_45 : validRep representative_45 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_45)=dictionary32.getD 91 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_91]
  decide +kernel
def representative_46 : Rep := ⟨![0,1,6,9],92⟩
theorem coefficient_46 : validRep representative_46 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_46)=dictionary32.getD 92 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_92]
  decide +kernel
def representative_47 : Rep := ⟨![0,1,6,10],433⟩
theorem coefficient_47 : validRep representative_47 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_47)=dictionary32.getD 433 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_433]
  decide +kernel
def representative_48 : Rep := ⟨![0,1,6,11],401⟩
theorem coefficient_48 : validRep representative_48 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_48)=dictionary32.getD 401 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_401]
  decide +kernel
def representative_49 : Rep := ⟨![0,1,6,12],364⟩
theorem coefficient_49 : validRep representative_49 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_49)=dictionary32.getD 364 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_364]
  decide +kernel
def representative_50 : Rep := ⟨![0,1,6,13],361⟩
theorem coefficient_50 : validRep representative_50 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_50)=dictionary32.getD 361 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_361]
  decide +kernel
def representative_51 : Rep := ⟨![0,1,6,14],154⟩
theorem coefficient_51 : validRep representative_51 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_51)=dictionary32.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_154]
  decide +kernel
def representative_52 : Rep := ⟨![0,1,6,15],339⟩
theorem coefficient_52 : validRep representative_52 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_52)=dictionary32.getD 339 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_339]
  decide +kernel
def representative_53 : Rep := ⟨![0,1,6,16],304⟩
theorem coefficient_53 : validRep representative_53 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_53)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
def representative_54 : Rep := ⟨![0,1,6,17],234⟩
theorem coefficient_54 : validRep representative_54 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_54)=dictionary32.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_234]
  decide +kernel
def representative_55 : Rep := ⟨![0,1,6,18],311⟩
theorem coefficient_55 : validRep representative_55 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_55)=dictionary32.getD 311 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_311]
  decide +kernel
def representative_56 : Rep := ⟨![0,1,6,19],508⟩
theorem coefficient_56 : validRep representative_56 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_56)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def representative_57 : Rep := ⟨![0,1,6,20],364⟩
theorem coefficient_57 : validRep representative_57 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_57)=dictionary32.getD 364 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_364]
  decide +kernel
def representative_58 : Rep := ⟨![0,1,6,21],360⟩
theorem coefficient_58 : validRep representative_58 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_58)=dictionary32.getD 360 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_360]
  decide +kernel
def representative_59 : Rep := ⟨![0,1,6,22],210⟩
theorem coefficient_59 : validRep representative_59 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_59)=dictionary32.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_210]
  decide +kernel
def representative_60 : Rep := ⟨![0,1,6,23],317⟩
theorem coefficient_60 : validRep representative_60 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_60)=dictionary32.getD 317 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_317]
  decide +kernel
def representative_61 : Rep := ⟨![0,1,6,24],89⟩
theorem coefficient_61 : validRep representative_61 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_61)=dictionary32.getD 89 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_89]
  decide +kernel
def representative_62 : Rep := ⟨![0,1,6,25],93⟩
theorem coefficient_62 : validRep representative_62 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_62)=dictionary32.getD 93 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_93]
  decide +kernel
def representative_63 : Rep := ⟨![0,1,6,26],397⟩
theorem coefficient_63 : validRep representative_63 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_63)=dictionary32.getD 397 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_397]
  decide +kernel
def tree_000 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 32 (QuarticIntegerRepresentativeTree.Tree.branch 16 (QuarticIntegerRepresentativeTree.Tree.branch 8 (QuarticIntegerRepresentativeTree.Tree.branch 4 (QuarticIntegerRepresentativeTree.Tree.branch 2 (QuarticIntegerRepresentativeTree.Tree.branch 1 (QuarticIntegerRepresentativeTree.Tree.leaf 0 representative_0) (QuarticIntegerRepresentativeTree.Tree.leaf 1 representative_1)) (QuarticIntegerRepresentativeTree.Tree.branch 3 (QuarticIntegerRepresentativeTree.Tree.leaf 2 representative_2) (QuarticIntegerRepresentativeTree.Tree.leaf 3 representative_3))) (QuarticIntegerRepresentativeTree.Tree.branch 6 (QuarticIntegerRepresentativeTree.Tree.branch 5 (QuarticIntegerRepresentativeTree.Tree.leaf 4 representative_4) (QuarticIntegerRepresentativeTree.Tree.leaf 5 representative_5)) (QuarticIntegerRepresentativeTree.Tree.branch 7 (QuarticIntegerRepresentativeTree.Tree.leaf 6 representative_6) (QuarticIntegerRepresentativeTree.Tree.leaf 7 representative_7)))) (QuarticIntegerRepresentativeTree.Tree.branch 12 (QuarticIntegerRepresentativeTree.Tree.branch 10 (QuarticIntegerRepresentativeTree.Tree.branch 9 (QuarticIntegerRepresentativeTree.Tree.leaf 8 representative_8) (QuarticIntegerRepresentativeTree.Tree.leaf 9 representative_9)) (QuarticIntegerRepresentativeTree.Tree.branch 11 (QuarticIntegerRepresentativeTree.Tree.leaf 10 representative_10) (QuarticIntegerRepresentativeTree.Tree.leaf 11 representative_11))) (QuarticIntegerRepresentativeTree.Tree.branch 14 (QuarticIntegerRepresentativeTree.Tree.branch 13 (QuarticIntegerRepresentativeTree.Tree.leaf 12 representative_12) (QuarticIntegerRepresentativeTree.Tree.leaf 13 representative_13)) (QuarticIntegerRepresentativeTree.Tree.branch 15 (QuarticIntegerRepresentativeTree.Tree.leaf 14 representative_14) (QuarticIntegerRepresentativeTree.Tree.leaf 15 representative_15))))) (QuarticIntegerRepresentativeTree.Tree.branch 24 (QuarticIntegerRepresentativeTree.Tree.branch 20 (QuarticIntegerRepresentativeTree.Tree.branch 18 (QuarticIntegerRepresentativeTree.Tree.branch 17 (QuarticIntegerRepresentativeTree.Tree.leaf 16 representative_16) (QuarticIntegerRepresentativeTree.Tree.leaf 17 representative_17)) (QuarticIntegerRepresentativeTree.Tree.branch 19 (QuarticIntegerRepresentativeTree.Tree.leaf 18 representative_18) (QuarticIntegerRepresentativeTree.Tree.leaf 19 representative_19))) (QuarticIntegerRepresentativeTree.Tree.branch 22 (QuarticIntegerRepresentativeTree.Tree.branch 21 (QuarticIntegerRepresentativeTree.Tree.leaf 20 representative_20) (QuarticIntegerRepresentativeTree.Tree.leaf 21 representative_21)) (QuarticIntegerRepresentativeTree.Tree.branch 23 (QuarticIntegerRepresentativeTree.Tree.leaf 22 representative_22) (QuarticIntegerRepresentativeTree.Tree.leaf 23 representative_23)))) (QuarticIntegerRepresentativeTree.Tree.branch 28 (QuarticIntegerRepresentativeTree.Tree.branch 26 (QuarticIntegerRepresentativeTree.Tree.branch 25 (QuarticIntegerRepresentativeTree.Tree.leaf 24 representative_24) (QuarticIntegerRepresentativeTree.Tree.leaf 25 representative_25)) (QuarticIntegerRepresentativeTree.Tree.branch 27 (QuarticIntegerRepresentativeTree.Tree.leaf 26 representative_26) (QuarticIntegerRepresentativeTree.Tree.leaf 27 representative_27))) (QuarticIntegerRepresentativeTree.Tree.branch 30 (QuarticIntegerRepresentativeTree.Tree.branch 29 (QuarticIntegerRepresentativeTree.Tree.leaf 28 representative_28) (QuarticIntegerRepresentativeTree.Tree.leaf 29 representative_29)) (QuarticIntegerRepresentativeTree.Tree.branch 31 (QuarticIntegerRepresentativeTree.Tree.leaf 30 representative_30) (QuarticIntegerRepresentativeTree.Tree.leaf 31 representative_31)))))) (QuarticIntegerRepresentativeTree.Tree.branch 48 (QuarticIntegerRepresentativeTree.Tree.branch 40 (QuarticIntegerRepresentativeTree.Tree.branch 36 (QuarticIntegerRepresentativeTree.Tree.branch 34 (QuarticIntegerRepresentativeTree.Tree.branch 33 (QuarticIntegerRepresentativeTree.Tree.leaf 32 representative_32) (QuarticIntegerRepresentativeTree.Tree.leaf 33 representative_33)) (QuarticIntegerRepresentativeTree.Tree.branch 35 (QuarticIntegerRepresentativeTree.Tree.leaf 34 representative_34) (QuarticIntegerRepresentativeTree.Tree.leaf 35 representative_35))) (QuarticIntegerRepresentativeTree.Tree.branch 38 (QuarticIntegerRepresentativeTree.Tree.branch 37 (QuarticIntegerRepresentativeTree.Tree.leaf 36 representative_36) (QuarticIntegerRepresentativeTree.Tree.leaf 37 representative_37)) (QuarticIntegerRepresentativeTree.Tree.branch 39 (QuarticIntegerRepresentativeTree.Tree.leaf 38 representative_38) (QuarticIntegerRepresentativeTree.Tree.leaf 39 representative_39)))) (QuarticIntegerRepresentativeTree.Tree.branch 44 (QuarticIntegerRepresentativeTree.Tree.branch 42 (QuarticIntegerRepresentativeTree.Tree.branch 41 (QuarticIntegerRepresentativeTree.Tree.leaf 40 representative_40) (QuarticIntegerRepresentativeTree.Tree.leaf 41 representative_41)) (QuarticIntegerRepresentativeTree.Tree.branch 43 (QuarticIntegerRepresentativeTree.Tree.leaf 42 representative_42) (QuarticIntegerRepresentativeTree.Tree.leaf 43 representative_43))) (QuarticIntegerRepresentativeTree.Tree.branch 46 (QuarticIntegerRepresentativeTree.Tree.branch 45 (QuarticIntegerRepresentativeTree.Tree.leaf 44 representative_44) (QuarticIntegerRepresentativeTree.Tree.leaf 45 representative_45)) (QuarticIntegerRepresentativeTree.Tree.branch 47 (QuarticIntegerRepresentativeTree.Tree.leaf 46 representative_46) (QuarticIntegerRepresentativeTree.Tree.leaf 47 representative_47))))) (QuarticIntegerRepresentativeTree.Tree.branch 56 (QuarticIntegerRepresentativeTree.Tree.branch 52 (QuarticIntegerRepresentativeTree.Tree.branch 50 (QuarticIntegerRepresentativeTree.Tree.branch 49 (QuarticIntegerRepresentativeTree.Tree.leaf 48 representative_48) (QuarticIntegerRepresentativeTree.Tree.leaf 49 representative_49)) (QuarticIntegerRepresentativeTree.Tree.branch 51 (QuarticIntegerRepresentativeTree.Tree.leaf 50 representative_50) (QuarticIntegerRepresentativeTree.Tree.leaf 51 representative_51))) (QuarticIntegerRepresentativeTree.Tree.branch 54 (QuarticIntegerRepresentativeTree.Tree.branch 53 (QuarticIntegerRepresentativeTree.Tree.leaf 52 representative_52) (QuarticIntegerRepresentativeTree.Tree.leaf 53 representative_53)) (QuarticIntegerRepresentativeTree.Tree.branch 55 (QuarticIntegerRepresentativeTree.Tree.leaf 54 representative_54) (QuarticIntegerRepresentativeTree.Tree.leaf 55 representative_55)))) (QuarticIntegerRepresentativeTree.Tree.branch 60 (QuarticIntegerRepresentativeTree.Tree.branch 58 (QuarticIntegerRepresentativeTree.Tree.branch 57 (QuarticIntegerRepresentativeTree.Tree.leaf 56 representative_56) (QuarticIntegerRepresentativeTree.Tree.leaf 57 representative_57)) (QuarticIntegerRepresentativeTree.Tree.branch 59 (QuarticIntegerRepresentativeTree.Tree.leaf 58 representative_58) (QuarticIntegerRepresentativeTree.Tree.leaf 59 representative_59))) (QuarticIntegerRepresentativeTree.Tree.branch 62 (QuarticIntegerRepresentativeTree.Tree.branch 61 (QuarticIntegerRepresentativeTree.Tree.leaf 60 representative_60) (QuarticIntegerRepresentativeTree.Tree.leaf 61 representative_61)) (QuarticIntegerRepresentativeTree.Tree.branch 63 (QuarticIntegerRepresentativeTree.Tree.leaf 62 representative_62) (QuarticIntegerRepresentativeTree.Tree.leaf 63 representative_63)))))))
theorem accepted_000 : All validRep tree_000 := ⟨⟨⟨⟨⟨⟨coefficient_0,coefficient_1⟩,⟨coefficient_2,coefficient_3⟩⟩,⟨⟨coefficient_4,coefficient_5⟩,⟨coefficient_6,coefficient_7⟩⟩⟩,⟨⟨⟨coefficient_8,coefficient_9⟩,⟨coefficient_10,coefficient_11⟩⟩,⟨⟨coefficient_12,coefficient_13⟩,⟨coefficient_14,coefficient_15⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_16,coefficient_17⟩,⟨coefficient_18,coefficient_19⟩⟩,⟨⟨coefficient_20,coefficient_21⟩,⟨coefficient_22,coefficient_23⟩⟩⟩,⟨⟨⟨coefficient_24,coefficient_25⟩,⟨coefficient_26,coefficient_27⟩⟩,⟨⟨coefficient_28,coefficient_29⟩,⟨coefficient_30,coefficient_31⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_32,coefficient_33⟩,⟨coefficient_34,coefficient_35⟩⟩,⟨⟨coefficient_36,coefficient_37⟩,⟨coefficient_38,coefficient_39⟩⟩⟩,⟨⟨⟨coefficient_40,coefficient_41⟩,⟨coefficient_42,coefficient_43⟩⟩,⟨⟨coefficient_44,coefficient_45⟩,⟨coefficient_46,coefficient_47⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_48,coefficient_49⟩,⟨coefficient_50,coefficient_51⟩⟩,⟨⟨coefficient_52,coefficient_53⟩,⟨coefficient_54,coefficient_55⟩⟩⟩,⟨⟨⟨coefficient_56,coefficient_57⟩,⟨coefficient_58,coefficient_59⟩⟩,⟨⟨coefficient_60,coefficient_61⟩,⟨coefficient_62,coefficient_63⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1088 : Rep := ⟨![0,16,8,24],508⟩
def representative_1089 : Rep := ⟨![0,16,8,25],508⟩
def representative_1090 : Rep := ⟨![0,16,8,26],508⟩
def representative_1091 : Rep := ⟨![0,16,9,25],508⟩
def representative_1092 : Rep := ⟨![0,16,9,26],508⟩
def representative_1093 : Rep := ⟨![0,16,9,27],508⟩
def representative_1094 : Rep := ⟨![0,16,10,26],508⟩
def representative_1095 : Rep := ⟨![0,17,1,16],508⟩
def representative_1096 : Rep := ⟨![0,17,1,18],508⟩
def representative_1097 : Rep := ⟨![0,17,1,19],508⟩
def representative_1098 : Rep := ⟨![0,17,2,19],508⟩
def representative_1099 : Rep := ⟨![0,17,3,18],508⟩
def representative_1100 : Rep := ⟨![0,17,4,21],508⟩
def representative_1101 : Rep := ⟨![0,17,4,22],508⟩
def representative_1102 : Rep := ⟨![0,17,4,23],508⟩
def representative_1103 : Rep := ⟨![0,17,5,20],508⟩
def representative_1104 : Rep := ⟨![0,17,5,22],508⟩
def representative_1105 : Rep := ⟨![0,17,5,23],508⟩
def representative_1106 : Rep := ⟨![0,17,6,23],508⟩
def representative_1107 : Rep := ⟨![0,17,7,22],508⟩
def representative_1108 : Rep := ⟨![0,17,8,25],508⟩
def representative_1109 : Rep := ⟨![0,17,8,26],508⟩
def representative_1110 : Rep := ⟨![0,17,8,27],508⟩
def representative_1111 : Rep := ⟨![0,17,10,27],508⟩
def representative_1112 : Rep := ⟨![0,18,1,19],508⟩
def representative_1113 : Rep := ⟨![0,18,2,16],508⟩
def representative_1114 : Rep := ⟨![0,18,4,22],508⟩
def representative_1115 : Rep := ⟨![0,18,5,23],508⟩
def representative_1116 : Rep := ⟨![0,18,6,20],508⟩
def representative_1117 : Rep := ⟨![0,18,8,26],508⟩
def representative_1118 : Rep := ⟨![0,18,9,27],508⟩
theorem coefficient_1088 : validRep representative_1088 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1088)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1089 : validRep representative_1089 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1089)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1090 : validRep representative_1090 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1090)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1091 : validRep representative_1091 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1091)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1092 : validRep representative_1092 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1092)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1093 : validRep representative_1093 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1093)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1094 : validRep representative_1094 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1094)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1095 : validRep representative_1095 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1095)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1096 : validRep representative_1096 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1096)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1097 : validRep representative_1097 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1097)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1098 : validRep representative_1098 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1098)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1099 : validRep representative_1099 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1099)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1100 : validRep representative_1100 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1100)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1101 : validRep representative_1101 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1101)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1102 : validRep representative_1102 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1102)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1103 : validRep representative_1103 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1103)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1104 : validRep representative_1104 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1104)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1105 : validRep representative_1105 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1105)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1106 : validRep representative_1106 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1106)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1107 : validRep representative_1107 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1107)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1108 : validRep representative_1108 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1108)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1109 : validRep representative_1109 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1109)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1110 : validRep representative_1110 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1110)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1111 : validRep representative_1111 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1111)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1112 : validRep representative_1112 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1112)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1113 : validRep representative_1113 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1113)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1114 : validRep representative_1114 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1114)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1115 : validRep representative_1115 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1115)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1116 : validRep representative_1116 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1116)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1117 : validRep representative_1117 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1117)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1118 : validRep representative_1118 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1118)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_017 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1103 (QuarticIntegerRepresentativeTree.Tree.branch 1095 (QuarticIntegerRepresentativeTree.Tree.branch 1091 (QuarticIntegerRepresentativeTree.Tree.branch 1089 (QuarticIntegerRepresentativeTree.Tree.leaf 1088 representative_1088) (QuarticIntegerRepresentativeTree.Tree.branch 1090 (QuarticIntegerRepresentativeTree.Tree.leaf 1089 representative_1089) (QuarticIntegerRepresentativeTree.Tree.leaf 1090 representative_1090))) (QuarticIntegerRepresentativeTree.Tree.branch 1093 (QuarticIntegerRepresentativeTree.Tree.branch 1092 (QuarticIntegerRepresentativeTree.Tree.leaf 1091 representative_1091) (QuarticIntegerRepresentativeTree.Tree.leaf 1092 representative_1092)) (QuarticIntegerRepresentativeTree.Tree.branch 1094 (QuarticIntegerRepresentativeTree.Tree.leaf 1093 representative_1093) (QuarticIntegerRepresentativeTree.Tree.leaf 1094 representative_1094)))) (QuarticIntegerRepresentativeTree.Tree.branch 1099 (QuarticIntegerRepresentativeTree.Tree.branch 1097 (QuarticIntegerRepresentativeTree.Tree.branch 1096 (QuarticIntegerRepresentativeTree.Tree.leaf 1095 representative_1095) (QuarticIntegerRepresentativeTree.Tree.leaf 1096 representative_1096)) (QuarticIntegerRepresentativeTree.Tree.branch 1098 (QuarticIntegerRepresentativeTree.Tree.leaf 1097 representative_1097) (QuarticIntegerRepresentativeTree.Tree.leaf 1098 representative_1098))) (QuarticIntegerRepresentativeTree.Tree.branch 1101 (QuarticIntegerRepresentativeTree.Tree.branch 1100 (QuarticIntegerRepresentativeTree.Tree.leaf 1099 representative_1099) (QuarticIntegerRepresentativeTree.Tree.leaf 1100 representative_1100)) (QuarticIntegerRepresentativeTree.Tree.branch 1102 (QuarticIntegerRepresentativeTree.Tree.leaf 1101 representative_1101) (QuarticIntegerRepresentativeTree.Tree.leaf 1102 representative_1102))))) (QuarticIntegerRepresentativeTree.Tree.branch 1111 (QuarticIntegerRepresentativeTree.Tree.branch 1107 (QuarticIntegerRepresentativeTree.Tree.branch 1105 (QuarticIntegerRepresentativeTree.Tree.branch 1104 (QuarticIntegerRepresentativeTree.Tree.leaf 1103 representative_1103) (QuarticIntegerRepresentativeTree.Tree.leaf 1104 representative_1104)) (QuarticIntegerRepresentativeTree.Tree.branch 1106 (QuarticIntegerRepresentativeTree.Tree.leaf 1105 representative_1105) (QuarticIntegerRepresentativeTree.Tree.leaf 1106 representative_1106))) (QuarticIntegerRepresentativeTree.Tree.branch 1109 (QuarticIntegerRepresentativeTree.Tree.branch 1108 (QuarticIntegerRepresentativeTree.Tree.leaf 1107 representative_1107) (QuarticIntegerRepresentativeTree.Tree.leaf 1108 representative_1108)) (QuarticIntegerRepresentativeTree.Tree.branch 1110 (QuarticIntegerRepresentativeTree.Tree.leaf 1109 representative_1109) (QuarticIntegerRepresentativeTree.Tree.leaf 1110 representative_1110)))) (QuarticIntegerRepresentativeTree.Tree.branch 1115 (QuarticIntegerRepresentativeTree.Tree.branch 1113 (QuarticIntegerRepresentativeTree.Tree.branch 1112 (QuarticIntegerRepresentativeTree.Tree.leaf 1111 representative_1111) (QuarticIntegerRepresentativeTree.Tree.leaf 1112 representative_1112)) (QuarticIntegerRepresentativeTree.Tree.branch 1114 (QuarticIntegerRepresentativeTree.Tree.leaf 1113 representative_1113) (QuarticIntegerRepresentativeTree.Tree.leaf 1114 representative_1114))) (QuarticIntegerRepresentativeTree.Tree.branch 1117 (QuarticIntegerRepresentativeTree.Tree.branch 1116 (QuarticIntegerRepresentativeTree.Tree.leaf 1115 representative_1115) (QuarticIntegerRepresentativeTree.Tree.leaf 1116 representative_1116)) (QuarticIntegerRepresentativeTree.Tree.branch 1118 (QuarticIntegerRepresentativeTree.Tree.leaf 1117 representative_1117) (QuarticIntegerRepresentativeTree.Tree.leaf 1118 representative_1118))))))
theorem accepted_017 : All validRep tree_017 := ⟨⟨⟨⟨coefficient_1088,⟨coefficient_1089,coefficient_1090⟩⟩,⟨⟨coefficient_1091,coefficient_1092⟩,⟨coefficient_1093,coefficient_1094⟩⟩⟩,⟨⟨⟨coefficient_1095,coefficient_1096⟩,⟨coefficient_1097,coefficient_1098⟩⟩,⟨⟨coefficient_1099,coefficient_1100⟩,⟨coefficient_1101,coefficient_1102⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1103,coefficient_1104⟩,⟨coefficient_1105,coefficient_1106⟩⟩,⟨⟨coefficient_1107,coefficient_1108⟩,⟨coefficient_1109,coefficient_1110⟩⟩⟩,⟨⟨⟨coefficient_1111,coefficient_1112⟩,⟨coefficient_1113,coefficient_1114⟩⟩,⟨⟨coefficient_1115,coefficient_1116⟩,⟨coefficient_1117,coefficient_1118⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

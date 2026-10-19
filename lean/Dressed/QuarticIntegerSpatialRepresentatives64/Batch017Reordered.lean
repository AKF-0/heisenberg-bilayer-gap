import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1088 : Rep := ⟨![0,3,5,24],239⟩
def representative_1089 : Rep := ⟨![0,3,5,25],241⟩
def representative_1090 : Rep := ⟨![0,3,5,26],238⟩
def representative_1091 : Rep := ⟨![0,3,5,27],256⟩
def representative_1092 : Rep := ⟨![0,3,5,28],238⟩
def representative_1093 : Rep := ⟨![0,3,5,29],256⟩
def representative_1094 : Rep := ⟨![0,3,5,30],462⟩
def representative_1095 : Rep := ⟨![0,3,5,31],241⟩
def representative_1096 : Rep := ⟨![0,3,5,32],240⟩
def representative_1097 : Rep := ⟨![0,3,5,33],462⟩
def representative_1098 : Rep := ⟨![0,3,5,34],462⟩
def representative_1099 : Rep := ⟨![0,3,5,35],239⟩
def representative_1100 : Rep := ⟨![0,3,5,36],462⟩
def representative_1101 : Rep := ⟨![0,3,5,37],462⟩
def representative_1102 : Rep := ⟨![0,3,5,38],462⟩
def representative_1103 : Rep := ⟨![0,3,5,39],462⟩
def representative_1104 : Rep := ⟨![0,3,8,11],269⟩
def representative_1105 : Rep := ⟨![0,3,8,12],236⟩
def representative_1106 : Rep := ⟨![0,3,8,13],259⟩
def representative_1107 : Rep := ⟨![0,3,8,17],158⟩
def representative_1108 : Rep := ⟨![0,3,8,18],260⟩
def representative_1109 : Rep := ⟨![0,3,8,19],238⟩
def representative_1110 : Rep := ⟨![0,3,8,20],243⟩
def representative_1111 : Rep := ⟨![0,3,8,21],462⟩
def representative_1112 : Rep := ⟨![0,3,8,22],258⟩
def representative_1113 : Rep := ⟨![0,3,8,23],159⟩
def representative_1114 : Rep := ⟨![0,3,8,25],254⟩
def representative_1115 : Rep := ⟨![0,3,8,26],462⟩
def representative_1116 : Rep := ⟨![0,3,8,27],241⟩
def representative_1117 : Rep := ⟨![0,3,8,28],462⟩
def representative_1118 : Rep := ⟨![0,3,8,29],462⟩
def representative_1119 : Rep := ⟨![0,3,8,30],462⟩
def representative_1120 : Rep := ⟨![0,3,8,31],254⟩
def representative_1121 : Rep := ⟨![0,3,8,33],462⟩
def representative_1122 : Rep := ⟨![0,3,8,34],462⟩
def representative_1123 : Rep := ⟨![0,3,8,35],462⟩
def representative_1124 : Rep := ⟨![0,3,8,36],462⟩
def representative_1125 : Rep := ⟨![0,3,8,37],462⟩
def representative_1126 : Rep := ⟨![0,3,8,38],462⟩
def representative_1127 : Rep := ⟨![0,3,8,39],462⟩
def representative_1128 : Rep := ⟨![0,3,8,40],201⟩
def representative_1129 : Rep := ⟨![0,3,8,41],263⟩
def representative_1130 : Rep := ⟨![0,3,8,42],462⟩
def representative_1131 : Rep := ⟨![0,3,8,43],241⟩
def representative_1132 : Rep := ⟨![0,3,8,44],462⟩
def representative_1133 : Rep := ⟨![0,3,8,45],462⟩
def representative_1134 : Rep := ⟨![0,3,8,46],462⟩
def representative_1135 : Rep := ⟨![0,3,8,47],263⟩
def representative_1136 : Rep := ⟨![0,3,8,49],154⟩
def representative_1137 : Rep := ⟨![0,3,8,50],271⟩
def representative_1138 : Rep := ⟨![0,3,8,51],238⟩
def representative_1139 : Rep := ⟨![0,3,8,52],243⟩
def representative_1140 : Rep := ⟨![0,3,8,53],462⟩
def representative_1141 : Rep := ⟨![0,3,8,54],269⟩
def representative_1142 : Rep := ⟨![0,3,8,55],154⟩
def representative_1143 : Rep := ⟨![0,3,8,57],376⟩
def representative_1144 : Rep := ⟨![0,3,8,58],152⟩
def representative_1145 : Rep := ⟨![0,3,8,59],274⟩
def representative_1146 : Rep := ⟨![0,3,8,60],236⟩
def representative_1147 : Rep := ⟨![0,3,8,61],264⟩
def representative_1148 : Rep := ⟨![0,3,8,62],154⟩
def representative_1149 : Rep := ⟨![0,3,8,63],373⟩
def representative_1150 : Rep := ⟨![0,3,9,12],296⟩
def representative_1151 : Rep := ⟨![0,3,9,13],231⟩
theorem coefficient_1088 : validRep representative_1088 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1088)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_1089 : validRep representative_1089 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1089)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1090 : validRep representative_1090 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1090)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1091 : validRep representative_1091 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1091)=dictionary64.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_1092 : validRep representative_1092 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1092)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1093 : validRep representative_1093 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1093)=dictionary64.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_1094 : validRep representative_1094 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1094)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1095 : validRep representative_1095 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1095)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1096 : validRep representative_1096 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1096)=dictionary64.getD 240 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_240]
  decide +kernel
theorem coefficient_1097 : validRep representative_1097 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1097)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1098 : validRep representative_1098 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1098)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1099 : validRep representative_1099 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1099)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_1100 : validRep representative_1100 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1100)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1101 : validRep representative_1101 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1101)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1102 : validRep representative_1102 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1102)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1103 : validRep representative_1103 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1103)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1104 : validRep representative_1104 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1104)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_1105 : validRep representative_1105 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1105)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1106 : validRep representative_1106 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1106)=dictionary64.getD 259 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_259]
  decide +kernel
theorem coefficient_1107 : validRep representative_1107 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1107)=dictionary64.getD 158 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_158]
  decide +kernel
theorem coefficient_1108 : validRep representative_1108 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1108)=dictionary64.getD 260 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_260]
  decide +kernel
theorem coefficient_1109 : validRep representative_1109 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1109)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1110 : validRep representative_1110 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1110)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1111 : validRep representative_1111 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1111)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1112 : validRep representative_1112 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1112)=dictionary64.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_1113 : validRep representative_1113 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1113)=dictionary64.getD 159 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_159]
  decide +kernel
theorem coefficient_1114 : validRep representative_1114 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1114)=dictionary64.getD 254 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_254]
  decide +kernel
theorem coefficient_1115 : validRep representative_1115 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1115)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1116 : validRep representative_1116 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1116)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1117 : validRep representative_1117 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1117)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1118 : validRep representative_1118 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1118)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1119 : validRep representative_1119 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1119)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1120 : validRep representative_1120 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1120)=dictionary64.getD 254 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_254]
  decide +kernel
theorem coefficient_1121 : validRep representative_1121 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1121)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1122 : validRep representative_1122 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1122)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1123 : validRep representative_1123 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1123)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1124 : validRep representative_1124 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1124)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1125 : validRep representative_1125 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1125)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1126 : validRep representative_1126 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1126)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1127 : validRep representative_1127 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1127)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1128 : validRep representative_1128 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1128)=dictionary64.getD 201 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_201]
  decide +kernel
theorem coefficient_1129 : validRep representative_1129 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1129)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_1130 : validRep representative_1130 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1130)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1131 : validRep representative_1131 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1131)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1132 : validRep representative_1132 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1132)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1133 : validRep representative_1133 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1133)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1134 : validRep representative_1134 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1134)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1135 : validRep representative_1135 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1135)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_1136 : validRep representative_1136 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1136)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_1137 : validRep representative_1137 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1137)=dictionary64.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_1138 : validRep representative_1138 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1138)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1139 : validRep representative_1139 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1139)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1140 : validRep representative_1140 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1140)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1141 : validRep representative_1141 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1141)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_1142 : validRep representative_1142 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1142)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_1143 : validRep representative_1143 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1143)=dictionary64.getD 376 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_376]
  decide +kernel
theorem coefficient_1144 : validRep representative_1144 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1144)=dictionary64.getD 152 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_152]
  decide +kernel
theorem coefficient_1145 : validRep representative_1145 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1145)=dictionary64.getD 274 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_274]
  decide +kernel
theorem coefficient_1146 : validRep representative_1146 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1146)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1147 : validRep representative_1147 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1147)=dictionary64.getD 264 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_264]
  decide +kernel
theorem coefficient_1148 : validRep representative_1148 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1148)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_1149 : validRep representative_1149 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1149)=dictionary64.getD 373 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_373]
  decide +kernel
theorem coefficient_1150 : validRep representative_1150 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1150)=dictionary64.getD 296 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_296]
  decide +kernel
theorem coefficient_1151 : validRep representative_1151 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1151)=dictionary64.getD 231 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_231]
  decide +kernel
def tree_017 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1120 (QuarticIntegerRepresentativeTree.Tree.branch 1104 (QuarticIntegerRepresentativeTree.Tree.branch 1096 (QuarticIntegerRepresentativeTree.Tree.branch 1092 (QuarticIntegerRepresentativeTree.Tree.branch 1090 (QuarticIntegerRepresentativeTree.Tree.branch 1089 (QuarticIntegerRepresentativeTree.Tree.leaf 1088 representative_1088) (QuarticIntegerRepresentativeTree.Tree.leaf 1089 representative_1089)) (QuarticIntegerRepresentativeTree.Tree.branch 1091 (QuarticIntegerRepresentativeTree.Tree.leaf 1090 representative_1090) (QuarticIntegerRepresentativeTree.Tree.leaf 1091 representative_1091))) (QuarticIntegerRepresentativeTree.Tree.branch 1094 (QuarticIntegerRepresentativeTree.Tree.branch 1093 (QuarticIntegerRepresentativeTree.Tree.leaf 1092 representative_1092) (QuarticIntegerRepresentativeTree.Tree.leaf 1093 representative_1093)) (QuarticIntegerRepresentativeTree.Tree.branch 1095 (QuarticIntegerRepresentativeTree.Tree.leaf 1094 representative_1094) (QuarticIntegerRepresentativeTree.Tree.leaf 1095 representative_1095)))) (QuarticIntegerRepresentativeTree.Tree.branch 1100 (QuarticIntegerRepresentativeTree.Tree.branch 1098 (QuarticIntegerRepresentativeTree.Tree.branch 1097 (QuarticIntegerRepresentativeTree.Tree.leaf 1096 representative_1096) (QuarticIntegerRepresentativeTree.Tree.leaf 1097 representative_1097)) (QuarticIntegerRepresentativeTree.Tree.branch 1099 (QuarticIntegerRepresentativeTree.Tree.leaf 1098 representative_1098) (QuarticIntegerRepresentativeTree.Tree.leaf 1099 representative_1099))) (QuarticIntegerRepresentativeTree.Tree.branch 1102 (QuarticIntegerRepresentativeTree.Tree.branch 1101 (QuarticIntegerRepresentativeTree.Tree.leaf 1100 representative_1100) (QuarticIntegerRepresentativeTree.Tree.leaf 1101 representative_1101)) (QuarticIntegerRepresentativeTree.Tree.branch 1103 (QuarticIntegerRepresentativeTree.Tree.leaf 1102 representative_1102) (QuarticIntegerRepresentativeTree.Tree.leaf 1103 representative_1103))))) (QuarticIntegerRepresentativeTree.Tree.branch 1112 (QuarticIntegerRepresentativeTree.Tree.branch 1108 (QuarticIntegerRepresentativeTree.Tree.branch 1106 (QuarticIntegerRepresentativeTree.Tree.branch 1105 (QuarticIntegerRepresentativeTree.Tree.leaf 1104 representative_1104) (QuarticIntegerRepresentativeTree.Tree.leaf 1105 representative_1105)) (QuarticIntegerRepresentativeTree.Tree.branch 1107 (QuarticIntegerRepresentativeTree.Tree.leaf 1106 representative_1106) (QuarticIntegerRepresentativeTree.Tree.leaf 1107 representative_1107))) (QuarticIntegerRepresentativeTree.Tree.branch 1110 (QuarticIntegerRepresentativeTree.Tree.branch 1109 (QuarticIntegerRepresentativeTree.Tree.leaf 1108 representative_1108) (QuarticIntegerRepresentativeTree.Tree.leaf 1109 representative_1109)) (QuarticIntegerRepresentativeTree.Tree.branch 1111 (QuarticIntegerRepresentativeTree.Tree.leaf 1110 representative_1110) (QuarticIntegerRepresentativeTree.Tree.leaf 1111 representative_1111)))) (QuarticIntegerRepresentativeTree.Tree.branch 1116 (QuarticIntegerRepresentativeTree.Tree.branch 1114 (QuarticIntegerRepresentativeTree.Tree.branch 1113 (QuarticIntegerRepresentativeTree.Tree.leaf 1112 representative_1112) (QuarticIntegerRepresentativeTree.Tree.leaf 1113 representative_1113)) (QuarticIntegerRepresentativeTree.Tree.branch 1115 (QuarticIntegerRepresentativeTree.Tree.leaf 1114 representative_1114) (QuarticIntegerRepresentativeTree.Tree.leaf 1115 representative_1115))) (QuarticIntegerRepresentativeTree.Tree.branch 1118 (QuarticIntegerRepresentativeTree.Tree.branch 1117 (QuarticIntegerRepresentativeTree.Tree.leaf 1116 representative_1116) (QuarticIntegerRepresentativeTree.Tree.leaf 1117 representative_1117)) (QuarticIntegerRepresentativeTree.Tree.branch 1119 (QuarticIntegerRepresentativeTree.Tree.leaf 1118 representative_1118) (QuarticIntegerRepresentativeTree.Tree.leaf 1119 representative_1119)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1136 (QuarticIntegerRepresentativeTree.Tree.branch 1128 (QuarticIntegerRepresentativeTree.Tree.branch 1124 (QuarticIntegerRepresentativeTree.Tree.branch 1122 (QuarticIntegerRepresentativeTree.Tree.branch 1121 (QuarticIntegerRepresentativeTree.Tree.leaf 1120 representative_1120) (QuarticIntegerRepresentativeTree.Tree.leaf 1121 representative_1121)) (QuarticIntegerRepresentativeTree.Tree.branch 1123 (QuarticIntegerRepresentativeTree.Tree.leaf 1122 representative_1122) (QuarticIntegerRepresentativeTree.Tree.leaf 1123 representative_1123))) (QuarticIntegerRepresentativeTree.Tree.branch 1126 (QuarticIntegerRepresentativeTree.Tree.branch 1125 (QuarticIntegerRepresentativeTree.Tree.leaf 1124 representative_1124) (QuarticIntegerRepresentativeTree.Tree.leaf 1125 representative_1125)) (QuarticIntegerRepresentativeTree.Tree.branch 1127 (QuarticIntegerRepresentativeTree.Tree.leaf 1126 representative_1126) (QuarticIntegerRepresentativeTree.Tree.leaf 1127 representative_1127)))) (QuarticIntegerRepresentativeTree.Tree.branch 1132 (QuarticIntegerRepresentativeTree.Tree.branch 1130 (QuarticIntegerRepresentativeTree.Tree.branch 1129 (QuarticIntegerRepresentativeTree.Tree.leaf 1128 representative_1128) (QuarticIntegerRepresentativeTree.Tree.leaf 1129 representative_1129)) (QuarticIntegerRepresentativeTree.Tree.branch 1131 (QuarticIntegerRepresentativeTree.Tree.leaf 1130 representative_1130) (QuarticIntegerRepresentativeTree.Tree.leaf 1131 representative_1131))) (QuarticIntegerRepresentativeTree.Tree.branch 1134 (QuarticIntegerRepresentativeTree.Tree.branch 1133 (QuarticIntegerRepresentativeTree.Tree.leaf 1132 representative_1132) (QuarticIntegerRepresentativeTree.Tree.leaf 1133 representative_1133)) (QuarticIntegerRepresentativeTree.Tree.branch 1135 (QuarticIntegerRepresentativeTree.Tree.leaf 1134 representative_1134) (QuarticIntegerRepresentativeTree.Tree.leaf 1135 representative_1135))))) (QuarticIntegerRepresentativeTree.Tree.branch 1144 (QuarticIntegerRepresentativeTree.Tree.branch 1140 (QuarticIntegerRepresentativeTree.Tree.branch 1138 (QuarticIntegerRepresentativeTree.Tree.branch 1137 (QuarticIntegerRepresentativeTree.Tree.leaf 1136 representative_1136) (QuarticIntegerRepresentativeTree.Tree.leaf 1137 representative_1137)) (QuarticIntegerRepresentativeTree.Tree.branch 1139 (QuarticIntegerRepresentativeTree.Tree.leaf 1138 representative_1138) (QuarticIntegerRepresentativeTree.Tree.leaf 1139 representative_1139))) (QuarticIntegerRepresentativeTree.Tree.branch 1142 (QuarticIntegerRepresentativeTree.Tree.branch 1141 (QuarticIntegerRepresentativeTree.Tree.leaf 1140 representative_1140) (QuarticIntegerRepresentativeTree.Tree.leaf 1141 representative_1141)) (QuarticIntegerRepresentativeTree.Tree.branch 1143 (QuarticIntegerRepresentativeTree.Tree.leaf 1142 representative_1142) (QuarticIntegerRepresentativeTree.Tree.leaf 1143 representative_1143)))) (QuarticIntegerRepresentativeTree.Tree.branch 1148 (QuarticIntegerRepresentativeTree.Tree.branch 1146 (QuarticIntegerRepresentativeTree.Tree.branch 1145 (QuarticIntegerRepresentativeTree.Tree.leaf 1144 representative_1144) (QuarticIntegerRepresentativeTree.Tree.leaf 1145 representative_1145)) (QuarticIntegerRepresentativeTree.Tree.branch 1147 (QuarticIntegerRepresentativeTree.Tree.leaf 1146 representative_1146) (QuarticIntegerRepresentativeTree.Tree.leaf 1147 representative_1147))) (QuarticIntegerRepresentativeTree.Tree.branch 1150 (QuarticIntegerRepresentativeTree.Tree.branch 1149 (QuarticIntegerRepresentativeTree.Tree.leaf 1148 representative_1148) (QuarticIntegerRepresentativeTree.Tree.leaf 1149 representative_1149)) (QuarticIntegerRepresentativeTree.Tree.branch 1151 (QuarticIntegerRepresentativeTree.Tree.leaf 1150 representative_1150) (QuarticIntegerRepresentativeTree.Tree.leaf 1151 representative_1151)))))))
theorem accepted_017 : All validRep tree_017 := ⟨⟨⟨⟨⟨⟨coefficient_1088,coefficient_1089⟩,⟨coefficient_1090,coefficient_1091⟩⟩,⟨⟨coefficient_1092,coefficient_1093⟩,⟨coefficient_1094,coefficient_1095⟩⟩⟩,⟨⟨⟨coefficient_1096,coefficient_1097⟩,⟨coefficient_1098,coefficient_1099⟩⟩,⟨⟨coefficient_1100,coefficient_1101⟩,⟨coefficient_1102,coefficient_1103⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1104,coefficient_1105⟩,⟨coefficient_1106,coefficient_1107⟩⟩,⟨⟨coefficient_1108,coefficient_1109⟩,⟨coefficient_1110,coefficient_1111⟩⟩⟩,⟨⟨⟨coefficient_1112,coefficient_1113⟩,⟨coefficient_1114,coefficient_1115⟩⟩,⟨⟨coefficient_1116,coefficient_1117⟩,⟨coefficient_1118,coefficient_1119⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1120,coefficient_1121⟩,⟨coefficient_1122,coefficient_1123⟩⟩,⟨⟨coefficient_1124,coefficient_1125⟩,⟨coefficient_1126,coefficient_1127⟩⟩⟩,⟨⟨⟨coefficient_1128,coefficient_1129⟩,⟨coefficient_1130,coefficient_1131⟩⟩,⟨⟨coefficient_1132,coefficient_1133⟩,⟨coefficient_1134,coefficient_1135⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1136,coefficient_1137⟩,⟨coefficient_1138,coefficient_1139⟩⟩,⟨⟨coefficient_1140,coefficient_1141⟩,⟨coefficient_1142,coefficient_1143⟩⟩⟩,⟨⟨⟨coefficient_1144,coefficient_1145⟩,⟨coefficient_1146,coefficient_1147⟩⟩,⟨⟨coefficient_1148,coefficient_1149⟩,⟨coefficient_1150,coefficient_1151⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

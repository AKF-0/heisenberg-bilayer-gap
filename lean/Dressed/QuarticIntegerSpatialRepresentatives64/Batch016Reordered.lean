import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1024 : Rep := ⟨![0,3,1,21],237⟩
def representative_1025 : Rep := ⟨![0,3,1,22],269⟩
def representative_1026 : Rep := ⟨![0,3,1,23],88⟩
def representative_1027 : Rep := ⟨![0,3,1,24],97⟩
def representative_1028 : Rep := ⟨![0,3,1,25],343⟩
def representative_1029 : Rep := ⟨![0,3,1,26],238⟩
def representative_1030 : Rep := ⟨![0,3,1,27],256⟩
def representative_1031 : Rep := ⟨![0,3,1,28],238⟩
def representative_1032 : Rep := ⟨![0,3,1,29],462⟩
def representative_1033 : Rep := ⟨![0,3,1,30],462⟩
def representative_1034 : Rep := ⟨![0,3,1,31],263⟩
def representative_1035 : Rep := ⟨![0,3,1,32],257⟩
def representative_1036 : Rep := ⟨![0,3,1,33],462⟩
def representative_1037 : Rep := ⟨![0,3,1,34],462⟩
def representative_1038 : Rep := ⟨![0,3,1,35],239⟩
def representative_1039 : Rep := ⟨![0,3,1,36],462⟩
def representative_1040 : Rep := ⟨![0,3,1,37],462⟩
def representative_1041 : Rep := ⟨![0,3,1,38],462⟩
def representative_1042 : Rep := ⟨![0,3,1,39],462⟩
def representative_1043 : Rep := ⟨![0,3,4,7],219⟩
def representative_1044 : Rep := ⟨![0,3,4,8],269⟩
def representative_1045 : Rep := ⟨![0,3,4,9],153⟩
def representative_1046 : Rep := ⟨![0,3,4,10],375⟩
def representative_1047 : Rep := ⟨![0,3,4,11],55⟩
def representative_1048 : Rep := ⟨![0,3,4,13],187⟩
def representative_1049 : Rep := ⟨![0,3,4,14],217⟩
def representative_1050 : Rep := ⟨![0,3,4,15],238⟩
def representative_1051 : Rep := ⟨![0,3,4,16],239⟩
def representative_1052 : Rep := ⟨![0,3,4,17],270⟩
def representative_1053 : Rep := ⟨![0,3,4,18],154⟩
def representative_1054 : Rep := ⟨![0,3,4,19],342⟩
def representative_1055 : Rep := ⟨![0,3,4,21],218⟩
def representative_1056 : Rep := ⟨![0,3,4,22],462⟩
def representative_1057 : Rep := ⟨![0,3,4,23],242⟩
def representative_1058 : Rep := ⟨![0,3,4,24],240⟩
def representative_1059 : Rep := ⟨![0,3,4,25],462⟩
def representative_1060 : Rep := ⟨![0,3,4,26],263⟩
def representative_1061 : Rep := ⟨![0,3,4,27],201⟩
def representative_1062 : Rep := ⟨![0,3,4,28],254⟩
def representative_1063 : Rep := ⟨![0,3,4,29],462⟩
def representative_1064 : Rep := ⟨![0,3,4,30],462⟩
def representative_1065 : Rep := ⟨![0,3,4,31],462⟩
def representative_1066 : Rep := ⟨![0,3,4,32],462⟩
def representative_1067 : Rep := ⟨![0,3,4,33],462⟩
def representative_1068 : Rep := ⟨![0,3,4,34],462⟩
def representative_1069 : Rep := ⟨![0,3,4,35],257⟩
def representative_1070 : Rep := ⟨![0,3,4,36],462⟩
def representative_1071 : Rep := ⟨![0,3,4,37],462⟩
def representative_1072 : Rep := ⟨![0,3,4,38],462⟩
def representative_1073 : Rep := ⟨![0,3,4,39],462⟩
def representative_1074 : Rep := ⟨![0,3,5,8],200⟩
def representative_1075 : Rep := ⟨![0,3,5,9],276⟩
def representative_1076 : Rep := ⟨![0,3,5,10],188⟩
def representative_1077 : Rep := ⟨![0,3,5,11],344⟩
def representative_1078 : Rep := ⟨![0,3,5,12],165⟩
def representative_1079 : Rep := ⟨![0,3,5,14],194⟩
def representative_1080 : Rep := ⟨![0,3,5,15],276⟩
def representative_1081 : Rep := ⟨![0,3,5,16],256⟩
def representative_1082 : Rep := ⟨![0,3,5,17],235⟩
def representative_1083 : Rep := ⟨![0,3,5,18],267⟩
def representative_1084 : Rep := ⟨![0,3,5,19],206⟩
def representative_1085 : Rep := ⟨![0,3,5,20],281⟩
def representative_1086 : Rep := ⟨![0,3,5,22],267⟩
def representative_1087 : Rep := ⟨![0,3,5,23],237⟩
theorem coefficient_1024 : validRep representative_1024 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1024)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1025 : validRep representative_1025 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1025)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_1026 : validRep representative_1026 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1026)=dictionary64.getD 88 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_88]
  decide +kernel
theorem coefficient_1027 : validRep representative_1027 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1027)=dictionary64.getD 97 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_97]
  decide +kernel
theorem coefficient_1028 : validRep representative_1028 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1028)=dictionary64.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_1029 : validRep representative_1029 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1029)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1030 : validRep representative_1030 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1030)=dictionary64.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_1031 : validRep representative_1031 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1031)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1032 : validRep representative_1032 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1032)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1033 : validRep representative_1033 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1033)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1034 : validRep representative_1034 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1034)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_1035 : validRep representative_1035 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1035)=dictionary64.getD 257 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_257]
  decide +kernel
theorem coefficient_1036 : validRep representative_1036 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1036)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1037 : validRep representative_1037 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1037)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1038 : validRep representative_1038 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1038)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_1039 : validRep representative_1039 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1039)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1040 : validRep representative_1040 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1040)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1041 : validRep representative_1041 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1041)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1042 : validRep representative_1042 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1042)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1043 : validRep representative_1043 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1043)=dictionary64.getD 219 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_219]
  decide +kernel
theorem coefficient_1044 : validRep representative_1044 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1044)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_1045 : validRep representative_1045 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1045)=dictionary64.getD 153 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_153]
  decide +kernel
theorem coefficient_1046 : validRep representative_1046 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1046)=dictionary64.getD 375 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_375]
  decide +kernel
theorem coefficient_1047 : validRep representative_1047 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1047)=dictionary64.getD 55 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_55]
  decide +kernel
theorem coefficient_1048 : validRep representative_1048 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1048)=dictionary64.getD 187 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_187]
  decide +kernel
theorem coefficient_1049 : validRep representative_1049 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1049)=dictionary64.getD 217 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_217]
  decide +kernel
theorem coefficient_1050 : validRep representative_1050 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1050)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1051 : validRep representative_1051 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1051)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_1052 : validRep representative_1052 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1052)=dictionary64.getD 270 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_270]
  decide +kernel
theorem coefficient_1053 : validRep representative_1053 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1053)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_1054 : validRep representative_1054 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1054)=dictionary64.getD 342 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_342]
  decide +kernel
theorem coefficient_1055 : validRep representative_1055 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1055)=dictionary64.getD 218 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_218]
  decide +kernel
theorem coefficient_1056 : validRep representative_1056 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1056)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1057 : validRep representative_1057 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1057)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1058 : validRep representative_1058 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1058)=dictionary64.getD 240 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_240]
  decide +kernel
theorem coefficient_1059 : validRep representative_1059 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1059)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1060 : validRep representative_1060 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1060)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_1061 : validRep representative_1061 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1061)=dictionary64.getD 201 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_201]
  decide +kernel
theorem coefficient_1062 : validRep representative_1062 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1062)=dictionary64.getD 254 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_254]
  decide +kernel
theorem coefficient_1063 : validRep representative_1063 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1063)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1064 : validRep representative_1064 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1064)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1065 : validRep representative_1065 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1065)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1066 : validRep representative_1066 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1066)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1067 : validRep representative_1067 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1067)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1068 : validRep representative_1068 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1068)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1069 : validRep representative_1069 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1069)=dictionary64.getD 257 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_257]
  decide +kernel
theorem coefficient_1070 : validRep representative_1070 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1070)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1071 : validRep representative_1071 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1071)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1072 : validRep representative_1072 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1072)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1073 : validRep representative_1073 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1073)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1074 : validRep representative_1074 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1074)=dictionary64.getD 200 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_200]
  decide +kernel
theorem coefficient_1075 : validRep representative_1075 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1075)=dictionary64.getD 276 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_276]
  decide +kernel
theorem coefficient_1076 : validRep representative_1076 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1076)=dictionary64.getD 188 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_188]
  decide +kernel
theorem coefficient_1077 : validRep representative_1077 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1077)=dictionary64.getD 344 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_344]
  decide +kernel
theorem coefficient_1078 : validRep representative_1078 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1078)=dictionary64.getD 165 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_165]
  decide +kernel
theorem coefficient_1079 : validRep representative_1079 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1079)=dictionary64.getD 194 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_194]
  decide +kernel
theorem coefficient_1080 : validRep representative_1080 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1080)=dictionary64.getD 276 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_276]
  decide +kernel
theorem coefficient_1081 : validRep representative_1081 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1081)=dictionary64.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_1082 : validRep representative_1082 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1082)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1083 : validRep representative_1083 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1083)=dictionary64.getD 267 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_267]
  decide +kernel
theorem coefficient_1084 : validRep representative_1084 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1084)=dictionary64.getD 206 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_206]
  decide +kernel
theorem coefficient_1085 : validRep representative_1085 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1085)=dictionary64.getD 281 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_281]
  decide +kernel
theorem coefficient_1086 : validRep representative_1086 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1086)=dictionary64.getD 267 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_267]
  decide +kernel
theorem coefficient_1087 : validRep representative_1087 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1087)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
def tree_016 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1056 (QuarticIntegerRepresentativeTree.Tree.branch 1040 (QuarticIntegerRepresentativeTree.Tree.branch 1032 (QuarticIntegerRepresentativeTree.Tree.branch 1028 (QuarticIntegerRepresentativeTree.Tree.branch 1026 (QuarticIntegerRepresentativeTree.Tree.branch 1025 (QuarticIntegerRepresentativeTree.Tree.leaf 1024 representative_1024) (QuarticIntegerRepresentativeTree.Tree.leaf 1025 representative_1025)) (QuarticIntegerRepresentativeTree.Tree.branch 1027 (QuarticIntegerRepresentativeTree.Tree.leaf 1026 representative_1026) (QuarticIntegerRepresentativeTree.Tree.leaf 1027 representative_1027))) (QuarticIntegerRepresentativeTree.Tree.branch 1030 (QuarticIntegerRepresentativeTree.Tree.branch 1029 (QuarticIntegerRepresentativeTree.Tree.leaf 1028 representative_1028) (QuarticIntegerRepresentativeTree.Tree.leaf 1029 representative_1029)) (QuarticIntegerRepresentativeTree.Tree.branch 1031 (QuarticIntegerRepresentativeTree.Tree.leaf 1030 representative_1030) (QuarticIntegerRepresentativeTree.Tree.leaf 1031 representative_1031)))) (QuarticIntegerRepresentativeTree.Tree.branch 1036 (QuarticIntegerRepresentativeTree.Tree.branch 1034 (QuarticIntegerRepresentativeTree.Tree.branch 1033 (QuarticIntegerRepresentativeTree.Tree.leaf 1032 representative_1032) (QuarticIntegerRepresentativeTree.Tree.leaf 1033 representative_1033)) (QuarticIntegerRepresentativeTree.Tree.branch 1035 (QuarticIntegerRepresentativeTree.Tree.leaf 1034 representative_1034) (QuarticIntegerRepresentativeTree.Tree.leaf 1035 representative_1035))) (QuarticIntegerRepresentativeTree.Tree.branch 1038 (QuarticIntegerRepresentativeTree.Tree.branch 1037 (QuarticIntegerRepresentativeTree.Tree.leaf 1036 representative_1036) (QuarticIntegerRepresentativeTree.Tree.leaf 1037 representative_1037)) (QuarticIntegerRepresentativeTree.Tree.branch 1039 (QuarticIntegerRepresentativeTree.Tree.leaf 1038 representative_1038) (QuarticIntegerRepresentativeTree.Tree.leaf 1039 representative_1039))))) (QuarticIntegerRepresentativeTree.Tree.branch 1048 (QuarticIntegerRepresentativeTree.Tree.branch 1044 (QuarticIntegerRepresentativeTree.Tree.branch 1042 (QuarticIntegerRepresentativeTree.Tree.branch 1041 (QuarticIntegerRepresentativeTree.Tree.leaf 1040 representative_1040) (QuarticIntegerRepresentativeTree.Tree.leaf 1041 representative_1041)) (QuarticIntegerRepresentativeTree.Tree.branch 1043 (QuarticIntegerRepresentativeTree.Tree.leaf 1042 representative_1042) (QuarticIntegerRepresentativeTree.Tree.leaf 1043 representative_1043))) (QuarticIntegerRepresentativeTree.Tree.branch 1046 (QuarticIntegerRepresentativeTree.Tree.branch 1045 (QuarticIntegerRepresentativeTree.Tree.leaf 1044 representative_1044) (QuarticIntegerRepresentativeTree.Tree.leaf 1045 representative_1045)) (QuarticIntegerRepresentativeTree.Tree.branch 1047 (QuarticIntegerRepresentativeTree.Tree.leaf 1046 representative_1046) (QuarticIntegerRepresentativeTree.Tree.leaf 1047 representative_1047)))) (QuarticIntegerRepresentativeTree.Tree.branch 1052 (QuarticIntegerRepresentativeTree.Tree.branch 1050 (QuarticIntegerRepresentativeTree.Tree.branch 1049 (QuarticIntegerRepresentativeTree.Tree.leaf 1048 representative_1048) (QuarticIntegerRepresentativeTree.Tree.leaf 1049 representative_1049)) (QuarticIntegerRepresentativeTree.Tree.branch 1051 (QuarticIntegerRepresentativeTree.Tree.leaf 1050 representative_1050) (QuarticIntegerRepresentativeTree.Tree.leaf 1051 representative_1051))) (QuarticIntegerRepresentativeTree.Tree.branch 1054 (QuarticIntegerRepresentativeTree.Tree.branch 1053 (QuarticIntegerRepresentativeTree.Tree.leaf 1052 representative_1052) (QuarticIntegerRepresentativeTree.Tree.leaf 1053 representative_1053)) (QuarticIntegerRepresentativeTree.Tree.branch 1055 (QuarticIntegerRepresentativeTree.Tree.leaf 1054 representative_1054) (QuarticIntegerRepresentativeTree.Tree.leaf 1055 representative_1055)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1072 (QuarticIntegerRepresentativeTree.Tree.branch 1064 (QuarticIntegerRepresentativeTree.Tree.branch 1060 (QuarticIntegerRepresentativeTree.Tree.branch 1058 (QuarticIntegerRepresentativeTree.Tree.branch 1057 (QuarticIntegerRepresentativeTree.Tree.leaf 1056 representative_1056) (QuarticIntegerRepresentativeTree.Tree.leaf 1057 representative_1057)) (QuarticIntegerRepresentativeTree.Tree.branch 1059 (QuarticIntegerRepresentativeTree.Tree.leaf 1058 representative_1058) (QuarticIntegerRepresentativeTree.Tree.leaf 1059 representative_1059))) (QuarticIntegerRepresentativeTree.Tree.branch 1062 (QuarticIntegerRepresentativeTree.Tree.branch 1061 (QuarticIntegerRepresentativeTree.Tree.leaf 1060 representative_1060) (QuarticIntegerRepresentativeTree.Tree.leaf 1061 representative_1061)) (QuarticIntegerRepresentativeTree.Tree.branch 1063 (QuarticIntegerRepresentativeTree.Tree.leaf 1062 representative_1062) (QuarticIntegerRepresentativeTree.Tree.leaf 1063 representative_1063)))) (QuarticIntegerRepresentativeTree.Tree.branch 1068 (QuarticIntegerRepresentativeTree.Tree.branch 1066 (QuarticIntegerRepresentativeTree.Tree.branch 1065 (QuarticIntegerRepresentativeTree.Tree.leaf 1064 representative_1064) (QuarticIntegerRepresentativeTree.Tree.leaf 1065 representative_1065)) (QuarticIntegerRepresentativeTree.Tree.branch 1067 (QuarticIntegerRepresentativeTree.Tree.leaf 1066 representative_1066) (QuarticIntegerRepresentativeTree.Tree.leaf 1067 representative_1067))) (QuarticIntegerRepresentativeTree.Tree.branch 1070 (QuarticIntegerRepresentativeTree.Tree.branch 1069 (QuarticIntegerRepresentativeTree.Tree.leaf 1068 representative_1068) (QuarticIntegerRepresentativeTree.Tree.leaf 1069 representative_1069)) (QuarticIntegerRepresentativeTree.Tree.branch 1071 (QuarticIntegerRepresentativeTree.Tree.leaf 1070 representative_1070) (QuarticIntegerRepresentativeTree.Tree.leaf 1071 representative_1071))))) (QuarticIntegerRepresentativeTree.Tree.branch 1080 (QuarticIntegerRepresentativeTree.Tree.branch 1076 (QuarticIntegerRepresentativeTree.Tree.branch 1074 (QuarticIntegerRepresentativeTree.Tree.branch 1073 (QuarticIntegerRepresentativeTree.Tree.leaf 1072 representative_1072) (QuarticIntegerRepresentativeTree.Tree.leaf 1073 representative_1073)) (QuarticIntegerRepresentativeTree.Tree.branch 1075 (QuarticIntegerRepresentativeTree.Tree.leaf 1074 representative_1074) (QuarticIntegerRepresentativeTree.Tree.leaf 1075 representative_1075))) (QuarticIntegerRepresentativeTree.Tree.branch 1078 (QuarticIntegerRepresentativeTree.Tree.branch 1077 (QuarticIntegerRepresentativeTree.Tree.leaf 1076 representative_1076) (QuarticIntegerRepresentativeTree.Tree.leaf 1077 representative_1077)) (QuarticIntegerRepresentativeTree.Tree.branch 1079 (QuarticIntegerRepresentativeTree.Tree.leaf 1078 representative_1078) (QuarticIntegerRepresentativeTree.Tree.leaf 1079 representative_1079)))) (QuarticIntegerRepresentativeTree.Tree.branch 1084 (QuarticIntegerRepresentativeTree.Tree.branch 1082 (QuarticIntegerRepresentativeTree.Tree.branch 1081 (QuarticIntegerRepresentativeTree.Tree.leaf 1080 representative_1080) (QuarticIntegerRepresentativeTree.Tree.leaf 1081 representative_1081)) (QuarticIntegerRepresentativeTree.Tree.branch 1083 (QuarticIntegerRepresentativeTree.Tree.leaf 1082 representative_1082) (QuarticIntegerRepresentativeTree.Tree.leaf 1083 representative_1083))) (QuarticIntegerRepresentativeTree.Tree.branch 1086 (QuarticIntegerRepresentativeTree.Tree.branch 1085 (QuarticIntegerRepresentativeTree.Tree.leaf 1084 representative_1084) (QuarticIntegerRepresentativeTree.Tree.leaf 1085 representative_1085)) (QuarticIntegerRepresentativeTree.Tree.branch 1087 (QuarticIntegerRepresentativeTree.Tree.leaf 1086 representative_1086) (QuarticIntegerRepresentativeTree.Tree.leaf 1087 representative_1087)))))))
theorem accepted_016 : All validRep tree_016 := ⟨⟨⟨⟨⟨⟨coefficient_1024,coefficient_1025⟩,⟨coefficient_1026,coefficient_1027⟩⟩,⟨⟨coefficient_1028,coefficient_1029⟩,⟨coefficient_1030,coefficient_1031⟩⟩⟩,⟨⟨⟨coefficient_1032,coefficient_1033⟩,⟨coefficient_1034,coefficient_1035⟩⟩,⟨⟨coefficient_1036,coefficient_1037⟩,⟨coefficient_1038,coefficient_1039⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1040,coefficient_1041⟩,⟨coefficient_1042,coefficient_1043⟩⟩,⟨⟨coefficient_1044,coefficient_1045⟩,⟨coefficient_1046,coefficient_1047⟩⟩⟩,⟨⟨⟨coefficient_1048,coefficient_1049⟩,⟨coefficient_1050,coefficient_1051⟩⟩,⟨⟨coefficient_1052,coefficient_1053⟩,⟨coefficient_1054,coefficient_1055⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1056,coefficient_1057⟩,⟨coefficient_1058,coefficient_1059⟩⟩,⟨⟨coefficient_1060,coefficient_1061⟩,⟨coefficient_1062,coefficient_1063⟩⟩⟩,⟨⟨⟨coefficient_1064,coefficient_1065⟩,⟨coefficient_1066,coefficient_1067⟩⟩,⟨⟨coefficient_1068,coefficient_1069⟩,⟨coefficient_1070,coefficient_1071⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1072,coefficient_1073⟩,⟨coefficient_1074,coefficient_1075⟩⟩,⟨⟨coefficient_1076,coefficient_1077⟩,⟨coefficient_1078,coefficient_1079⟩⟩⟩,⟨⟨⟨coefficient_1080,coefficient_1081⟩,⟨coefficient_1082,coefficient_1083⟩⟩,⟨⟨coefficient_1084,coefficient_1085⟩,⟨coefficient_1086,coefficient_1087⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

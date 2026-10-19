import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_64 : Rep := ⟨![0,1,3,32],257⟩
def representative_65 : Rep := ⟨![0,1,3,33],208⟩
def representative_66 : Rep := ⟨![0,1,3,34],462⟩
def representative_67 : Rep := ⟨![0,1,3,35],462⟩
def representative_68 : Rep := ⟨![0,1,3,36],462⟩
def representative_69 : Rep := ⟨![0,1,3,37],462⟩
def representative_70 : Rep := ⟨![0,1,3,38],462⟩
def representative_71 : Rep := ⟨![0,1,3,39],462⟩
def representative_72 : Rep := ⟨![0,1,4,5],185⟩
def representative_73 : Rep := ⟨![0,1,4,8],71⟩
def representative_74 : Rep := ⟨![0,1,4,9],66⟩
def representative_75 : Rep := ⟨![0,1,4,10],353⟩
def representative_76 : Rep := ⟨![0,1,4,11],179⟩
def representative_77 : Rep := ⟨![0,1,4,12],269⟩
def representative_78 : Rep := ⟨![0,1,4,13],238⟩
def representative_79 : Rep := ⟨![0,1,4,14],169⟩
def representative_80 : Rep := ⟨![0,1,4,15],357⟩
def representative_81 : Rep := ⟨![0,1,4,16],333⟩
def representative_82 : Rep := ⟨![0,1,4,17],328⟩
def representative_83 : Rep := ⟨![0,1,4,18],180⟩
def representative_84 : Rep := ⟨![0,1,4,19],270⟩
def representative_85 : Rep := ⟨![0,1,4,20],239⟩
def representative_86 : Rep := ⟨![0,1,4,21],242⟩
def representative_87 : Rep := ⟨![0,1,4,22],462⟩
def representative_88 : Rep := ⟨![0,1,4,23],170⟩
def representative_89 : Rep := ⟨![0,1,4,24],203⟩
def representative_90 : Rep := ⟨![0,1,4,25],208⟩
def representative_91 : Rep := ⟨![0,1,4,26],263⟩
def representative_92 : Rep := ⟨![0,1,4,27],462⟩
def representative_93 : Rep := ⟨![0,1,4,28],240⟩
def representative_94 : Rep := ⟨![0,1,4,29],462⟩
def representative_95 : Rep := ⟨![0,1,4,30],462⟩
def representative_96 : Rep := ⟨![0,1,4,31],462⟩
def representative_97 : Rep := ⟨![0,1,4,32],462⟩
def representative_98 : Rep := ⟨![0,1,4,33],257⟩
def representative_99 : Rep := ⟨![0,1,4,34],462⟩
def representative_100 : Rep := ⟨![0,1,4,35],462⟩
def representative_101 : Rep := ⟨![0,1,4,36],462⟩
def representative_102 : Rep := ⟨![0,1,4,37],462⟩
def representative_103 : Rep := ⟨![0,1,4,38],462⟩
def representative_104 : Rep := ⟨![0,1,4,39],462⟩
def representative_105 : Rep := ⟨![0,1,8,9],20⟩
def representative_106 : Rep := ⟨![0,1,8,10],451⟩
def representative_107 : Rep := ⟨![0,1,8,11],44⟩
def representative_108 : Rep := ⟨![0,1,8,12],163⟩
def representative_109 : Rep := ⟨![0,1,8,13],359⟩
def representative_110 : Rep := ⟨![0,1,8,14],34⟩
def representative_111 : Rep := ⟨![0,1,8,15],457⟩
def representative_112 : Rep := ⟨![0,1,8,17],442⟩
def representative_113 : Rep := ⟨![0,1,8,18],46⟩
def representative_114 : Rep := ⟨![0,1,8,19],139⟩
def representative_115 : Rep := ⟨![0,1,8,20],462⟩
def representative_116 : Rep := ⟨![0,1,8,21],462⟩
def representative_117 : Rep := ⟨![0,1,8,22],389⟩
def representative_118 : Rep := ⟨![0,1,8,23],32⟩
def representative_119 : Rep := ⟨![0,1,8,24],56⟩
def representative_120 : Rep := ⟨![0,1,8,25],74⟩
def representative_121 : Rep := ⟨![0,1,8,26],163⟩
def representative_122 : Rep := ⟨![0,1,8,27],462⟩
def representative_123 : Rep := ⟨![0,1,8,28],462⟩
def representative_124 : Rep := ⟨![0,1,8,29],462⟩
def representative_125 : Rep := ⟨![0,1,8,30],462⟩
def representative_126 : Rep := ⟨![0,1,8,31],383⟩
def representative_127 : Rep := ⟨![0,1,8,32],341⟩
theorem coefficient_64 : validRep representative_64 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_64)=dictionary64.getD 257 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_257]
  decide +kernel
theorem coefficient_65 : validRep representative_65 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_65)=dictionary64.getD 208 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_208]
  decide +kernel
theorem coefficient_66 : validRep representative_66 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_66)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_67 : validRep representative_67 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_67)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_68 : validRep representative_68 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_68)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_69 : validRep representative_69 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_69)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_70 : validRep representative_70 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_70)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_71 : validRep representative_71 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_71)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_72 : validRep representative_72 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_72)=dictionary64.getD 185 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_185]
  decide +kernel
theorem coefficient_73 : validRep representative_73 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_73)=dictionary64.getD 71 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_71]
  decide +kernel
theorem coefficient_74 : validRep representative_74 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_74)=dictionary64.getD 66 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_66]
  decide +kernel
theorem coefficient_75 : validRep representative_75 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_75)=dictionary64.getD 353 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_353]
  decide +kernel
theorem coefficient_76 : validRep representative_76 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_76)=dictionary64.getD 179 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_179]
  decide +kernel
theorem coefficient_77 : validRep representative_77 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_77)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_78 : validRep representative_78 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_78)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_79 : validRep representative_79 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_79)=dictionary64.getD 169 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_169]
  decide +kernel
theorem coefficient_80 : validRep representative_80 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_80)=dictionary64.getD 357 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_357]
  decide +kernel
theorem coefficient_81 : validRep representative_81 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_81)=dictionary64.getD 333 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_333]
  decide +kernel
theorem coefficient_82 : validRep representative_82 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_82)=dictionary64.getD 328 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_328]
  decide +kernel
theorem coefficient_83 : validRep representative_83 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_83)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_84 : validRep representative_84 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_84)=dictionary64.getD 270 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_270]
  decide +kernel
theorem coefficient_85 : validRep representative_85 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_85)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_86 : validRep representative_86 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_86)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_87 : validRep representative_87 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_87)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_88 : validRep representative_88 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_88)=dictionary64.getD 170 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_170]
  decide +kernel
theorem coefficient_89 : validRep representative_89 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_89)=dictionary64.getD 203 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_203]
  decide +kernel
theorem coefficient_90 : validRep representative_90 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_90)=dictionary64.getD 208 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_208]
  decide +kernel
theorem coefficient_91 : validRep representative_91 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_91)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_92 : validRep representative_92 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_92)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_93 : validRep representative_93 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_93)=dictionary64.getD 240 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_240]
  decide +kernel
theorem coefficient_94 : validRep representative_94 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_94)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_95 : validRep representative_95 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_95)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_96 : validRep representative_96 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_96)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_97 : validRep representative_97 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_97)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_98 : validRep representative_98 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_98)=dictionary64.getD 257 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_257]
  decide +kernel
theorem coefficient_99 : validRep representative_99 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_99)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_100 : validRep representative_100 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_100)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_101 : validRep representative_101 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_101)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_102 : validRep representative_102 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_102)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_103 : validRep representative_103 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_103)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_104 : validRep representative_104 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_104)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_105 : validRep representative_105 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_105)=dictionary64.getD 20 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_20]
  decide +kernel
theorem coefficient_106 : validRep representative_106 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_106)=dictionary64.getD 451 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_451]
  decide +kernel
theorem coefficient_107 : validRep representative_107 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_107)=dictionary64.getD 44 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_44]
  decide +kernel
theorem coefficient_108 : validRep representative_108 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_108)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_109 : validRep representative_109 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_109)=dictionary64.getD 359 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_359]
  decide +kernel
theorem coefficient_110 : validRep representative_110 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_110)=dictionary64.getD 34 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_34]
  decide +kernel
theorem coefficient_111 : validRep representative_111 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_111)=dictionary64.getD 457 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_457]
  decide +kernel
theorem coefficient_112 : validRep representative_112 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_112)=dictionary64.getD 442 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_442]
  decide +kernel
theorem coefficient_113 : validRep representative_113 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_113)=dictionary64.getD 46 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_46]
  decide +kernel
theorem coefficient_114 : validRep representative_114 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_114)=dictionary64.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_139]
  decide +kernel
theorem coefficient_115 : validRep representative_115 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_115)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_116 : validRep representative_116 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_116)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_117 : validRep representative_117 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_117)=dictionary64.getD 389 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_389]
  decide +kernel
theorem coefficient_118 : validRep representative_118 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_118)=dictionary64.getD 32 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_32]
  decide +kernel
theorem coefficient_119 : validRep representative_119 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_119)=dictionary64.getD 56 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_56]
  decide +kernel
theorem coefficient_120 : validRep representative_120 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_120)=dictionary64.getD 74 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_74]
  decide +kernel
theorem coefficient_121 : validRep representative_121 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_121)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_122 : validRep representative_122 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_122)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_123 : validRep representative_123 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_123)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_124 : validRep representative_124 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_124)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_125 : validRep representative_125 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_125)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_126 : validRep representative_126 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_126)=dictionary64.getD 383 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_383]
  decide +kernel
theorem coefficient_127 : validRep representative_127 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_127)=dictionary64.getD 341 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_341]
  decide +kernel
def tree_001 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 96 (QuarticIntegerRepresentativeTree.Tree.branch 80 (QuarticIntegerRepresentativeTree.Tree.branch 72 (QuarticIntegerRepresentativeTree.Tree.branch 68 (QuarticIntegerRepresentativeTree.Tree.branch 66 (QuarticIntegerRepresentativeTree.Tree.branch 65 (QuarticIntegerRepresentativeTree.Tree.leaf 64 representative_64) (QuarticIntegerRepresentativeTree.Tree.leaf 65 representative_65)) (QuarticIntegerRepresentativeTree.Tree.branch 67 (QuarticIntegerRepresentativeTree.Tree.leaf 66 representative_66) (QuarticIntegerRepresentativeTree.Tree.leaf 67 representative_67))) (QuarticIntegerRepresentativeTree.Tree.branch 70 (QuarticIntegerRepresentativeTree.Tree.branch 69 (QuarticIntegerRepresentativeTree.Tree.leaf 68 representative_68) (QuarticIntegerRepresentativeTree.Tree.leaf 69 representative_69)) (QuarticIntegerRepresentativeTree.Tree.branch 71 (QuarticIntegerRepresentativeTree.Tree.leaf 70 representative_70) (QuarticIntegerRepresentativeTree.Tree.leaf 71 representative_71)))) (QuarticIntegerRepresentativeTree.Tree.branch 76 (QuarticIntegerRepresentativeTree.Tree.branch 74 (QuarticIntegerRepresentativeTree.Tree.branch 73 (QuarticIntegerRepresentativeTree.Tree.leaf 72 representative_72) (QuarticIntegerRepresentativeTree.Tree.leaf 73 representative_73)) (QuarticIntegerRepresentativeTree.Tree.branch 75 (QuarticIntegerRepresentativeTree.Tree.leaf 74 representative_74) (QuarticIntegerRepresentativeTree.Tree.leaf 75 representative_75))) (QuarticIntegerRepresentativeTree.Tree.branch 78 (QuarticIntegerRepresentativeTree.Tree.branch 77 (QuarticIntegerRepresentativeTree.Tree.leaf 76 representative_76) (QuarticIntegerRepresentativeTree.Tree.leaf 77 representative_77)) (QuarticIntegerRepresentativeTree.Tree.branch 79 (QuarticIntegerRepresentativeTree.Tree.leaf 78 representative_78) (QuarticIntegerRepresentativeTree.Tree.leaf 79 representative_79))))) (QuarticIntegerRepresentativeTree.Tree.branch 88 (QuarticIntegerRepresentativeTree.Tree.branch 84 (QuarticIntegerRepresentativeTree.Tree.branch 82 (QuarticIntegerRepresentativeTree.Tree.branch 81 (QuarticIntegerRepresentativeTree.Tree.leaf 80 representative_80) (QuarticIntegerRepresentativeTree.Tree.leaf 81 representative_81)) (QuarticIntegerRepresentativeTree.Tree.branch 83 (QuarticIntegerRepresentativeTree.Tree.leaf 82 representative_82) (QuarticIntegerRepresentativeTree.Tree.leaf 83 representative_83))) (QuarticIntegerRepresentativeTree.Tree.branch 86 (QuarticIntegerRepresentativeTree.Tree.branch 85 (QuarticIntegerRepresentativeTree.Tree.leaf 84 representative_84) (QuarticIntegerRepresentativeTree.Tree.leaf 85 representative_85)) (QuarticIntegerRepresentativeTree.Tree.branch 87 (QuarticIntegerRepresentativeTree.Tree.leaf 86 representative_86) (QuarticIntegerRepresentativeTree.Tree.leaf 87 representative_87)))) (QuarticIntegerRepresentativeTree.Tree.branch 92 (QuarticIntegerRepresentativeTree.Tree.branch 90 (QuarticIntegerRepresentativeTree.Tree.branch 89 (QuarticIntegerRepresentativeTree.Tree.leaf 88 representative_88) (QuarticIntegerRepresentativeTree.Tree.leaf 89 representative_89)) (QuarticIntegerRepresentativeTree.Tree.branch 91 (QuarticIntegerRepresentativeTree.Tree.leaf 90 representative_90) (QuarticIntegerRepresentativeTree.Tree.leaf 91 representative_91))) (QuarticIntegerRepresentativeTree.Tree.branch 94 (QuarticIntegerRepresentativeTree.Tree.branch 93 (QuarticIntegerRepresentativeTree.Tree.leaf 92 representative_92) (QuarticIntegerRepresentativeTree.Tree.leaf 93 representative_93)) (QuarticIntegerRepresentativeTree.Tree.branch 95 (QuarticIntegerRepresentativeTree.Tree.leaf 94 representative_94) (QuarticIntegerRepresentativeTree.Tree.leaf 95 representative_95)))))) (QuarticIntegerRepresentativeTree.Tree.branch 112 (QuarticIntegerRepresentativeTree.Tree.branch 104 (QuarticIntegerRepresentativeTree.Tree.branch 100 (QuarticIntegerRepresentativeTree.Tree.branch 98 (QuarticIntegerRepresentativeTree.Tree.branch 97 (QuarticIntegerRepresentativeTree.Tree.leaf 96 representative_96) (QuarticIntegerRepresentativeTree.Tree.leaf 97 representative_97)) (QuarticIntegerRepresentativeTree.Tree.branch 99 (QuarticIntegerRepresentativeTree.Tree.leaf 98 representative_98) (QuarticIntegerRepresentativeTree.Tree.leaf 99 representative_99))) (QuarticIntegerRepresentativeTree.Tree.branch 102 (QuarticIntegerRepresentativeTree.Tree.branch 101 (QuarticIntegerRepresentativeTree.Tree.leaf 100 representative_100) (QuarticIntegerRepresentativeTree.Tree.leaf 101 representative_101)) (QuarticIntegerRepresentativeTree.Tree.branch 103 (QuarticIntegerRepresentativeTree.Tree.leaf 102 representative_102) (QuarticIntegerRepresentativeTree.Tree.leaf 103 representative_103)))) (QuarticIntegerRepresentativeTree.Tree.branch 108 (QuarticIntegerRepresentativeTree.Tree.branch 106 (QuarticIntegerRepresentativeTree.Tree.branch 105 (QuarticIntegerRepresentativeTree.Tree.leaf 104 representative_104) (QuarticIntegerRepresentativeTree.Tree.leaf 105 representative_105)) (QuarticIntegerRepresentativeTree.Tree.branch 107 (QuarticIntegerRepresentativeTree.Tree.leaf 106 representative_106) (QuarticIntegerRepresentativeTree.Tree.leaf 107 representative_107))) (QuarticIntegerRepresentativeTree.Tree.branch 110 (QuarticIntegerRepresentativeTree.Tree.branch 109 (QuarticIntegerRepresentativeTree.Tree.leaf 108 representative_108) (QuarticIntegerRepresentativeTree.Tree.leaf 109 representative_109)) (QuarticIntegerRepresentativeTree.Tree.branch 111 (QuarticIntegerRepresentativeTree.Tree.leaf 110 representative_110) (QuarticIntegerRepresentativeTree.Tree.leaf 111 representative_111))))) (QuarticIntegerRepresentativeTree.Tree.branch 120 (QuarticIntegerRepresentativeTree.Tree.branch 116 (QuarticIntegerRepresentativeTree.Tree.branch 114 (QuarticIntegerRepresentativeTree.Tree.branch 113 (QuarticIntegerRepresentativeTree.Tree.leaf 112 representative_112) (QuarticIntegerRepresentativeTree.Tree.leaf 113 representative_113)) (QuarticIntegerRepresentativeTree.Tree.branch 115 (QuarticIntegerRepresentativeTree.Tree.leaf 114 representative_114) (QuarticIntegerRepresentativeTree.Tree.leaf 115 representative_115))) (QuarticIntegerRepresentativeTree.Tree.branch 118 (QuarticIntegerRepresentativeTree.Tree.branch 117 (QuarticIntegerRepresentativeTree.Tree.leaf 116 representative_116) (QuarticIntegerRepresentativeTree.Tree.leaf 117 representative_117)) (QuarticIntegerRepresentativeTree.Tree.branch 119 (QuarticIntegerRepresentativeTree.Tree.leaf 118 representative_118) (QuarticIntegerRepresentativeTree.Tree.leaf 119 representative_119)))) (QuarticIntegerRepresentativeTree.Tree.branch 124 (QuarticIntegerRepresentativeTree.Tree.branch 122 (QuarticIntegerRepresentativeTree.Tree.branch 121 (QuarticIntegerRepresentativeTree.Tree.leaf 120 representative_120) (QuarticIntegerRepresentativeTree.Tree.leaf 121 representative_121)) (QuarticIntegerRepresentativeTree.Tree.branch 123 (QuarticIntegerRepresentativeTree.Tree.leaf 122 representative_122) (QuarticIntegerRepresentativeTree.Tree.leaf 123 representative_123))) (QuarticIntegerRepresentativeTree.Tree.branch 126 (QuarticIntegerRepresentativeTree.Tree.branch 125 (QuarticIntegerRepresentativeTree.Tree.leaf 124 representative_124) (QuarticIntegerRepresentativeTree.Tree.leaf 125 representative_125)) (QuarticIntegerRepresentativeTree.Tree.branch 127 (QuarticIntegerRepresentativeTree.Tree.leaf 126 representative_126) (QuarticIntegerRepresentativeTree.Tree.leaf 127 representative_127)))))))
theorem accepted_001 : All validRep tree_001 := ⟨⟨⟨⟨⟨⟨coefficient_64,coefficient_65⟩,⟨coefficient_66,coefficient_67⟩⟩,⟨⟨coefficient_68,coefficient_69⟩,⟨coefficient_70,coefficient_71⟩⟩⟩,⟨⟨⟨coefficient_72,coefficient_73⟩,⟨coefficient_74,coefficient_75⟩⟩,⟨⟨coefficient_76,coefficient_77⟩,⟨coefficient_78,coefficient_79⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_80,coefficient_81⟩,⟨coefficient_82,coefficient_83⟩⟩,⟨⟨coefficient_84,coefficient_85⟩,⟨coefficient_86,coefficient_87⟩⟩⟩,⟨⟨⟨coefficient_88,coefficient_89⟩,⟨coefficient_90,coefficient_91⟩⟩,⟨⟨coefficient_92,coefficient_93⟩,⟨coefficient_94,coefficient_95⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_96,coefficient_97⟩,⟨coefficient_98,coefficient_99⟩⟩,⟨⟨coefficient_100,coefficient_101⟩,⟨coefficient_102,coefficient_103⟩⟩⟩,⟨⟨⟨coefficient_104,coefficient_105⟩,⟨coefficient_106,coefficient_107⟩⟩,⟨⟨coefficient_108,coefficient_109⟩,⟨coefficient_110,coefficient_111⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_112,coefficient_113⟩,⟨coefficient_114,coefficient_115⟩⟩,⟨⟨coefficient_116,coefficient_117⟩,⟨coefficient_118,coefficient_119⟩⟩⟩,⟨⟨⟨coefficient_120,coefficient_121⟩,⟨coefficient_122,coefficient_123⟩⟩,⟨⟨coefficient_124,coefficient_125⟩,⟨coefficient_126,coefficient_127⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

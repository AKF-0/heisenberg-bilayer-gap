import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_64 : Rep := ⟨![0,1,6,27],402⟩
def representative_65 : Rep := ⟨![0,1,6,30],66⟩
def representative_66 : Rep := ⟨![0,1,6,31],65⟩
def representative_67 : Rep := ⟨![0,1,8,9],90⟩
def representative_68 : Rep := ⟨![0,1,8,10],376⟩
def representative_69 : Rep := ⟨![0,1,8,11],395⟩
def representative_70 : Rep := ⟨![0,1,8,12],392⟩
def representative_71 : Rep := ⟨![0,1,8,13],350⟩
def representative_72 : Rep := ⟨![0,1,8,14],329⟩
def representative_73 : Rep := ⟨![0,1,8,15],185⟩
def representative_74 : Rep := ⟨![0,1,8,16],218⟩
def representative_75 : Rep := ⟨![0,1,8,17],314⟩
def representative_76 : Rep := ⟨![0,1,8,18],508⟩
def representative_77 : Rep := ⟨![0,1,8,19],309⟩
def representative_78 : Rep := ⟨![0,1,8,20],349⟩
def representative_79 : Rep := ⟨![0,1,8,21],351⟩
def representative_80 : Rep := ⟨![0,1,8,22],304⟩
def representative_81 : Rep := ⟨![0,1,8,23],234⟩
def representative_82 : Rep := ⟨![0,1,8,24],105⟩
def representative_83 : Rep := ⟨![0,1,8,25],104⟩
def representative_84 : Rep := ⟨![0,1,8,26],377⟩
def representative_85 : Rep := ⟨![0,1,8,27],370⟩
def representative_86 : Rep := ⟨![0,1,10,11],142⟩
def representative_87 : Rep := ⟨![0,1,10,12],217⟩
def representative_88 : Rep := ⟨![0,1,10,13],222⟩
def representative_89 : Rep := ⟨![0,1,10,14],330⟩
def representative_90 : Rep := ⟨![0,1,10,15],258⟩
def representative_91 : Rep := ⟨![0,1,10,16],508⟩
def representative_92 : Rep := ⟨![0,1,10,17],289⟩
def representative_93 : Rep := ⟨![0,1,10,18],265⟩
def representative_94 : Rep := ⟨![0,1,10,19],279⟩
def representative_95 : Rep := ⟨![0,1,10,20],216⟩
def representative_96 : Rep := ⟨![0,1,10,21],225⟩
def representative_97 : Rep := ⟨![0,1,10,22],305⟩
def representative_98 : Rep := ⟨![0,1,10,23],508⟩
def representative_99 : Rep := ⟨![0,1,10,26],180⟩
def representative_100 : Rep := ⟨![0,1,10,27],166⟩
def representative_101 : Rep := ⟨![0,1,12,13],227⟩
def representative_102 : Rep := ⟨![0,1,12,14],272⟩
def representative_103 : Rep := ⟨![0,1,12,15],291⟩
def representative_104 : Rep := ⟨![0,1,12,16],287⟩
def representative_105 : Rep := ⟨![0,1,12,17],272⟩
def representative_106 : Rep := ⟨![0,1,12,18],275⟩
def representative_107 : Rep := ⟨![0,1,12,19],272⟩
def representative_108 : Rep := ⟨![0,1,12,20],243⟩
def representative_109 : Rep := ⟨![0,1,12,21],241⟩
def representative_110 : Rep := ⟨![0,1,12,22],508⟩
def representative_111 : Rep := ⟨![0,1,12,23],285⟩
def representative_112 : Rep := ⟨![0,1,14,15],508⟩
def representative_113 : Rep := ⟨![0,1,14,16],508⟩
def representative_114 : Rep := ⟨![0,1,14,17],508⟩
def representative_115 : Rep := ⟨![0,1,14,18],508⟩
def representative_116 : Rep := ⟨![0,1,14,19],508⟩
def representative_117 : Rep := ⟨![0,1,14,22],508⟩
def representative_118 : Rep := ⟨![0,1,14,23],508⟩
def representative_119 : Rep := ⟨![0,1,16,17],508⟩
def representative_120 : Rep := ⟨![0,1,16,18],508⟩
def representative_121 : Rep := ⟨![0,1,16,19],508⟩
def representative_122 : Rep := ⟨![0,1,18,19],508⟩
def representative_123 : Rep := ⟨![0,2,1,3],507⟩
def representative_124 : Rep := ⟨![0,2,1,4],504⟩
def representative_125 : Rep := ⟨![0,2,1,5],22⟩
def representative_126 : Rep := ⟨![0,2,1,7],33⟩
def representative_127 : Rep := ⟨![0,2,1,8],40⟩
theorem coefficient_64 : validRep representative_64 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_64)=dictionary32.getD 402 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_402]
  decide +kernel
theorem coefficient_65 : validRep representative_65 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_65)=dictionary32.getD 66 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_66]
  decide +kernel
theorem coefficient_66 : validRep representative_66 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_66)=dictionary32.getD 65 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_65]
  decide +kernel
theorem coefficient_67 : validRep representative_67 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_67)=dictionary32.getD 90 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_90]
  decide +kernel
theorem coefficient_68 : validRep representative_68 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_68)=dictionary32.getD 376 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_376]
  decide +kernel
theorem coefficient_69 : validRep representative_69 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_69)=dictionary32.getD 395 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_395]
  decide +kernel
theorem coefficient_70 : validRep representative_70 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_70)=dictionary32.getD 392 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_392]
  decide +kernel
theorem coefficient_71 : validRep representative_71 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_71)=dictionary32.getD 350 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_350]
  decide +kernel
theorem coefficient_72 : validRep representative_72 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_72)=dictionary32.getD 329 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_329]
  decide +kernel
theorem coefficient_73 : validRep representative_73 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_73)=dictionary32.getD 185 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_185]
  decide +kernel
theorem coefficient_74 : validRep representative_74 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_74)=dictionary32.getD 218 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_218]
  decide +kernel
theorem coefficient_75 : validRep representative_75 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_75)=dictionary32.getD 314 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_314]
  decide +kernel
theorem coefficient_76 : validRep representative_76 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_76)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_77 : validRep representative_77 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_77)=dictionary32.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_78 : validRep representative_78 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_78)=dictionary32.getD 349 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_349]
  decide +kernel
theorem coefficient_79 : validRep representative_79 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_79)=dictionary32.getD 351 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_351]
  decide +kernel
theorem coefficient_80 : validRep representative_80 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_80)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_81 : validRep representative_81 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_81)=dictionary32.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_82 : validRep representative_82 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_82)=dictionary32.getD 105 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_105]
  decide +kernel
theorem coefficient_83 : validRep representative_83 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_83)=dictionary32.getD 104 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_104]
  decide +kernel
theorem coefficient_84 : validRep representative_84 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_84)=dictionary32.getD 377 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_377]
  decide +kernel
theorem coefficient_85 : validRep representative_85 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_85)=dictionary32.getD 370 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_370]
  decide +kernel
theorem coefficient_86 : validRep representative_86 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_86)=dictionary32.getD 142 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_142]
  decide +kernel
theorem coefficient_87 : validRep representative_87 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_87)=dictionary32.getD 217 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_217]
  decide +kernel
theorem coefficient_88 : validRep representative_88 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_88)=dictionary32.getD 222 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_222]
  decide +kernel
theorem coefficient_89 : validRep representative_89 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_89)=dictionary32.getD 330 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_330]
  decide +kernel
theorem coefficient_90 : validRep representative_90 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_90)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_91 : validRep representative_91 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_91)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_92 : validRep representative_92 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_92)=dictionary32.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_93 : validRep representative_93 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_93)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_94 : validRep representative_94 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_94)=dictionary32.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_95 : validRep representative_95 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_95)=dictionary32.getD 216 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_216]
  decide +kernel
theorem coefficient_96 : validRep representative_96 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_96)=dictionary32.getD 225 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_225]
  decide +kernel
theorem coefficient_97 : validRep representative_97 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_97)=dictionary32.getD 305 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_305]
  decide +kernel
theorem coefficient_98 : validRep representative_98 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_98)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_99 : validRep representative_99 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_99)=dictionary32.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_100 : validRep representative_100 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_100)=dictionary32.getD 166 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_166]
  decide +kernel
theorem coefficient_101 : validRep representative_101 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_101)=dictionary32.getD 227 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_227]
  decide +kernel
theorem coefficient_102 : validRep representative_102 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_102)=dictionary32.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_103 : validRep representative_103 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_103)=dictionary32.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_104 : validRep representative_104 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_104)=dictionary32.getD 287 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_287]
  decide +kernel
theorem coefficient_105 : validRep representative_105 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_105)=dictionary32.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_106 : validRep representative_106 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_106)=dictionary32.getD 275 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_275]
  decide +kernel
theorem coefficient_107 : validRep representative_107 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_107)=dictionary32.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_108 : validRep representative_108 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_108)=dictionary32.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_109 : validRep representative_109 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_109)=dictionary32.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_110 : validRep representative_110 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_110)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_111 : validRep representative_111 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_111)=dictionary32.getD 285 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_285]
  decide +kernel
theorem coefficient_112 : validRep representative_112 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_112)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_113 : validRep representative_113 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_113)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_114 : validRep representative_114 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_114)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_115 : validRep representative_115 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_115)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_116 : validRep representative_116 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_116)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_117 : validRep representative_117 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_117)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_118 : validRep representative_118 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_118)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_119 : validRep representative_119 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_119)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_120 : validRep representative_120 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_120)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_121 : validRep representative_121 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_121)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_122 : validRep representative_122 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_122)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_123 : validRep representative_123 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_123)=dictionary32.getD 507 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_507]
  decide +kernel
theorem coefficient_124 : validRep representative_124 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_124)=dictionary32.getD 504 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_504]
  decide +kernel
theorem coefficient_125 : validRep representative_125 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_125)=dictionary32.getD 22 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_22]
  decide +kernel
theorem coefficient_126 : validRep representative_126 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_126)=dictionary32.getD 33 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_127 : validRep representative_127 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_127)=dictionary32.getD 40 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_40]
  decide +kernel
def tree_001 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 96 (QuarticIntegerRepresentativeTree.Tree.branch 80 (QuarticIntegerRepresentativeTree.Tree.branch 72 (QuarticIntegerRepresentativeTree.Tree.branch 68 (QuarticIntegerRepresentativeTree.Tree.branch 66 (QuarticIntegerRepresentativeTree.Tree.branch 65 (QuarticIntegerRepresentativeTree.Tree.leaf 64 representative_64) (QuarticIntegerRepresentativeTree.Tree.leaf 65 representative_65)) (QuarticIntegerRepresentativeTree.Tree.branch 67 (QuarticIntegerRepresentativeTree.Tree.leaf 66 representative_66) (QuarticIntegerRepresentativeTree.Tree.leaf 67 representative_67))) (QuarticIntegerRepresentativeTree.Tree.branch 70 (QuarticIntegerRepresentativeTree.Tree.branch 69 (QuarticIntegerRepresentativeTree.Tree.leaf 68 representative_68) (QuarticIntegerRepresentativeTree.Tree.leaf 69 representative_69)) (QuarticIntegerRepresentativeTree.Tree.branch 71 (QuarticIntegerRepresentativeTree.Tree.leaf 70 representative_70) (QuarticIntegerRepresentativeTree.Tree.leaf 71 representative_71)))) (QuarticIntegerRepresentativeTree.Tree.branch 76 (QuarticIntegerRepresentativeTree.Tree.branch 74 (QuarticIntegerRepresentativeTree.Tree.branch 73 (QuarticIntegerRepresentativeTree.Tree.leaf 72 representative_72) (QuarticIntegerRepresentativeTree.Tree.leaf 73 representative_73)) (QuarticIntegerRepresentativeTree.Tree.branch 75 (QuarticIntegerRepresentativeTree.Tree.leaf 74 representative_74) (QuarticIntegerRepresentativeTree.Tree.leaf 75 representative_75))) (QuarticIntegerRepresentativeTree.Tree.branch 78 (QuarticIntegerRepresentativeTree.Tree.branch 77 (QuarticIntegerRepresentativeTree.Tree.leaf 76 representative_76) (QuarticIntegerRepresentativeTree.Tree.leaf 77 representative_77)) (QuarticIntegerRepresentativeTree.Tree.branch 79 (QuarticIntegerRepresentativeTree.Tree.leaf 78 representative_78) (QuarticIntegerRepresentativeTree.Tree.leaf 79 representative_79))))) (QuarticIntegerRepresentativeTree.Tree.branch 88 (QuarticIntegerRepresentativeTree.Tree.branch 84 (QuarticIntegerRepresentativeTree.Tree.branch 82 (QuarticIntegerRepresentativeTree.Tree.branch 81 (QuarticIntegerRepresentativeTree.Tree.leaf 80 representative_80) (QuarticIntegerRepresentativeTree.Tree.leaf 81 representative_81)) (QuarticIntegerRepresentativeTree.Tree.branch 83 (QuarticIntegerRepresentativeTree.Tree.leaf 82 representative_82) (QuarticIntegerRepresentativeTree.Tree.leaf 83 representative_83))) (QuarticIntegerRepresentativeTree.Tree.branch 86 (QuarticIntegerRepresentativeTree.Tree.branch 85 (QuarticIntegerRepresentativeTree.Tree.leaf 84 representative_84) (QuarticIntegerRepresentativeTree.Tree.leaf 85 representative_85)) (QuarticIntegerRepresentativeTree.Tree.branch 87 (QuarticIntegerRepresentativeTree.Tree.leaf 86 representative_86) (QuarticIntegerRepresentativeTree.Tree.leaf 87 representative_87)))) (QuarticIntegerRepresentativeTree.Tree.branch 92 (QuarticIntegerRepresentativeTree.Tree.branch 90 (QuarticIntegerRepresentativeTree.Tree.branch 89 (QuarticIntegerRepresentativeTree.Tree.leaf 88 representative_88) (QuarticIntegerRepresentativeTree.Tree.leaf 89 representative_89)) (QuarticIntegerRepresentativeTree.Tree.branch 91 (QuarticIntegerRepresentativeTree.Tree.leaf 90 representative_90) (QuarticIntegerRepresentativeTree.Tree.leaf 91 representative_91))) (QuarticIntegerRepresentativeTree.Tree.branch 94 (QuarticIntegerRepresentativeTree.Tree.branch 93 (QuarticIntegerRepresentativeTree.Tree.leaf 92 representative_92) (QuarticIntegerRepresentativeTree.Tree.leaf 93 representative_93)) (QuarticIntegerRepresentativeTree.Tree.branch 95 (QuarticIntegerRepresentativeTree.Tree.leaf 94 representative_94) (QuarticIntegerRepresentativeTree.Tree.leaf 95 representative_95)))))) (QuarticIntegerRepresentativeTree.Tree.branch 112 (QuarticIntegerRepresentativeTree.Tree.branch 104 (QuarticIntegerRepresentativeTree.Tree.branch 100 (QuarticIntegerRepresentativeTree.Tree.branch 98 (QuarticIntegerRepresentativeTree.Tree.branch 97 (QuarticIntegerRepresentativeTree.Tree.leaf 96 representative_96) (QuarticIntegerRepresentativeTree.Tree.leaf 97 representative_97)) (QuarticIntegerRepresentativeTree.Tree.branch 99 (QuarticIntegerRepresentativeTree.Tree.leaf 98 representative_98) (QuarticIntegerRepresentativeTree.Tree.leaf 99 representative_99))) (QuarticIntegerRepresentativeTree.Tree.branch 102 (QuarticIntegerRepresentativeTree.Tree.branch 101 (QuarticIntegerRepresentativeTree.Tree.leaf 100 representative_100) (QuarticIntegerRepresentativeTree.Tree.leaf 101 representative_101)) (QuarticIntegerRepresentativeTree.Tree.branch 103 (QuarticIntegerRepresentativeTree.Tree.leaf 102 representative_102) (QuarticIntegerRepresentativeTree.Tree.leaf 103 representative_103)))) (QuarticIntegerRepresentativeTree.Tree.branch 108 (QuarticIntegerRepresentativeTree.Tree.branch 106 (QuarticIntegerRepresentativeTree.Tree.branch 105 (QuarticIntegerRepresentativeTree.Tree.leaf 104 representative_104) (QuarticIntegerRepresentativeTree.Tree.leaf 105 representative_105)) (QuarticIntegerRepresentativeTree.Tree.branch 107 (QuarticIntegerRepresentativeTree.Tree.leaf 106 representative_106) (QuarticIntegerRepresentativeTree.Tree.leaf 107 representative_107))) (QuarticIntegerRepresentativeTree.Tree.branch 110 (QuarticIntegerRepresentativeTree.Tree.branch 109 (QuarticIntegerRepresentativeTree.Tree.leaf 108 representative_108) (QuarticIntegerRepresentativeTree.Tree.leaf 109 representative_109)) (QuarticIntegerRepresentativeTree.Tree.branch 111 (QuarticIntegerRepresentativeTree.Tree.leaf 110 representative_110) (QuarticIntegerRepresentativeTree.Tree.leaf 111 representative_111))))) (QuarticIntegerRepresentativeTree.Tree.branch 120 (QuarticIntegerRepresentativeTree.Tree.branch 116 (QuarticIntegerRepresentativeTree.Tree.branch 114 (QuarticIntegerRepresentativeTree.Tree.branch 113 (QuarticIntegerRepresentativeTree.Tree.leaf 112 representative_112) (QuarticIntegerRepresentativeTree.Tree.leaf 113 representative_113)) (QuarticIntegerRepresentativeTree.Tree.branch 115 (QuarticIntegerRepresentativeTree.Tree.leaf 114 representative_114) (QuarticIntegerRepresentativeTree.Tree.leaf 115 representative_115))) (QuarticIntegerRepresentativeTree.Tree.branch 118 (QuarticIntegerRepresentativeTree.Tree.branch 117 (QuarticIntegerRepresentativeTree.Tree.leaf 116 representative_116) (QuarticIntegerRepresentativeTree.Tree.leaf 117 representative_117)) (QuarticIntegerRepresentativeTree.Tree.branch 119 (QuarticIntegerRepresentativeTree.Tree.leaf 118 representative_118) (QuarticIntegerRepresentativeTree.Tree.leaf 119 representative_119)))) (QuarticIntegerRepresentativeTree.Tree.branch 124 (QuarticIntegerRepresentativeTree.Tree.branch 122 (QuarticIntegerRepresentativeTree.Tree.branch 121 (QuarticIntegerRepresentativeTree.Tree.leaf 120 representative_120) (QuarticIntegerRepresentativeTree.Tree.leaf 121 representative_121)) (QuarticIntegerRepresentativeTree.Tree.branch 123 (QuarticIntegerRepresentativeTree.Tree.leaf 122 representative_122) (QuarticIntegerRepresentativeTree.Tree.leaf 123 representative_123))) (QuarticIntegerRepresentativeTree.Tree.branch 126 (QuarticIntegerRepresentativeTree.Tree.branch 125 (QuarticIntegerRepresentativeTree.Tree.leaf 124 representative_124) (QuarticIntegerRepresentativeTree.Tree.leaf 125 representative_125)) (QuarticIntegerRepresentativeTree.Tree.branch 127 (QuarticIntegerRepresentativeTree.Tree.leaf 126 representative_126) (QuarticIntegerRepresentativeTree.Tree.leaf 127 representative_127)))))))
theorem accepted_001 : All validRep tree_001 := ⟨⟨⟨⟨⟨⟨coefficient_64,coefficient_65⟩,⟨coefficient_66,coefficient_67⟩⟩,⟨⟨coefficient_68,coefficient_69⟩,⟨coefficient_70,coefficient_71⟩⟩⟩,⟨⟨⟨coefficient_72,coefficient_73⟩,⟨coefficient_74,coefficient_75⟩⟩,⟨⟨coefficient_76,coefficient_77⟩,⟨coefficient_78,coefficient_79⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_80,coefficient_81⟩,⟨coefficient_82,coefficient_83⟩⟩,⟨⟨coefficient_84,coefficient_85⟩,⟨coefficient_86,coefficient_87⟩⟩⟩,⟨⟨⟨coefficient_88,coefficient_89⟩,⟨coefficient_90,coefficient_91⟩⟩,⟨⟨coefficient_92,coefficient_93⟩,⟨coefficient_94,coefficient_95⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_96,coefficient_97⟩,⟨coefficient_98,coefficient_99⟩⟩,⟨⟨coefficient_100,coefficient_101⟩,⟨coefficient_102,coefficient_103⟩⟩⟩,⟨⟨⟨coefficient_104,coefficient_105⟩,⟨coefficient_106,coefficient_107⟩⟩,⟨⟨coefficient_108,coefficient_109⟩,⟨coefficient_110,coefficient_111⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_112,coefficient_113⟩,⟨coefficient_114,coefficient_115⟩⟩,⟨⟨coefficient_116,coefficient_117⟩,⟨coefficient_118,coefficient_119⟩⟩⟩,⟨⟨⟨coefficient_120,coefficient_121⟩,⟨coefficient_122,coefficient_123⟩⟩,⟨⟨coefficient_124,coefficient_125⟩,⟨coefficient_126,coefficient_127⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

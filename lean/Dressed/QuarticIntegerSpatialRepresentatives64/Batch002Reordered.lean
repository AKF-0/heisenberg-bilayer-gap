import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_128 : Rep := ⟨![0,1,8,33],193⟩
def representative_129 : Rep := ⟨![0,1,8,34],462⟩
def representative_130 : Rep := ⟨![0,1,8,35],462⟩
def representative_131 : Rep := ⟨![0,1,8,36],462⟩
def representative_132 : Rep := ⟨![0,1,8,37],462⟩
def representative_133 : Rep := ⟨![0,1,8,38],462⟩
def representative_134 : Rep := ⟨![0,1,8,39],462⟩
def representative_135 : Rep := ⟨![0,1,8,40],64⟩
def representative_136 : Rep := ⟨![0,1,8,41],73⟩
def representative_137 : Rep := ⟨![0,1,8,42],163⟩
def representative_138 : Rep := ⟨![0,1,8,43],462⟩
def representative_139 : Rep := ⟨![0,1,8,44],462⟩
def representative_140 : Rep := ⟨![0,1,8,45],462⟩
def representative_141 : Rep := ⟨![0,1,8,46],462⟩
def representative_142 : Rep := ⟨![0,1,8,47],358⟩
def representative_143 : Rep := ⟨![0,1,8,48],448⟩
def representative_144 : Rep := ⟨![0,1,8,49],443⟩
def representative_145 : Rep := ⟨![0,1,8,50],45⟩
def representative_146 : Rep := ⟨![0,1,8,51],139⟩
def representative_147 : Rep := ⟨![0,1,8,52],462⟩
def representative_148 : Rep := ⟨![0,1,8,53],462⟩
def representative_149 : Rep := ⟨![0,1,8,54],377⟩
def representative_150 : Rep := ⟨![0,1,8,55],35⟩
def representative_151 : Rep := ⟨![0,1,8,56],18⟩
def representative_152 : Rep := ⟨![0,1,8,57],23⟩
def representative_153 : Rep := ⟨![0,1,8,58],452⟩
def representative_154 : Rep := ⟨![0,1,8,59],43⟩
def representative_155 : Rep := ⟨![0,1,8,60],163⟩
def representative_156 : Rep := ⟨![0,1,8,61],358⟩
def representative_157 : Rep := ⟨![0,1,8,62],36⟩
def representative_158 : Rep := ⟨![0,1,8,63],456⟩
def representative_159 : Rep := ⟨![0,1,10,11],417⟩
def representative_160 : Rep := ⟨![0,1,10,12],127⟩
def representative_161 : Rep := ⟨![0,1,10,13],301⟩
def representative_162 : Rep := ⟨![0,1,10,14],399⟩
def representative_163 : Rep := ⟨![0,1,10,15],40⟩
def representative_164 : Rep := ⟨![0,1,10,16],60⟩
def representative_165 : Rep := ⟨![0,1,10,17],61⟩
def representative_166 : Rep := ⟨![0,1,10,18],418⟩
def representative_167 : Rep := ⟨![0,1,10,19],100⟩
def representative_168 : Rep := ⟨![0,1,10,20],309⟩
def representative_169 : Rep := ⟨![0,1,10,21],462⟩
def representative_170 : Rep := ⟨![0,1,10,22],293⟩
def representative_171 : Rep := ⟨![0,1,10,23],398⟩
def representative_172 : Rep := ⟨![0,1,10,24],356⟩
def representative_173 : Rep := ⟨![0,1,10,25],354⟩
def representative_174 : Rep := ⟨![0,1,10,26],127⟩
def representative_175 : Rep := ⟨![0,1,10,27],309⟩
def representative_176 : Rep := ⟨![0,1,10,28],462⟩
def representative_177 : Rep := ⟨![0,1,10,29],462⟩
def representative_178 : Rep := ⟨![0,1,10,30],462⟩
def representative_179 : Rep := ⟨![0,1,10,31],284⟩
def representative_180 : Rep := ⟨![0,1,10,32],269⟩
def representative_181 : Rep := ⟨![0,1,10,33],193⟩
def representative_182 : Rep := ⟨![0,1,10,34],279⟩
def representative_183 : Rep := ⟨![0,1,10,35],462⟩
def representative_184 : Rep := ⟨![0,1,10,36],462⟩
def representative_185 : Rep := ⟨![0,1,10,37],462⟩
def representative_186 : Rep := ⟨![0,1,10,38],462⟩
def representative_187 : Rep := ⟨![0,1,10,39],462⟩
def representative_188 : Rep := ⟨![0,1,10,40],356⟩
def representative_189 : Rep := ⟨![0,1,10,41],352⟩
def representative_190 : Rep := ⟨![0,1,10,42],163⟩
def representative_191 : Rep := ⟨![0,1,10,43],462⟩
theorem coefficient_128 : validRep representative_128 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_128)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_129 : validRep representative_129 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_129)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_130 : validRep representative_130 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_130)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_131 : validRep representative_131 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_131)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_132 : validRep representative_132 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_132)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_133 : validRep representative_133 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_133)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_134 : validRep representative_134 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_134)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_135 : validRep representative_135 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_135)=dictionary64.getD 64 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_64]
  decide +kernel
theorem coefficient_136 : validRep representative_136 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_136)=dictionary64.getD 73 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_73]
  decide +kernel
theorem coefficient_137 : validRep representative_137 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_137)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_138 : validRep representative_138 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_138)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_139 : validRep representative_139 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_139)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_140 : validRep representative_140 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_140)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_141 : validRep representative_141 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_141)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_142 : validRep representative_142 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_142)=dictionary64.getD 358 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_358]
  decide +kernel
theorem coefficient_143 : validRep representative_143 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_143)=dictionary64.getD 448 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_448]
  decide +kernel
theorem coefficient_144 : validRep representative_144 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_144)=dictionary64.getD 443 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_443]
  decide +kernel
theorem coefficient_145 : validRep representative_145 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_145)=dictionary64.getD 45 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_45]
  decide +kernel
theorem coefficient_146 : validRep representative_146 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_146)=dictionary64.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_139]
  decide +kernel
theorem coefficient_147 : validRep representative_147 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_147)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_148 : validRep representative_148 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_148)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_149 : validRep representative_149 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_149)=dictionary64.getD 377 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_377]
  decide +kernel
theorem coefficient_150 : validRep representative_150 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_150)=dictionary64.getD 35 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_35]
  decide +kernel
theorem coefficient_151 : validRep representative_151 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_151)=dictionary64.getD 18 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_18]
  decide +kernel
theorem coefficient_152 : validRep representative_152 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_152)=dictionary64.getD 23 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_23]
  decide +kernel
theorem coefficient_153 : validRep representative_153 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_153)=dictionary64.getD 452 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_452]
  decide +kernel
theorem coefficient_154 : validRep representative_154 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_154)=dictionary64.getD 43 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_43]
  decide +kernel
theorem coefficient_155 : validRep representative_155 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_155)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_156 : validRep representative_156 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_156)=dictionary64.getD 358 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_358]
  decide +kernel
theorem coefficient_157 : validRep representative_157 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_157)=dictionary64.getD 36 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_36]
  decide +kernel
theorem coefficient_158 : validRep representative_158 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_158)=dictionary64.getD 456 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_456]
  decide +kernel
theorem coefficient_159 : validRep representative_159 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_159)=dictionary64.getD 417 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_417]
  decide +kernel
theorem coefficient_160 : validRep representative_160 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_160)=dictionary64.getD 127 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_127]
  decide +kernel
theorem coefficient_161 : validRep representative_161 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_161)=dictionary64.getD 301 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_301]
  decide +kernel
theorem coefficient_162 : validRep representative_162 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_162)=dictionary64.getD 399 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_399]
  decide +kernel
theorem coefficient_163 : validRep representative_163 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_163)=dictionary64.getD 40 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_40]
  decide +kernel
theorem coefficient_164 : validRep representative_164 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_164)=dictionary64.getD 60 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_60]
  decide +kernel
theorem coefficient_165 : validRep representative_165 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_165)=dictionary64.getD 61 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_61]
  decide +kernel
theorem coefficient_166 : validRep representative_166 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_166)=dictionary64.getD 418 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_418]
  decide +kernel
theorem coefficient_167 : validRep representative_167 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_167)=dictionary64.getD 100 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_100]
  decide +kernel
theorem coefficient_168 : validRep representative_168 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_168)=dictionary64.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_169 : validRep representative_169 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_169)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_170 : validRep representative_170 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_170)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_171 : validRep representative_171 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_171)=dictionary64.getD 398 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_398]
  decide +kernel
theorem coefficient_172 : validRep representative_172 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_172)=dictionary64.getD 356 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_356]
  decide +kernel
theorem coefficient_173 : validRep representative_173 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_173)=dictionary64.getD 354 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_354]
  decide +kernel
theorem coefficient_174 : validRep representative_174 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_174)=dictionary64.getD 127 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_127]
  decide +kernel
theorem coefficient_175 : validRep representative_175 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_175)=dictionary64.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_176 : validRep representative_176 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_176)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_177 : validRep representative_177 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_177)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_178 : validRep representative_178 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_178)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_179 : validRep representative_179 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_179)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_180 : validRep representative_180 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_180)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_181 : validRep representative_181 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_181)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_182 : validRep representative_182 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_182)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_183 : validRep representative_183 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_183)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_184 : validRep representative_184 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_184)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_185 : validRep representative_185 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_185)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_186 : validRep representative_186 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_186)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_187 : validRep representative_187 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_187)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_188 : validRep representative_188 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_188)=dictionary64.getD 356 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_356]
  decide +kernel
theorem coefficient_189 : validRep representative_189 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_189)=dictionary64.getD 352 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_352]
  decide +kernel
theorem coefficient_190 : validRep representative_190 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_190)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_191 : validRep representative_191 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_191)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_002 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 160 (QuarticIntegerRepresentativeTree.Tree.branch 144 (QuarticIntegerRepresentativeTree.Tree.branch 136 (QuarticIntegerRepresentativeTree.Tree.branch 132 (QuarticIntegerRepresentativeTree.Tree.branch 130 (QuarticIntegerRepresentativeTree.Tree.branch 129 (QuarticIntegerRepresentativeTree.Tree.leaf 128 representative_128) (QuarticIntegerRepresentativeTree.Tree.leaf 129 representative_129)) (QuarticIntegerRepresentativeTree.Tree.branch 131 (QuarticIntegerRepresentativeTree.Tree.leaf 130 representative_130) (QuarticIntegerRepresentativeTree.Tree.leaf 131 representative_131))) (QuarticIntegerRepresentativeTree.Tree.branch 134 (QuarticIntegerRepresentativeTree.Tree.branch 133 (QuarticIntegerRepresentativeTree.Tree.leaf 132 representative_132) (QuarticIntegerRepresentativeTree.Tree.leaf 133 representative_133)) (QuarticIntegerRepresentativeTree.Tree.branch 135 (QuarticIntegerRepresentativeTree.Tree.leaf 134 representative_134) (QuarticIntegerRepresentativeTree.Tree.leaf 135 representative_135)))) (QuarticIntegerRepresentativeTree.Tree.branch 140 (QuarticIntegerRepresentativeTree.Tree.branch 138 (QuarticIntegerRepresentativeTree.Tree.branch 137 (QuarticIntegerRepresentativeTree.Tree.leaf 136 representative_136) (QuarticIntegerRepresentativeTree.Tree.leaf 137 representative_137)) (QuarticIntegerRepresentativeTree.Tree.branch 139 (QuarticIntegerRepresentativeTree.Tree.leaf 138 representative_138) (QuarticIntegerRepresentativeTree.Tree.leaf 139 representative_139))) (QuarticIntegerRepresentativeTree.Tree.branch 142 (QuarticIntegerRepresentativeTree.Tree.branch 141 (QuarticIntegerRepresentativeTree.Tree.leaf 140 representative_140) (QuarticIntegerRepresentativeTree.Tree.leaf 141 representative_141)) (QuarticIntegerRepresentativeTree.Tree.branch 143 (QuarticIntegerRepresentativeTree.Tree.leaf 142 representative_142) (QuarticIntegerRepresentativeTree.Tree.leaf 143 representative_143))))) (QuarticIntegerRepresentativeTree.Tree.branch 152 (QuarticIntegerRepresentativeTree.Tree.branch 148 (QuarticIntegerRepresentativeTree.Tree.branch 146 (QuarticIntegerRepresentativeTree.Tree.branch 145 (QuarticIntegerRepresentativeTree.Tree.leaf 144 representative_144) (QuarticIntegerRepresentativeTree.Tree.leaf 145 representative_145)) (QuarticIntegerRepresentativeTree.Tree.branch 147 (QuarticIntegerRepresentativeTree.Tree.leaf 146 representative_146) (QuarticIntegerRepresentativeTree.Tree.leaf 147 representative_147))) (QuarticIntegerRepresentativeTree.Tree.branch 150 (QuarticIntegerRepresentativeTree.Tree.branch 149 (QuarticIntegerRepresentativeTree.Tree.leaf 148 representative_148) (QuarticIntegerRepresentativeTree.Tree.leaf 149 representative_149)) (QuarticIntegerRepresentativeTree.Tree.branch 151 (QuarticIntegerRepresentativeTree.Tree.leaf 150 representative_150) (QuarticIntegerRepresentativeTree.Tree.leaf 151 representative_151)))) (QuarticIntegerRepresentativeTree.Tree.branch 156 (QuarticIntegerRepresentativeTree.Tree.branch 154 (QuarticIntegerRepresentativeTree.Tree.branch 153 (QuarticIntegerRepresentativeTree.Tree.leaf 152 representative_152) (QuarticIntegerRepresentativeTree.Tree.leaf 153 representative_153)) (QuarticIntegerRepresentativeTree.Tree.branch 155 (QuarticIntegerRepresentativeTree.Tree.leaf 154 representative_154) (QuarticIntegerRepresentativeTree.Tree.leaf 155 representative_155))) (QuarticIntegerRepresentativeTree.Tree.branch 158 (QuarticIntegerRepresentativeTree.Tree.branch 157 (QuarticIntegerRepresentativeTree.Tree.leaf 156 representative_156) (QuarticIntegerRepresentativeTree.Tree.leaf 157 representative_157)) (QuarticIntegerRepresentativeTree.Tree.branch 159 (QuarticIntegerRepresentativeTree.Tree.leaf 158 representative_158) (QuarticIntegerRepresentativeTree.Tree.leaf 159 representative_159)))))) (QuarticIntegerRepresentativeTree.Tree.branch 176 (QuarticIntegerRepresentativeTree.Tree.branch 168 (QuarticIntegerRepresentativeTree.Tree.branch 164 (QuarticIntegerRepresentativeTree.Tree.branch 162 (QuarticIntegerRepresentativeTree.Tree.branch 161 (QuarticIntegerRepresentativeTree.Tree.leaf 160 representative_160) (QuarticIntegerRepresentativeTree.Tree.leaf 161 representative_161)) (QuarticIntegerRepresentativeTree.Tree.branch 163 (QuarticIntegerRepresentativeTree.Tree.leaf 162 representative_162) (QuarticIntegerRepresentativeTree.Tree.leaf 163 representative_163))) (QuarticIntegerRepresentativeTree.Tree.branch 166 (QuarticIntegerRepresentativeTree.Tree.branch 165 (QuarticIntegerRepresentativeTree.Tree.leaf 164 representative_164) (QuarticIntegerRepresentativeTree.Tree.leaf 165 representative_165)) (QuarticIntegerRepresentativeTree.Tree.branch 167 (QuarticIntegerRepresentativeTree.Tree.leaf 166 representative_166) (QuarticIntegerRepresentativeTree.Tree.leaf 167 representative_167)))) (QuarticIntegerRepresentativeTree.Tree.branch 172 (QuarticIntegerRepresentativeTree.Tree.branch 170 (QuarticIntegerRepresentativeTree.Tree.branch 169 (QuarticIntegerRepresentativeTree.Tree.leaf 168 representative_168) (QuarticIntegerRepresentativeTree.Tree.leaf 169 representative_169)) (QuarticIntegerRepresentativeTree.Tree.branch 171 (QuarticIntegerRepresentativeTree.Tree.leaf 170 representative_170) (QuarticIntegerRepresentativeTree.Tree.leaf 171 representative_171))) (QuarticIntegerRepresentativeTree.Tree.branch 174 (QuarticIntegerRepresentativeTree.Tree.branch 173 (QuarticIntegerRepresentativeTree.Tree.leaf 172 representative_172) (QuarticIntegerRepresentativeTree.Tree.leaf 173 representative_173)) (QuarticIntegerRepresentativeTree.Tree.branch 175 (QuarticIntegerRepresentativeTree.Tree.leaf 174 representative_174) (QuarticIntegerRepresentativeTree.Tree.leaf 175 representative_175))))) (QuarticIntegerRepresentativeTree.Tree.branch 184 (QuarticIntegerRepresentativeTree.Tree.branch 180 (QuarticIntegerRepresentativeTree.Tree.branch 178 (QuarticIntegerRepresentativeTree.Tree.branch 177 (QuarticIntegerRepresentativeTree.Tree.leaf 176 representative_176) (QuarticIntegerRepresentativeTree.Tree.leaf 177 representative_177)) (QuarticIntegerRepresentativeTree.Tree.branch 179 (QuarticIntegerRepresentativeTree.Tree.leaf 178 representative_178) (QuarticIntegerRepresentativeTree.Tree.leaf 179 representative_179))) (QuarticIntegerRepresentativeTree.Tree.branch 182 (QuarticIntegerRepresentativeTree.Tree.branch 181 (QuarticIntegerRepresentativeTree.Tree.leaf 180 representative_180) (QuarticIntegerRepresentativeTree.Tree.leaf 181 representative_181)) (QuarticIntegerRepresentativeTree.Tree.branch 183 (QuarticIntegerRepresentativeTree.Tree.leaf 182 representative_182) (QuarticIntegerRepresentativeTree.Tree.leaf 183 representative_183)))) (QuarticIntegerRepresentativeTree.Tree.branch 188 (QuarticIntegerRepresentativeTree.Tree.branch 186 (QuarticIntegerRepresentativeTree.Tree.branch 185 (QuarticIntegerRepresentativeTree.Tree.leaf 184 representative_184) (QuarticIntegerRepresentativeTree.Tree.leaf 185 representative_185)) (QuarticIntegerRepresentativeTree.Tree.branch 187 (QuarticIntegerRepresentativeTree.Tree.leaf 186 representative_186) (QuarticIntegerRepresentativeTree.Tree.leaf 187 representative_187))) (QuarticIntegerRepresentativeTree.Tree.branch 190 (QuarticIntegerRepresentativeTree.Tree.branch 189 (QuarticIntegerRepresentativeTree.Tree.leaf 188 representative_188) (QuarticIntegerRepresentativeTree.Tree.leaf 189 representative_189)) (QuarticIntegerRepresentativeTree.Tree.branch 191 (QuarticIntegerRepresentativeTree.Tree.leaf 190 representative_190) (QuarticIntegerRepresentativeTree.Tree.leaf 191 representative_191)))))))
theorem accepted_002 : All validRep tree_002 := ⟨⟨⟨⟨⟨⟨coefficient_128,coefficient_129⟩,⟨coefficient_130,coefficient_131⟩⟩,⟨⟨coefficient_132,coefficient_133⟩,⟨coefficient_134,coefficient_135⟩⟩⟩,⟨⟨⟨coefficient_136,coefficient_137⟩,⟨coefficient_138,coefficient_139⟩⟩,⟨⟨coefficient_140,coefficient_141⟩,⟨coefficient_142,coefficient_143⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_144,coefficient_145⟩,⟨coefficient_146,coefficient_147⟩⟩,⟨⟨coefficient_148,coefficient_149⟩,⟨coefficient_150,coefficient_151⟩⟩⟩,⟨⟨⟨coefficient_152,coefficient_153⟩,⟨coefficient_154,coefficient_155⟩⟩,⟨⟨coefficient_156,coefficient_157⟩,⟨coefficient_158,coefficient_159⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_160,coefficient_161⟩,⟨coefficient_162,coefficient_163⟩⟩,⟨⟨coefficient_164,coefficient_165⟩,⟨coefficient_166,coefficient_167⟩⟩⟩,⟨⟨⟨coefficient_168,coefficient_169⟩,⟨coefficient_170,coefficient_171⟩⟩,⟨⟨coefficient_172,coefficient_173⟩,⟨coefficient_174,coefficient_175⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_176,coefficient_177⟩,⟨coefficient_178,coefficient_179⟩⟩,⟨⟨coefficient_180,coefficient_181⟩,⟨coefficient_182,coefficient_183⟩⟩⟩,⟨⟨⟨coefficient_184,coefficient_185⟩,⟨coefficient_186,coefficient_187⟩⟩,⟨⟨coefficient_188,coefficient_189⟩,⟨coefficient_190,coefficient_191⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

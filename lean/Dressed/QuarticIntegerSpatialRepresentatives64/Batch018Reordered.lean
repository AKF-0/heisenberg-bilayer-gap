import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1152 : Rep := ⟨![0,3,9,14],297⟩
def representative_1153 : Rep := ⟨![0,3,9,16],110⟩
def representative_1154 : Rep := ⟨![0,3,9,18],120⟩
def representative_1155 : Rep := ⟨![0,3,9,19],318⟩
def representative_1156 : Rep := ⟨![0,3,9,20],234⟩
def representative_1157 : Rep := ⟨![0,3,9,21],244⟩
def representative_1158 : Rep := ⟨![0,3,9,22],235⟩
def representative_1159 : Rep := ⟨![0,3,9,23],320⟩
def representative_1160 : Rep := ⟨![0,3,9,24],317⟩
def representative_1161 : Rep := ⟨![0,3,9,26],310⟩
def representative_1162 : Rep := ⟨![0,3,9,27],237⟩
def representative_1163 : Rep := ⟨![0,3,9,28],243⟩
def representative_1164 : Rep := ⟨![0,3,9,29],462⟩
def representative_1165 : Rep := ⟨![0,3,9,30],462⟩
def representative_1166 : Rep := ⟨![0,3,9,31],236⟩
def representative_1167 : Rep := ⟨![0,3,9,32],238⟩
def representative_1168 : Rep := ⟨![0,3,9,33],279⟩
def representative_1169 : Rep := ⟨![0,3,9,34],462⟩
def representative_1170 : Rep := ⟨![0,3,9,35],242⟩
def representative_1171 : Rep := ⟨![0,3,9,36],462⟩
def representative_1172 : Rep := ⟨![0,3,9,37],462⟩
def representative_1173 : Rep := ⟨![0,3,9,38],462⟩
def representative_1174 : Rep := ⟨![0,3,9,39],462⟩
def representative_1175 : Rep := ⟨![0,3,9,40],262⟩
def representative_1176 : Rep := ⟨![0,3,9,41],236⟩
def representative_1177 : Rep := ⟨![0,3,9,42],243⟩
def representative_1178 : Rep := ⟨![0,3,9,43],237⟩
def representative_1179 : Rep := ⟨![0,3,9,44],243⟩
def representative_1180 : Rep := ⟨![0,3,9,45],462⟩
def representative_1181 : Rep := ⟨![0,3,9,46],462⟩
def representative_1182 : Rep := ⟨![0,3,9,47],236⟩
def representative_1183 : Rep := ⟨![0,3,9,48],190⟩
def representative_1184 : Rep := ⟨![0,3,9,49],298⟩
def representative_1185 : Rep := ⟨![0,3,9,50],229⟩
def representative_1186 : Rep := ⟨![0,3,9,51],266⟩
def representative_1187 : Rep := ⟨![0,3,9,52],234⟩
def representative_1188 : Rep := ⟨![0,3,9,53],244⟩
def representative_1189 : Rep := ⟨![0,3,9,54],235⟩
def representative_1190 : Rep := ⟨![0,3,9,55],279⟩
def representative_1191 : Rep := ⟨![0,3,9,58],324⟩
def representative_1192 : Rep := ⟨![0,3,9,60],279⟩
def representative_1193 : Rep := ⟨![0,3,9,61],231⟩
def representative_1194 : Rep := ⟨![0,3,9,62],280⟩
def representative_1195 : Rep := ⟨![0,3,9,63],161⟩
def representative_1196 : Rep := ⟨![0,3,12,15],462⟩
def representative_1197 : Rep := ⟨![0,3,12,16],462⟩
def representative_1198 : Rep := ⟨![0,3,12,17],235⟩
def representative_1199 : Rep := ⟨![0,3,12,18],283⟩
def representative_1200 : Rep := ⟨![0,3,12,19],190⟩
def representative_1201 : Rep := ⟨![0,3,12,21],235⟩
def representative_1202 : Rep := ⟨![0,3,12,22],462⟩
def representative_1203 : Rep := ⟨![0,3,12,23],462⟩
def representative_1204 : Rep := ⟨![0,3,12,24],462⟩
def representative_1205 : Rep := ⟨![0,3,12,25],462⟩
def representative_1206 : Rep := ⟨![0,3,12,26],236⟩
def representative_1207 : Rep := ⟨![0,3,12,27],262⟩
def representative_1208 : Rep := ⟨![0,3,12,29],462⟩
def representative_1209 : Rep := ⟨![0,3,12,30],462⟩
def representative_1210 : Rep := ⟨![0,3,12,31],462⟩
def representative_1211 : Rep := ⟨![0,3,12,32],462⟩
def representative_1212 : Rep := ⟨![0,3,12,33],462⟩
def representative_1213 : Rep := ⟨![0,3,12,34],462⟩
def representative_1214 : Rep := ⟨![0,3,12,35],238⟩
def representative_1215 : Rep := ⟨![0,3,12,36],462⟩
theorem coefficient_1152 : validRep representative_1152 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1152)=dictionary64.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_1153 : validRep representative_1153 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1153)=dictionary64.getD 110 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_110]
  decide +kernel
theorem coefficient_1154 : validRep representative_1154 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1154)=dictionary64.getD 120 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_120]
  decide +kernel
theorem coefficient_1155 : validRep representative_1155 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1155)=dictionary64.getD 318 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_318]
  decide +kernel
theorem coefficient_1156 : validRep representative_1156 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1156)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1157 : validRep representative_1157 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1157)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_1158 : validRep representative_1158 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1158)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1159 : validRep representative_1159 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1159)=dictionary64.getD 320 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_320]
  decide +kernel
theorem coefficient_1160 : validRep representative_1160 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1160)=dictionary64.getD 317 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_317]
  decide +kernel
theorem coefficient_1161 : validRep representative_1161 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1161)=dictionary64.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_1162 : validRep representative_1162 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1162)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1163 : validRep representative_1163 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1163)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1164 : validRep representative_1164 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1164)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1165 : validRep representative_1165 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1165)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1166 : validRep representative_1166 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1166)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1167 : validRep representative_1167 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1167)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1168 : validRep representative_1168 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1168)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_1169 : validRep representative_1169 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1169)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1170 : validRep representative_1170 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1170)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1171 : validRep representative_1171 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1171)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1172 : validRep representative_1172 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1172)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1173 : validRep representative_1173 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1173)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1174 : validRep representative_1174 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1174)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1175 : validRep representative_1175 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1175)=dictionary64.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_1176 : validRep representative_1176 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1176)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1177 : validRep representative_1177 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1177)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1178 : validRep representative_1178 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1178)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1179 : validRep representative_1179 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1179)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1180 : validRep representative_1180 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1180)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1181 : validRep representative_1181 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1181)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1182 : validRep representative_1182 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1182)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1183 : validRep representative_1183 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1183)=dictionary64.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_1184 : validRep representative_1184 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1184)=dictionary64.getD 298 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_298]
  decide +kernel
theorem coefficient_1185 : validRep representative_1185 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1185)=dictionary64.getD 229 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_229]
  decide +kernel
theorem coefficient_1186 : validRep representative_1186 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1186)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_1187 : validRep representative_1187 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1187)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1188 : validRep representative_1188 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1188)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_1189 : validRep representative_1189 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1189)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1190 : validRep representative_1190 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1190)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_1191 : validRep representative_1191 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1191)=dictionary64.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_1192 : validRep representative_1192 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1192)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_1193 : validRep representative_1193 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1193)=dictionary64.getD 231 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_231]
  decide +kernel
theorem coefficient_1194 : validRep representative_1194 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1194)=dictionary64.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_1195 : validRep representative_1195 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1195)=dictionary64.getD 161 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_161]
  decide +kernel
theorem coefficient_1196 : validRep representative_1196 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1196)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1197 : validRep representative_1197 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1197)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1198 : validRep representative_1198 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1198)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1199 : validRep representative_1199 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1199)=dictionary64.getD 283 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_283]
  decide +kernel
theorem coefficient_1200 : validRep representative_1200 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1200)=dictionary64.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_1201 : validRep representative_1201 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1201)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1202 : validRep representative_1202 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1202)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1203 : validRep representative_1203 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1203)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1204 : validRep representative_1204 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1204)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1205 : validRep representative_1205 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1205)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1206 : validRep representative_1206 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1206)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1207 : validRep representative_1207 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1207)=dictionary64.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_1208 : validRep representative_1208 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1208)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1209 : validRep representative_1209 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1209)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1210 : validRep representative_1210 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1210)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1211 : validRep representative_1211 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1211)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1212 : validRep representative_1212 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1212)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1213 : validRep representative_1213 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1213)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1214 : validRep representative_1214 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1214)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1215 : validRep representative_1215 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1215)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_018 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1184 (QuarticIntegerRepresentativeTree.Tree.branch 1168 (QuarticIntegerRepresentativeTree.Tree.branch 1160 (QuarticIntegerRepresentativeTree.Tree.branch 1156 (QuarticIntegerRepresentativeTree.Tree.branch 1154 (QuarticIntegerRepresentativeTree.Tree.branch 1153 (QuarticIntegerRepresentativeTree.Tree.leaf 1152 representative_1152) (QuarticIntegerRepresentativeTree.Tree.leaf 1153 representative_1153)) (QuarticIntegerRepresentativeTree.Tree.branch 1155 (QuarticIntegerRepresentativeTree.Tree.leaf 1154 representative_1154) (QuarticIntegerRepresentativeTree.Tree.leaf 1155 representative_1155))) (QuarticIntegerRepresentativeTree.Tree.branch 1158 (QuarticIntegerRepresentativeTree.Tree.branch 1157 (QuarticIntegerRepresentativeTree.Tree.leaf 1156 representative_1156) (QuarticIntegerRepresentativeTree.Tree.leaf 1157 representative_1157)) (QuarticIntegerRepresentativeTree.Tree.branch 1159 (QuarticIntegerRepresentativeTree.Tree.leaf 1158 representative_1158) (QuarticIntegerRepresentativeTree.Tree.leaf 1159 representative_1159)))) (QuarticIntegerRepresentativeTree.Tree.branch 1164 (QuarticIntegerRepresentativeTree.Tree.branch 1162 (QuarticIntegerRepresentativeTree.Tree.branch 1161 (QuarticIntegerRepresentativeTree.Tree.leaf 1160 representative_1160) (QuarticIntegerRepresentativeTree.Tree.leaf 1161 representative_1161)) (QuarticIntegerRepresentativeTree.Tree.branch 1163 (QuarticIntegerRepresentativeTree.Tree.leaf 1162 representative_1162) (QuarticIntegerRepresentativeTree.Tree.leaf 1163 representative_1163))) (QuarticIntegerRepresentativeTree.Tree.branch 1166 (QuarticIntegerRepresentativeTree.Tree.branch 1165 (QuarticIntegerRepresentativeTree.Tree.leaf 1164 representative_1164) (QuarticIntegerRepresentativeTree.Tree.leaf 1165 representative_1165)) (QuarticIntegerRepresentativeTree.Tree.branch 1167 (QuarticIntegerRepresentativeTree.Tree.leaf 1166 representative_1166) (QuarticIntegerRepresentativeTree.Tree.leaf 1167 representative_1167))))) (QuarticIntegerRepresentativeTree.Tree.branch 1176 (QuarticIntegerRepresentativeTree.Tree.branch 1172 (QuarticIntegerRepresentativeTree.Tree.branch 1170 (QuarticIntegerRepresentativeTree.Tree.branch 1169 (QuarticIntegerRepresentativeTree.Tree.leaf 1168 representative_1168) (QuarticIntegerRepresentativeTree.Tree.leaf 1169 representative_1169)) (QuarticIntegerRepresentativeTree.Tree.branch 1171 (QuarticIntegerRepresentativeTree.Tree.leaf 1170 representative_1170) (QuarticIntegerRepresentativeTree.Tree.leaf 1171 representative_1171))) (QuarticIntegerRepresentativeTree.Tree.branch 1174 (QuarticIntegerRepresentativeTree.Tree.branch 1173 (QuarticIntegerRepresentativeTree.Tree.leaf 1172 representative_1172) (QuarticIntegerRepresentativeTree.Tree.leaf 1173 representative_1173)) (QuarticIntegerRepresentativeTree.Tree.branch 1175 (QuarticIntegerRepresentativeTree.Tree.leaf 1174 representative_1174) (QuarticIntegerRepresentativeTree.Tree.leaf 1175 representative_1175)))) (QuarticIntegerRepresentativeTree.Tree.branch 1180 (QuarticIntegerRepresentativeTree.Tree.branch 1178 (QuarticIntegerRepresentativeTree.Tree.branch 1177 (QuarticIntegerRepresentativeTree.Tree.leaf 1176 representative_1176) (QuarticIntegerRepresentativeTree.Tree.leaf 1177 representative_1177)) (QuarticIntegerRepresentativeTree.Tree.branch 1179 (QuarticIntegerRepresentativeTree.Tree.leaf 1178 representative_1178) (QuarticIntegerRepresentativeTree.Tree.leaf 1179 representative_1179))) (QuarticIntegerRepresentativeTree.Tree.branch 1182 (QuarticIntegerRepresentativeTree.Tree.branch 1181 (QuarticIntegerRepresentativeTree.Tree.leaf 1180 representative_1180) (QuarticIntegerRepresentativeTree.Tree.leaf 1181 representative_1181)) (QuarticIntegerRepresentativeTree.Tree.branch 1183 (QuarticIntegerRepresentativeTree.Tree.leaf 1182 representative_1182) (QuarticIntegerRepresentativeTree.Tree.leaf 1183 representative_1183)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1200 (QuarticIntegerRepresentativeTree.Tree.branch 1192 (QuarticIntegerRepresentativeTree.Tree.branch 1188 (QuarticIntegerRepresentativeTree.Tree.branch 1186 (QuarticIntegerRepresentativeTree.Tree.branch 1185 (QuarticIntegerRepresentativeTree.Tree.leaf 1184 representative_1184) (QuarticIntegerRepresentativeTree.Tree.leaf 1185 representative_1185)) (QuarticIntegerRepresentativeTree.Tree.branch 1187 (QuarticIntegerRepresentativeTree.Tree.leaf 1186 representative_1186) (QuarticIntegerRepresentativeTree.Tree.leaf 1187 representative_1187))) (QuarticIntegerRepresentativeTree.Tree.branch 1190 (QuarticIntegerRepresentativeTree.Tree.branch 1189 (QuarticIntegerRepresentativeTree.Tree.leaf 1188 representative_1188) (QuarticIntegerRepresentativeTree.Tree.leaf 1189 representative_1189)) (QuarticIntegerRepresentativeTree.Tree.branch 1191 (QuarticIntegerRepresentativeTree.Tree.leaf 1190 representative_1190) (QuarticIntegerRepresentativeTree.Tree.leaf 1191 representative_1191)))) (QuarticIntegerRepresentativeTree.Tree.branch 1196 (QuarticIntegerRepresentativeTree.Tree.branch 1194 (QuarticIntegerRepresentativeTree.Tree.branch 1193 (QuarticIntegerRepresentativeTree.Tree.leaf 1192 representative_1192) (QuarticIntegerRepresentativeTree.Tree.leaf 1193 representative_1193)) (QuarticIntegerRepresentativeTree.Tree.branch 1195 (QuarticIntegerRepresentativeTree.Tree.leaf 1194 representative_1194) (QuarticIntegerRepresentativeTree.Tree.leaf 1195 representative_1195))) (QuarticIntegerRepresentativeTree.Tree.branch 1198 (QuarticIntegerRepresentativeTree.Tree.branch 1197 (QuarticIntegerRepresentativeTree.Tree.leaf 1196 representative_1196) (QuarticIntegerRepresentativeTree.Tree.leaf 1197 representative_1197)) (QuarticIntegerRepresentativeTree.Tree.branch 1199 (QuarticIntegerRepresentativeTree.Tree.leaf 1198 representative_1198) (QuarticIntegerRepresentativeTree.Tree.leaf 1199 representative_1199))))) (QuarticIntegerRepresentativeTree.Tree.branch 1208 (QuarticIntegerRepresentativeTree.Tree.branch 1204 (QuarticIntegerRepresentativeTree.Tree.branch 1202 (QuarticIntegerRepresentativeTree.Tree.branch 1201 (QuarticIntegerRepresentativeTree.Tree.leaf 1200 representative_1200) (QuarticIntegerRepresentativeTree.Tree.leaf 1201 representative_1201)) (QuarticIntegerRepresentativeTree.Tree.branch 1203 (QuarticIntegerRepresentativeTree.Tree.leaf 1202 representative_1202) (QuarticIntegerRepresentativeTree.Tree.leaf 1203 representative_1203))) (QuarticIntegerRepresentativeTree.Tree.branch 1206 (QuarticIntegerRepresentativeTree.Tree.branch 1205 (QuarticIntegerRepresentativeTree.Tree.leaf 1204 representative_1204) (QuarticIntegerRepresentativeTree.Tree.leaf 1205 representative_1205)) (QuarticIntegerRepresentativeTree.Tree.branch 1207 (QuarticIntegerRepresentativeTree.Tree.leaf 1206 representative_1206) (QuarticIntegerRepresentativeTree.Tree.leaf 1207 representative_1207)))) (QuarticIntegerRepresentativeTree.Tree.branch 1212 (QuarticIntegerRepresentativeTree.Tree.branch 1210 (QuarticIntegerRepresentativeTree.Tree.branch 1209 (QuarticIntegerRepresentativeTree.Tree.leaf 1208 representative_1208) (QuarticIntegerRepresentativeTree.Tree.leaf 1209 representative_1209)) (QuarticIntegerRepresentativeTree.Tree.branch 1211 (QuarticIntegerRepresentativeTree.Tree.leaf 1210 representative_1210) (QuarticIntegerRepresentativeTree.Tree.leaf 1211 representative_1211))) (QuarticIntegerRepresentativeTree.Tree.branch 1214 (QuarticIntegerRepresentativeTree.Tree.branch 1213 (QuarticIntegerRepresentativeTree.Tree.leaf 1212 representative_1212) (QuarticIntegerRepresentativeTree.Tree.leaf 1213 representative_1213)) (QuarticIntegerRepresentativeTree.Tree.branch 1215 (QuarticIntegerRepresentativeTree.Tree.leaf 1214 representative_1214) (QuarticIntegerRepresentativeTree.Tree.leaf 1215 representative_1215)))))))
theorem accepted_018 : All validRep tree_018 := ⟨⟨⟨⟨⟨⟨coefficient_1152,coefficient_1153⟩,⟨coefficient_1154,coefficient_1155⟩⟩,⟨⟨coefficient_1156,coefficient_1157⟩,⟨coefficient_1158,coefficient_1159⟩⟩⟩,⟨⟨⟨coefficient_1160,coefficient_1161⟩,⟨coefficient_1162,coefficient_1163⟩⟩,⟨⟨coefficient_1164,coefficient_1165⟩,⟨coefficient_1166,coefficient_1167⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1168,coefficient_1169⟩,⟨coefficient_1170,coefficient_1171⟩⟩,⟨⟨coefficient_1172,coefficient_1173⟩,⟨coefficient_1174,coefficient_1175⟩⟩⟩,⟨⟨⟨coefficient_1176,coefficient_1177⟩,⟨coefficient_1178,coefficient_1179⟩⟩,⟨⟨coefficient_1180,coefficient_1181⟩,⟨coefficient_1182,coefficient_1183⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1184,coefficient_1185⟩,⟨coefficient_1186,coefficient_1187⟩⟩,⟨⟨coefficient_1188,coefficient_1189⟩,⟨coefficient_1190,coefficient_1191⟩⟩⟩,⟨⟨⟨coefficient_1192,coefficient_1193⟩,⟨coefficient_1194,coefficient_1195⟩⟩,⟨⟨coefficient_1196,coefficient_1197⟩,⟨coefficient_1198,coefficient_1199⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1200,coefficient_1201⟩,⟨coefficient_1202,coefficient_1203⟩⟩,⟨⟨coefficient_1204,coefficient_1205⟩,⟨coefficient_1206,coefficient_1207⟩⟩⟩,⟨⟨⟨coefficient_1208,coefficient_1209⟩,⟨coefficient_1210,coefficient_1211⟩⟩,⟨⟨coefficient_1212,coefficient_1213⟩,⟨coefficient_1214,coefficient_1215⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

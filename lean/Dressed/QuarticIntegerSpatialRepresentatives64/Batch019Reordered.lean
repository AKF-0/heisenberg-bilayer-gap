import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1216 : Rep := ⟨![0,3,12,37],462⟩
def representative_1217 : Rep := ⟨![0,3,12,38],462⟩
def representative_1218 : Rep := ⟨![0,3,12,39],462⟩
def representative_1219 : Rep := ⟨![0,3,12,40],462⟩
def representative_1220 : Rep := ⟨![0,3,12,41],462⟩
def representative_1221 : Rep := ⟨![0,3,12,42],236⟩
def representative_1222 : Rep := ⟨![0,3,12,43],262⟩
def representative_1223 : Rep := ⟨![0,3,12,44],236⟩
def representative_1224 : Rep := ⟨![0,3,12,45],462⟩
def representative_1225 : Rep := ⟨![0,3,12,46],462⟩
def representative_1226 : Rep := ⟨![0,3,12,47],462⟩
def representative_1227 : Rep := ⟨![0,3,12,48],462⟩
def representative_1228 : Rep := ⟨![0,3,12,49],235⟩
def representative_1229 : Rep := ⟨![0,3,12,50],279⟩
def representative_1230 : Rep := ⟨![0,3,12,51],190⟩
def representative_1231 : Rep := ⟨![0,3,12,53],235⟩
def representative_1232 : Rep := ⟨![0,3,12,54],462⟩
def representative_1233 : Rep := ⟨![0,3,12,55],462⟩
def representative_1234 : Rep := ⟨![0,3,12,61],282⟩
def representative_1235 : Rep := ⟨![0,3,12,62],236⟩
def representative_1236 : Rep := ⟨![0,3,12,63],462⟩
def representative_1237 : Rep := ⟨![0,3,13,16],238⟩
def representative_1238 : Rep := ⟨![0,3,13,17],245⟩
def representative_1239 : Rep := ⟨![0,3,13,18],234⟩
def representative_1240 : Rep := ⟨![0,3,13,19],268⟩
def representative_1241 : Rep := ⟨![0,3,13,20],226⟩
def representative_1242 : Rep := ⟨![0,3,13,22],232⟩
def representative_1243 : Rep := ⟨![0,3,13,23],247⟩
def representative_1244 : Rep := ⟨![0,3,13,24],241⟩
def representative_1245 : Rep := ⟨![0,3,13,25],462⟩
def representative_1246 : Rep := ⟨![0,3,13,26],243⟩
def representative_1247 : Rep := ⟨![0,3,13,27],237⟩
def representative_1248 : Rep := ⟨![0,3,13,28],247⟩
def representative_1249 : Rep := ⟨![0,3,13,30],246⟩
def representative_1250 : Rep := ⟨![0,3,13,31],462⟩
def representative_1251 : Rep := ⟨![0,3,13,32],462⟩
def representative_1252 : Rep := ⟨![0,3,13,33],462⟩
def representative_1253 : Rep := ⟨![0,3,13,34],462⟩
def representative_1254 : Rep := ⟨![0,3,13,35],242⟩
def representative_1255 : Rep := ⟨![0,3,13,36],462⟩
def representative_1256 : Rep := ⟨![0,3,13,37],243⟩
def representative_1257 : Rep := ⟨![0,3,13,38],462⟩
def representative_1258 : Rep := ⟨![0,3,13,39],462⟩
def representative_1259 : Rep := ⟨![0,3,13,40],241⟩
def representative_1260 : Rep := ⟨![0,3,13,41],462⟩
def representative_1261 : Rep := ⟨![0,3,13,42],243⟩
def representative_1262 : Rep := ⟨![0,3,13,43],237⟩
def representative_1263 : Rep := ⟨![0,3,13,44],243⟩
def representative_1264 : Rep := ⟨![0,3,13,45],462⟩
def representative_1265 : Rep := ⟨![0,3,13,46],462⟩
def representative_1266 : Rep := ⟨![0,3,13,47],462⟩
def representative_1267 : Rep := ⟨![0,3,13,48],238⟩
def representative_1268 : Rep := ⟨![0,3,13,49],245⟩
def representative_1269 : Rep := ⟨![0,3,13,50],234⟩
def representative_1270 : Rep := ⟨![0,3,13,51],266⟩
def representative_1271 : Rep := ⟨![0,3,13,52],234⟩
def representative_1272 : Rep := ⟨![0,3,13,53],245⟩
def representative_1273 : Rep := ⟨![0,3,13,54],462⟩
def representative_1274 : Rep := ⟨![0,3,13,55],243⟩
def representative_1275 : Rep := ⟨![0,3,13,62],252⟩
def representative_1276 : Rep := ⟨![0,3,16,19],462⟩
def representative_1277 : Rep := ⟨![0,3,16,20],462⟩
def representative_1278 : Rep := ⟨![0,3,16,21],462⟩
def representative_1279 : Rep := ⟨![0,3,16,25],238⟩
theorem coefficient_1216 : validRep representative_1216 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1216)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1217 : validRep representative_1217 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1217)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1218 : validRep representative_1218 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1218)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1219 : validRep representative_1219 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1219)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1220 : validRep representative_1220 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1220)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1221 : validRep representative_1221 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1221)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1222 : validRep representative_1222 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1222)=dictionary64.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_1223 : validRep representative_1223 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1223)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1224 : validRep representative_1224 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1224)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1225 : validRep representative_1225 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1225)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1226 : validRep representative_1226 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1226)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1227 : validRep representative_1227 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1227)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1228 : validRep representative_1228 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1228)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1229 : validRep representative_1229 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1229)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_1230 : validRep representative_1230 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1230)=dictionary64.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_1231 : validRep representative_1231 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1231)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1232 : validRep representative_1232 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1232)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1233 : validRep representative_1233 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1233)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1234 : validRep representative_1234 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1234)=dictionary64.getD 282 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_282]
  decide +kernel
theorem coefficient_1235 : validRep representative_1235 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1235)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1236 : validRep representative_1236 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1236)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1237 : validRep representative_1237 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1237)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1238 : validRep representative_1238 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1238)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_1239 : validRep representative_1239 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1239)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1240 : validRep representative_1240 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1240)=dictionary64.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_1241 : validRep representative_1241 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1241)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_1242 : validRep representative_1242 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1242)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1243 : validRep representative_1243 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1243)=dictionary64.getD 247 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_247]
  decide +kernel
theorem coefficient_1244 : validRep representative_1244 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1244)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1245 : validRep representative_1245 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1245)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1246 : validRep representative_1246 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1246)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1247 : validRep representative_1247 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1247)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1248 : validRep representative_1248 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1248)=dictionary64.getD 247 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_247]
  decide +kernel
theorem coefficient_1249 : validRep representative_1249 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1249)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_1250 : validRep representative_1250 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1250)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1251 : validRep representative_1251 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1251)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1252 : validRep representative_1252 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1252)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1253 : validRep representative_1253 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1253)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1254 : validRep representative_1254 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1254)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1255 : validRep representative_1255 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1255)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1256 : validRep representative_1256 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1256)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1257 : validRep representative_1257 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1257)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1258 : validRep representative_1258 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1258)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1259 : validRep representative_1259 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1259)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1260 : validRep representative_1260 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1260)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1261 : validRep representative_1261 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1261)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1262 : validRep representative_1262 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1262)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1263 : validRep representative_1263 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1263)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1264 : validRep representative_1264 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1264)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1265 : validRep representative_1265 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1265)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1266 : validRep representative_1266 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1266)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1267 : validRep representative_1267 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1267)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1268 : validRep representative_1268 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1268)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_1269 : validRep representative_1269 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1269)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1270 : validRep representative_1270 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1270)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_1271 : validRep representative_1271 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1271)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1272 : validRep representative_1272 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1272)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_1273 : validRep representative_1273 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1273)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1274 : validRep representative_1274 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1274)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1275 : validRep representative_1275 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1275)=dictionary64.getD 252 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_252]
  decide +kernel
theorem coefficient_1276 : validRep representative_1276 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1276)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1277 : validRep representative_1277 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1277)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1278 : validRep representative_1278 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1278)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1279 : validRep representative_1279 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1279)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
def tree_019 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1248 (QuarticIntegerRepresentativeTree.Tree.branch 1232 (QuarticIntegerRepresentativeTree.Tree.branch 1224 (QuarticIntegerRepresentativeTree.Tree.branch 1220 (QuarticIntegerRepresentativeTree.Tree.branch 1218 (QuarticIntegerRepresentativeTree.Tree.branch 1217 (QuarticIntegerRepresentativeTree.Tree.leaf 1216 representative_1216) (QuarticIntegerRepresentativeTree.Tree.leaf 1217 representative_1217)) (QuarticIntegerRepresentativeTree.Tree.branch 1219 (QuarticIntegerRepresentativeTree.Tree.leaf 1218 representative_1218) (QuarticIntegerRepresentativeTree.Tree.leaf 1219 representative_1219))) (QuarticIntegerRepresentativeTree.Tree.branch 1222 (QuarticIntegerRepresentativeTree.Tree.branch 1221 (QuarticIntegerRepresentativeTree.Tree.leaf 1220 representative_1220) (QuarticIntegerRepresentativeTree.Tree.leaf 1221 representative_1221)) (QuarticIntegerRepresentativeTree.Tree.branch 1223 (QuarticIntegerRepresentativeTree.Tree.leaf 1222 representative_1222) (QuarticIntegerRepresentativeTree.Tree.leaf 1223 representative_1223)))) (QuarticIntegerRepresentativeTree.Tree.branch 1228 (QuarticIntegerRepresentativeTree.Tree.branch 1226 (QuarticIntegerRepresentativeTree.Tree.branch 1225 (QuarticIntegerRepresentativeTree.Tree.leaf 1224 representative_1224) (QuarticIntegerRepresentativeTree.Tree.leaf 1225 representative_1225)) (QuarticIntegerRepresentativeTree.Tree.branch 1227 (QuarticIntegerRepresentativeTree.Tree.leaf 1226 representative_1226) (QuarticIntegerRepresentativeTree.Tree.leaf 1227 representative_1227))) (QuarticIntegerRepresentativeTree.Tree.branch 1230 (QuarticIntegerRepresentativeTree.Tree.branch 1229 (QuarticIntegerRepresentativeTree.Tree.leaf 1228 representative_1228) (QuarticIntegerRepresentativeTree.Tree.leaf 1229 representative_1229)) (QuarticIntegerRepresentativeTree.Tree.branch 1231 (QuarticIntegerRepresentativeTree.Tree.leaf 1230 representative_1230) (QuarticIntegerRepresentativeTree.Tree.leaf 1231 representative_1231))))) (QuarticIntegerRepresentativeTree.Tree.branch 1240 (QuarticIntegerRepresentativeTree.Tree.branch 1236 (QuarticIntegerRepresentativeTree.Tree.branch 1234 (QuarticIntegerRepresentativeTree.Tree.branch 1233 (QuarticIntegerRepresentativeTree.Tree.leaf 1232 representative_1232) (QuarticIntegerRepresentativeTree.Tree.leaf 1233 representative_1233)) (QuarticIntegerRepresentativeTree.Tree.branch 1235 (QuarticIntegerRepresentativeTree.Tree.leaf 1234 representative_1234) (QuarticIntegerRepresentativeTree.Tree.leaf 1235 representative_1235))) (QuarticIntegerRepresentativeTree.Tree.branch 1238 (QuarticIntegerRepresentativeTree.Tree.branch 1237 (QuarticIntegerRepresentativeTree.Tree.leaf 1236 representative_1236) (QuarticIntegerRepresentativeTree.Tree.leaf 1237 representative_1237)) (QuarticIntegerRepresentativeTree.Tree.branch 1239 (QuarticIntegerRepresentativeTree.Tree.leaf 1238 representative_1238) (QuarticIntegerRepresentativeTree.Tree.leaf 1239 representative_1239)))) (QuarticIntegerRepresentativeTree.Tree.branch 1244 (QuarticIntegerRepresentativeTree.Tree.branch 1242 (QuarticIntegerRepresentativeTree.Tree.branch 1241 (QuarticIntegerRepresentativeTree.Tree.leaf 1240 representative_1240) (QuarticIntegerRepresentativeTree.Tree.leaf 1241 representative_1241)) (QuarticIntegerRepresentativeTree.Tree.branch 1243 (QuarticIntegerRepresentativeTree.Tree.leaf 1242 representative_1242) (QuarticIntegerRepresentativeTree.Tree.leaf 1243 representative_1243))) (QuarticIntegerRepresentativeTree.Tree.branch 1246 (QuarticIntegerRepresentativeTree.Tree.branch 1245 (QuarticIntegerRepresentativeTree.Tree.leaf 1244 representative_1244) (QuarticIntegerRepresentativeTree.Tree.leaf 1245 representative_1245)) (QuarticIntegerRepresentativeTree.Tree.branch 1247 (QuarticIntegerRepresentativeTree.Tree.leaf 1246 representative_1246) (QuarticIntegerRepresentativeTree.Tree.leaf 1247 representative_1247)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1264 (QuarticIntegerRepresentativeTree.Tree.branch 1256 (QuarticIntegerRepresentativeTree.Tree.branch 1252 (QuarticIntegerRepresentativeTree.Tree.branch 1250 (QuarticIntegerRepresentativeTree.Tree.branch 1249 (QuarticIntegerRepresentativeTree.Tree.leaf 1248 representative_1248) (QuarticIntegerRepresentativeTree.Tree.leaf 1249 representative_1249)) (QuarticIntegerRepresentativeTree.Tree.branch 1251 (QuarticIntegerRepresentativeTree.Tree.leaf 1250 representative_1250) (QuarticIntegerRepresentativeTree.Tree.leaf 1251 representative_1251))) (QuarticIntegerRepresentativeTree.Tree.branch 1254 (QuarticIntegerRepresentativeTree.Tree.branch 1253 (QuarticIntegerRepresentativeTree.Tree.leaf 1252 representative_1252) (QuarticIntegerRepresentativeTree.Tree.leaf 1253 representative_1253)) (QuarticIntegerRepresentativeTree.Tree.branch 1255 (QuarticIntegerRepresentativeTree.Tree.leaf 1254 representative_1254) (QuarticIntegerRepresentativeTree.Tree.leaf 1255 representative_1255)))) (QuarticIntegerRepresentativeTree.Tree.branch 1260 (QuarticIntegerRepresentativeTree.Tree.branch 1258 (QuarticIntegerRepresentativeTree.Tree.branch 1257 (QuarticIntegerRepresentativeTree.Tree.leaf 1256 representative_1256) (QuarticIntegerRepresentativeTree.Tree.leaf 1257 representative_1257)) (QuarticIntegerRepresentativeTree.Tree.branch 1259 (QuarticIntegerRepresentativeTree.Tree.leaf 1258 representative_1258) (QuarticIntegerRepresentativeTree.Tree.leaf 1259 representative_1259))) (QuarticIntegerRepresentativeTree.Tree.branch 1262 (QuarticIntegerRepresentativeTree.Tree.branch 1261 (QuarticIntegerRepresentativeTree.Tree.leaf 1260 representative_1260) (QuarticIntegerRepresentativeTree.Tree.leaf 1261 representative_1261)) (QuarticIntegerRepresentativeTree.Tree.branch 1263 (QuarticIntegerRepresentativeTree.Tree.leaf 1262 representative_1262) (QuarticIntegerRepresentativeTree.Tree.leaf 1263 representative_1263))))) (QuarticIntegerRepresentativeTree.Tree.branch 1272 (QuarticIntegerRepresentativeTree.Tree.branch 1268 (QuarticIntegerRepresentativeTree.Tree.branch 1266 (QuarticIntegerRepresentativeTree.Tree.branch 1265 (QuarticIntegerRepresentativeTree.Tree.leaf 1264 representative_1264) (QuarticIntegerRepresentativeTree.Tree.leaf 1265 representative_1265)) (QuarticIntegerRepresentativeTree.Tree.branch 1267 (QuarticIntegerRepresentativeTree.Tree.leaf 1266 representative_1266) (QuarticIntegerRepresentativeTree.Tree.leaf 1267 representative_1267))) (QuarticIntegerRepresentativeTree.Tree.branch 1270 (QuarticIntegerRepresentativeTree.Tree.branch 1269 (QuarticIntegerRepresentativeTree.Tree.leaf 1268 representative_1268) (QuarticIntegerRepresentativeTree.Tree.leaf 1269 representative_1269)) (QuarticIntegerRepresentativeTree.Tree.branch 1271 (QuarticIntegerRepresentativeTree.Tree.leaf 1270 representative_1270) (QuarticIntegerRepresentativeTree.Tree.leaf 1271 representative_1271)))) (QuarticIntegerRepresentativeTree.Tree.branch 1276 (QuarticIntegerRepresentativeTree.Tree.branch 1274 (QuarticIntegerRepresentativeTree.Tree.branch 1273 (QuarticIntegerRepresentativeTree.Tree.leaf 1272 representative_1272) (QuarticIntegerRepresentativeTree.Tree.leaf 1273 representative_1273)) (QuarticIntegerRepresentativeTree.Tree.branch 1275 (QuarticIntegerRepresentativeTree.Tree.leaf 1274 representative_1274) (QuarticIntegerRepresentativeTree.Tree.leaf 1275 representative_1275))) (QuarticIntegerRepresentativeTree.Tree.branch 1278 (QuarticIntegerRepresentativeTree.Tree.branch 1277 (QuarticIntegerRepresentativeTree.Tree.leaf 1276 representative_1276) (QuarticIntegerRepresentativeTree.Tree.leaf 1277 representative_1277)) (QuarticIntegerRepresentativeTree.Tree.branch 1279 (QuarticIntegerRepresentativeTree.Tree.leaf 1278 representative_1278) (QuarticIntegerRepresentativeTree.Tree.leaf 1279 representative_1279)))))))
theorem accepted_019 : All validRep tree_019 := ⟨⟨⟨⟨⟨⟨coefficient_1216,coefficient_1217⟩,⟨coefficient_1218,coefficient_1219⟩⟩,⟨⟨coefficient_1220,coefficient_1221⟩,⟨coefficient_1222,coefficient_1223⟩⟩⟩,⟨⟨⟨coefficient_1224,coefficient_1225⟩,⟨coefficient_1226,coefficient_1227⟩⟩,⟨⟨coefficient_1228,coefficient_1229⟩,⟨coefficient_1230,coefficient_1231⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1232,coefficient_1233⟩,⟨coefficient_1234,coefficient_1235⟩⟩,⟨⟨coefficient_1236,coefficient_1237⟩,⟨coefficient_1238,coefficient_1239⟩⟩⟩,⟨⟨⟨coefficient_1240,coefficient_1241⟩,⟨coefficient_1242,coefficient_1243⟩⟩,⟨⟨coefficient_1244,coefficient_1245⟩,⟨coefficient_1246,coefficient_1247⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1248,coefficient_1249⟩,⟨coefficient_1250,coefficient_1251⟩⟩,⟨⟨coefficient_1252,coefficient_1253⟩,⟨coefficient_1254,coefficient_1255⟩⟩⟩,⟨⟨⟨coefficient_1256,coefficient_1257⟩,⟨coefficient_1258,coefficient_1259⟩⟩,⟨⟨coefficient_1260,coefficient_1261⟩,⟨coefficient_1262,coefficient_1263⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1264,coefficient_1265⟩,⟨coefficient_1266,coefficient_1267⟩⟩,⟨⟨coefficient_1268,coefficient_1269⟩,⟨coefficient_1270,coefficient_1271⟩⟩⟩,⟨⟨⟨coefficient_1272,coefficient_1273⟩,⟨coefficient_1274,coefficient_1275⟩⟩,⟨⟨coefficient_1276,coefficient_1277⟩,⟨coefficient_1278,coefficient_1279⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

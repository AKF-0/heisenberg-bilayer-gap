import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1280 : Rep := ⟨![0,3,16,26],462⟩
def representative_1281 : Rep := ⟨![0,3,16,27],462⟩
def representative_1282 : Rep := ⟨![0,3,16,28],462⟩
def representative_1283 : Rep := ⟨![0,3,16,29],462⟩
def representative_1284 : Rep := ⟨![0,3,16,30],462⟩
def representative_1285 : Rep := ⟨![0,3,16,31],238⟩
def representative_1286 : Rep := ⟨![0,3,16,33],462⟩
def representative_1287 : Rep := ⟨![0,3,16,34],462⟩
def representative_1288 : Rep := ⟨![0,3,16,35],462⟩
def representative_1289 : Rep := ⟨![0,3,16,36],462⟩
def representative_1290 : Rep := ⟨![0,3,16,37],462⟩
def representative_1291 : Rep := ⟨![0,3,16,38],462⟩
def representative_1292 : Rep := ⟨![0,3,16,39],462⟩
def representative_1293 : Rep := ⟨![0,3,16,41],238⟩
def representative_1294 : Rep := ⟨![0,3,16,42],462⟩
def representative_1295 : Rep := ⟨![0,3,16,43],462⟩
def representative_1296 : Rep := ⟨![0,3,16,44],462⟩
def representative_1297 : Rep := ⟨![0,3,16,45],462⟩
def representative_1298 : Rep := ⟨![0,3,16,46],462⟩
def representative_1299 : Rep := ⟨![0,3,16,47],238⟩
def representative_1300 : Rep := ⟨![0,3,16,48],206⟩
def representative_1301 : Rep := ⟨![0,3,16,49],266⟩
def representative_1302 : Rep := ⟨![0,3,16,50],237⟩
def representative_1303 : Rep := ⟨![0,3,16,51],462⟩
def representative_1304 : Rep := ⟨![0,3,16,52],462⟩
def representative_1305 : Rep := ⟨![0,3,16,53],462⟩
def representative_1306 : Rep := ⟨![0,3,16,54],237⟩
def representative_1307 : Rep := ⟨![0,3,16,55],266⟩
def representative_1308 : Rep := ⟨![0,3,17,20],246⟩
def representative_1309 : Rep := ⟨![0,3,17,21],462⟩
def representative_1310 : Rep := ⟨![0,3,17,22],246⟩
def representative_1311 : Rep := ⟨![0,3,17,24],226⟩
def representative_1312 : Rep := ⟨![0,3,17,26],228⟩
def representative_1313 : Rep := ⟨![0,3,17,27],249⟩
def representative_1314 : Rep := ⟨![0,3,17,28],462⟩
def representative_1315 : Rep := ⟨![0,3,17,29],462⟩
def representative_1316 : Rep := ⟨![0,3,17,30],462⟩
def representative_1317 : Rep := ⟨![0,3,17,31],250⟩
def representative_1318 : Rep := ⟨![0,3,17,32],249⟩
def representative_1319 : Rep := ⟨![0,3,17,34],248⟩
def representative_1320 : Rep := ⟨![0,3,17,35],462⟩
def representative_1321 : Rep := ⟨![0,3,17,36],462⟩
def representative_1322 : Rep := ⟨![0,3,17,37],462⟩
def representative_1323 : Rep := ⟨![0,3,17,38],462⟩
def representative_1324 : Rep := ⟨![0,3,17,39],462⟩
def representative_1325 : Rep := ⟨![0,3,17,40],237⟩
def representative_1326 : Rep := ⟨![0,3,17,42],462⟩
def representative_1327 : Rep := ⟨![0,3,17,43],242⟩
def representative_1328 : Rep := ⟨![0,3,17,44],462⟩
def representative_1329 : Rep := ⟨![0,3,17,45],462⟩
def representative_1330 : Rep := ⟨![0,3,17,46],462⟩
def representative_1331 : Rep := ⟨![0,3,17,47],243⟩
def representative_1332 : Rep := ⟨![0,3,17,49],234⟩
def representative_1333 : Rep := ⟨![0,3,17,50],246⟩
def representative_1334 : Rep := ⟨![0,3,17,52],244⟩
def representative_1335 : Rep := ⟨![0,3,17,53],462⟩
def representative_1336 : Rep := ⟨![0,3,17,54],244⟩
def representative_1337 : Rep := ⟨![0,3,17,55],234⟩
def representative_1338 : Rep := ⟨![0,3,20,23],462⟩
def representative_1339 : Rep := ⟨![0,3,20,24],462⟩
def representative_1340 : Rep := ⟨![0,3,20,25],462⟩
def representative_1341 : Rep := ⟨![0,3,20,26],243⟩
def representative_1342 : Rep := ⟨![0,3,20,27],237⟩
def representative_1343 : Rep := ⟨![0,3,20,29],462⟩
theorem coefficient_1280 : validRep representative_1280 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1280)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1281 : validRep representative_1281 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1281)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1282 : validRep representative_1282 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1282)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1283 : validRep representative_1283 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1283)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1284 : validRep representative_1284 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1284)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1285 : validRep representative_1285 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1285)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1286 : validRep representative_1286 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1286)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1287 : validRep representative_1287 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1287)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1288 : validRep representative_1288 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1288)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1289 : validRep representative_1289 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1289)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1290 : validRep representative_1290 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1290)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1291 : validRep representative_1291 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1291)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1292 : validRep representative_1292 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1292)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1293 : validRep representative_1293 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1293)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1294 : validRep representative_1294 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1294)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1295 : validRep representative_1295 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1295)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1296 : validRep representative_1296 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1296)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1297 : validRep representative_1297 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1297)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1298 : validRep representative_1298 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1298)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1299 : validRep representative_1299 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1299)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1300 : validRep representative_1300 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1300)=dictionary64.getD 206 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_206]
  decide +kernel
theorem coefficient_1301 : validRep representative_1301 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1301)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_1302 : validRep representative_1302 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1302)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1303 : validRep representative_1303 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1303)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1304 : validRep representative_1304 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1304)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1305 : validRep representative_1305 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1305)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1306 : validRep representative_1306 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1306)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1307 : validRep representative_1307 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1307)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_1308 : validRep representative_1308 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1308)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_1309 : validRep representative_1309 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1309)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1310 : validRep representative_1310 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1310)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_1311 : validRep representative_1311 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1311)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_1312 : validRep representative_1312 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1312)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1313 : validRep representative_1313 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1313)=dictionary64.getD 249 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_249]
  decide +kernel
theorem coefficient_1314 : validRep representative_1314 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1314)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1315 : validRep representative_1315 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1315)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1316 : validRep representative_1316 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1316)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1317 : validRep representative_1317 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1317)=dictionary64.getD 250 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_250]
  decide +kernel
theorem coefficient_1318 : validRep representative_1318 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1318)=dictionary64.getD 249 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_249]
  decide +kernel
theorem coefficient_1319 : validRep representative_1319 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1319)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_1320 : validRep representative_1320 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1320)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1321 : validRep representative_1321 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1321)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1322 : validRep representative_1322 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1322)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1323 : validRep representative_1323 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1323)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1324 : validRep representative_1324 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1324)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1325 : validRep representative_1325 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1325)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1326 : validRep representative_1326 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1326)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1327 : validRep representative_1327 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1327)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1328 : validRep representative_1328 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1328)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1329 : validRep representative_1329 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1329)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1330 : validRep representative_1330 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1330)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1331 : validRep representative_1331 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1331)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1332 : validRep representative_1332 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1332)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1333 : validRep representative_1333 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1333)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_1334 : validRep representative_1334 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1334)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_1335 : validRep representative_1335 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1335)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1336 : validRep representative_1336 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1336)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_1337 : validRep representative_1337 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1337)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1338 : validRep representative_1338 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1338)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1339 : validRep representative_1339 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1339)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1340 : validRep representative_1340 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1340)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1341 : validRep representative_1341 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1341)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1342 : validRep representative_1342 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1342)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1343 : validRep representative_1343 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1343)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_020 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1312 (QuarticIntegerRepresentativeTree.Tree.branch 1296 (QuarticIntegerRepresentativeTree.Tree.branch 1288 (QuarticIntegerRepresentativeTree.Tree.branch 1284 (QuarticIntegerRepresentativeTree.Tree.branch 1282 (QuarticIntegerRepresentativeTree.Tree.branch 1281 (QuarticIntegerRepresentativeTree.Tree.leaf 1280 representative_1280) (QuarticIntegerRepresentativeTree.Tree.leaf 1281 representative_1281)) (QuarticIntegerRepresentativeTree.Tree.branch 1283 (QuarticIntegerRepresentativeTree.Tree.leaf 1282 representative_1282) (QuarticIntegerRepresentativeTree.Tree.leaf 1283 representative_1283))) (QuarticIntegerRepresentativeTree.Tree.branch 1286 (QuarticIntegerRepresentativeTree.Tree.branch 1285 (QuarticIntegerRepresentativeTree.Tree.leaf 1284 representative_1284) (QuarticIntegerRepresentativeTree.Tree.leaf 1285 representative_1285)) (QuarticIntegerRepresentativeTree.Tree.branch 1287 (QuarticIntegerRepresentativeTree.Tree.leaf 1286 representative_1286) (QuarticIntegerRepresentativeTree.Tree.leaf 1287 representative_1287)))) (QuarticIntegerRepresentativeTree.Tree.branch 1292 (QuarticIntegerRepresentativeTree.Tree.branch 1290 (QuarticIntegerRepresentativeTree.Tree.branch 1289 (QuarticIntegerRepresentativeTree.Tree.leaf 1288 representative_1288) (QuarticIntegerRepresentativeTree.Tree.leaf 1289 representative_1289)) (QuarticIntegerRepresentativeTree.Tree.branch 1291 (QuarticIntegerRepresentativeTree.Tree.leaf 1290 representative_1290) (QuarticIntegerRepresentativeTree.Tree.leaf 1291 representative_1291))) (QuarticIntegerRepresentativeTree.Tree.branch 1294 (QuarticIntegerRepresentativeTree.Tree.branch 1293 (QuarticIntegerRepresentativeTree.Tree.leaf 1292 representative_1292) (QuarticIntegerRepresentativeTree.Tree.leaf 1293 representative_1293)) (QuarticIntegerRepresentativeTree.Tree.branch 1295 (QuarticIntegerRepresentativeTree.Tree.leaf 1294 representative_1294) (QuarticIntegerRepresentativeTree.Tree.leaf 1295 representative_1295))))) (QuarticIntegerRepresentativeTree.Tree.branch 1304 (QuarticIntegerRepresentativeTree.Tree.branch 1300 (QuarticIntegerRepresentativeTree.Tree.branch 1298 (QuarticIntegerRepresentativeTree.Tree.branch 1297 (QuarticIntegerRepresentativeTree.Tree.leaf 1296 representative_1296) (QuarticIntegerRepresentativeTree.Tree.leaf 1297 representative_1297)) (QuarticIntegerRepresentativeTree.Tree.branch 1299 (QuarticIntegerRepresentativeTree.Tree.leaf 1298 representative_1298) (QuarticIntegerRepresentativeTree.Tree.leaf 1299 representative_1299))) (QuarticIntegerRepresentativeTree.Tree.branch 1302 (QuarticIntegerRepresentativeTree.Tree.branch 1301 (QuarticIntegerRepresentativeTree.Tree.leaf 1300 representative_1300) (QuarticIntegerRepresentativeTree.Tree.leaf 1301 representative_1301)) (QuarticIntegerRepresentativeTree.Tree.branch 1303 (QuarticIntegerRepresentativeTree.Tree.leaf 1302 representative_1302) (QuarticIntegerRepresentativeTree.Tree.leaf 1303 representative_1303)))) (QuarticIntegerRepresentativeTree.Tree.branch 1308 (QuarticIntegerRepresentativeTree.Tree.branch 1306 (QuarticIntegerRepresentativeTree.Tree.branch 1305 (QuarticIntegerRepresentativeTree.Tree.leaf 1304 representative_1304) (QuarticIntegerRepresentativeTree.Tree.leaf 1305 representative_1305)) (QuarticIntegerRepresentativeTree.Tree.branch 1307 (QuarticIntegerRepresentativeTree.Tree.leaf 1306 representative_1306) (QuarticIntegerRepresentativeTree.Tree.leaf 1307 representative_1307))) (QuarticIntegerRepresentativeTree.Tree.branch 1310 (QuarticIntegerRepresentativeTree.Tree.branch 1309 (QuarticIntegerRepresentativeTree.Tree.leaf 1308 representative_1308) (QuarticIntegerRepresentativeTree.Tree.leaf 1309 representative_1309)) (QuarticIntegerRepresentativeTree.Tree.branch 1311 (QuarticIntegerRepresentativeTree.Tree.leaf 1310 representative_1310) (QuarticIntegerRepresentativeTree.Tree.leaf 1311 representative_1311)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1328 (QuarticIntegerRepresentativeTree.Tree.branch 1320 (QuarticIntegerRepresentativeTree.Tree.branch 1316 (QuarticIntegerRepresentativeTree.Tree.branch 1314 (QuarticIntegerRepresentativeTree.Tree.branch 1313 (QuarticIntegerRepresentativeTree.Tree.leaf 1312 representative_1312) (QuarticIntegerRepresentativeTree.Tree.leaf 1313 representative_1313)) (QuarticIntegerRepresentativeTree.Tree.branch 1315 (QuarticIntegerRepresentativeTree.Tree.leaf 1314 representative_1314) (QuarticIntegerRepresentativeTree.Tree.leaf 1315 representative_1315))) (QuarticIntegerRepresentativeTree.Tree.branch 1318 (QuarticIntegerRepresentativeTree.Tree.branch 1317 (QuarticIntegerRepresentativeTree.Tree.leaf 1316 representative_1316) (QuarticIntegerRepresentativeTree.Tree.leaf 1317 representative_1317)) (QuarticIntegerRepresentativeTree.Tree.branch 1319 (QuarticIntegerRepresentativeTree.Tree.leaf 1318 representative_1318) (QuarticIntegerRepresentativeTree.Tree.leaf 1319 representative_1319)))) (QuarticIntegerRepresentativeTree.Tree.branch 1324 (QuarticIntegerRepresentativeTree.Tree.branch 1322 (QuarticIntegerRepresentativeTree.Tree.branch 1321 (QuarticIntegerRepresentativeTree.Tree.leaf 1320 representative_1320) (QuarticIntegerRepresentativeTree.Tree.leaf 1321 representative_1321)) (QuarticIntegerRepresentativeTree.Tree.branch 1323 (QuarticIntegerRepresentativeTree.Tree.leaf 1322 representative_1322) (QuarticIntegerRepresentativeTree.Tree.leaf 1323 representative_1323))) (QuarticIntegerRepresentativeTree.Tree.branch 1326 (QuarticIntegerRepresentativeTree.Tree.branch 1325 (QuarticIntegerRepresentativeTree.Tree.leaf 1324 representative_1324) (QuarticIntegerRepresentativeTree.Tree.leaf 1325 representative_1325)) (QuarticIntegerRepresentativeTree.Tree.branch 1327 (QuarticIntegerRepresentativeTree.Tree.leaf 1326 representative_1326) (QuarticIntegerRepresentativeTree.Tree.leaf 1327 representative_1327))))) (QuarticIntegerRepresentativeTree.Tree.branch 1336 (QuarticIntegerRepresentativeTree.Tree.branch 1332 (QuarticIntegerRepresentativeTree.Tree.branch 1330 (QuarticIntegerRepresentativeTree.Tree.branch 1329 (QuarticIntegerRepresentativeTree.Tree.leaf 1328 representative_1328) (QuarticIntegerRepresentativeTree.Tree.leaf 1329 representative_1329)) (QuarticIntegerRepresentativeTree.Tree.branch 1331 (QuarticIntegerRepresentativeTree.Tree.leaf 1330 representative_1330) (QuarticIntegerRepresentativeTree.Tree.leaf 1331 representative_1331))) (QuarticIntegerRepresentativeTree.Tree.branch 1334 (QuarticIntegerRepresentativeTree.Tree.branch 1333 (QuarticIntegerRepresentativeTree.Tree.leaf 1332 representative_1332) (QuarticIntegerRepresentativeTree.Tree.leaf 1333 representative_1333)) (QuarticIntegerRepresentativeTree.Tree.branch 1335 (QuarticIntegerRepresentativeTree.Tree.leaf 1334 representative_1334) (QuarticIntegerRepresentativeTree.Tree.leaf 1335 representative_1335)))) (QuarticIntegerRepresentativeTree.Tree.branch 1340 (QuarticIntegerRepresentativeTree.Tree.branch 1338 (QuarticIntegerRepresentativeTree.Tree.branch 1337 (QuarticIntegerRepresentativeTree.Tree.leaf 1336 representative_1336) (QuarticIntegerRepresentativeTree.Tree.leaf 1337 representative_1337)) (QuarticIntegerRepresentativeTree.Tree.branch 1339 (QuarticIntegerRepresentativeTree.Tree.leaf 1338 representative_1338) (QuarticIntegerRepresentativeTree.Tree.leaf 1339 representative_1339))) (QuarticIntegerRepresentativeTree.Tree.branch 1342 (QuarticIntegerRepresentativeTree.Tree.branch 1341 (QuarticIntegerRepresentativeTree.Tree.leaf 1340 representative_1340) (QuarticIntegerRepresentativeTree.Tree.leaf 1341 representative_1341)) (QuarticIntegerRepresentativeTree.Tree.branch 1343 (QuarticIntegerRepresentativeTree.Tree.leaf 1342 representative_1342) (QuarticIntegerRepresentativeTree.Tree.leaf 1343 representative_1343)))))))
theorem accepted_020 : All validRep tree_020 := ⟨⟨⟨⟨⟨⟨coefficient_1280,coefficient_1281⟩,⟨coefficient_1282,coefficient_1283⟩⟩,⟨⟨coefficient_1284,coefficient_1285⟩,⟨coefficient_1286,coefficient_1287⟩⟩⟩,⟨⟨⟨coefficient_1288,coefficient_1289⟩,⟨coefficient_1290,coefficient_1291⟩⟩,⟨⟨coefficient_1292,coefficient_1293⟩,⟨coefficient_1294,coefficient_1295⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1296,coefficient_1297⟩,⟨coefficient_1298,coefficient_1299⟩⟩,⟨⟨coefficient_1300,coefficient_1301⟩,⟨coefficient_1302,coefficient_1303⟩⟩⟩,⟨⟨⟨coefficient_1304,coefficient_1305⟩,⟨coefficient_1306,coefficient_1307⟩⟩,⟨⟨coefficient_1308,coefficient_1309⟩,⟨coefficient_1310,coefficient_1311⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1312,coefficient_1313⟩,⟨coefficient_1314,coefficient_1315⟩⟩,⟨⟨coefficient_1316,coefficient_1317⟩,⟨coefficient_1318,coefficient_1319⟩⟩⟩,⟨⟨⟨coefficient_1320,coefficient_1321⟩,⟨coefficient_1322,coefficient_1323⟩⟩,⟨⟨coefficient_1324,coefficient_1325⟩,⟨coefficient_1326,coefficient_1327⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1328,coefficient_1329⟩,⟨coefficient_1330,coefficient_1331⟩⟩,⟨⟨coefficient_1332,coefficient_1333⟩,⟨coefficient_1334,coefficient_1335⟩⟩⟩,⟨⟨⟨coefficient_1336,coefficient_1337⟩,⟨coefficient_1338,coefficient_1339⟩⟩,⟨⟨coefficient_1340,coefficient_1341⟩,⟨coefficient_1342,coefficient_1343⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

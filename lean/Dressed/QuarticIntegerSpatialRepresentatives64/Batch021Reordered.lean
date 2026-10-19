import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1344 : Rep := ⟨![0,3,20,30],462⟩
def representative_1345 : Rep := ⟨![0,3,20,31],462⟩
def representative_1346 : Rep := ⟨![0,3,20,32],462⟩
def representative_1347 : Rep := ⟨![0,3,20,33],462⟩
def representative_1348 : Rep := ⟨![0,3,20,34],462⟩
def representative_1349 : Rep := ⟨![0,3,20,35],242⟩
def representative_1350 : Rep := ⟨![0,3,20,37],462⟩
def representative_1351 : Rep := ⟨![0,3,20,38],462⟩
def representative_1352 : Rep := ⟨![0,3,20,39],462⟩
def representative_1353 : Rep := ⟨![0,3,20,40],462⟩
def representative_1354 : Rep := ⟨![0,3,20,41],462⟩
def representative_1355 : Rep := ⟨![0,3,20,42],243⟩
def representative_1356 : Rep := ⟨![0,3,20,43],237⟩
def representative_1357 : Rep := ⟨![0,3,20,45],462⟩
def representative_1358 : Rep := ⟨![0,3,20,46],462⟩
def representative_1359 : Rep := ⟨![0,3,20,47],462⟩
def representative_1360 : Rep := ⟨![0,3,20,52],234⟩
def representative_1361 : Rep := ⟨![0,3,20,53],244⟩
def representative_1362 : Rep := ⟨![0,3,20,54],462⟩
def representative_1363 : Rep := ⟨![0,3,20,55],462⟩
def representative_1364 : Rep := ⟨![0,3,21,24],462⟩
def representative_1365 : Rep := ⟨![0,3,21,25],462⟩
def representative_1366 : Rep := ⟨![0,3,21,26],462⟩
def representative_1367 : Rep := ⟨![0,3,21,27],242⟩
def representative_1368 : Rep := ⟨![0,3,21,28],462⟩
def representative_1369 : Rep := ⟨![0,3,21,30],462⟩
def representative_1370 : Rep := ⟨![0,3,21,31],462⟩
def representative_1371 : Rep := ⟨![0,3,21,32],462⟩
def representative_1372 : Rep := ⟨![0,3,21,33],462⟩
def representative_1373 : Rep := ⟨![0,3,21,34],462⟩
def representative_1374 : Rep := ⟨![0,3,21,35],462⟩
def representative_1375 : Rep := ⟨![0,3,21,36],462⟩
def representative_1376 : Rep := ⟨![0,3,21,38],462⟩
def representative_1377 : Rep := ⟨![0,3,21,39],462⟩
def representative_1378 : Rep := ⟨![0,3,21,40],462⟩
def representative_1379 : Rep := ⟨![0,3,21,41],462⟩
def representative_1380 : Rep := ⟨![0,3,21,42],462⟩
def representative_1381 : Rep := ⟨![0,3,21,43],242⟩
def representative_1382 : Rep := ⟨![0,3,21,44],462⟩
def representative_1383 : Rep := ⟨![0,3,21,45],462⟩
def representative_1384 : Rep := ⟨![0,3,21,46],462⟩
def representative_1385 : Rep := ⟨![0,3,21,47],462⟩
def representative_1386 : Rep := ⟨![0,3,21,53],462⟩
def representative_1387 : Rep := ⟨![0,3,21,54],462⟩
def representative_1388 : Rep := ⟨![0,3,24,27],462⟩
def representative_1389 : Rep := ⟨![0,3,24,28],462⟩
def representative_1390 : Rep := ⟨![0,3,24,29],462⟩
def representative_1391 : Rep := ⟨![0,3,24,33],462⟩
def representative_1392 : Rep := ⟨![0,3,24,34],462⟩
def representative_1393 : Rep := ⟨![0,3,24,35],462⟩
def representative_1394 : Rep := ⟨![0,3,24,36],462⟩
def representative_1395 : Rep := ⟨![0,3,24,37],462⟩
def representative_1396 : Rep := ⟨![0,3,24,38],462⟩
def representative_1397 : Rep := ⟨![0,3,24,39],462⟩
def representative_1398 : Rep := ⟨![0,3,24,41],241⟩
def representative_1399 : Rep := ⟨![0,3,24,42],462⟩
def representative_1400 : Rep := ⟨![0,3,24,43],462⟩
def representative_1401 : Rep := ⟨![0,3,24,44],462⟩
def representative_1402 : Rep := ⟨![0,3,24,45],462⟩
def representative_1403 : Rep := ⟨![0,3,24,46],462⟩
def representative_1404 : Rep := ⟨![0,3,24,47],241⟩
def representative_1405 : Rep := ⟨![0,3,25,28],462⟩
def representative_1406 : Rep := ⟨![0,3,25,29],462⟩
def representative_1407 : Rep := ⟨![0,3,25,30],462⟩
theorem coefficient_1344 : validRep representative_1344 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1344)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1345 : validRep representative_1345 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1345)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1346 : validRep representative_1346 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1346)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1347 : validRep representative_1347 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1347)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1348 : validRep representative_1348 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1348)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1349 : validRep representative_1349 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1349)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1350 : validRep representative_1350 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1350)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1351 : validRep representative_1351 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1351)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1352 : validRep representative_1352 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1352)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1353 : validRep representative_1353 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1353)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1354 : validRep representative_1354 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1354)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1355 : validRep representative_1355 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1355)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_1356 : validRep representative_1356 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1356)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_1357 : validRep representative_1357 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1357)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1358 : validRep representative_1358 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1358)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1359 : validRep representative_1359 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1359)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1360 : validRep representative_1360 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1360)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1361 : validRep representative_1361 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1361)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_1362 : validRep representative_1362 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1362)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1363 : validRep representative_1363 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1363)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1364 : validRep representative_1364 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1364)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1365 : validRep representative_1365 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1365)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1366 : validRep representative_1366 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1366)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1367 : validRep representative_1367 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1367)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1368 : validRep representative_1368 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1368)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1369 : validRep representative_1369 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1369)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1370 : validRep representative_1370 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1370)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1371 : validRep representative_1371 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1371)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1372 : validRep representative_1372 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1372)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1373 : validRep representative_1373 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1373)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1374 : validRep representative_1374 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1374)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1375 : validRep representative_1375 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1375)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1376 : validRep representative_1376 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1376)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1377 : validRep representative_1377 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1377)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1378 : validRep representative_1378 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1378)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1379 : validRep representative_1379 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1379)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1380 : validRep representative_1380 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1380)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1381 : validRep representative_1381 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1381)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_1382 : validRep representative_1382 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1382)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1383 : validRep representative_1383 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1383)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1384 : validRep representative_1384 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1384)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1385 : validRep representative_1385 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1385)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1386 : validRep representative_1386 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1386)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1387 : validRep representative_1387 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1387)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1388 : validRep representative_1388 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1388)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1389 : validRep representative_1389 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1389)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1390 : validRep representative_1390 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1390)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1391 : validRep representative_1391 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1391)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1392 : validRep representative_1392 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1392)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1393 : validRep representative_1393 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1393)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1394 : validRep representative_1394 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1394)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1395 : validRep representative_1395 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1395)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1396 : validRep representative_1396 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1396)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1397 : validRep representative_1397 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1397)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1398 : validRep representative_1398 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1398)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1399 : validRep representative_1399 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1399)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1400 : validRep representative_1400 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1400)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1401 : validRep representative_1401 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1401)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1402 : validRep representative_1402 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1402)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1403 : validRep representative_1403 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1403)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1404 : validRep representative_1404 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1404)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_1405 : validRep representative_1405 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1405)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1406 : validRep representative_1406 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1406)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1407 : validRep representative_1407 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1407)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_021 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1376 (QuarticIntegerRepresentativeTree.Tree.branch 1360 (QuarticIntegerRepresentativeTree.Tree.branch 1352 (QuarticIntegerRepresentativeTree.Tree.branch 1348 (QuarticIntegerRepresentativeTree.Tree.branch 1346 (QuarticIntegerRepresentativeTree.Tree.branch 1345 (QuarticIntegerRepresentativeTree.Tree.leaf 1344 representative_1344) (QuarticIntegerRepresentativeTree.Tree.leaf 1345 representative_1345)) (QuarticIntegerRepresentativeTree.Tree.branch 1347 (QuarticIntegerRepresentativeTree.Tree.leaf 1346 representative_1346) (QuarticIntegerRepresentativeTree.Tree.leaf 1347 representative_1347))) (QuarticIntegerRepresentativeTree.Tree.branch 1350 (QuarticIntegerRepresentativeTree.Tree.branch 1349 (QuarticIntegerRepresentativeTree.Tree.leaf 1348 representative_1348) (QuarticIntegerRepresentativeTree.Tree.leaf 1349 representative_1349)) (QuarticIntegerRepresentativeTree.Tree.branch 1351 (QuarticIntegerRepresentativeTree.Tree.leaf 1350 representative_1350) (QuarticIntegerRepresentativeTree.Tree.leaf 1351 representative_1351)))) (QuarticIntegerRepresentativeTree.Tree.branch 1356 (QuarticIntegerRepresentativeTree.Tree.branch 1354 (QuarticIntegerRepresentativeTree.Tree.branch 1353 (QuarticIntegerRepresentativeTree.Tree.leaf 1352 representative_1352) (QuarticIntegerRepresentativeTree.Tree.leaf 1353 representative_1353)) (QuarticIntegerRepresentativeTree.Tree.branch 1355 (QuarticIntegerRepresentativeTree.Tree.leaf 1354 representative_1354) (QuarticIntegerRepresentativeTree.Tree.leaf 1355 representative_1355))) (QuarticIntegerRepresentativeTree.Tree.branch 1358 (QuarticIntegerRepresentativeTree.Tree.branch 1357 (QuarticIntegerRepresentativeTree.Tree.leaf 1356 representative_1356) (QuarticIntegerRepresentativeTree.Tree.leaf 1357 representative_1357)) (QuarticIntegerRepresentativeTree.Tree.branch 1359 (QuarticIntegerRepresentativeTree.Tree.leaf 1358 representative_1358) (QuarticIntegerRepresentativeTree.Tree.leaf 1359 representative_1359))))) (QuarticIntegerRepresentativeTree.Tree.branch 1368 (QuarticIntegerRepresentativeTree.Tree.branch 1364 (QuarticIntegerRepresentativeTree.Tree.branch 1362 (QuarticIntegerRepresentativeTree.Tree.branch 1361 (QuarticIntegerRepresentativeTree.Tree.leaf 1360 representative_1360) (QuarticIntegerRepresentativeTree.Tree.leaf 1361 representative_1361)) (QuarticIntegerRepresentativeTree.Tree.branch 1363 (QuarticIntegerRepresentativeTree.Tree.leaf 1362 representative_1362) (QuarticIntegerRepresentativeTree.Tree.leaf 1363 representative_1363))) (QuarticIntegerRepresentativeTree.Tree.branch 1366 (QuarticIntegerRepresentativeTree.Tree.branch 1365 (QuarticIntegerRepresentativeTree.Tree.leaf 1364 representative_1364) (QuarticIntegerRepresentativeTree.Tree.leaf 1365 representative_1365)) (QuarticIntegerRepresentativeTree.Tree.branch 1367 (QuarticIntegerRepresentativeTree.Tree.leaf 1366 representative_1366) (QuarticIntegerRepresentativeTree.Tree.leaf 1367 representative_1367)))) (QuarticIntegerRepresentativeTree.Tree.branch 1372 (QuarticIntegerRepresentativeTree.Tree.branch 1370 (QuarticIntegerRepresentativeTree.Tree.branch 1369 (QuarticIntegerRepresentativeTree.Tree.leaf 1368 representative_1368) (QuarticIntegerRepresentativeTree.Tree.leaf 1369 representative_1369)) (QuarticIntegerRepresentativeTree.Tree.branch 1371 (QuarticIntegerRepresentativeTree.Tree.leaf 1370 representative_1370) (QuarticIntegerRepresentativeTree.Tree.leaf 1371 representative_1371))) (QuarticIntegerRepresentativeTree.Tree.branch 1374 (QuarticIntegerRepresentativeTree.Tree.branch 1373 (QuarticIntegerRepresentativeTree.Tree.leaf 1372 representative_1372) (QuarticIntegerRepresentativeTree.Tree.leaf 1373 representative_1373)) (QuarticIntegerRepresentativeTree.Tree.branch 1375 (QuarticIntegerRepresentativeTree.Tree.leaf 1374 representative_1374) (QuarticIntegerRepresentativeTree.Tree.leaf 1375 representative_1375)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1392 (QuarticIntegerRepresentativeTree.Tree.branch 1384 (QuarticIntegerRepresentativeTree.Tree.branch 1380 (QuarticIntegerRepresentativeTree.Tree.branch 1378 (QuarticIntegerRepresentativeTree.Tree.branch 1377 (QuarticIntegerRepresentativeTree.Tree.leaf 1376 representative_1376) (QuarticIntegerRepresentativeTree.Tree.leaf 1377 representative_1377)) (QuarticIntegerRepresentativeTree.Tree.branch 1379 (QuarticIntegerRepresentativeTree.Tree.leaf 1378 representative_1378) (QuarticIntegerRepresentativeTree.Tree.leaf 1379 representative_1379))) (QuarticIntegerRepresentativeTree.Tree.branch 1382 (QuarticIntegerRepresentativeTree.Tree.branch 1381 (QuarticIntegerRepresentativeTree.Tree.leaf 1380 representative_1380) (QuarticIntegerRepresentativeTree.Tree.leaf 1381 representative_1381)) (QuarticIntegerRepresentativeTree.Tree.branch 1383 (QuarticIntegerRepresentativeTree.Tree.leaf 1382 representative_1382) (QuarticIntegerRepresentativeTree.Tree.leaf 1383 representative_1383)))) (QuarticIntegerRepresentativeTree.Tree.branch 1388 (QuarticIntegerRepresentativeTree.Tree.branch 1386 (QuarticIntegerRepresentativeTree.Tree.branch 1385 (QuarticIntegerRepresentativeTree.Tree.leaf 1384 representative_1384) (QuarticIntegerRepresentativeTree.Tree.leaf 1385 representative_1385)) (QuarticIntegerRepresentativeTree.Tree.branch 1387 (QuarticIntegerRepresentativeTree.Tree.leaf 1386 representative_1386) (QuarticIntegerRepresentativeTree.Tree.leaf 1387 representative_1387))) (QuarticIntegerRepresentativeTree.Tree.branch 1390 (QuarticIntegerRepresentativeTree.Tree.branch 1389 (QuarticIntegerRepresentativeTree.Tree.leaf 1388 representative_1388) (QuarticIntegerRepresentativeTree.Tree.leaf 1389 representative_1389)) (QuarticIntegerRepresentativeTree.Tree.branch 1391 (QuarticIntegerRepresentativeTree.Tree.leaf 1390 representative_1390) (QuarticIntegerRepresentativeTree.Tree.leaf 1391 representative_1391))))) (QuarticIntegerRepresentativeTree.Tree.branch 1400 (QuarticIntegerRepresentativeTree.Tree.branch 1396 (QuarticIntegerRepresentativeTree.Tree.branch 1394 (QuarticIntegerRepresentativeTree.Tree.branch 1393 (QuarticIntegerRepresentativeTree.Tree.leaf 1392 representative_1392) (QuarticIntegerRepresentativeTree.Tree.leaf 1393 representative_1393)) (QuarticIntegerRepresentativeTree.Tree.branch 1395 (QuarticIntegerRepresentativeTree.Tree.leaf 1394 representative_1394) (QuarticIntegerRepresentativeTree.Tree.leaf 1395 representative_1395))) (QuarticIntegerRepresentativeTree.Tree.branch 1398 (QuarticIntegerRepresentativeTree.Tree.branch 1397 (QuarticIntegerRepresentativeTree.Tree.leaf 1396 representative_1396) (QuarticIntegerRepresentativeTree.Tree.leaf 1397 representative_1397)) (QuarticIntegerRepresentativeTree.Tree.branch 1399 (QuarticIntegerRepresentativeTree.Tree.leaf 1398 representative_1398) (QuarticIntegerRepresentativeTree.Tree.leaf 1399 representative_1399)))) (QuarticIntegerRepresentativeTree.Tree.branch 1404 (QuarticIntegerRepresentativeTree.Tree.branch 1402 (QuarticIntegerRepresentativeTree.Tree.branch 1401 (QuarticIntegerRepresentativeTree.Tree.leaf 1400 representative_1400) (QuarticIntegerRepresentativeTree.Tree.leaf 1401 representative_1401)) (QuarticIntegerRepresentativeTree.Tree.branch 1403 (QuarticIntegerRepresentativeTree.Tree.leaf 1402 representative_1402) (QuarticIntegerRepresentativeTree.Tree.leaf 1403 representative_1403))) (QuarticIntegerRepresentativeTree.Tree.branch 1406 (QuarticIntegerRepresentativeTree.Tree.branch 1405 (QuarticIntegerRepresentativeTree.Tree.leaf 1404 representative_1404) (QuarticIntegerRepresentativeTree.Tree.leaf 1405 representative_1405)) (QuarticIntegerRepresentativeTree.Tree.branch 1407 (QuarticIntegerRepresentativeTree.Tree.leaf 1406 representative_1406) (QuarticIntegerRepresentativeTree.Tree.leaf 1407 representative_1407)))))))
theorem accepted_021 : All validRep tree_021 := ⟨⟨⟨⟨⟨⟨coefficient_1344,coefficient_1345⟩,⟨coefficient_1346,coefficient_1347⟩⟩,⟨⟨coefficient_1348,coefficient_1349⟩,⟨coefficient_1350,coefficient_1351⟩⟩⟩,⟨⟨⟨coefficient_1352,coefficient_1353⟩,⟨coefficient_1354,coefficient_1355⟩⟩,⟨⟨coefficient_1356,coefficient_1357⟩,⟨coefficient_1358,coefficient_1359⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1360,coefficient_1361⟩,⟨coefficient_1362,coefficient_1363⟩⟩,⟨⟨coefficient_1364,coefficient_1365⟩,⟨coefficient_1366,coefficient_1367⟩⟩⟩,⟨⟨⟨coefficient_1368,coefficient_1369⟩,⟨coefficient_1370,coefficient_1371⟩⟩,⟨⟨coefficient_1372,coefficient_1373⟩,⟨coefficient_1374,coefficient_1375⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1376,coefficient_1377⟩,⟨coefficient_1378,coefficient_1379⟩⟩,⟨⟨coefficient_1380,coefficient_1381⟩,⟨coefficient_1382,coefficient_1383⟩⟩⟩,⟨⟨⟨coefficient_1384,coefficient_1385⟩,⟨coefficient_1386,coefficient_1387⟩⟩,⟨⟨coefficient_1388,coefficient_1389⟩,⟨coefficient_1390,coefficient_1391⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1392,coefficient_1393⟩,⟨coefficient_1394,coefficient_1395⟩⟩,⟨⟨coefficient_1396,coefficient_1397⟩,⟨coefficient_1398,coefficient_1399⟩⟩⟩,⟨⟨⟨coefficient_1400,coefficient_1401⟩,⟨coefficient_1402,coefficient_1403⟩⟩,⟨⟨coefficient_1404,coefficient_1405⟩,⟨coefficient_1406,coefficient_1407⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

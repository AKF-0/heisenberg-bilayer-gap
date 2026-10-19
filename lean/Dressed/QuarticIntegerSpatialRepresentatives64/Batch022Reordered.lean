import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1408 : Rep := ⟨![0,3,25,32],462⟩
def representative_1409 : Rep := ⟨![0,3,25,34],462⟩
def representative_1410 : Rep := ⟨![0,3,25,35],462⟩
def representative_1411 : Rep := ⟨![0,3,25,36],462⟩
def representative_1412 : Rep := ⟨![0,3,25,37],462⟩
def representative_1413 : Rep := ⟨![0,3,25,38],462⟩
def representative_1414 : Rep := ⟨![0,3,25,39],462⟩
def representative_1415 : Rep := ⟨![0,3,25,42],462⟩
def representative_1416 : Rep := ⟨![0,3,25,44],462⟩
def representative_1417 : Rep := ⟨![0,3,25,45],462⟩
def representative_1418 : Rep := ⟨![0,3,25,46],462⟩
def representative_1419 : Rep := ⟨![0,3,25,47],462⟩
def representative_1420 : Rep := ⟨![0,3,28,31],462⟩
def representative_1421 : Rep := ⟨![0,3,28,32],462⟩
def representative_1422 : Rep := ⟨![0,3,28,33],462⟩
def representative_1423 : Rep := ⟨![0,3,28,34],462⟩
def representative_1424 : Rep := ⟨![0,3,28,35],462⟩
def representative_1425 : Rep := ⟨![0,3,28,37],462⟩
def representative_1426 : Rep := ⟨![0,3,28,38],462⟩
def representative_1427 : Rep := ⟨![0,3,28,39],462⟩
def representative_1428 : Rep := ⟨![0,3,28,45],462⟩
def representative_1429 : Rep := ⟨![0,3,28,46],462⟩
def representative_1430 : Rep := ⟨![0,3,28,47],462⟩
def representative_1431 : Rep := ⟨![0,3,29,32],462⟩
def representative_1432 : Rep := ⟨![0,3,29,33],462⟩
def representative_1433 : Rep := ⟨![0,3,29,34],462⟩
def representative_1434 : Rep := ⟨![0,3,29,35],462⟩
def representative_1435 : Rep := ⟨![0,3,29,36],462⟩
def representative_1436 : Rep := ⟨![0,3,29,38],462⟩
def representative_1437 : Rep := ⟨![0,3,29,39],462⟩
def representative_1438 : Rep := ⟨![0,3,29,46],462⟩
def representative_1439 : Rep := ⟨![0,3,32,35],462⟩
def representative_1440 : Rep := ⟨![0,3,32,36],462⟩
def representative_1441 : Rep := ⟨![0,3,32,37],462⟩
def representative_1442 : Rep := ⟨![0,3,33,36],462⟩
def representative_1443 : Rep := ⟨![0,3,33,37],462⟩
def representative_1444 : Rep := ⟨![0,3,33,38],462⟩
def representative_1445 : Rep := ⟨![0,3,36,39],462⟩
def representative_1446 : Rep := ⟨![0,4,1,5],9⟩
def representative_1447 : Rep := ⟨![0,4,1,8],429⟩
def representative_1448 : Rep := ⟨![0,4,1,10],366⟩
def representative_1449 : Rep := ⟨![0,4,1,11],151⟩
def representative_1450 : Rep := ⟨![0,4,1,12],462⟩
def representative_1451 : Rep := ⟨![0,4,1,13],462⟩
def representative_1452 : Rep := ⟨![0,4,1,14],10⟩
def representative_1453 : Rep := ⟨![0,4,1,15],90⟩
def representative_1454 : Rep := ⟨![0,4,1,16],94⟩
def representative_1455 : Rep := ⟨![0,4,1,18],154⟩
def representative_1456 : Rep := ⟨![0,4,1,19],462⟩
def representative_1457 : Rep := ⟨![0,4,1,20],462⟩
def representative_1458 : Rep := ⟨![0,4,1,21],462⟩
def representative_1459 : Rep := ⟨![0,4,1,22],462⟩
def representative_1460 : Rep := ⟨![0,4,1,23],10⟩
def representative_1461 : Rep := ⟨![0,4,1,24],8⟩
def representative_1462 : Rep := ⟨![0,4,1,26],462⟩
def representative_1463 : Rep := ⟨![0,4,1,27],462⟩
def representative_1464 : Rep := ⟨![0,4,1,28],462⟩
def representative_1465 : Rep := ⟨![0,4,1,29],462⟩
def representative_1466 : Rep := ⟨![0,4,1,30],462⟩
def representative_1467 : Rep := ⟨![0,4,1,31],462⟩
def representative_1468 : Rep := ⟨![0,4,1,32],462⟩
def representative_1469 : Rep := ⟨![0,4,1,33],462⟩
def representative_1470 : Rep := ⟨![0,4,1,34],462⟩
def representative_1471 : Rep := ⟨![0,4,1,35],462⟩
theorem coefficient_1408 : validRep representative_1408 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1408)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1409 : validRep representative_1409 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1409)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1410 : validRep representative_1410 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1410)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1411 : validRep representative_1411 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1411)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1412 : validRep representative_1412 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1412)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1413 : validRep representative_1413 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1413)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1414 : validRep representative_1414 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1414)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1415 : validRep representative_1415 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1415)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1416 : validRep representative_1416 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1416)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1417 : validRep representative_1417 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1417)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1418 : validRep representative_1418 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1418)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1419 : validRep representative_1419 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1419)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1420 : validRep representative_1420 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1420)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1421 : validRep representative_1421 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1421)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1422 : validRep representative_1422 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1422)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1423 : validRep representative_1423 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1423)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1424 : validRep representative_1424 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1424)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1425 : validRep representative_1425 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1425)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1426 : validRep representative_1426 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1426)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1427 : validRep representative_1427 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1427)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1428 : validRep representative_1428 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1428)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1429 : validRep representative_1429 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1429)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1430 : validRep representative_1430 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1430)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1431 : validRep representative_1431 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1431)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1432 : validRep representative_1432 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1432)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1433 : validRep representative_1433 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1433)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1434 : validRep representative_1434 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1434)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1435 : validRep representative_1435 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1435)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1436 : validRep representative_1436 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1436)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1437 : validRep representative_1437 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1437)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1438 : validRep representative_1438 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1438)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1439 : validRep representative_1439 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1439)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1440 : validRep representative_1440 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1440)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1441 : validRep representative_1441 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1441)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1442 : validRep representative_1442 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1442)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1443 : validRep representative_1443 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1443)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1444 : validRep representative_1444 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1444)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1445 : validRep representative_1445 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1445)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1446 : validRep representative_1446 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1446)=dictionary64.getD 9 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_1447 : validRep representative_1447 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1447)=dictionary64.getD 429 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_429]
  decide +kernel
theorem coefficient_1448 : validRep representative_1448 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1448)=dictionary64.getD 366 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_366]
  decide +kernel
theorem coefficient_1449 : validRep representative_1449 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1449)=dictionary64.getD 151 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_151]
  decide +kernel
theorem coefficient_1450 : validRep representative_1450 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1450)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1451 : validRep representative_1451 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1451)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1452 : validRep representative_1452 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1452)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_1453 : validRep representative_1453 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1453)=dictionary64.getD 90 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_90]
  decide +kernel
theorem coefficient_1454 : validRep representative_1454 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1454)=dictionary64.getD 94 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_94]
  decide +kernel
theorem coefficient_1455 : validRep representative_1455 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1455)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_1456 : validRep representative_1456 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1456)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1457 : validRep representative_1457 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1457)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1458 : validRep representative_1458 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1458)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1459 : validRep representative_1459 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1459)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1460 : validRep representative_1460 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1460)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_1461 : validRep representative_1461 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1461)=dictionary64.getD 8 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_8]
  decide +kernel
theorem coefficient_1462 : validRep representative_1462 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1462)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1463 : validRep representative_1463 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1463)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1464 : validRep representative_1464 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1464)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1465 : validRep representative_1465 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1465)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1466 : validRep representative_1466 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1466)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1467 : validRep representative_1467 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1467)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1468 : validRep representative_1468 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1468)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1469 : validRep representative_1469 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1469)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1470 : validRep representative_1470 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1470)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1471 : validRep representative_1471 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1471)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_022 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1440 (QuarticIntegerRepresentativeTree.Tree.branch 1424 (QuarticIntegerRepresentativeTree.Tree.branch 1416 (QuarticIntegerRepresentativeTree.Tree.branch 1412 (QuarticIntegerRepresentativeTree.Tree.branch 1410 (QuarticIntegerRepresentativeTree.Tree.branch 1409 (QuarticIntegerRepresentativeTree.Tree.leaf 1408 representative_1408) (QuarticIntegerRepresentativeTree.Tree.leaf 1409 representative_1409)) (QuarticIntegerRepresentativeTree.Tree.branch 1411 (QuarticIntegerRepresentativeTree.Tree.leaf 1410 representative_1410) (QuarticIntegerRepresentativeTree.Tree.leaf 1411 representative_1411))) (QuarticIntegerRepresentativeTree.Tree.branch 1414 (QuarticIntegerRepresentativeTree.Tree.branch 1413 (QuarticIntegerRepresentativeTree.Tree.leaf 1412 representative_1412) (QuarticIntegerRepresentativeTree.Tree.leaf 1413 representative_1413)) (QuarticIntegerRepresentativeTree.Tree.branch 1415 (QuarticIntegerRepresentativeTree.Tree.leaf 1414 representative_1414) (QuarticIntegerRepresentativeTree.Tree.leaf 1415 representative_1415)))) (QuarticIntegerRepresentativeTree.Tree.branch 1420 (QuarticIntegerRepresentativeTree.Tree.branch 1418 (QuarticIntegerRepresentativeTree.Tree.branch 1417 (QuarticIntegerRepresentativeTree.Tree.leaf 1416 representative_1416) (QuarticIntegerRepresentativeTree.Tree.leaf 1417 representative_1417)) (QuarticIntegerRepresentativeTree.Tree.branch 1419 (QuarticIntegerRepresentativeTree.Tree.leaf 1418 representative_1418) (QuarticIntegerRepresentativeTree.Tree.leaf 1419 representative_1419))) (QuarticIntegerRepresentativeTree.Tree.branch 1422 (QuarticIntegerRepresentativeTree.Tree.branch 1421 (QuarticIntegerRepresentativeTree.Tree.leaf 1420 representative_1420) (QuarticIntegerRepresentativeTree.Tree.leaf 1421 representative_1421)) (QuarticIntegerRepresentativeTree.Tree.branch 1423 (QuarticIntegerRepresentativeTree.Tree.leaf 1422 representative_1422) (QuarticIntegerRepresentativeTree.Tree.leaf 1423 representative_1423))))) (QuarticIntegerRepresentativeTree.Tree.branch 1432 (QuarticIntegerRepresentativeTree.Tree.branch 1428 (QuarticIntegerRepresentativeTree.Tree.branch 1426 (QuarticIntegerRepresentativeTree.Tree.branch 1425 (QuarticIntegerRepresentativeTree.Tree.leaf 1424 representative_1424) (QuarticIntegerRepresentativeTree.Tree.leaf 1425 representative_1425)) (QuarticIntegerRepresentativeTree.Tree.branch 1427 (QuarticIntegerRepresentativeTree.Tree.leaf 1426 representative_1426) (QuarticIntegerRepresentativeTree.Tree.leaf 1427 representative_1427))) (QuarticIntegerRepresentativeTree.Tree.branch 1430 (QuarticIntegerRepresentativeTree.Tree.branch 1429 (QuarticIntegerRepresentativeTree.Tree.leaf 1428 representative_1428) (QuarticIntegerRepresentativeTree.Tree.leaf 1429 representative_1429)) (QuarticIntegerRepresentativeTree.Tree.branch 1431 (QuarticIntegerRepresentativeTree.Tree.leaf 1430 representative_1430) (QuarticIntegerRepresentativeTree.Tree.leaf 1431 representative_1431)))) (QuarticIntegerRepresentativeTree.Tree.branch 1436 (QuarticIntegerRepresentativeTree.Tree.branch 1434 (QuarticIntegerRepresentativeTree.Tree.branch 1433 (QuarticIntegerRepresentativeTree.Tree.leaf 1432 representative_1432) (QuarticIntegerRepresentativeTree.Tree.leaf 1433 representative_1433)) (QuarticIntegerRepresentativeTree.Tree.branch 1435 (QuarticIntegerRepresentativeTree.Tree.leaf 1434 representative_1434) (QuarticIntegerRepresentativeTree.Tree.leaf 1435 representative_1435))) (QuarticIntegerRepresentativeTree.Tree.branch 1438 (QuarticIntegerRepresentativeTree.Tree.branch 1437 (QuarticIntegerRepresentativeTree.Tree.leaf 1436 representative_1436) (QuarticIntegerRepresentativeTree.Tree.leaf 1437 representative_1437)) (QuarticIntegerRepresentativeTree.Tree.branch 1439 (QuarticIntegerRepresentativeTree.Tree.leaf 1438 representative_1438) (QuarticIntegerRepresentativeTree.Tree.leaf 1439 representative_1439)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1456 (QuarticIntegerRepresentativeTree.Tree.branch 1448 (QuarticIntegerRepresentativeTree.Tree.branch 1444 (QuarticIntegerRepresentativeTree.Tree.branch 1442 (QuarticIntegerRepresentativeTree.Tree.branch 1441 (QuarticIntegerRepresentativeTree.Tree.leaf 1440 representative_1440) (QuarticIntegerRepresentativeTree.Tree.leaf 1441 representative_1441)) (QuarticIntegerRepresentativeTree.Tree.branch 1443 (QuarticIntegerRepresentativeTree.Tree.leaf 1442 representative_1442) (QuarticIntegerRepresentativeTree.Tree.leaf 1443 representative_1443))) (QuarticIntegerRepresentativeTree.Tree.branch 1446 (QuarticIntegerRepresentativeTree.Tree.branch 1445 (QuarticIntegerRepresentativeTree.Tree.leaf 1444 representative_1444) (QuarticIntegerRepresentativeTree.Tree.leaf 1445 representative_1445)) (QuarticIntegerRepresentativeTree.Tree.branch 1447 (QuarticIntegerRepresentativeTree.Tree.leaf 1446 representative_1446) (QuarticIntegerRepresentativeTree.Tree.leaf 1447 representative_1447)))) (QuarticIntegerRepresentativeTree.Tree.branch 1452 (QuarticIntegerRepresentativeTree.Tree.branch 1450 (QuarticIntegerRepresentativeTree.Tree.branch 1449 (QuarticIntegerRepresentativeTree.Tree.leaf 1448 representative_1448) (QuarticIntegerRepresentativeTree.Tree.leaf 1449 representative_1449)) (QuarticIntegerRepresentativeTree.Tree.branch 1451 (QuarticIntegerRepresentativeTree.Tree.leaf 1450 representative_1450) (QuarticIntegerRepresentativeTree.Tree.leaf 1451 representative_1451))) (QuarticIntegerRepresentativeTree.Tree.branch 1454 (QuarticIntegerRepresentativeTree.Tree.branch 1453 (QuarticIntegerRepresentativeTree.Tree.leaf 1452 representative_1452) (QuarticIntegerRepresentativeTree.Tree.leaf 1453 representative_1453)) (QuarticIntegerRepresentativeTree.Tree.branch 1455 (QuarticIntegerRepresentativeTree.Tree.leaf 1454 representative_1454) (QuarticIntegerRepresentativeTree.Tree.leaf 1455 representative_1455))))) (QuarticIntegerRepresentativeTree.Tree.branch 1464 (QuarticIntegerRepresentativeTree.Tree.branch 1460 (QuarticIntegerRepresentativeTree.Tree.branch 1458 (QuarticIntegerRepresentativeTree.Tree.branch 1457 (QuarticIntegerRepresentativeTree.Tree.leaf 1456 representative_1456) (QuarticIntegerRepresentativeTree.Tree.leaf 1457 representative_1457)) (QuarticIntegerRepresentativeTree.Tree.branch 1459 (QuarticIntegerRepresentativeTree.Tree.leaf 1458 representative_1458) (QuarticIntegerRepresentativeTree.Tree.leaf 1459 representative_1459))) (QuarticIntegerRepresentativeTree.Tree.branch 1462 (QuarticIntegerRepresentativeTree.Tree.branch 1461 (QuarticIntegerRepresentativeTree.Tree.leaf 1460 representative_1460) (QuarticIntegerRepresentativeTree.Tree.leaf 1461 representative_1461)) (QuarticIntegerRepresentativeTree.Tree.branch 1463 (QuarticIntegerRepresentativeTree.Tree.leaf 1462 representative_1462) (QuarticIntegerRepresentativeTree.Tree.leaf 1463 representative_1463)))) (QuarticIntegerRepresentativeTree.Tree.branch 1468 (QuarticIntegerRepresentativeTree.Tree.branch 1466 (QuarticIntegerRepresentativeTree.Tree.branch 1465 (QuarticIntegerRepresentativeTree.Tree.leaf 1464 representative_1464) (QuarticIntegerRepresentativeTree.Tree.leaf 1465 representative_1465)) (QuarticIntegerRepresentativeTree.Tree.branch 1467 (QuarticIntegerRepresentativeTree.Tree.leaf 1466 representative_1466) (QuarticIntegerRepresentativeTree.Tree.leaf 1467 representative_1467))) (QuarticIntegerRepresentativeTree.Tree.branch 1470 (QuarticIntegerRepresentativeTree.Tree.branch 1469 (QuarticIntegerRepresentativeTree.Tree.leaf 1468 representative_1468) (QuarticIntegerRepresentativeTree.Tree.leaf 1469 representative_1469)) (QuarticIntegerRepresentativeTree.Tree.branch 1471 (QuarticIntegerRepresentativeTree.Tree.leaf 1470 representative_1470) (QuarticIntegerRepresentativeTree.Tree.leaf 1471 representative_1471)))))))
theorem accepted_022 : All validRep tree_022 := ⟨⟨⟨⟨⟨⟨coefficient_1408,coefficient_1409⟩,⟨coefficient_1410,coefficient_1411⟩⟩,⟨⟨coefficient_1412,coefficient_1413⟩,⟨coefficient_1414,coefficient_1415⟩⟩⟩,⟨⟨⟨coefficient_1416,coefficient_1417⟩,⟨coefficient_1418,coefficient_1419⟩⟩,⟨⟨coefficient_1420,coefficient_1421⟩,⟨coefficient_1422,coefficient_1423⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1424,coefficient_1425⟩,⟨coefficient_1426,coefficient_1427⟩⟩,⟨⟨coefficient_1428,coefficient_1429⟩,⟨coefficient_1430,coefficient_1431⟩⟩⟩,⟨⟨⟨coefficient_1432,coefficient_1433⟩,⟨coefficient_1434,coefficient_1435⟩⟩,⟨⟨coefficient_1436,coefficient_1437⟩,⟨coefficient_1438,coefficient_1439⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1440,coefficient_1441⟩,⟨coefficient_1442,coefficient_1443⟩⟩,⟨⟨coefficient_1444,coefficient_1445⟩,⟨coefficient_1446,coefficient_1447⟩⟩⟩,⟨⟨⟨coefficient_1448,coefficient_1449⟩,⟨coefficient_1450,coefficient_1451⟩⟩,⟨⟨coefficient_1452,coefficient_1453⟩,⟨coefficient_1454,coefficient_1455⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1456,coefficient_1457⟩,⟨coefficient_1458,coefficient_1459⟩⟩,⟨⟨coefficient_1460,coefficient_1461⟩,⟨coefficient_1462,coefficient_1463⟩⟩⟩,⟨⟨⟨coefficient_1464,coefficient_1465⟩,⟨coefficient_1466,coefficient_1467⟩⟩,⟨⟨coefficient_1468,coefficient_1469⟩,⟨coefficient_1470,coefficient_1471⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1472 : Rep := ⟨![0,4,1,36],462⟩
def representative_1473 : Rep := ⟨![0,4,1,37],462⟩
def representative_1474 : Rep := ⟨![0,4,1,38],462⟩
def representative_1475 : Rep := ⟨![0,4,1,39],462⟩
def representative_1476 : Rep := ⟨![0,4,2,6],462⟩
def representative_1477 : Rep := ⟨![0,4,2,8],178⟩
def representative_1478 : Rep := ⟨![0,4,2,9],350⟩
def representative_1479 : Rep := ⟨![0,4,2,13],462⟩
def representative_1480 : Rep := ⟨![0,4,2,14],462⟩
def representative_1481 : Rep := ⟨![0,4,2,16],462⟩
def representative_1482 : Rep := ⟨![0,4,2,17],178⟩
def representative_1483 : Rep := ⟨![0,4,2,21],462⟩
def representative_1484 : Rep := ⟨![0,4,2,22],462⟩
def representative_1485 : Rep := ⟨![0,4,2,24],462⟩
def representative_1486 : Rep := ⟨![0,4,2,25],462⟩
def representative_1487 : Rep := ⟨![0,4,2,29],462⟩
def representative_1488 : Rep := ⟨![0,4,2,30],462⟩
def representative_1489 : Rep := ⟨![0,4,2,32],462⟩
def representative_1490 : Rep := ⟨![0,4,2,33],462⟩
def representative_1491 : Rep := ⟨![0,4,2,34],462⟩
def representative_1492 : Rep := ⟨![0,4,2,37],462⟩
def representative_1493 : Rep := ⟨![0,4,2,38],462⟩
def representative_1494 : Rep := ⟨![0,4,8,12],462⟩
def representative_1495 : Rep := ⟨![0,4,8,17],462⟩
def representative_1496 : Rep := ⟨![0,4,8,18],462⟩
def representative_1497 : Rep := ⟨![0,4,8,19],462⟩
def representative_1498 : Rep := ⟨![0,4,8,20],462⟩
def representative_1499 : Rep := ⟨![0,4,8,25],462⟩
def representative_1500 : Rep := ⟨![0,4,8,26],462⟩
def representative_1501 : Rep := ⟨![0,4,8,27],462⟩
def representative_1502 : Rep := ⟨![0,4,8,28],462⟩
def representative_1503 : Rep := ⟨![0,4,8,33],462⟩
def representative_1504 : Rep := ⟨![0,4,8,34],462⟩
def representative_1505 : Rep := ⟨![0,4,8,35],462⟩
def representative_1506 : Rep := ⟨![0,4,8,36],462⟩
def representative_1507 : Rep := ⟨![0,4,8,41],462⟩
def representative_1508 : Rep := ⟨![0,4,8,42],462⟩
def representative_1509 : Rep := ⟨![0,4,8,43],462⟩
def representative_1510 : Rep := ⟨![0,4,8,44],462⟩
def representative_1511 : Rep := ⟨![0,4,8,49],462⟩
def representative_1512 : Rep := ⟨![0,4,8,50],462⟩
def representative_1513 : Rep := ⟨![0,4,8,51],462⟩
def representative_1514 : Rep := ⟨![0,4,8,52],462⟩
def representative_1515 : Rep := ⟨![0,4,8,57],232⟩
def representative_1516 : Rep := ⟨![0,4,8,58],462⟩
def representative_1517 : Rep := ⟨![0,4,8,59],462⟩
def representative_1518 : Rep := ⟨![0,4,8,60],462⟩
def representative_1519 : Rep := ⟨![0,4,9,13],462⟩
def representative_1520 : Rep := ⟨![0,4,9,16],288⟩
def representative_1521 : Rep := ⟨![0,4,9,18],288⟩
def representative_1522 : Rep := ⟨![0,4,9,19],232⟩
def representative_1523 : Rep := ⟨![0,4,9,20],462⟩
def representative_1524 : Rep := ⟨![0,4,9,21],462⟩
def representative_1525 : Rep := ⟨![0,4,9,22],462⟩
def representative_1526 : Rep := ⟨![0,4,9,23],232⟩
def representative_1527 : Rep := ⟨![0,4,9,24],232⟩
def representative_1528 : Rep := ⟨![0,4,9,26],232⟩
def representative_1529 : Rep := ⟨![0,4,9,27],462⟩
def representative_1530 : Rep := ⟨![0,4,9,28],462⟩
def representative_1531 : Rep := ⟨![0,4,9,29],462⟩
def representative_1532 : Rep := ⟨![0,4,9,30],462⟩
def representative_1533 : Rep := ⟨![0,4,9,31],462⟩
def representative_1534 : Rep := ⟨![0,4,9,32],462⟩
def representative_1535 : Rep := ⟨![0,4,9,34],462⟩
theorem coefficient_1472 : validRep representative_1472 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1472)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1473 : validRep representative_1473 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1473)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1474 : validRep representative_1474 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1474)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1475 : validRep representative_1475 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1475)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1476 : validRep representative_1476 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1476)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1477 : validRep representative_1477 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1477)=dictionary64.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_1478 : validRep representative_1478 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1478)=dictionary64.getD 350 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_350]
  decide +kernel
theorem coefficient_1479 : validRep representative_1479 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1479)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1480 : validRep representative_1480 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1480)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1481 : validRep representative_1481 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1481)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1482 : validRep representative_1482 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1482)=dictionary64.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_1483 : validRep representative_1483 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1483)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1484 : validRep representative_1484 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1484)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1485 : validRep representative_1485 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1485)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1486 : validRep representative_1486 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1486)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1487 : validRep representative_1487 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1487)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1488 : validRep representative_1488 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1488)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1489 : validRep representative_1489 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1489)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1490 : validRep representative_1490 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1490)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1491 : validRep representative_1491 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1491)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1492 : validRep representative_1492 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1492)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1493 : validRep representative_1493 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1493)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1494 : validRep representative_1494 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1494)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1495 : validRep representative_1495 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1495)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1496 : validRep representative_1496 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1496)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1497 : validRep representative_1497 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1497)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1498 : validRep representative_1498 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1498)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1499 : validRep representative_1499 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1499)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1500 : validRep representative_1500 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1500)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1501 : validRep representative_1501 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1501)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1502 : validRep representative_1502 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1502)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1503 : validRep representative_1503 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1503)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1504 : validRep representative_1504 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1504)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1505 : validRep representative_1505 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1505)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1506 : validRep representative_1506 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1506)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1507 : validRep representative_1507 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1507)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1508 : validRep representative_1508 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1508)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1509 : validRep representative_1509 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1509)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1510 : validRep representative_1510 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1510)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1511 : validRep representative_1511 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1511)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1512 : validRep representative_1512 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1512)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1513 : validRep representative_1513 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1513)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1514 : validRep representative_1514 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1514)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1515 : validRep representative_1515 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1515)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1516 : validRep representative_1516 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1516)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1517 : validRep representative_1517 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1517)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1518 : validRep representative_1518 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1518)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1519 : validRep representative_1519 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1519)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1520 : validRep representative_1520 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1520)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1521 : validRep representative_1521 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1521)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1522 : validRep representative_1522 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1522)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1523 : validRep representative_1523 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1523)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1524 : validRep representative_1524 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1524)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1525 : validRep representative_1525 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1525)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1526 : validRep representative_1526 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1526)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1527 : validRep representative_1527 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1527)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1528 : validRep representative_1528 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1528)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1529 : validRep representative_1529 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1529)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1530 : validRep representative_1530 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1530)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1531 : validRep representative_1531 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1531)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1532 : validRep representative_1532 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1532)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1533 : validRep representative_1533 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1533)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1534 : validRep representative_1534 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1534)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1535 : validRep representative_1535 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1535)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_023 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1504 (QuarticIntegerRepresentativeTree.Tree.branch 1488 (QuarticIntegerRepresentativeTree.Tree.branch 1480 (QuarticIntegerRepresentativeTree.Tree.branch 1476 (QuarticIntegerRepresentativeTree.Tree.branch 1474 (QuarticIntegerRepresentativeTree.Tree.branch 1473 (QuarticIntegerRepresentativeTree.Tree.leaf 1472 representative_1472) (QuarticIntegerRepresentativeTree.Tree.leaf 1473 representative_1473)) (QuarticIntegerRepresentativeTree.Tree.branch 1475 (QuarticIntegerRepresentativeTree.Tree.leaf 1474 representative_1474) (QuarticIntegerRepresentativeTree.Tree.leaf 1475 representative_1475))) (QuarticIntegerRepresentativeTree.Tree.branch 1478 (QuarticIntegerRepresentativeTree.Tree.branch 1477 (QuarticIntegerRepresentativeTree.Tree.leaf 1476 representative_1476) (QuarticIntegerRepresentativeTree.Tree.leaf 1477 representative_1477)) (QuarticIntegerRepresentativeTree.Tree.branch 1479 (QuarticIntegerRepresentativeTree.Tree.leaf 1478 representative_1478) (QuarticIntegerRepresentativeTree.Tree.leaf 1479 representative_1479)))) (QuarticIntegerRepresentativeTree.Tree.branch 1484 (QuarticIntegerRepresentativeTree.Tree.branch 1482 (QuarticIntegerRepresentativeTree.Tree.branch 1481 (QuarticIntegerRepresentativeTree.Tree.leaf 1480 representative_1480) (QuarticIntegerRepresentativeTree.Tree.leaf 1481 representative_1481)) (QuarticIntegerRepresentativeTree.Tree.branch 1483 (QuarticIntegerRepresentativeTree.Tree.leaf 1482 representative_1482) (QuarticIntegerRepresentativeTree.Tree.leaf 1483 representative_1483))) (QuarticIntegerRepresentativeTree.Tree.branch 1486 (QuarticIntegerRepresentativeTree.Tree.branch 1485 (QuarticIntegerRepresentativeTree.Tree.leaf 1484 representative_1484) (QuarticIntegerRepresentativeTree.Tree.leaf 1485 representative_1485)) (QuarticIntegerRepresentativeTree.Tree.branch 1487 (QuarticIntegerRepresentativeTree.Tree.leaf 1486 representative_1486) (QuarticIntegerRepresentativeTree.Tree.leaf 1487 representative_1487))))) (QuarticIntegerRepresentativeTree.Tree.branch 1496 (QuarticIntegerRepresentativeTree.Tree.branch 1492 (QuarticIntegerRepresentativeTree.Tree.branch 1490 (QuarticIntegerRepresentativeTree.Tree.branch 1489 (QuarticIntegerRepresentativeTree.Tree.leaf 1488 representative_1488) (QuarticIntegerRepresentativeTree.Tree.leaf 1489 representative_1489)) (QuarticIntegerRepresentativeTree.Tree.branch 1491 (QuarticIntegerRepresentativeTree.Tree.leaf 1490 representative_1490) (QuarticIntegerRepresentativeTree.Tree.leaf 1491 representative_1491))) (QuarticIntegerRepresentativeTree.Tree.branch 1494 (QuarticIntegerRepresentativeTree.Tree.branch 1493 (QuarticIntegerRepresentativeTree.Tree.leaf 1492 representative_1492) (QuarticIntegerRepresentativeTree.Tree.leaf 1493 representative_1493)) (QuarticIntegerRepresentativeTree.Tree.branch 1495 (QuarticIntegerRepresentativeTree.Tree.leaf 1494 representative_1494) (QuarticIntegerRepresentativeTree.Tree.leaf 1495 representative_1495)))) (QuarticIntegerRepresentativeTree.Tree.branch 1500 (QuarticIntegerRepresentativeTree.Tree.branch 1498 (QuarticIntegerRepresentativeTree.Tree.branch 1497 (QuarticIntegerRepresentativeTree.Tree.leaf 1496 representative_1496) (QuarticIntegerRepresentativeTree.Tree.leaf 1497 representative_1497)) (QuarticIntegerRepresentativeTree.Tree.branch 1499 (QuarticIntegerRepresentativeTree.Tree.leaf 1498 representative_1498) (QuarticIntegerRepresentativeTree.Tree.leaf 1499 representative_1499))) (QuarticIntegerRepresentativeTree.Tree.branch 1502 (QuarticIntegerRepresentativeTree.Tree.branch 1501 (QuarticIntegerRepresentativeTree.Tree.leaf 1500 representative_1500) (QuarticIntegerRepresentativeTree.Tree.leaf 1501 representative_1501)) (QuarticIntegerRepresentativeTree.Tree.branch 1503 (QuarticIntegerRepresentativeTree.Tree.leaf 1502 representative_1502) (QuarticIntegerRepresentativeTree.Tree.leaf 1503 representative_1503)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1520 (QuarticIntegerRepresentativeTree.Tree.branch 1512 (QuarticIntegerRepresentativeTree.Tree.branch 1508 (QuarticIntegerRepresentativeTree.Tree.branch 1506 (QuarticIntegerRepresentativeTree.Tree.branch 1505 (QuarticIntegerRepresentativeTree.Tree.leaf 1504 representative_1504) (QuarticIntegerRepresentativeTree.Tree.leaf 1505 representative_1505)) (QuarticIntegerRepresentativeTree.Tree.branch 1507 (QuarticIntegerRepresentativeTree.Tree.leaf 1506 representative_1506) (QuarticIntegerRepresentativeTree.Tree.leaf 1507 representative_1507))) (QuarticIntegerRepresentativeTree.Tree.branch 1510 (QuarticIntegerRepresentativeTree.Tree.branch 1509 (QuarticIntegerRepresentativeTree.Tree.leaf 1508 representative_1508) (QuarticIntegerRepresentativeTree.Tree.leaf 1509 representative_1509)) (QuarticIntegerRepresentativeTree.Tree.branch 1511 (QuarticIntegerRepresentativeTree.Tree.leaf 1510 representative_1510) (QuarticIntegerRepresentativeTree.Tree.leaf 1511 representative_1511)))) (QuarticIntegerRepresentativeTree.Tree.branch 1516 (QuarticIntegerRepresentativeTree.Tree.branch 1514 (QuarticIntegerRepresentativeTree.Tree.branch 1513 (QuarticIntegerRepresentativeTree.Tree.leaf 1512 representative_1512) (QuarticIntegerRepresentativeTree.Tree.leaf 1513 representative_1513)) (QuarticIntegerRepresentativeTree.Tree.branch 1515 (QuarticIntegerRepresentativeTree.Tree.leaf 1514 representative_1514) (QuarticIntegerRepresentativeTree.Tree.leaf 1515 representative_1515))) (QuarticIntegerRepresentativeTree.Tree.branch 1518 (QuarticIntegerRepresentativeTree.Tree.branch 1517 (QuarticIntegerRepresentativeTree.Tree.leaf 1516 representative_1516) (QuarticIntegerRepresentativeTree.Tree.leaf 1517 representative_1517)) (QuarticIntegerRepresentativeTree.Tree.branch 1519 (QuarticIntegerRepresentativeTree.Tree.leaf 1518 representative_1518) (QuarticIntegerRepresentativeTree.Tree.leaf 1519 representative_1519))))) (QuarticIntegerRepresentativeTree.Tree.branch 1528 (QuarticIntegerRepresentativeTree.Tree.branch 1524 (QuarticIntegerRepresentativeTree.Tree.branch 1522 (QuarticIntegerRepresentativeTree.Tree.branch 1521 (QuarticIntegerRepresentativeTree.Tree.leaf 1520 representative_1520) (QuarticIntegerRepresentativeTree.Tree.leaf 1521 representative_1521)) (QuarticIntegerRepresentativeTree.Tree.branch 1523 (QuarticIntegerRepresentativeTree.Tree.leaf 1522 representative_1522) (QuarticIntegerRepresentativeTree.Tree.leaf 1523 representative_1523))) (QuarticIntegerRepresentativeTree.Tree.branch 1526 (QuarticIntegerRepresentativeTree.Tree.branch 1525 (QuarticIntegerRepresentativeTree.Tree.leaf 1524 representative_1524) (QuarticIntegerRepresentativeTree.Tree.leaf 1525 representative_1525)) (QuarticIntegerRepresentativeTree.Tree.branch 1527 (QuarticIntegerRepresentativeTree.Tree.leaf 1526 representative_1526) (QuarticIntegerRepresentativeTree.Tree.leaf 1527 representative_1527)))) (QuarticIntegerRepresentativeTree.Tree.branch 1532 (QuarticIntegerRepresentativeTree.Tree.branch 1530 (QuarticIntegerRepresentativeTree.Tree.branch 1529 (QuarticIntegerRepresentativeTree.Tree.leaf 1528 representative_1528) (QuarticIntegerRepresentativeTree.Tree.leaf 1529 representative_1529)) (QuarticIntegerRepresentativeTree.Tree.branch 1531 (QuarticIntegerRepresentativeTree.Tree.leaf 1530 representative_1530) (QuarticIntegerRepresentativeTree.Tree.leaf 1531 representative_1531))) (QuarticIntegerRepresentativeTree.Tree.branch 1534 (QuarticIntegerRepresentativeTree.Tree.branch 1533 (QuarticIntegerRepresentativeTree.Tree.leaf 1532 representative_1532) (QuarticIntegerRepresentativeTree.Tree.leaf 1533 representative_1533)) (QuarticIntegerRepresentativeTree.Tree.branch 1535 (QuarticIntegerRepresentativeTree.Tree.leaf 1534 representative_1534) (QuarticIntegerRepresentativeTree.Tree.leaf 1535 representative_1535)))))))
theorem accepted_023 : All validRep tree_023 := ⟨⟨⟨⟨⟨⟨coefficient_1472,coefficient_1473⟩,⟨coefficient_1474,coefficient_1475⟩⟩,⟨⟨coefficient_1476,coefficient_1477⟩,⟨coefficient_1478,coefficient_1479⟩⟩⟩,⟨⟨⟨coefficient_1480,coefficient_1481⟩,⟨coefficient_1482,coefficient_1483⟩⟩,⟨⟨coefficient_1484,coefficient_1485⟩,⟨coefficient_1486,coefficient_1487⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1488,coefficient_1489⟩,⟨coefficient_1490,coefficient_1491⟩⟩,⟨⟨coefficient_1492,coefficient_1493⟩,⟨coefficient_1494,coefficient_1495⟩⟩⟩,⟨⟨⟨coefficient_1496,coefficient_1497⟩,⟨coefficient_1498,coefficient_1499⟩⟩,⟨⟨coefficient_1500,coefficient_1501⟩,⟨coefficient_1502,coefficient_1503⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1504,coefficient_1505⟩,⟨coefficient_1506,coefficient_1507⟩⟩,⟨⟨coefficient_1508,coefficient_1509⟩,⟨coefficient_1510,coefficient_1511⟩⟩⟩,⟨⟨⟨coefficient_1512,coefficient_1513⟩,⟨coefficient_1514,coefficient_1515⟩⟩,⟨⟨coefficient_1516,coefficient_1517⟩,⟨coefficient_1518,coefficient_1519⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1520,coefficient_1521⟩,⟨coefficient_1522,coefficient_1523⟩⟩,⟨⟨coefficient_1524,coefficient_1525⟩,⟨coefficient_1526,coefficient_1527⟩⟩⟩,⟨⟨⟨coefficient_1528,coefficient_1529⟩,⟨coefficient_1530,coefficient_1531⟩⟩,⟨⟨coefficient_1532,coefficient_1533⟩,⟨coefficient_1534,coefficient_1535⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1536 : Rep := ⟨![0,4,9,35],462⟩
def representative_1537 : Rep := ⟨![0,4,9,36],462⟩
def representative_1538 : Rep := ⟨![0,4,9,37],462⟩
def representative_1539 : Rep := ⟨![0,4,9,38],462⟩
def representative_1540 : Rep := ⟨![0,4,9,39],462⟩
def representative_1541 : Rep := ⟨![0,4,9,40],462⟩
def representative_1542 : Rep := ⟨![0,4,9,41],462⟩
def representative_1543 : Rep := ⟨![0,4,9,42],462⟩
def representative_1544 : Rep := ⟨![0,4,9,43],462⟩
def representative_1545 : Rep := ⟨![0,4,9,44],462⟩
def representative_1546 : Rep := ⟨![0,4,9,45],462⟩
def representative_1547 : Rep := ⟨![0,4,9,46],462⟩
def representative_1548 : Rep := ⟨![0,4,9,47],462⟩
def representative_1549 : Rep := ⟨![0,4,9,48],462⟩
def representative_1550 : Rep := ⟨![0,4,9,50],462⟩
def representative_1551 : Rep := ⟨![0,4,9,51],462⟩
def representative_1552 : Rep := ⟨![0,4,9,52],462⟩
def representative_1553 : Rep := ⟨![0,4,9,53],462⟩
def representative_1554 : Rep := ⟨![0,4,9,54],462⟩
def representative_1555 : Rep := ⟨![0,4,9,55],462⟩
def representative_1556 : Rep := ⟨![0,4,9,58],221⟩
def representative_1557 : Rep := ⟨![0,4,9,59],462⟩
def representative_1558 : Rep := ⟨![0,4,9,61],462⟩
def representative_1559 : Rep := ⟨![0,4,9,62],462⟩
def representative_1560 : Rep := ⟨![0,4,9,63],462⟩
def representative_1561 : Rep := ⟨![0,4,10,14],462⟩
def representative_1562 : Rep := ⟨![0,4,10,16],224⟩
def representative_1563 : Rep := ⟨![0,4,10,17],306⟩
def representative_1564 : Rep := ⟨![0,4,10,21],462⟩
def representative_1565 : Rep := ⟨![0,4,10,22],462⟩
def representative_1566 : Rep := ⟨![0,4,10,24],462⟩
def representative_1567 : Rep := ⟨![0,4,10,25],224⟩
def representative_1568 : Rep := ⟨![0,4,10,29],462⟩
def representative_1569 : Rep := ⟨![0,4,10,30],462⟩
def representative_1570 : Rep := ⟨![0,4,10,32],462⟩
def representative_1571 : Rep := ⟨![0,4,10,33],462⟩
def representative_1572 : Rep := ⟨![0,4,10,37],462⟩
def representative_1573 : Rep := ⟨![0,4,10,38],462⟩
def representative_1574 : Rep := ⟨![0,4,10,40],462⟩
def representative_1575 : Rep := ⟨![0,4,10,41],462⟩
def representative_1576 : Rep := ⟨![0,4,10,42],462⟩
def representative_1577 : Rep := ⟨![0,4,10,45],462⟩
def representative_1578 : Rep := ⟨![0,4,10,46],462⟩
def representative_1579 : Rep := ⟨![0,4,10,48],462⟩
def representative_1580 : Rep := ⟨![0,4,10,49],462⟩
def representative_1581 : Rep := ⟨![0,4,10,53],462⟩
def representative_1582 : Rep := ⟨![0,4,10,54],462⟩
def representative_1583 : Rep := ⟨![0,4,10,62],462⟩
def representative_1584 : Rep := ⟨![0,4,16,20],462⟩
def representative_1585 : Rep := ⟨![0,4,16,25],462⟩
def representative_1586 : Rep := ⟨![0,4,16,26],462⟩
def representative_1587 : Rep := ⟨![0,4,16,27],462⟩
def representative_1588 : Rep := ⟨![0,4,16,28],462⟩
def representative_1589 : Rep := ⟨![0,4,16,33],462⟩
def representative_1590 : Rep := ⟨![0,4,16,34],462⟩
def representative_1591 : Rep := ⟨![0,4,16,35],462⟩
def representative_1592 : Rep := ⟨![0,4,16,36],462⟩
def representative_1593 : Rep := ⟨![0,4,16,41],462⟩
def representative_1594 : Rep := ⟨![0,4,16,42],462⟩
def representative_1595 : Rep := ⟨![0,4,16,43],462⟩
def representative_1596 : Rep := ⟨![0,4,16,44],462⟩
def representative_1597 : Rep := ⟨![0,4,16,49],462⟩
def representative_1598 : Rep := ⟨![0,4,16,50],462⟩
def representative_1599 : Rep := ⟨![0,4,16,51],462⟩
theorem coefficient_1536 : validRep representative_1536 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1536)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1537 : validRep representative_1537 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1537)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1538 : validRep representative_1538 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1538)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1539 : validRep representative_1539 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1539)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1540 : validRep representative_1540 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1540)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1541 : validRep representative_1541 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1541)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1542 : validRep representative_1542 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1542)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1543 : validRep representative_1543 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1543)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1544 : validRep representative_1544 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1544)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1545 : validRep representative_1545 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1545)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1546 : validRep representative_1546 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1546)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1547 : validRep representative_1547 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1547)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1548 : validRep representative_1548 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1548)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1549 : validRep representative_1549 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1549)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1550 : validRep representative_1550 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1550)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1551 : validRep representative_1551 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1551)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1552 : validRep representative_1552 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1552)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1553 : validRep representative_1553 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1553)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1554 : validRep representative_1554 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1554)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1555 : validRep representative_1555 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1555)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1556 : validRep representative_1556 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1556)=dictionary64.getD 221 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_221]
  decide +kernel
theorem coefficient_1557 : validRep representative_1557 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1557)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1558 : validRep representative_1558 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1558)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1559 : validRep representative_1559 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1559)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1560 : validRep representative_1560 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1560)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1561 : validRep representative_1561 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1561)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1562 : validRep representative_1562 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1562)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_1563 : validRep representative_1563 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1563)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1564 : validRep representative_1564 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1564)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1565 : validRep representative_1565 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1565)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1566 : validRep representative_1566 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1566)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1567 : validRep representative_1567 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1567)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_1568 : validRep representative_1568 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1568)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1569 : validRep representative_1569 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1569)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1570 : validRep representative_1570 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1570)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1571 : validRep representative_1571 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1571)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1572 : validRep representative_1572 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1572)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1573 : validRep representative_1573 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1573)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1574 : validRep representative_1574 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1574)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1575 : validRep representative_1575 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1575)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1576 : validRep representative_1576 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1576)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1577 : validRep representative_1577 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1577)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1578 : validRep representative_1578 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1578)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1579 : validRep representative_1579 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1579)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1580 : validRep representative_1580 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1580)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1581 : validRep representative_1581 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1581)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1582 : validRep representative_1582 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1582)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1583 : validRep representative_1583 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1583)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1584 : validRep representative_1584 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1584)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1585 : validRep representative_1585 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1585)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1586 : validRep representative_1586 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1586)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1587 : validRep representative_1587 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1587)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1588 : validRep representative_1588 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1588)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1589 : validRep representative_1589 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1589)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1590 : validRep representative_1590 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1590)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1591 : validRep representative_1591 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1591)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1592 : validRep representative_1592 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1592)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1593 : validRep representative_1593 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1593)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1594 : validRep representative_1594 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1594)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1595 : validRep representative_1595 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1595)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1596 : validRep representative_1596 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1596)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1597 : validRep representative_1597 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1597)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1598 : validRep representative_1598 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1598)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1599 : validRep representative_1599 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1599)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_024 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1568 (QuarticIntegerRepresentativeTree.Tree.branch 1552 (QuarticIntegerRepresentativeTree.Tree.branch 1544 (QuarticIntegerRepresentativeTree.Tree.branch 1540 (QuarticIntegerRepresentativeTree.Tree.branch 1538 (QuarticIntegerRepresentativeTree.Tree.branch 1537 (QuarticIntegerRepresentativeTree.Tree.leaf 1536 representative_1536) (QuarticIntegerRepresentativeTree.Tree.leaf 1537 representative_1537)) (QuarticIntegerRepresentativeTree.Tree.branch 1539 (QuarticIntegerRepresentativeTree.Tree.leaf 1538 representative_1538) (QuarticIntegerRepresentativeTree.Tree.leaf 1539 representative_1539))) (QuarticIntegerRepresentativeTree.Tree.branch 1542 (QuarticIntegerRepresentativeTree.Tree.branch 1541 (QuarticIntegerRepresentativeTree.Tree.leaf 1540 representative_1540) (QuarticIntegerRepresentativeTree.Tree.leaf 1541 representative_1541)) (QuarticIntegerRepresentativeTree.Tree.branch 1543 (QuarticIntegerRepresentativeTree.Tree.leaf 1542 representative_1542) (QuarticIntegerRepresentativeTree.Tree.leaf 1543 representative_1543)))) (QuarticIntegerRepresentativeTree.Tree.branch 1548 (QuarticIntegerRepresentativeTree.Tree.branch 1546 (QuarticIntegerRepresentativeTree.Tree.branch 1545 (QuarticIntegerRepresentativeTree.Tree.leaf 1544 representative_1544) (QuarticIntegerRepresentativeTree.Tree.leaf 1545 representative_1545)) (QuarticIntegerRepresentativeTree.Tree.branch 1547 (QuarticIntegerRepresentativeTree.Tree.leaf 1546 representative_1546) (QuarticIntegerRepresentativeTree.Tree.leaf 1547 representative_1547))) (QuarticIntegerRepresentativeTree.Tree.branch 1550 (QuarticIntegerRepresentativeTree.Tree.branch 1549 (QuarticIntegerRepresentativeTree.Tree.leaf 1548 representative_1548) (QuarticIntegerRepresentativeTree.Tree.leaf 1549 representative_1549)) (QuarticIntegerRepresentativeTree.Tree.branch 1551 (QuarticIntegerRepresentativeTree.Tree.leaf 1550 representative_1550) (QuarticIntegerRepresentativeTree.Tree.leaf 1551 representative_1551))))) (QuarticIntegerRepresentativeTree.Tree.branch 1560 (QuarticIntegerRepresentativeTree.Tree.branch 1556 (QuarticIntegerRepresentativeTree.Tree.branch 1554 (QuarticIntegerRepresentativeTree.Tree.branch 1553 (QuarticIntegerRepresentativeTree.Tree.leaf 1552 representative_1552) (QuarticIntegerRepresentativeTree.Tree.leaf 1553 representative_1553)) (QuarticIntegerRepresentativeTree.Tree.branch 1555 (QuarticIntegerRepresentativeTree.Tree.leaf 1554 representative_1554) (QuarticIntegerRepresentativeTree.Tree.leaf 1555 representative_1555))) (QuarticIntegerRepresentativeTree.Tree.branch 1558 (QuarticIntegerRepresentativeTree.Tree.branch 1557 (QuarticIntegerRepresentativeTree.Tree.leaf 1556 representative_1556) (QuarticIntegerRepresentativeTree.Tree.leaf 1557 representative_1557)) (QuarticIntegerRepresentativeTree.Tree.branch 1559 (QuarticIntegerRepresentativeTree.Tree.leaf 1558 representative_1558) (QuarticIntegerRepresentativeTree.Tree.leaf 1559 representative_1559)))) (QuarticIntegerRepresentativeTree.Tree.branch 1564 (QuarticIntegerRepresentativeTree.Tree.branch 1562 (QuarticIntegerRepresentativeTree.Tree.branch 1561 (QuarticIntegerRepresentativeTree.Tree.leaf 1560 representative_1560) (QuarticIntegerRepresentativeTree.Tree.leaf 1561 representative_1561)) (QuarticIntegerRepresentativeTree.Tree.branch 1563 (QuarticIntegerRepresentativeTree.Tree.leaf 1562 representative_1562) (QuarticIntegerRepresentativeTree.Tree.leaf 1563 representative_1563))) (QuarticIntegerRepresentativeTree.Tree.branch 1566 (QuarticIntegerRepresentativeTree.Tree.branch 1565 (QuarticIntegerRepresentativeTree.Tree.leaf 1564 representative_1564) (QuarticIntegerRepresentativeTree.Tree.leaf 1565 representative_1565)) (QuarticIntegerRepresentativeTree.Tree.branch 1567 (QuarticIntegerRepresentativeTree.Tree.leaf 1566 representative_1566) (QuarticIntegerRepresentativeTree.Tree.leaf 1567 representative_1567)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1584 (QuarticIntegerRepresentativeTree.Tree.branch 1576 (QuarticIntegerRepresentativeTree.Tree.branch 1572 (QuarticIntegerRepresentativeTree.Tree.branch 1570 (QuarticIntegerRepresentativeTree.Tree.branch 1569 (QuarticIntegerRepresentativeTree.Tree.leaf 1568 representative_1568) (QuarticIntegerRepresentativeTree.Tree.leaf 1569 representative_1569)) (QuarticIntegerRepresentativeTree.Tree.branch 1571 (QuarticIntegerRepresentativeTree.Tree.leaf 1570 representative_1570) (QuarticIntegerRepresentativeTree.Tree.leaf 1571 representative_1571))) (QuarticIntegerRepresentativeTree.Tree.branch 1574 (QuarticIntegerRepresentativeTree.Tree.branch 1573 (QuarticIntegerRepresentativeTree.Tree.leaf 1572 representative_1572) (QuarticIntegerRepresentativeTree.Tree.leaf 1573 representative_1573)) (QuarticIntegerRepresentativeTree.Tree.branch 1575 (QuarticIntegerRepresentativeTree.Tree.leaf 1574 representative_1574) (QuarticIntegerRepresentativeTree.Tree.leaf 1575 representative_1575)))) (QuarticIntegerRepresentativeTree.Tree.branch 1580 (QuarticIntegerRepresentativeTree.Tree.branch 1578 (QuarticIntegerRepresentativeTree.Tree.branch 1577 (QuarticIntegerRepresentativeTree.Tree.leaf 1576 representative_1576) (QuarticIntegerRepresentativeTree.Tree.leaf 1577 representative_1577)) (QuarticIntegerRepresentativeTree.Tree.branch 1579 (QuarticIntegerRepresentativeTree.Tree.leaf 1578 representative_1578) (QuarticIntegerRepresentativeTree.Tree.leaf 1579 representative_1579))) (QuarticIntegerRepresentativeTree.Tree.branch 1582 (QuarticIntegerRepresentativeTree.Tree.branch 1581 (QuarticIntegerRepresentativeTree.Tree.leaf 1580 representative_1580) (QuarticIntegerRepresentativeTree.Tree.leaf 1581 representative_1581)) (QuarticIntegerRepresentativeTree.Tree.branch 1583 (QuarticIntegerRepresentativeTree.Tree.leaf 1582 representative_1582) (QuarticIntegerRepresentativeTree.Tree.leaf 1583 representative_1583))))) (QuarticIntegerRepresentativeTree.Tree.branch 1592 (QuarticIntegerRepresentativeTree.Tree.branch 1588 (QuarticIntegerRepresentativeTree.Tree.branch 1586 (QuarticIntegerRepresentativeTree.Tree.branch 1585 (QuarticIntegerRepresentativeTree.Tree.leaf 1584 representative_1584) (QuarticIntegerRepresentativeTree.Tree.leaf 1585 representative_1585)) (QuarticIntegerRepresentativeTree.Tree.branch 1587 (QuarticIntegerRepresentativeTree.Tree.leaf 1586 representative_1586) (QuarticIntegerRepresentativeTree.Tree.leaf 1587 representative_1587))) (QuarticIntegerRepresentativeTree.Tree.branch 1590 (QuarticIntegerRepresentativeTree.Tree.branch 1589 (QuarticIntegerRepresentativeTree.Tree.leaf 1588 representative_1588) (QuarticIntegerRepresentativeTree.Tree.leaf 1589 representative_1589)) (QuarticIntegerRepresentativeTree.Tree.branch 1591 (QuarticIntegerRepresentativeTree.Tree.leaf 1590 representative_1590) (QuarticIntegerRepresentativeTree.Tree.leaf 1591 representative_1591)))) (QuarticIntegerRepresentativeTree.Tree.branch 1596 (QuarticIntegerRepresentativeTree.Tree.branch 1594 (QuarticIntegerRepresentativeTree.Tree.branch 1593 (QuarticIntegerRepresentativeTree.Tree.leaf 1592 representative_1592) (QuarticIntegerRepresentativeTree.Tree.leaf 1593 representative_1593)) (QuarticIntegerRepresentativeTree.Tree.branch 1595 (QuarticIntegerRepresentativeTree.Tree.leaf 1594 representative_1594) (QuarticIntegerRepresentativeTree.Tree.leaf 1595 representative_1595))) (QuarticIntegerRepresentativeTree.Tree.branch 1598 (QuarticIntegerRepresentativeTree.Tree.branch 1597 (QuarticIntegerRepresentativeTree.Tree.leaf 1596 representative_1596) (QuarticIntegerRepresentativeTree.Tree.leaf 1597 representative_1597)) (QuarticIntegerRepresentativeTree.Tree.branch 1599 (QuarticIntegerRepresentativeTree.Tree.leaf 1598 representative_1598) (QuarticIntegerRepresentativeTree.Tree.leaf 1599 representative_1599)))))))
theorem accepted_024 : All validRep tree_024 := ⟨⟨⟨⟨⟨⟨coefficient_1536,coefficient_1537⟩,⟨coefficient_1538,coefficient_1539⟩⟩,⟨⟨coefficient_1540,coefficient_1541⟩,⟨coefficient_1542,coefficient_1543⟩⟩⟩,⟨⟨⟨coefficient_1544,coefficient_1545⟩,⟨coefficient_1546,coefficient_1547⟩⟩,⟨⟨coefficient_1548,coefficient_1549⟩,⟨coefficient_1550,coefficient_1551⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1552,coefficient_1553⟩,⟨coefficient_1554,coefficient_1555⟩⟩,⟨⟨coefficient_1556,coefficient_1557⟩,⟨coefficient_1558,coefficient_1559⟩⟩⟩,⟨⟨⟨coefficient_1560,coefficient_1561⟩,⟨coefficient_1562,coefficient_1563⟩⟩,⟨⟨coefficient_1564,coefficient_1565⟩,⟨coefficient_1566,coefficient_1567⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1568,coefficient_1569⟩,⟨coefficient_1570,coefficient_1571⟩⟩,⟨⟨coefficient_1572,coefficient_1573⟩,⟨coefficient_1574,coefficient_1575⟩⟩⟩,⟨⟨⟨coefficient_1576,coefficient_1577⟩,⟨coefficient_1578,coefficient_1579⟩⟩,⟨⟨coefficient_1580,coefficient_1581⟩,⟨coefficient_1582,coefficient_1583⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1584,coefficient_1585⟩,⟨coefficient_1586,coefficient_1587⟩⟩,⟨⟨coefficient_1588,coefficient_1589⟩,⟨coefficient_1590,coefficient_1591⟩⟩⟩,⟨⟨⟨coefficient_1592,coefficient_1593⟩,⟨coefficient_1594,coefficient_1595⟩⟩,⟨⟨coefficient_1596,coefficient_1597⟩,⟨coefficient_1598,coefficient_1599⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

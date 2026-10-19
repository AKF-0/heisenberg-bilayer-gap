import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1600 : Rep := ⟨![0,4,16,52],462⟩
def representative_1601 : Rep := ⟨![0,4,17,21],462⟩
def representative_1602 : Rep := ⟨![0,4,17,24],462⟩
def representative_1603 : Rep := ⟨![0,4,17,26],462⟩
def representative_1604 : Rep := ⟨![0,4,17,27],462⟩
def representative_1605 : Rep := ⟨![0,4,17,28],462⟩
def representative_1606 : Rep := ⟨![0,4,17,29],462⟩
def representative_1607 : Rep := ⟨![0,4,17,30],462⟩
def representative_1608 : Rep := ⟨![0,4,17,31],462⟩
def representative_1609 : Rep := ⟨![0,4,17,32],462⟩
def representative_1610 : Rep := ⟨![0,4,17,34],462⟩
def representative_1611 : Rep := ⟨![0,4,17,35],462⟩
def representative_1612 : Rep := ⟨![0,4,17,36],462⟩
def representative_1613 : Rep := ⟨![0,4,17,37],462⟩
def representative_1614 : Rep := ⟨![0,4,17,38],462⟩
def representative_1615 : Rep := ⟨![0,4,17,39],462⟩
def representative_1616 : Rep := ⟨![0,4,17,40],462⟩
def representative_1617 : Rep := ⟨![0,4,17,42],462⟩
def representative_1618 : Rep := ⟨![0,4,17,43],462⟩
def representative_1619 : Rep := ⟨![0,4,17,44],462⟩
def representative_1620 : Rep := ⟨![0,4,17,45],462⟩
def representative_1621 : Rep := ⟨![0,4,17,46],462⟩
def representative_1622 : Rep := ⟨![0,4,17,47],462⟩
def representative_1623 : Rep := ⟨![0,4,17,50],462⟩
def representative_1624 : Rep := ⟨![0,4,17,51],462⟩
def representative_1625 : Rep := ⟨![0,4,17,53],462⟩
def representative_1626 : Rep := ⟨![0,4,17,54],462⟩
def representative_1627 : Rep := ⟨![0,4,17,55],462⟩
def representative_1628 : Rep := ⟨![0,4,18,22],462⟩
def representative_1629 : Rep := ⟨![0,4,18,24],462⟩
def representative_1630 : Rep := ⟨![0,4,18,25],462⟩
def representative_1631 : Rep := ⟨![0,4,18,29],462⟩
def representative_1632 : Rep := ⟨![0,4,18,30],462⟩
def representative_1633 : Rep := ⟨![0,4,18,32],462⟩
def representative_1634 : Rep := ⟨![0,4,18,33],462⟩
def representative_1635 : Rep := ⟨![0,4,18,37],462⟩
def representative_1636 : Rep := ⟨![0,4,18,38],462⟩
def representative_1637 : Rep := ⟨![0,4,18,40],462⟩
def representative_1638 : Rep := ⟨![0,4,18,41],462⟩
def representative_1639 : Rep := ⟨![0,4,18,45],462⟩
def representative_1640 : Rep := ⟨![0,4,18,46],462⟩
def representative_1641 : Rep := ⟨![0,4,18,50],462⟩
def representative_1642 : Rep := ⟨![0,4,18,54],462⟩
def representative_1643 : Rep := ⟨![0,4,24,28],462⟩
def representative_1644 : Rep := ⟨![0,4,24,33],462⟩
def representative_1645 : Rep := ⟨![0,4,24,34],462⟩
def representative_1646 : Rep := ⟨![0,4,24,35],462⟩
def representative_1647 : Rep := ⟨![0,4,24,36],462⟩
def representative_1648 : Rep := ⟨![0,4,24,41],462⟩
def representative_1649 : Rep := ⟨![0,4,24,42],462⟩
def representative_1650 : Rep := ⟨![0,4,24,43],462⟩
def representative_1651 : Rep := ⟨![0,4,24,44],462⟩
def representative_1652 : Rep := ⟨![0,4,25,29],462⟩
def representative_1653 : Rep := ⟨![0,4,25,32],462⟩
def representative_1654 : Rep := ⟨![0,4,25,34],462⟩
def representative_1655 : Rep := ⟨![0,4,25,35],462⟩
def representative_1656 : Rep := ⟨![0,4,25,36],462⟩
def representative_1657 : Rep := ⟨![0,4,25,37],462⟩
def representative_1658 : Rep := ⟨![0,4,25,38],462⟩
def representative_1659 : Rep := ⟨![0,4,25,39],462⟩
def representative_1660 : Rep := ⟨![0,4,25,42],462⟩
def representative_1661 : Rep := ⟨![0,4,25,43],462⟩
def representative_1662 : Rep := ⟨![0,4,25,45],462⟩
def representative_1663 : Rep := ⟨![0,4,25,46],462⟩
theorem coefficient_1600 : validRep representative_1600 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1600)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1601 : validRep representative_1601 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1601)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1602 : validRep representative_1602 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1602)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1603 : validRep representative_1603 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1603)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1604 : validRep representative_1604 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1604)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1605 : validRep representative_1605 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1605)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1606 : validRep representative_1606 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1606)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1607 : validRep representative_1607 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1607)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1608 : validRep representative_1608 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1608)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1609 : validRep representative_1609 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1609)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1610 : validRep representative_1610 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1610)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1611 : validRep representative_1611 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1611)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1612 : validRep representative_1612 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1612)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1613 : validRep representative_1613 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1613)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1614 : validRep representative_1614 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1614)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1615 : validRep representative_1615 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1615)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1616 : validRep representative_1616 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1616)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1617 : validRep representative_1617 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1617)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1618 : validRep representative_1618 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1618)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1619 : validRep representative_1619 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1619)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1620 : validRep representative_1620 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1620)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1621 : validRep representative_1621 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1621)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1622 : validRep representative_1622 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1622)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1623 : validRep representative_1623 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1623)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1624 : validRep representative_1624 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1624)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1625 : validRep representative_1625 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1625)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1626 : validRep representative_1626 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1626)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1627 : validRep representative_1627 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1627)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1628 : validRep representative_1628 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1628)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1629 : validRep representative_1629 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1629)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1630 : validRep representative_1630 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1630)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1631 : validRep representative_1631 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1631)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1632 : validRep representative_1632 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1632)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1633 : validRep representative_1633 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1633)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1634 : validRep representative_1634 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1634)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1635 : validRep representative_1635 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1635)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1636 : validRep representative_1636 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1636)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1637 : validRep representative_1637 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1637)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1638 : validRep representative_1638 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1638)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1639 : validRep representative_1639 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1639)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1640 : validRep representative_1640 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1640)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1641 : validRep representative_1641 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1641)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1642 : validRep representative_1642 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1642)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1643 : validRep representative_1643 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1643)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1644 : validRep representative_1644 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1644)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1645 : validRep representative_1645 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1645)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1646 : validRep representative_1646 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1646)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1647 : validRep representative_1647 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1647)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1648 : validRep representative_1648 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1648)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1649 : validRep representative_1649 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1649)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1650 : validRep representative_1650 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1650)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1651 : validRep representative_1651 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1651)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1652 : validRep representative_1652 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1652)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1653 : validRep representative_1653 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1653)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1654 : validRep representative_1654 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1654)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1655 : validRep representative_1655 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1655)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1656 : validRep representative_1656 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1656)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1657 : validRep representative_1657 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1657)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1658 : validRep representative_1658 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1658)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1659 : validRep representative_1659 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1659)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1660 : validRep representative_1660 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1660)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1661 : validRep representative_1661 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1661)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1662 : validRep representative_1662 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1662)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1663 : validRep representative_1663 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1663)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_025 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1632 (QuarticIntegerRepresentativeTree.Tree.branch 1616 (QuarticIntegerRepresentativeTree.Tree.branch 1608 (QuarticIntegerRepresentativeTree.Tree.branch 1604 (QuarticIntegerRepresentativeTree.Tree.branch 1602 (QuarticIntegerRepresentativeTree.Tree.branch 1601 (QuarticIntegerRepresentativeTree.Tree.leaf 1600 representative_1600) (QuarticIntegerRepresentativeTree.Tree.leaf 1601 representative_1601)) (QuarticIntegerRepresentativeTree.Tree.branch 1603 (QuarticIntegerRepresentativeTree.Tree.leaf 1602 representative_1602) (QuarticIntegerRepresentativeTree.Tree.leaf 1603 representative_1603))) (QuarticIntegerRepresentativeTree.Tree.branch 1606 (QuarticIntegerRepresentativeTree.Tree.branch 1605 (QuarticIntegerRepresentativeTree.Tree.leaf 1604 representative_1604) (QuarticIntegerRepresentativeTree.Tree.leaf 1605 representative_1605)) (QuarticIntegerRepresentativeTree.Tree.branch 1607 (QuarticIntegerRepresentativeTree.Tree.leaf 1606 representative_1606) (QuarticIntegerRepresentativeTree.Tree.leaf 1607 representative_1607)))) (QuarticIntegerRepresentativeTree.Tree.branch 1612 (QuarticIntegerRepresentativeTree.Tree.branch 1610 (QuarticIntegerRepresentativeTree.Tree.branch 1609 (QuarticIntegerRepresentativeTree.Tree.leaf 1608 representative_1608) (QuarticIntegerRepresentativeTree.Tree.leaf 1609 representative_1609)) (QuarticIntegerRepresentativeTree.Tree.branch 1611 (QuarticIntegerRepresentativeTree.Tree.leaf 1610 representative_1610) (QuarticIntegerRepresentativeTree.Tree.leaf 1611 representative_1611))) (QuarticIntegerRepresentativeTree.Tree.branch 1614 (QuarticIntegerRepresentativeTree.Tree.branch 1613 (QuarticIntegerRepresentativeTree.Tree.leaf 1612 representative_1612) (QuarticIntegerRepresentativeTree.Tree.leaf 1613 representative_1613)) (QuarticIntegerRepresentativeTree.Tree.branch 1615 (QuarticIntegerRepresentativeTree.Tree.leaf 1614 representative_1614) (QuarticIntegerRepresentativeTree.Tree.leaf 1615 representative_1615))))) (QuarticIntegerRepresentativeTree.Tree.branch 1624 (QuarticIntegerRepresentativeTree.Tree.branch 1620 (QuarticIntegerRepresentativeTree.Tree.branch 1618 (QuarticIntegerRepresentativeTree.Tree.branch 1617 (QuarticIntegerRepresentativeTree.Tree.leaf 1616 representative_1616) (QuarticIntegerRepresentativeTree.Tree.leaf 1617 representative_1617)) (QuarticIntegerRepresentativeTree.Tree.branch 1619 (QuarticIntegerRepresentativeTree.Tree.leaf 1618 representative_1618) (QuarticIntegerRepresentativeTree.Tree.leaf 1619 representative_1619))) (QuarticIntegerRepresentativeTree.Tree.branch 1622 (QuarticIntegerRepresentativeTree.Tree.branch 1621 (QuarticIntegerRepresentativeTree.Tree.leaf 1620 representative_1620) (QuarticIntegerRepresentativeTree.Tree.leaf 1621 representative_1621)) (QuarticIntegerRepresentativeTree.Tree.branch 1623 (QuarticIntegerRepresentativeTree.Tree.leaf 1622 representative_1622) (QuarticIntegerRepresentativeTree.Tree.leaf 1623 representative_1623)))) (QuarticIntegerRepresentativeTree.Tree.branch 1628 (QuarticIntegerRepresentativeTree.Tree.branch 1626 (QuarticIntegerRepresentativeTree.Tree.branch 1625 (QuarticIntegerRepresentativeTree.Tree.leaf 1624 representative_1624) (QuarticIntegerRepresentativeTree.Tree.leaf 1625 representative_1625)) (QuarticIntegerRepresentativeTree.Tree.branch 1627 (QuarticIntegerRepresentativeTree.Tree.leaf 1626 representative_1626) (QuarticIntegerRepresentativeTree.Tree.leaf 1627 representative_1627))) (QuarticIntegerRepresentativeTree.Tree.branch 1630 (QuarticIntegerRepresentativeTree.Tree.branch 1629 (QuarticIntegerRepresentativeTree.Tree.leaf 1628 representative_1628) (QuarticIntegerRepresentativeTree.Tree.leaf 1629 representative_1629)) (QuarticIntegerRepresentativeTree.Tree.branch 1631 (QuarticIntegerRepresentativeTree.Tree.leaf 1630 representative_1630) (QuarticIntegerRepresentativeTree.Tree.leaf 1631 representative_1631)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1648 (QuarticIntegerRepresentativeTree.Tree.branch 1640 (QuarticIntegerRepresentativeTree.Tree.branch 1636 (QuarticIntegerRepresentativeTree.Tree.branch 1634 (QuarticIntegerRepresentativeTree.Tree.branch 1633 (QuarticIntegerRepresentativeTree.Tree.leaf 1632 representative_1632) (QuarticIntegerRepresentativeTree.Tree.leaf 1633 representative_1633)) (QuarticIntegerRepresentativeTree.Tree.branch 1635 (QuarticIntegerRepresentativeTree.Tree.leaf 1634 representative_1634) (QuarticIntegerRepresentativeTree.Tree.leaf 1635 representative_1635))) (QuarticIntegerRepresentativeTree.Tree.branch 1638 (QuarticIntegerRepresentativeTree.Tree.branch 1637 (QuarticIntegerRepresentativeTree.Tree.leaf 1636 representative_1636) (QuarticIntegerRepresentativeTree.Tree.leaf 1637 representative_1637)) (QuarticIntegerRepresentativeTree.Tree.branch 1639 (QuarticIntegerRepresentativeTree.Tree.leaf 1638 representative_1638) (QuarticIntegerRepresentativeTree.Tree.leaf 1639 representative_1639)))) (QuarticIntegerRepresentativeTree.Tree.branch 1644 (QuarticIntegerRepresentativeTree.Tree.branch 1642 (QuarticIntegerRepresentativeTree.Tree.branch 1641 (QuarticIntegerRepresentativeTree.Tree.leaf 1640 representative_1640) (QuarticIntegerRepresentativeTree.Tree.leaf 1641 representative_1641)) (QuarticIntegerRepresentativeTree.Tree.branch 1643 (QuarticIntegerRepresentativeTree.Tree.leaf 1642 representative_1642) (QuarticIntegerRepresentativeTree.Tree.leaf 1643 representative_1643))) (QuarticIntegerRepresentativeTree.Tree.branch 1646 (QuarticIntegerRepresentativeTree.Tree.branch 1645 (QuarticIntegerRepresentativeTree.Tree.leaf 1644 representative_1644) (QuarticIntegerRepresentativeTree.Tree.leaf 1645 representative_1645)) (QuarticIntegerRepresentativeTree.Tree.branch 1647 (QuarticIntegerRepresentativeTree.Tree.leaf 1646 representative_1646) (QuarticIntegerRepresentativeTree.Tree.leaf 1647 representative_1647))))) (QuarticIntegerRepresentativeTree.Tree.branch 1656 (QuarticIntegerRepresentativeTree.Tree.branch 1652 (QuarticIntegerRepresentativeTree.Tree.branch 1650 (QuarticIntegerRepresentativeTree.Tree.branch 1649 (QuarticIntegerRepresentativeTree.Tree.leaf 1648 representative_1648) (QuarticIntegerRepresentativeTree.Tree.leaf 1649 representative_1649)) (QuarticIntegerRepresentativeTree.Tree.branch 1651 (QuarticIntegerRepresentativeTree.Tree.leaf 1650 representative_1650) (QuarticIntegerRepresentativeTree.Tree.leaf 1651 representative_1651))) (QuarticIntegerRepresentativeTree.Tree.branch 1654 (QuarticIntegerRepresentativeTree.Tree.branch 1653 (QuarticIntegerRepresentativeTree.Tree.leaf 1652 representative_1652) (QuarticIntegerRepresentativeTree.Tree.leaf 1653 representative_1653)) (QuarticIntegerRepresentativeTree.Tree.branch 1655 (QuarticIntegerRepresentativeTree.Tree.leaf 1654 representative_1654) (QuarticIntegerRepresentativeTree.Tree.leaf 1655 representative_1655)))) (QuarticIntegerRepresentativeTree.Tree.branch 1660 (QuarticIntegerRepresentativeTree.Tree.branch 1658 (QuarticIntegerRepresentativeTree.Tree.branch 1657 (QuarticIntegerRepresentativeTree.Tree.leaf 1656 representative_1656) (QuarticIntegerRepresentativeTree.Tree.leaf 1657 representative_1657)) (QuarticIntegerRepresentativeTree.Tree.branch 1659 (QuarticIntegerRepresentativeTree.Tree.leaf 1658 representative_1658) (QuarticIntegerRepresentativeTree.Tree.leaf 1659 representative_1659))) (QuarticIntegerRepresentativeTree.Tree.branch 1662 (QuarticIntegerRepresentativeTree.Tree.branch 1661 (QuarticIntegerRepresentativeTree.Tree.leaf 1660 representative_1660) (QuarticIntegerRepresentativeTree.Tree.leaf 1661 representative_1661)) (QuarticIntegerRepresentativeTree.Tree.branch 1663 (QuarticIntegerRepresentativeTree.Tree.leaf 1662 representative_1662) (QuarticIntegerRepresentativeTree.Tree.leaf 1663 representative_1663)))))))
theorem accepted_025 : All validRep tree_025 := ⟨⟨⟨⟨⟨⟨coefficient_1600,coefficient_1601⟩,⟨coefficient_1602,coefficient_1603⟩⟩,⟨⟨coefficient_1604,coefficient_1605⟩,⟨coefficient_1606,coefficient_1607⟩⟩⟩,⟨⟨⟨coefficient_1608,coefficient_1609⟩,⟨coefficient_1610,coefficient_1611⟩⟩,⟨⟨coefficient_1612,coefficient_1613⟩,⟨coefficient_1614,coefficient_1615⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1616,coefficient_1617⟩,⟨coefficient_1618,coefficient_1619⟩⟩,⟨⟨coefficient_1620,coefficient_1621⟩,⟨coefficient_1622,coefficient_1623⟩⟩⟩,⟨⟨⟨coefficient_1624,coefficient_1625⟩,⟨coefficient_1626,coefficient_1627⟩⟩,⟨⟨coefficient_1628,coefficient_1629⟩,⟨coefficient_1630,coefficient_1631⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1632,coefficient_1633⟩,⟨coefficient_1634,coefficient_1635⟩⟩,⟨⟨coefficient_1636,coefficient_1637⟩,⟨coefficient_1638,coefficient_1639⟩⟩⟩,⟨⟨⟨coefficient_1640,coefficient_1641⟩,⟨coefficient_1642,coefficient_1643⟩⟩,⟨⟨coefficient_1644,coefficient_1645⟩,⟨coefficient_1646,coefficient_1647⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1648,coefficient_1649⟩,⟨coefficient_1650,coefficient_1651⟩⟩,⟨⟨coefficient_1652,coefficient_1653⟩,⟨coefficient_1654,coefficient_1655⟩⟩⟩,⟨⟨⟨coefficient_1656,coefficient_1657⟩,⟨coefficient_1658,coefficient_1659⟩⟩,⟨⟨coefficient_1660,coefficient_1661⟩,⟨coefficient_1662,coefficient_1663⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1664 : Rep := ⟨![0,4,25,47],462⟩
def representative_1665 : Rep := ⟨![0,4,26,30],462⟩
def representative_1666 : Rep := ⟨![0,4,26,32],462⟩
def representative_1667 : Rep := ⟨![0,4,26,33],462⟩
def representative_1668 : Rep := ⟨![0,4,26,37],462⟩
def representative_1669 : Rep := ⟨![0,4,26,38],462⟩
def representative_1670 : Rep := ⟨![0,4,26,46],462⟩
def representative_1671 : Rep := ⟨![0,4,32,36],462⟩
def representative_1672 : Rep := ⟨![0,4,33,37],462⟩
def representative_1673 : Rep := ⟨![0,4,34,38],462⟩
def representative_1674 : Rep := ⟨![0,9,1,8],17⟩
def representative_1675 : Rep := ⟨![0,9,1,10],461⟩
def representative_1676 : Rep := ⟨![0,9,1,11],27⟩
def representative_1677 : Rep := ⟨![0,9,1,12],429⟩
def representative_1678 : Rep := ⟨![0,9,1,13],139⟩
def representative_1679 : Rep := ⟨![0,9,1,14],439⟩
def representative_1680 : Rep := ⟨![0,9,1,15],24⟩
def representative_1681 : Rep := ⟨![0,9,1,18],25⟩
def representative_1682 : Rep := ⟨![0,9,1,19],436⟩
def representative_1683 : Rep := ⟨![0,9,1,20],163⟩
def representative_1684 : Rep := ⟨![0,9,1,21],462⟩
def representative_1685 : Rep := ⟨![0,9,1,22],124⟩
def representative_1686 : Rep := ⟨![0,9,1,23],440⟩
def representative_1687 : Rep := ⟨![0,9,1,26],436⟩
def representative_1688 : Rep := ⟨![0,9,1,27],139⟩
def representative_1689 : Rep := ⟨![0,9,1,28],462⟩
def representative_1690 : Rep := ⟨![0,9,1,29],462⟩
def representative_1691 : Rep := ⟨![0,9,1,30],462⟩
def representative_1692 : Rep := ⟨![0,9,1,34],163⟩
def representative_1693 : Rep := ⟨![0,9,1,35],462⟩
def representative_1694 : Rep := ⟨![0,9,1,36],462⟩
def representative_1695 : Rep := ⟨![0,9,1,37],462⟩
def representative_1696 : Rep := ⟨![0,9,1,42],462⟩
def representative_1697 : Rep := ⟨![0,9,1,43],462⟩
def representative_1698 : Rep := ⟨![0,9,1,44],462⟩
def representative_1699 : Rep := ⟨![0,9,1,50],31⟩
def representative_1700 : Rep := ⟨![0,9,1,51],462⟩
def representative_1701 : Rep := ⟨![0,9,1,58],458⟩
def representative_1702 : Rep := ⟨![0,9,2,11],404⟩
def representative_1703 : Rep := ⟨![0,9,2,12],125⟩
def representative_1704 : Rep := ⟨![0,9,2,13],288⟩
def representative_1705 : Rep := ⟨![0,9,2,14],128⟩
def representative_1706 : Rep := ⟨![0,9,2,15],403⟩
def representative_1707 : Rep := ⟨![0,9,2,16],405⟩
def representative_1708 : Rep := ⟨![0,9,2,17],33⟩
def representative_1709 : Rep := ⟨![0,9,2,19],99⟩
def representative_1710 : Rep := ⟨![0,9,2,20],288⟩
def representative_1711 : Rep := ⟨![0,9,2,21],462⟩
def representative_1712 : Rep := ⟨![0,9,2,22],300⟩
def representative_1713 : Rep := ⟨![0,9,2,23],101⟩
def representative_1714 : Rep := ⟨![0,9,2,24],111⟩
def representative_1715 : Rep := ⟨![0,9,2,25],380⟩
def representative_1716 : Rep := ⟨![0,9,2,27],295⟩
def representative_1717 : Rep := ⟨![0,9,2,28],462⟩
def representative_1718 : Rep := ⟨![0,9,2,29],462⟩
def representative_1719 : Rep := ⟨![0,9,2,30],462⟩
def representative_1720 : Rep := ⟨![0,9,2,31],304⟩
def representative_1721 : Rep := ⟨![0,9,2,32],290⟩
def representative_1722 : Rep := ⟨![0,9,2,33],176⟩
def representative_1723 : Rep := ⟨![0,9,2,35],462⟩
def representative_1724 : Rep := ⟨![0,9,2,36],462⟩
def representative_1725 : Rep := ⟨![0,9,2,37],462⟩
def representative_1726 : Rep := ⟨![0,9,2,38],462⟩
def representative_1727 : Rep := ⟨![0,9,2,39],462⟩
theorem coefficient_1664 : validRep representative_1664 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1664)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1665 : validRep representative_1665 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1665)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1666 : validRep representative_1666 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1666)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1667 : validRep representative_1667 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1667)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1668 : validRep representative_1668 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1668)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1669 : validRep representative_1669 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1669)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1670 : validRep representative_1670 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1670)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1671 : validRep representative_1671 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1671)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1672 : validRep representative_1672 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1672)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1673 : validRep representative_1673 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1673)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1674 : validRep representative_1674 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1674)=dictionary64.getD 17 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_17]
  decide +kernel
theorem coefficient_1675 : validRep representative_1675 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1675)=dictionary64.getD 461 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_461]
  decide +kernel
theorem coefficient_1676 : validRep representative_1676 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1676)=dictionary64.getD 27 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_27]
  decide +kernel
theorem coefficient_1677 : validRep representative_1677 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1677)=dictionary64.getD 429 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_429]
  decide +kernel
theorem coefficient_1678 : validRep representative_1678 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1678)=dictionary64.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_139]
  decide +kernel
theorem coefficient_1679 : validRep representative_1679 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1679)=dictionary64.getD 439 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_439]
  decide +kernel
theorem coefficient_1680 : validRep representative_1680 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1680)=dictionary64.getD 24 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_24]
  decide +kernel
theorem coefficient_1681 : validRep representative_1681 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1681)=dictionary64.getD 25 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_25]
  decide +kernel
theorem coefficient_1682 : validRep representative_1682 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1682)=dictionary64.getD 436 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_436]
  decide +kernel
theorem coefficient_1683 : validRep representative_1683 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1683)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_1684 : validRep representative_1684 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1684)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1685 : validRep representative_1685 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1685)=dictionary64.getD 124 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_124]
  decide +kernel
theorem coefficient_1686 : validRep representative_1686 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1686)=dictionary64.getD 440 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_440]
  decide +kernel
theorem coefficient_1687 : validRep representative_1687 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1687)=dictionary64.getD 436 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_436]
  decide +kernel
theorem coefficient_1688 : validRep representative_1688 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1688)=dictionary64.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_139]
  decide +kernel
theorem coefficient_1689 : validRep representative_1689 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1689)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1690 : validRep representative_1690 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1690)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1691 : validRep representative_1691 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1691)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1692 : validRep representative_1692 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1692)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_1693 : validRep representative_1693 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1693)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1694 : validRep representative_1694 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1694)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1695 : validRep representative_1695 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1695)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1696 : validRep representative_1696 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1696)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1697 : validRep representative_1697 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1697)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1698 : validRep representative_1698 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1698)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1699 : validRep representative_1699 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1699)=dictionary64.getD 31 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_31]
  decide +kernel
theorem coefficient_1700 : validRep representative_1700 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1700)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1701 : validRep representative_1701 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1701)=dictionary64.getD 458 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_458]
  decide +kernel
theorem coefficient_1702 : validRep representative_1702 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1702)=dictionary64.getD 404 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_404]
  decide +kernel
theorem coefficient_1703 : validRep representative_1703 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1703)=dictionary64.getD 125 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_125]
  decide +kernel
theorem coefficient_1704 : validRep representative_1704 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1704)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1705 : validRep representative_1705 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1705)=dictionary64.getD 128 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_128]
  decide +kernel
theorem coefficient_1706 : validRep representative_1706 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1706)=dictionary64.getD 403 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_403]
  decide +kernel
theorem coefficient_1707 : validRep representative_1707 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1707)=dictionary64.getD 405 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_405]
  decide +kernel
theorem coefficient_1708 : validRep representative_1708 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1708)=dictionary64.getD 33 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_1709 : validRep representative_1709 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1709)=dictionary64.getD 99 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_99]
  decide +kernel
theorem coefficient_1710 : validRep representative_1710 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1710)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1711 : validRep representative_1711 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1711)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1712 : validRep representative_1712 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1712)=dictionary64.getD 300 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_300]
  decide +kernel
theorem coefficient_1713 : validRep representative_1713 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1713)=dictionary64.getD 101 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_101]
  decide +kernel
theorem coefficient_1714 : validRep representative_1714 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1714)=dictionary64.getD 111 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_111]
  decide +kernel
theorem coefficient_1715 : validRep representative_1715 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1715)=dictionary64.getD 380 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_380]
  decide +kernel
theorem coefficient_1716 : validRep representative_1716 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1716)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_1717 : validRep representative_1717 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1717)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1718 : validRep representative_1718 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1718)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1719 : validRep representative_1719 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1719)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1720 : validRep representative_1720 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1720)=dictionary64.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_1721 : validRep representative_1721 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1721)=dictionary64.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_1722 : validRep representative_1722 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1722)=dictionary64.getD 176 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_176]
  decide +kernel
theorem coefficient_1723 : validRep representative_1723 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1723)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1724 : validRep representative_1724 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1724)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1725 : validRep representative_1725 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1725)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1726 : validRep representative_1726 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1726)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1727 : validRep representative_1727 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1727)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_026 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1696 (QuarticIntegerRepresentativeTree.Tree.branch 1680 (QuarticIntegerRepresentativeTree.Tree.branch 1672 (QuarticIntegerRepresentativeTree.Tree.branch 1668 (QuarticIntegerRepresentativeTree.Tree.branch 1666 (QuarticIntegerRepresentativeTree.Tree.branch 1665 (QuarticIntegerRepresentativeTree.Tree.leaf 1664 representative_1664) (QuarticIntegerRepresentativeTree.Tree.leaf 1665 representative_1665)) (QuarticIntegerRepresentativeTree.Tree.branch 1667 (QuarticIntegerRepresentativeTree.Tree.leaf 1666 representative_1666) (QuarticIntegerRepresentativeTree.Tree.leaf 1667 representative_1667))) (QuarticIntegerRepresentativeTree.Tree.branch 1670 (QuarticIntegerRepresentativeTree.Tree.branch 1669 (QuarticIntegerRepresentativeTree.Tree.leaf 1668 representative_1668) (QuarticIntegerRepresentativeTree.Tree.leaf 1669 representative_1669)) (QuarticIntegerRepresentativeTree.Tree.branch 1671 (QuarticIntegerRepresentativeTree.Tree.leaf 1670 representative_1670) (QuarticIntegerRepresentativeTree.Tree.leaf 1671 representative_1671)))) (QuarticIntegerRepresentativeTree.Tree.branch 1676 (QuarticIntegerRepresentativeTree.Tree.branch 1674 (QuarticIntegerRepresentativeTree.Tree.branch 1673 (QuarticIntegerRepresentativeTree.Tree.leaf 1672 representative_1672) (QuarticIntegerRepresentativeTree.Tree.leaf 1673 representative_1673)) (QuarticIntegerRepresentativeTree.Tree.branch 1675 (QuarticIntegerRepresentativeTree.Tree.leaf 1674 representative_1674) (QuarticIntegerRepresentativeTree.Tree.leaf 1675 representative_1675))) (QuarticIntegerRepresentativeTree.Tree.branch 1678 (QuarticIntegerRepresentativeTree.Tree.branch 1677 (QuarticIntegerRepresentativeTree.Tree.leaf 1676 representative_1676) (QuarticIntegerRepresentativeTree.Tree.leaf 1677 representative_1677)) (QuarticIntegerRepresentativeTree.Tree.branch 1679 (QuarticIntegerRepresentativeTree.Tree.leaf 1678 representative_1678) (QuarticIntegerRepresentativeTree.Tree.leaf 1679 representative_1679))))) (QuarticIntegerRepresentativeTree.Tree.branch 1688 (QuarticIntegerRepresentativeTree.Tree.branch 1684 (QuarticIntegerRepresentativeTree.Tree.branch 1682 (QuarticIntegerRepresentativeTree.Tree.branch 1681 (QuarticIntegerRepresentativeTree.Tree.leaf 1680 representative_1680) (QuarticIntegerRepresentativeTree.Tree.leaf 1681 representative_1681)) (QuarticIntegerRepresentativeTree.Tree.branch 1683 (QuarticIntegerRepresentativeTree.Tree.leaf 1682 representative_1682) (QuarticIntegerRepresentativeTree.Tree.leaf 1683 representative_1683))) (QuarticIntegerRepresentativeTree.Tree.branch 1686 (QuarticIntegerRepresentativeTree.Tree.branch 1685 (QuarticIntegerRepresentativeTree.Tree.leaf 1684 representative_1684) (QuarticIntegerRepresentativeTree.Tree.leaf 1685 representative_1685)) (QuarticIntegerRepresentativeTree.Tree.branch 1687 (QuarticIntegerRepresentativeTree.Tree.leaf 1686 representative_1686) (QuarticIntegerRepresentativeTree.Tree.leaf 1687 representative_1687)))) (QuarticIntegerRepresentativeTree.Tree.branch 1692 (QuarticIntegerRepresentativeTree.Tree.branch 1690 (QuarticIntegerRepresentativeTree.Tree.branch 1689 (QuarticIntegerRepresentativeTree.Tree.leaf 1688 representative_1688) (QuarticIntegerRepresentativeTree.Tree.leaf 1689 representative_1689)) (QuarticIntegerRepresentativeTree.Tree.branch 1691 (QuarticIntegerRepresentativeTree.Tree.leaf 1690 representative_1690) (QuarticIntegerRepresentativeTree.Tree.leaf 1691 representative_1691))) (QuarticIntegerRepresentativeTree.Tree.branch 1694 (QuarticIntegerRepresentativeTree.Tree.branch 1693 (QuarticIntegerRepresentativeTree.Tree.leaf 1692 representative_1692) (QuarticIntegerRepresentativeTree.Tree.leaf 1693 representative_1693)) (QuarticIntegerRepresentativeTree.Tree.branch 1695 (QuarticIntegerRepresentativeTree.Tree.leaf 1694 representative_1694) (QuarticIntegerRepresentativeTree.Tree.leaf 1695 representative_1695)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1712 (QuarticIntegerRepresentativeTree.Tree.branch 1704 (QuarticIntegerRepresentativeTree.Tree.branch 1700 (QuarticIntegerRepresentativeTree.Tree.branch 1698 (QuarticIntegerRepresentativeTree.Tree.branch 1697 (QuarticIntegerRepresentativeTree.Tree.leaf 1696 representative_1696) (QuarticIntegerRepresentativeTree.Tree.leaf 1697 representative_1697)) (QuarticIntegerRepresentativeTree.Tree.branch 1699 (QuarticIntegerRepresentativeTree.Tree.leaf 1698 representative_1698) (QuarticIntegerRepresentativeTree.Tree.leaf 1699 representative_1699))) (QuarticIntegerRepresentativeTree.Tree.branch 1702 (QuarticIntegerRepresentativeTree.Tree.branch 1701 (QuarticIntegerRepresentativeTree.Tree.leaf 1700 representative_1700) (QuarticIntegerRepresentativeTree.Tree.leaf 1701 representative_1701)) (QuarticIntegerRepresentativeTree.Tree.branch 1703 (QuarticIntegerRepresentativeTree.Tree.leaf 1702 representative_1702) (QuarticIntegerRepresentativeTree.Tree.leaf 1703 representative_1703)))) (QuarticIntegerRepresentativeTree.Tree.branch 1708 (QuarticIntegerRepresentativeTree.Tree.branch 1706 (QuarticIntegerRepresentativeTree.Tree.branch 1705 (QuarticIntegerRepresentativeTree.Tree.leaf 1704 representative_1704) (QuarticIntegerRepresentativeTree.Tree.leaf 1705 representative_1705)) (QuarticIntegerRepresentativeTree.Tree.branch 1707 (QuarticIntegerRepresentativeTree.Tree.leaf 1706 representative_1706) (QuarticIntegerRepresentativeTree.Tree.leaf 1707 representative_1707))) (QuarticIntegerRepresentativeTree.Tree.branch 1710 (QuarticIntegerRepresentativeTree.Tree.branch 1709 (QuarticIntegerRepresentativeTree.Tree.leaf 1708 representative_1708) (QuarticIntegerRepresentativeTree.Tree.leaf 1709 representative_1709)) (QuarticIntegerRepresentativeTree.Tree.branch 1711 (QuarticIntegerRepresentativeTree.Tree.leaf 1710 representative_1710) (QuarticIntegerRepresentativeTree.Tree.leaf 1711 representative_1711))))) (QuarticIntegerRepresentativeTree.Tree.branch 1720 (QuarticIntegerRepresentativeTree.Tree.branch 1716 (QuarticIntegerRepresentativeTree.Tree.branch 1714 (QuarticIntegerRepresentativeTree.Tree.branch 1713 (QuarticIntegerRepresentativeTree.Tree.leaf 1712 representative_1712) (QuarticIntegerRepresentativeTree.Tree.leaf 1713 representative_1713)) (QuarticIntegerRepresentativeTree.Tree.branch 1715 (QuarticIntegerRepresentativeTree.Tree.leaf 1714 representative_1714) (QuarticIntegerRepresentativeTree.Tree.leaf 1715 representative_1715))) (QuarticIntegerRepresentativeTree.Tree.branch 1718 (QuarticIntegerRepresentativeTree.Tree.branch 1717 (QuarticIntegerRepresentativeTree.Tree.leaf 1716 representative_1716) (QuarticIntegerRepresentativeTree.Tree.leaf 1717 representative_1717)) (QuarticIntegerRepresentativeTree.Tree.branch 1719 (QuarticIntegerRepresentativeTree.Tree.leaf 1718 representative_1718) (QuarticIntegerRepresentativeTree.Tree.leaf 1719 representative_1719)))) (QuarticIntegerRepresentativeTree.Tree.branch 1724 (QuarticIntegerRepresentativeTree.Tree.branch 1722 (QuarticIntegerRepresentativeTree.Tree.branch 1721 (QuarticIntegerRepresentativeTree.Tree.leaf 1720 representative_1720) (QuarticIntegerRepresentativeTree.Tree.leaf 1721 representative_1721)) (QuarticIntegerRepresentativeTree.Tree.branch 1723 (QuarticIntegerRepresentativeTree.Tree.leaf 1722 representative_1722) (QuarticIntegerRepresentativeTree.Tree.leaf 1723 representative_1723))) (QuarticIntegerRepresentativeTree.Tree.branch 1726 (QuarticIntegerRepresentativeTree.Tree.branch 1725 (QuarticIntegerRepresentativeTree.Tree.leaf 1724 representative_1724) (QuarticIntegerRepresentativeTree.Tree.leaf 1725 representative_1725)) (QuarticIntegerRepresentativeTree.Tree.branch 1727 (QuarticIntegerRepresentativeTree.Tree.leaf 1726 representative_1726) (QuarticIntegerRepresentativeTree.Tree.leaf 1727 representative_1727)))))))
theorem accepted_026 : All validRep tree_026 := ⟨⟨⟨⟨⟨⟨coefficient_1664,coefficient_1665⟩,⟨coefficient_1666,coefficient_1667⟩⟩,⟨⟨coefficient_1668,coefficient_1669⟩,⟨coefficient_1670,coefficient_1671⟩⟩⟩,⟨⟨⟨coefficient_1672,coefficient_1673⟩,⟨coefficient_1674,coefficient_1675⟩⟩,⟨⟨coefficient_1676,coefficient_1677⟩,⟨coefficient_1678,coefficient_1679⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1680,coefficient_1681⟩,⟨coefficient_1682,coefficient_1683⟩⟩,⟨⟨coefficient_1684,coefficient_1685⟩,⟨coefficient_1686,coefficient_1687⟩⟩⟩,⟨⟨⟨coefficient_1688,coefficient_1689⟩,⟨coefficient_1690,coefficient_1691⟩⟩,⟨⟨coefficient_1692,coefficient_1693⟩,⟨coefficient_1694,coefficient_1695⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1696,coefficient_1697⟩,⟨coefficient_1698,coefficient_1699⟩⟩,⟨⟨coefficient_1700,coefficient_1701⟩,⟨coefficient_1702,coefficient_1703⟩⟩⟩,⟨⟨⟨coefficient_1704,coefficient_1705⟩,⟨coefficient_1706,coefficient_1707⟩⟩,⟨⟨coefficient_1708,coefficient_1709⟩,⟨coefficient_1710,coefficient_1711⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1712,coefficient_1713⟩,⟨coefficient_1714,coefficient_1715⟩⟩,⟨⟨coefficient_1716,coefficient_1717⟩,⟨coefficient_1718,coefficient_1719⟩⟩⟩,⟨⟨⟨coefficient_1720,coefficient_1721⟩,⟨coefficient_1722,coefficient_1723⟩⟩,⟨⟨coefficient_1724,coefficient_1725⟩,⟨coefficient_1726,coefficient_1727⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

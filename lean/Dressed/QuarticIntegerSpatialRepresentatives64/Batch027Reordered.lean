import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1728 : Rep := ⟨![0,9,2,40],198⟩
def representative_1729 : Rep := ⟨![0,9,2,41],288⟩
def representative_1730 : Rep := ⟨![0,9,2,43],462⟩
def representative_1731 : Rep := ⟨![0,9,2,44],462⟩
def representative_1732 : Rep := ⟨![0,9,2,45],462⟩
def representative_1733 : Rep := ⟨![0,9,2,46],462⟩
def representative_1734 : Rep := ⟨![0,9,2,47],273⟩
def representative_1735 : Rep := ⟨![0,9,2,48],350⟩
def representative_1736 : Rep := ⟨![0,9,2,49],106⟩
def representative_1737 : Rep := ⟨![0,9,2,51],137⟩
def representative_1738 : Rep := ⟨![0,9,2,52],462⟩
def representative_1739 : Rep := ⟨![0,9,2,53],462⟩
def representative_1740 : Rep := ⟨![0,9,2,54],278⟩
def representative_1741 : Rep := ⟨![0,9,2,55],146⟩
def representative_1742 : Rep := ⟨![0,9,2,56],50⟩
def representative_1743 : Rep := ⟨![0,9,2,57],421⟩
def representative_1744 : Rep := ⟨![0,9,2,59],382⟩
def representative_1745 : Rep := ⟨![0,9,2,60],137⟩
def representative_1746 : Rep := ⟨![0,9,2,61],273⟩
def representative_1747 : Rep := ⟨![0,9,2,62],146⟩
def representative_1748 : Rep := ⟨![0,9,2,63],381⟩
def representative_1749 : Rep := ⟨![0,9,3,10],413⟩
def representative_1750 : Rep := ⟨![0,9,3,12],295⟩
def representative_1751 : Rep := ⟨![0,9,3,13],227⟩
def representative_1752 : Rep := ⟨![0,9,3,14],295⟩
def representative_1753 : Rep := ⟨![0,9,3,17],407⟩
def representative_1754 : Rep := ⟨![0,9,3,18],120⟩
def representative_1755 : Rep := ⟨![0,9,3,20],226⟩
def representative_1756 : Rep := ⟨![0,9,3,21],462⟩
def representative_1757 : Rep := ⟨![0,9,3,22],228⟩
def representative_1758 : Rep := ⟨![0,9,3,23],319⟩
def representative_1759 : Rep := ⟨![0,9,3,24],308⟩
def representative_1760 : Rep := ⟨![0,9,3,25],145⟩
def representative_1761 : Rep := ⟨![0,9,3,26],306⟩
def representative_1762 : Rep := ⟨![0,9,3,28],462⟩
def representative_1763 : Rep := ⟨![0,9,3,29],462⟩
def representative_1764 : Rep := ⟨![0,9,3,30],462⟩
def representative_1765 : Rep := ⟨![0,9,3,31],225⟩
def representative_1766 : Rep := ⟨![0,9,3,32],230⟩
def representative_1767 : Rep := ⟨![0,9,3,33],278⟩
def representative_1768 : Rep := ⟨![0,9,3,34],232⟩
def representative_1769 : Rep := ⟨![0,9,3,36],462⟩
def representative_1770 : Rep := ⟨![0,9,3,37],462⟩
def representative_1771 : Rep := ⟨![0,9,3,38],462⟩
def representative_1772 : Rep := ⟨![0,9,3,39],462⟩
def representative_1773 : Rep := ⟨![0,9,3,40],261⟩
def representative_1774 : Rep := ⟨![0,9,3,41],233⟩
def representative_1775 : Rep := ⟨![0,9,3,42],462⟩
def representative_1776 : Rep := ⟨![0,9,3,44],462⟩
def representative_1777 : Rep := ⟨![0,9,3,45],462⟩
def representative_1778 : Rep := ⟨![0,9,3,46],462⟩
def representative_1779 : Rep := ⟨![0,9,3,47],236⟩
def representative_1780 : Rep := ⟨![0,9,3,48],196⟩
def representative_1781 : Rep := ⟨![0,9,3,49],295⟩
def representative_1782 : Rep := ⟨![0,9,3,50],224⟩
def representative_1783 : Rep := ⟨![0,9,3,52],234⟩
def representative_1784 : Rep := ⟨![0,9,3,53],462⟩
def representative_1785 : Rep := ⟨![0,9,3,54],235⟩
def representative_1786 : Rep := ⟨![0,9,3,55],278⟩
def representative_1787 : Rep := ⟨![0,9,3,56],366⟩
def representative_1788 : Rep := ⟨![0,9,3,58],323⟩
def representative_1789 : Rep := ⟨![0,9,3,60],278⟩
def representative_1790 : Rep := ⟨![0,9,3,61],231⟩
def representative_1791 : Rep := ⟨![0,9,3,62],278⟩
theorem coefficient_1728 : validRep representative_1728 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1728)=dictionary64.getD 198 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_198]
  decide +kernel
theorem coefficient_1729 : validRep representative_1729 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1729)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1730 : validRep representative_1730 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1730)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1731 : validRep representative_1731 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1731)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1732 : validRep representative_1732 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1732)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1733 : validRep representative_1733 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1733)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1734 : validRep representative_1734 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1734)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1735 : validRep representative_1735 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1735)=dictionary64.getD 350 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_350]
  decide +kernel
theorem coefficient_1736 : validRep representative_1736 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1736)=dictionary64.getD 106 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_106]
  decide +kernel
theorem coefficient_1737 : validRep representative_1737 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1737)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_1738 : validRep representative_1738 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1738)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1739 : validRep representative_1739 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1739)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1740 : validRep representative_1740 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1740)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1741 : validRep representative_1741 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1741)=dictionary64.getD 146 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_146]
  decide +kernel
theorem coefficient_1742 : validRep representative_1742 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1742)=dictionary64.getD 50 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_50]
  decide +kernel
theorem coefficient_1743 : validRep representative_1743 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1743)=dictionary64.getD 421 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_421]
  decide +kernel
theorem coefficient_1744 : validRep representative_1744 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1744)=dictionary64.getD 382 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_382]
  decide +kernel
theorem coefficient_1745 : validRep representative_1745 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1745)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_1746 : validRep representative_1746 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1746)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1747 : validRep representative_1747 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1747)=dictionary64.getD 146 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_146]
  decide +kernel
theorem coefficient_1748 : validRep representative_1748 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1748)=dictionary64.getD 381 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_381]
  decide +kernel
theorem coefficient_1749 : validRep representative_1749 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1749)=dictionary64.getD 413 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_413]
  decide +kernel
theorem coefficient_1750 : validRep representative_1750 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1750)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_1751 : validRep representative_1751 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1751)=dictionary64.getD 227 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_227]
  decide +kernel
theorem coefficient_1752 : validRep representative_1752 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1752)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_1753 : validRep representative_1753 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1753)=dictionary64.getD 407 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_407]
  decide +kernel
theorem coefficient_1754 : validRep representative_1754 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1754)=dictionary64.getD 120 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_120]
  decide +kernel
theorem coefficient_1755 : validRep representative_1755 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1755)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_1756 : validRep representative_1756 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1756)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1757 : validRep representative_1757 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1757)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1758 : validRep representative_1758 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1758)=dictionary64.getD 319 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_319]
  decide +kernel
theorem coefficient_1759 : validRep representative_1759 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1759)=dictionary64.getD 308 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_308]
  decide +kernel
theorem coefficient_1760 : validRep representative_1760 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1760)=dictionary64.getD 145 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_145]
  decide +kernel
theorem coefficient_1761 : validRep representative_1761 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1761)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1762 : validRep representative_1762 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1762)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1763 : validRep representative_1763 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1763)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1764 : validRep representative_1764 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1764)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1765 : validRep representative_1765 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1765)=dictionary64.getD 225 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_225]
  decide +kernel
theorem coefficient_1766 : validRep representative_1766 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1766)=dictionary64.getD 230 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_230]
  decide +kernel
theorem coefficient_1767 : validRep representative_1767 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1767)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1768 : validRep representative_1768 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1768)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1769 : validRep representative_1769 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1769)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1770 : validRep representative_1770 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1770)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1771 : validRep representative_1771 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1771)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1772 : validRep representative_1772 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1772)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1773 : validRep representative_1773 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1773)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_1774 : validRep representative_1774 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1774)=dictionary64.getD 233 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_233]
  decide +kernel
theorem coefficient_1775 : validRep representative_1775 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1775)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1776 : validRep representative_1776 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1776)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1777 : validRep representative_1777 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1777)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1778 : validRep representative_1778 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1778)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1779 : validRep representative_1779 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1779)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1780 : validRep representative_1780 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1780)=dictionary64.getD 196 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_196]
  decide +kernel
theorem coefficient_1781 : validRep representative_1781 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1781)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_1782 : validRep representative_1782 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1782)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_1783 : validRep representative_1783 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1783)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_1784 : validRep representative_1784 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1784)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1785 : validRep representative_1785 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1785)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1786 : validRep representative_1786 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1786)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1787 : validRep representative_1787 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1787)=dictionary64.getD 366 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_366]
  decide +kernel
theorem coefficient_1788 : validRep representative_1788 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1788)=dictionary64.getD 323 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_323]
  decide +kernel
theorem coefficient_1789 : validRep representative_1789 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1789)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1790 : validRep representative_1790 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1790)=dictionary64.getD 231 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_231]
  decide +kernel
theorem coefficient_1791 : validRep representative_1791 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1791)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
def tree_027 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1760 (QuarticIntegerRepresentativeTree.Tree.branch 1744 (QuarticIntegerRepresentativeTree.Tree.branch 1736 (QuarticIntegerRepresentativeTree.Tree.branch 1732 (QuarticIntegerRepresentativeTree.Tree.branch 1730 (QuarticIntegerRepresentativeTree.Tree.branch 1729 (QuarticIntegerRepresentativeTree.Tree.leaf 1728 representative_1728) (QuarticIntegerRepresentativeTree.Tree.leaf 1729 representative_1729)) (QuarticIntegerRepresentativeTree.Tree.branch 1731 (QuarticIntegerRepresentativeTree.Tree.leaf 1730 representative_1730) (QuarticIntegerRepresentativeTree.Tree.leaf 1731 representative_1731))) (QuarticIntegerRepresentativeTree.Tree.branch 1734 (QuarticIntegerRepresentativeTree.Tree.branch 1733 (QuarticIntegerRepresentativeTree.Tree.leaf 1732 representative_1732) (QuarticIntegerRepresentativeTree.Tree.leaf 1733 representative_1733)) (QuarticIntegerRepresentativeTree.Tree.branch 1735 (QuarticIntegerRepresentativeTree.Tree.leaf 1734 representative_1734) (QuarticIntegerRepresentativeTree.Tree.leaf 1735 representative_1735)))) (QuarticIntegerRepresentativeTree.Tree.branch 1740 (QuarticIntegerRepresentativeTree.Tree.branch 1738 (QuarticIntegerRepresentativeTree.Tree.branch 1737 (QuarticIntegerRepresentativeTree.Tree.leaf 1736 representative_1736) (QuarticIntegerRepresentativeTree.Tree.leaf 1737 representative_1737)) (QuarticIntegerRepresentativeTree.Tree.branch 1739 (QuarticIntegerRepresentativeTree.Tree.leaf 1738 representative_1738) (QuarticIntegerRepresentativeTree.Tree.leaf 1739 representative_1739))) (QuarticIntegerRepresentativeTree.Tree.branch 1742 (QuarticIntegerRepresentativeTree.Tree.branch 1741 (QuarticIntegerRepresentativeTree.Tree.leaf 1740 representative_1740) (QuarticIntegerRepresentativeTree.Tree.leaf 1741 representative_1741)) (QuarticIntegerRepresentativeTree.Tree.branch 1743 (QuarticIntegerRepresentativeTree.Tree.leaf 1742 representative_1742) (QuarticIntegerRepresentativeTree.Tree.leaf 1743 representative_1743))))) (QuarticIntegerRepresentativeTree.Tree.branch 1752 (QuarticIntegerRepresentativeTree.Tree.branch 1748 (QuarticIntegerRepresentativeTree.Tree.branch 1746 (QuarticIntegerRepresentativeTree.Tree.branch 1745 (QuarticIntegerRepresentativeTree.Tree.leaf 1744 representative_1744) (QuarticIntegerRepresentativeTree.Tree.leaf 1745 representative_1745)) (QuarticIntegerRepresentativeTree.Tree.branch 1747 (QuarticIntegerRepresentativeTree.Tree.leaf 1746 representative_1746) (QuarticIntegerRepresentativeTree.Tree.leaf 1747 representative_1747))) (QuarticIntegerRepresentativeTree.Tree.branch 1750 (QuarticIntegerRepresentativeTree.Tree.branch 1749 (QuarticIntegerRepresentativeTree.Tree.leaf 1748 representative_1748) (QuarticIntegerRepresentativeTree.Tree.leaf 1749 representative_1749)) (QuarticIntegerRepresentativeTree.Tree.branch 1751 (QuarticIntegerRepresentativeTree.Tree.leaf 1750 representative_1750) (QuarticIntegerRepresentativeTree.Tree.leaf 1751 representative_1751)))) (QuarticIntegerRepresentativeTree.Tree.branch 1756 (QuarticIntegerRepresentativeTree.Tree.branch 1754 (QuarticIntegerRepresentativeTree.Tree.branch 1753 (QuarticIntegerRepresentativeTree.Tree.leaf 1752 representative_1752) (QuarticIntegerRepresentativeTree.Tree.leaf 1753 representative_1753)) (QuarticIntegerRepresentativeTree.Tree.branch 1755 (QuarticIntegerRepresentativeTree.Tree.leaf 1754 representative_1754) (QuarticIntegerRepresentativeTree.Tree.leaf 1755 representative_1755))) (QuarticIntegerRepresentativeTree.Tree.branch 1758 (QuarticIntegerRepresentativeTree.Tree.branch 1757 (QuarticIntegerRepresentativeTree.Tree.leaf 1756 representative_1756) (QuarticIntegerRepresentativeTree.Tree.leaf 1757 representative_1757)) (QuarticIntegerRepresentativeTree.Tree.branch 1759 (QuarticIntegerRepresentativeTree.Tree.leaf 1758 representative_1758) (QuarticIntegerRepresentativeTree.Tree.leaf 1759 representative_1759)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1776 (QuarticIntegerRepresentativeTree.Tree.branch 1768 (QuarticIntegerRepresentativeTree.Tree.branch 1764 (QuarticIntegerRepresentativeTree.Tree.branch 1762 (QuarticIntegerRepresentativeTree.Tree.branch 1761 (QuarticIntegerRepresentativeTree.Tree.leaf 1760 representative_1760) (QuarticIntegerRepresentativeTree.Tree.leaf 1761 representative_1761)) (QuarticIntegerRepresentativeTree.Tree.branch 1763 (QuarticIntegerRepresentativeTree.Tree.leaf 1762 representative_1762) (QuarticIntegerRepresentativeTree.Tree.leaf 1763 representative_1763))) (QuarticIntegerRepresentativeTree.Tree.branch 1766 (QuarticIntegerRepresentativeTree.Tree.branch 1765 (QuarticIntegerRepresentativeTree.Tree.leaf 1764 representative_1764) (QuarticIntegerRepresentativeTree.Tree.leaf 1765 representative_1765)) (QuarticIntegerRepresentativeTree.Tree.branch 1767 (QuarticIntegerRepresentativeTree.Tree.leaf 1766 representative_1766) (QuarticIntegerRepresentativeTree.Tree.leaf 1767 representative_1767)))) (QuarticIntegerRepresentativeTree.Tree.branch 1772 (QuarticIntegerRepresentativeTree.Tree.branch 1770 (QuarticIntegerRepresentativeTree.Tree.branch 1769 (QuarticIntegerRepresentativeTree.Tree.leaf 1768 representative_1768) (QuarticIntegerRepresentativeTree.Tree.leaf 1769 representative_1769)) (QuarticIntegerRepresentativeTree.Tree.branch 1771 (QuarticIntegerRepresentativeTree.Tree.leaf 1770 representative_1770) (QuarticIntegerRepresentativeTree.Tree.leaf 1771 representative_1771))) (QuarticIntegerRepresentativeTree.Tree.branch 1774 (QuarticIntegerRepresentativeTree.Tree.branch 1773 (QuarticIntegerRepresentativeTree.Tree.leaf 1772 representative_1772) (QuarticIntegerRepresentativeTree.Tree.leaf 1773 representative_1773)) (QuarticIntegerRepresentativeTree.Tree.branch 1775 (QuarticIntegerRepresentativeTree.Tree.leaf 1774 representative_1774) (QuarticIntegerRepresentativeTree.Tree.leaf 1775 representative_1775))))) (QuarticIntegerRepresentativeTree.Tree.branch 1784 (QuarticIntegerRepresentativeTree.Tree.branch 1780 (QuarticIntegerRepresentativeTree.Tree.branch 1778 (QuarticIntegerRepresentativeTree.Tree.branch 1777 (QuarticIntegerRepresentativeTree.Tree.leaf 1776 representative_1776) (QuarticIntegerRepresentativeTree.Tree.leaf 1777 representative_1777)) (QuarticIntegerRepresentativeTree.Tree.branch 1779 (QuarticIntegerRepresentativeTree.Tree.leaf 1778 representative_1778) (QuarticIntegerRepresentativeTree.Tree.leaf 1779 representative_1779))) (QuarticIntegerRepresentativeTree.Tree.branch 1782 (QuarticIntegerRepresentativeTree.Tree.branch 1781 (QuarticIntegerRepresentativeTree.Tree.leaf 1780 representative_1780) (QuarticIntegerRepresentativeTree.Tree.leaf 1781 representative_1781)) (QuarticIntegerRepresentativeTree.Tree.branch 1783 (QuarticIntegerRepresentativeTree.Tree.leaf 1782 representative_1782) (QuarticIntegerRepresentativeTree.Tree.leaf 1783 representative_1783)))) (QuarticIntegerRepresentativeTree.Tree.branch 1788 (QuarticIntegerRepresentativeTree.Tree.branch 1786 (QuarticIntegerRepresentativeTree.Tree.branch 1785 (QuarticIntegerRepresentativeTree.Tree.leaf 1784 representative_1784) (QuarticIntegerRepresentativeTree.Tree.leaf 1785 representative_1785)) (QuarticIntegerRepresentativeTree.Tree.branch 1787 (QuarticIntegerRepresentativeTree.Tree.leaf 1786 representative_1786) (QuarticIntegerRepresentativeTree.Tree.leaf 1787 representative_1787))) (QuarticIntegerRepresentativeTree.Tree.branch 1790 (QuarticIntegerRepresentativeTree.Tree.branch 1789 (QuarticIntegerRepresentativeTree.Tree.leaf 1788 representative_1788) (QuarticIntegerRepresentativeTree.Tree.leaf 1789 representative_1789)) (QuarticIntegerRepresentativeTree.Tree.branch 1791 (QuarticIntegerRepresentativeTree.Tree.leaf 1790 representative_1790) (QuarticIntegerRepresentativeTree.Tree.leaf 1791 representative_1791)))))))
theorem accepted_027 : All validRep tree_027 := ⟨⟨⟨⟨⟨⟨coefficient_1728,coefficient_1729⟩,⟨coefficient_1730,coefficient_1731⟩⟩,⟨⟨coefficient_1732,coefficient_1733⟩,⟨coefficient_1734,coefficient_1735⟩⟩⟩,⟨⟨⟨coefficient_1736,coefficient_1737⟩,⟨coefficient_1738,coefficient_1739⟩⟩,⟨⟨coefficient_1740,coefficient_1741⟩,⟨coefficient_1742,coefficient_1743⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1744,coefficient_1745⟩,⟨coefficient_1746,coefficient_1747⟩⟩,⟨⟨coefficient_1748,coefficient_1749⟩,⟨coefficient_1750,coefficient_1751⟩⟩⟩,⟨⟨⟨coefficient_1752,coefficient_1753⟩,⟨coefficient_1754,coefficient_1755⟩⟩,⟨⟨coefficient_1756,coefficient_1757⟩,⟨coefficient_1758,coefficient_1759⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1760,coefficient_1761⟩,⟨coefficient_1762,coefficient_1763⟩⟩,⟨⟨coefficient_1764,coefficient_1765⟩,⟨coefficient_1766,coefficient_1767⟩⟩⟩,⟨⟨⟨coefficient_1768,coefficient_1769⟩,⟨coefficient_1770,coefficient_1771⟩⟩,⟨⟨coefficient_1772,coefficient_1773⟩,⟨coefficient_1774,coefficient_1775⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1776,coefficient_1777⟩,⟨coefficient_1778,coefficient_1779⟩⟩,⟨⟨coefficient_1780,coefficient_1781⟩,⟨coefficient_1782,coefficient_1783⟩⟩⟩,⟨⟨⟨coefficient_1784,coefficient_1785⟩,⟨coefficient_1786,coefficient_1787⟩⟩,⟨⟨coefficient_1788,coefficient_1789⟩,⟨coefficient_1790,coefficient_1791⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1792 : Rep := ⟨![0,9,3,63],175⟩
def representative_1793 : Rep := ⟨![0,9,4,10],156⟩
def representative_1794 : Rep := ⟨![0,9,4,11],288⟩
def representative_1795 : Rep := ⟨![0,9,4,13],462⟩
def representative_1796 : Rep := ⟨![0,9,4,17],162⟩
def representative_1797 : Rep := ⟨![0,9,4,18],288⟩
def representative_1798 : Rep := ⟨![0,9,4,19],232⟩
def representative_1799 : Rep := ⟨![0,9,4,21],462⟩
def representative_1800 : Rep := ⟨![0,9,4,22],462⟩
def representative_1801 : Rep := ⟨![0,9,4,23],228⟩
def representative_1802 : Rep := ⟨![0,9,4,25],273⟩
def representative_1803 : Rep := ⟨![0,9,4,26],232⟩
def representative_1804 : Rep := ⟨![0,9,4,27],462⟩
def representative_1805 : Rep := ⟨![0,9,4,29],462⟩
def representative_1806 : Rep := ⟨![0,9,4,30],462⟩
def representative_1807 : Rep := ⟨![0,9,4,31],462⟩
def representative_1808 : Rep := ⟨![0,9,4,32],462⟩
def representative_1809 : Rep := ⟨![0,9,4,33],236⟩
def representative_1810 : Rep := ⟨![0,9,4,34],462⟩
def representative_1811 : Rep := ⟨![0,9,4,35],462⟩
def representative_1812 : Rep := ⟨![0,9,4,37],462⟩
def representative_1813 : Rep := ⟨![0,9,4,38],462⟩
def representative_1814 : Rep := ⟨![0,9,4,39],462⟩
def representative_1815 : Rep := ⟨![0,9,4,40],238⟩
def representative_1816 : Rep := ⟨![0,9,4,41],462⟩
def representative_1817 : Rep := ⟨![0,9,4,42],462⟩
def representative_1818 : Rep := ⟨![0,9,4,43],462⟩
def representative_1819 : Rep := ⟨![0,9,4,45],462⟩
def representative_1820 : Rep := ⟨![0,9,4,46],462⟩
def representative_1821 : Rep := ⟨![0,9,4,47],462⟩
def representative_1822 : Rep := ⟨![0,9,4,48],261⟩
def representative_1823 : Rep := ⟨![0,9,4,50],462⟩
def representative_1824 : Rep := ⟨![0,9,4,51],462⟩
def representative_1825 : Rep := ⟨![0,9,4,53],462⟩
def representative_1826 : Rep := ⟨![0,9,4,54],462⟩
def representative_1827 : Rep := ⟨![0,9,4,55],235⟩
def representative_1828 : Rep := ⟨![0,9,4,56],189⟩
def representative_1829 : Rep := ⟨![0,9,4,58],220⟩
def representative_1830 : Rep := ⟨![0,9,4,59],462⟩
def representative_1831 : Rep := ⟨![0,9,4,61],462⟩
def representative_1832 : Rep := ⟨![0,9,4,62],235⟩
def representative_1833 : Rep := ⟨![0,9,4,63],273⟩
def representative_1834 : Rep := ⟨![0,9,5,10],278⟩
def representative_1835 : Rep := ⟨![0,9,5,11],233⟩
def representative_1836 : Rep := ⟨![0,9,5,12],462⟩
def representative_1837 : Rep := ⟨![0,9,5,17],278⟩
def representative_1838 : Rep := ⟨![0,9,5,18],235⟩
def representative_1839 : Rep := ⟨![0,9,5,19],462⟩
def representative_1840 : Rep := ⟨![0,9,5,20],462⟩
def representative_1841 : Rep := ⟨![0,9,5,22],235⟩
def representative_1842 : Rep := ⟨![0,9,5,23],278⟩
def representative_1843 : Rep := ⟨![0,9,5,25],236⟩
def representative_1844 : Rep := ⟨![0,9,5,26],462⟩
def representative_1845 : Rep := ⟨![0,9,5,27],462⟩
def representative_1846 : Rep := ⟨![0,9,5,28],462⟩
def representative_1847 : Rep := ⟨![0,9,5,30],462⟩
def representative_1848 : Rep := ⟨![0,9,5,31],236⟩
def representative_1849 : Rep := ⟨![0,9,5,33],462⟩
def representative_1850 : Rep := ⟨![0,9,5,34],462⟩
def representative_1851 : Rep := ⟨![0,9,5,35],462⟩
def representative_1852 : Rep := ⟨![0,9,5,36],462⟩
def representative_1853 : Rep := ⟨![0,9,5,38],462⟩
def representative_1854 : Rep := ⟨![0,9,5,39],462⟩
def representative_1855 : Rep := ⟨![0,9,5,40],261⟩
theorem coefficient_1792 : validRep representative_1792 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1792)=dictionary64.getD 175 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_175]
  decide +kernel
theorem coefficient_1793 : validRep representative_1793 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1793)=dictionary64.getD 156 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_156]
  decide +kernel
theorem coefficient_1794 : validRep representative_1794 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1794)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1795 : validRep representative_1795 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1795)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1796 : validRep representative_1796 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1796)=dictionary64.getD 162 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_162]
  decide +kernel
theorem coefficient_1797 : validRep representative_1797 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1797)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1798 : validRep representative_1798 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1798)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1799 : validRep representative_1799 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1799)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1800 : validRep representative_1800 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1800)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1801 : validRep representative_1801 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1801)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1802 : validRep representative_1802 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1802)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1803 : validRep representative_1803 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1803)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1804 : validRep representative_1804 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1804)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1805 : validRep representative_1805 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1805)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1806 : validRep representative_1806 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1806)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1807 : validRep representative_1807 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1807)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1808 : validRep representative_1808 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1808)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1809 : validRep representative_1809 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1809)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1810 : validRep representative_1810 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1810)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1811 : validRep representative_1811 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1811)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1812 : validRep representative_1812 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1812)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1813 : validRep representative_1813 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1813)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1814 : validRep representative_1814 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1814)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1815 : validRep representative_1815 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1815)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_1816 : validRep representative_1816 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1816)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1817 : validRep representative_1817 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1817)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1818 : validRep representative_1818 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1818)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1819 : validRep representative_1819 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1819)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1820 : validRep representative_1820 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1820)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1821 : validRep representative_1821 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1821)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1822 : validRep representative_1822 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1822)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_1823 : validRep representative_1823 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1823)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1824 : validRep representative_1824 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1824)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1825 : validRep representative_1825 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1825)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1826 : validRep representative_1826 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1826)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1827 : validRep representative_1827 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1827)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1828 : validRep representative_1828 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1828)=dictionary64.getD 189 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_189]
  decide +kernel
theorem coefficient_1829 : validRep representative_1829 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1829)=dictionary64.getD 220 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_220]
  decide +kernel
theorem coefficient_1830 : validRep representative_1830 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1830)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1831 : validRep representative_1831 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1831)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1832 : validRep representative_1832 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1832)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1833 : validRep representative_1833 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1833)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1834 : validRep representative_1834 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1834)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1835 : validRep representative_1835 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1835)=dictionary64.getD 233 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_233]
  decide +kernel
theorem coefficient_1836 : validRep representative_1836 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1836)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1837 : validRep representative_1837 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1837)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1838 : validRep representative_1838 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1838)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1839 : validRep representative_1839 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1839)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1840 : validRep representative_1840 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1840)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1841 : validRep representative_1841 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1841)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1842 : validRep representative_1842 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1842)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1843 : validRep representative_1843 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1843)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1844 : validRep representative_1844 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1844)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1845 : validRep representative_1845 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1845)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1846 : validRep representative_1846 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1846)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1847 : validRep representative_1847 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1847)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1848 : validRep representative_1848 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1848)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1849 : validRep representative_1849 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1849)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1850 : validRep representative_1850 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1850)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1851 : validRep representative_1851 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1851)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1852 : validRep representative_1852 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1852)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1853 : validRep representative_1853 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1853)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1854 : validRep representative_1854 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1854)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1855 : validRep representative_1855 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1855)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
def tree_028 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1824 (QuarticIntegerRepresentativeTree.Tree.branch 1808 (QuarticIntegerRepresentativeTree.Tree.branch 1800 (QuarticIntegerRepresentativeTree.Tree.branch 1796 (QuarticIntegerRepresentativeTree.Tree.branch 1794 (QuarticIntegerRepresentativeTree.Tree.branch 1793 (QuarticIntegerRepresentativeTree.Tree.leaf 1792 representative_1792) (QuarticIntegerRepresentativeTree.Tree.leaf 1793 representative_1793)) (QuarticIntegerRepresentativeTree.Tree.branch 1795 (QuarticIntegerRepresentativeTree.Tree.leaf 1794 representative_1794) (QuarticIntegerRepresentativeTree.Tree.leaf 1795 representative_1795))) (QuarticIntegerRepresentativeTree.Tree.branch 1798 (QuarticIntegerRepresentativeTree.Tree.branch 1797 (QuarticIntegerRepresentativeTree.Tree.leaf 1796 representative_1796) (QuarticIntegerRepresentativeTree.Tree.leaf 1797 representative_1797)) (QuarticIntegerRepresentativeTree.Tree.branch 1799 (QuarticIntegerRepresentativeTree.Tree.leaf 1798 representative_1798) (QuarticIntegerRepresentativeTree.Tree.leaf 1799 representative_1799)))) (QuarticIntegerRepresentativeTree.Tree.branch 1804 (QuarticIntegerRepresentativeTree.Tree.branch 1802 (QuarticIntegerRepresentativeTree.Tree.branch 1801 (QuarticIntegerRepresentativeTree.Tree.leaf 1800 representative_1800) (QuarticIntegerRepresentativeTree.Tree.leaf 1801 representative_1801)) (QuarticIntegerRepresentativeTree.Tree.branch 1803 (QuarticIntegerRepresentativeTree.Tree.leaf 1802 representative_1802) (QuarticIntegerRepresentativeTree.Tree.leaf 1803 representative_1803))) (QuarticIntegerRepresentativeTree.Tree.branch 1806 (QuarticIntegerRepresentativeTree.Tree.branch 1805 (QuarticIntegerRepresentativeTree.Tree.leaf 1804 representative_1804) (QuarticIntegerRepresentativeTree.Tree.leaf 1805 representative_1805)) (QuarticIntegerRepresentativeTree.Tree.branch 1807 (QuarticIntegerRepresentativeTree.Tree.leaf 1806 representative_1806) (QuarticIntegerRepresentativeTree.Tree.leaf 1807 representative_1807))))) (QuarticIntegerRepresentativeTree.Tree.branch 1816 (QuarticIntegerRepresentativeTree.Tree.branch 1812 (QuarticIntegerRepresentativeTree.Tree.branch 1810 (QuarticIntegerRepresentativeTree.Tree.branch 1809 (QuarticIntegerRepresentativeTree.Tree.leaf 1808 representative_1808) (QuarticIntegerRepresentativeTree.Tree.leaf 1809 representative_1809)) (QuarticIntegerRepresentativeTree.Tree.branch 1811 (QuarticIntegerRepresentativeTree.Tree.leaf 1810 representative_1810) (QuarticIntegerRepresentativeTree.Tree.leaf 1811 representative_1811))) (QuarticIntegerRepresentativeTree.Tree.branch 1814 (QuarticIntegerRepresentativeTree.Tree.branch 1813 (QuarticIntegerRepresentativeTree.Tree.leaf 1812 representative_1812) (QuarticIntegerRepresentativeTree.Tree.leaf 1813 representative_1813)) (QuarticIntegerRepresentativeTree.Tree.branch 1815 (QuarticIntegerRepresentativeTree.Tree.leaf 1814 representative_1814) (QuarticIntegerRepresentativeTree.Tree.leaf 1815 representative_1815)))) (QuarticIntegerRepresentativeTree.Tree.branch 1820 (QuarticIntegerRepresentativeTree.Tree.branch 1818 (QuarticIntegerRepresentativeTree.Tree.branch 1817 (QuarticIntegerRepresentativeTree.Tree.leaf 1816 representative_1816) (QuarticIntegerRepresentativeTree.Tree.leaf 1817 representative_1817)) (QuarticIntegerRepresentativeTree.Tree.branch 1819 (QuarticIntegerRepresentativeTree.Tree.leaf 1818 representative_1818) (QuarticIntegerRepresentativeTree.Tree.leaf 1819 representative_1819))) (QuarticIntegerRepresentativeTree.Tree.branch 1822 (QuarticIntegerRepresentativeTree.Tree.branch 1821 (QuarticIntegerRepresentativeTree.Tree.leaf 1820 representative_1820) (QuarticIntegerRepresentativeTree.Tree.leaf 1821 representative_1821)) (QuarticIntegerRepresentativeTree.Tree.branch 1823 (QuarticIntegerRepresentativeTree.Tree.leaf 1822 representative_1822) (QuarticIntegerRepresentativeTree.Tree.leaf 1823 representative_1823)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1840 (QuarticIntegerRepresentativeTree.Tree.branch 1832 (QuarticIntegerRepresentativeTree.Tree.branch 1828 (QuarticIntegerRepresentativeTree.Tree.branch 1826 (QuarticIntegerRepresentativeTree.Tree.branch 1825 (QuarticIntegerRepresentativeTree.Tree.leaf 1824 representative_1824) (QuarticIntegerRepresentativeTree.Tree.leaf 1825 representative_1825)) (QuarticIntegerRepresentativeTree.Tree.branch 1827 (QuarticIntegerRepresentativeTree.Tree.leaf 1826 representative_1826) (QuarticIntegerRepresentativeTree.Tree.leaf 1827 representative_1827))) (QuarticIntegerRepresentativeTree.Tree.branch 1830 (QuarticIntegerRepresentativeTree.Tree.branch 1829 (QuarticIntegerRepresentativeTree.Tree.leaf 1828 representative_1828) (QuarticIntegerRepresentativeTree.Tree.leaf 1829 representative_1829)) (QuarticIntegerRepresentativeTree.Tree.branch 1831 (QuarticIntegerRepresentativeTree.Tree.leaf 1830 representative_1830) (QuarticIntegerRepresentativeTree.Tree.leaf 1831 representative_1831)))) (QuarticIntegerRepresentativeTree.Tree.branch 1836 (QuarticIntegerRepresentativeTree.Tree.branch 1834 (QuarticIntegerRepresentativeTree.Tree.branch 1833 (QuarticIntegerRepresentativeTree.Tree.leaf 1832 representative_1832) (QuarticIntegerRepresentativeTree.Tree.leaf 1833 representative_1833)) (QuarticIntegerRepresentativeTree.Tree.branch 1835 (QuarticIntegerRepresentativeTree.Tree.leaf 1834 representative_1834) (QuarticIntegerRepresentativeTree.Tree.leaf 1835 representative_1835))) (QuarticIntegerRepresentativeTree.Tree.branch 1838 (QuarticIntegerRepresentativeTree.Tree.branch 1837 (QuarticIntegerRepresentativeTree.Tree.leaf 1836 representative_1836) (QuarticIntegerRepresentativeTree.Tree.leaf 1837 representative_1837)) (QuarticIntegerRepresentativeTree.Tree.branch 1839 (QuarticIntegerRepresentativeTree.Tree.leaf 1838 representative_1838) (QuarticIntegerRepresentativeTree.Tree.leaf 1839 representative_1839))))) (QuarticIntegerRepresentativeTree.Tree.branch 1848 (QuarticIntegerRepresentativeTree.Tree.branch 1844 (QuarticIntegerRepresentativeTree.Tree.branch 1842 (QuarticIntegerRepresentativeTree.Tree.branch 1841 (QuarticIntegerRepresentativeTree.Tree.leaf 1840 representative_1840) (QuarticIntegerRepresentativeTree.Tree.leaf 1841 representative_1841)) (QuarticIntegerRepresentativeTree.Tree.branch 1843 (QuarticIntegerRepresentativeTree.Tree.leaf 1842 representative_1842) (QuarticIntegerRepresentativeTree.Tree.leaf 1843 representative_1843))) (QuarticIntegerRepresentativeTree.Tree.branch 1846 (QuarticIntegerRepresentativeTree.Tree.branch 1845 (QuarticIntegerRepresentativeTree.Tree.leaf 1844 representative_1844) (QuarticIntegerRepresentativeTree.Tree.leaf 1845 representative_1845)) (QuarticIntegerRepresentativeTree.Tree.branch 1847 (QuarticIntegerRepresentativeTree.Tree.leaf 1846 representative_1846) (QuarticIntegerRepresentativeTree.Tree.leaf 1847 representative_1847)))) (QuarticIntegerRepresentativeTree.Tree.branch 1852 (QuarticIntegerRepresentativeTree.Tree.branch 1850 (QuarticIntegerRepresentativeTree.Tree.branch 1849 (QuarticIntegerRepresentativeTree.Tree.leaf 1848 representative_1848) (QuarticIntegerRepresentativeTree.Tree.leaf 1849 representative_1849)) (QuarticIntegerRepresentativeTree.Tree.branch 1851 (QuarticIntegerRepresentativeTree.Tree.leaf 1850 representative_1850) (QuarticIntegerRepresentativeTree.Tree.leaf 1851 representative_1851))) (QuarticIntegerRepresentativeTree.Tree.branch 1854 (QuarticIntegerRepresentativeTree.Tree.branch 1853 (QuarticIntegerRepresentativeTree.Tree.leaf 1852 representative_1852) (QuarticIntegerRepresentativeTree.Tree.leaf 1853 representative_1853)) (QuarticIntegerRepresentativeTree.Tree.branch 1855 (QuarticIntegerRepresentativeTree.Tree.leaf 1854 representative_1854) (QuarticIntegerRepresentativeTree.Tree.leaf 1855 representative_1855)))))))
theorem accepted_028 : All validRep tree_028 := ⟨⟨⟨⟨⟨⟨coefficient_1792,coefficient_1793⟩,⟨coefficient_1794,coefficient_1795⟩⟩,⟨⟨coefficient_1796,coefficient_1797⟩,⟨coefficient_1798,coefficient_1799⟩⟩⟩,⟨⟨⟨coefficient_1800,coefficient_1801⟩,⟨coefficient_1802,coefficient_1803⟩⟩,⟨⟨coefficient_1804,coefficient_1805⟩,⟨coefficient_1806,coefficient_1807⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1808,coefficient_1809⟩,⟨coefficient_1810,coefficient_1811⟩⟩,⟨⟨coefficient_1812,coefficient_1813⟩,⟨coefficient_1814,coefficient_1815⟩⟩⟩,⟨⟨⟨coefficient_1816,coefficient_1817⟩,⟨coefficient_1818,coefficient_1819⟩⟩,⟨⟨coefficient_1820,coefficient_1821⟩,⟨coefficient_1822,coefficient_1823⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1824,coefficient_1825⟩,⟨coefficient_1826,coefficient_1827⟩⟩,⟨⟨coefficient_1828,coefficient_1829⟩,⟨coefficient_1830,coefficient_1831⟩⟩⟩,⟨⟨⟨coefficient_1832,coefficient_1833⟩,⟨coefficient_1834,coefficient_1835⟩⟩,⟨⟨coefficient_1836,coefficient_1837⟩,⟨coefficient_1838,coefficient_1839⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1840,coefficient_1841⟩,⟨coefficient_1842,coefficient_1843⟩⟩,⟨⟨coefficient_1844,coefficient_1845⟩,⟨coefficient_1846,coefficient_1847⟩⟩⟩,⟨⟨⟨coefficient_1848,coefficient_1849⟩,⟨coefficient_1850,coefficient_1851⟩⟩,⟨⟨coefficient_1852,coefficient_1853⟩,⟨coefficient_1854,coefficient_1855⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

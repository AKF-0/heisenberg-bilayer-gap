import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1856 : Rep := ⟨![0,9,5,42],462⟩
def representative_1857 : Rep := ⟨![0,9,5,43],462⟩
def representative_1858 : Rep := ⟨![0,9,5,44],462⟩
def representative_1859 : Rep := ⟨![0,9,5,46],462⟩
def representative_1860 : Rep := ⟨![0,9,5,47],236⟩
def representative_1861 : Rep := ⟨![0,9,5,48],198⟩
def representative_1862 : Rep := ⟨![0,9,5,50],235⟩
def representative_1863 : Rep := ⟨![0,9,5,51],462⟩
def representative_1864 : Rep := ⟨![0,9,5,52],462⟩
def representative_1865 : Rep := ⟨![0,9,5,54],235⟩
def representative_1866 : Rep := ⟨![0,9,5,55],278⟩
def representative_1867 : Rep := ⟨![0,9,5,56],365⟩
def representative_1868 : Rep := ⟨![0,9,5,58],278⟩
def representative_1869 : Rep := ⟨![0,9,5,59],236⟩
def representative_1870 : Rep := ⟨![0,9,5,60],462⟩
def representative_1871 : Rep := ⟨![0,9,5,63],175⟩
def representative_1872 : Rep := ⟨![0,9,6,10],126⟩
def representative_1873 : Rep := ⟨![0,9,6,11],288⟩
def representative_1874 : Rep := ⟨![0,9,6,17],126⟩
def representative_1875 : Rep := ⟨![0,9,6,18],300⟩
def representative_1876 : Rep := ⟨![0,9,6,19],232⟩
def representative_1877 : Rep := ⟨![0,9,6,20],462⟩
def representative_1878 : Rep := ⟨![0,9,6,21],235⟩
def representative_1879 : Rep := ⟨![0,9,6,23],141⟩
def representative_1880 : Rep := ⟨![0,9,6,25],288⟩
def representative_1881 : Rep := ⟨![0,9,6,26],232⟩
def representative_1882 : Rep := ⟨![0,9,6,27],462⟩
def representative_1883 : Rep := ⟨![0,9,6,28],462⟩
def representative_1884 : Rep := ⟨![0,9,6,29],462⟩
def representative_1885 : Rep := ⟨![0,9,6,31],273⟩
def representative_1886 : Rep := ⟨![0,9,6,34],462⟩
def representative_1887 : Rep := ⟨![0,9,6,35],462⟩
def representative_1888 : Rep := ⟨![0,9,6,36],462⟩
def representative_1889 : Rep := ⟨![0,9,6,37],462⟩
def representative_1890 : Rep := ⟨![0,9,6,39],462⟩
def representative_1891 : Rep := ⟨![0,9,6,42],462⟩
def representative_1892 : Rep := ⟨![0,9,6,43],462⟩
def representative_1893 : Rep := ⟨![0,9,6,44],462⟩
def representative_1894 : Rep := ⟨![0,9,6,45],462⟩
def representative_1895 : Rep := ⟨![0,9,6,47],273⟩
def representative_1896 : Rep := ⟨![0,9,6,48],347⟩
def representative_1897 : Rep := ⟨![0,9,6,50],278⟩
def representative_1898 : Rep := ⟨![0,9,6,51],462⟩
def representative_1899 : Rep := ⟨![0,9,6,52],462⟩
def representative_1900 : Rep := ⟨![0,9,6,53],235⟩
def representative_1901 : Rep := ⟨![0,9,6,55],144⟩
def representative_1902 : Rep := ⟨![0,9,6,56],52⟩
def representative_1903 : Rep := ⟨![0,9,6,58],143⟩
def representative_1904 : Rep := ⟨![0,9,6,59],273⟩
def representative_1905 : Rep := ⟨![0,9,6,60],235⟩
def representative_1906 : Rep := ⟨![0,9,6,61],288⟩
def representative_1907 : Rep := ⟨![0,9,7,10],422⟩
def representative_1908 : Rep := ⟨![0,9,7,17],422⟩
def representative_1909 : Rep := ⟨![0,9,7,18],100⟩
def representative_1910 : Rep := ⟨![0,9,7,19],306⟩
def representative_1911 : Rep := ⟨![0,9,7,20],232⟩
def representative_1912 : Rep := ⟨![0,9,7,21],462⟩
def representative_1913 : Rep := ⟨![0,9,7,22],134⟩
def representative_1914 : Rep := ⟨![0,9,7,26],306⟩
def representative_1915 : Rep := ⟨![0,9,7,27],228⟩
def representative_1916 : Rep := ⟨![0,9,7,28],462⟩
def representative_1917 : Rep := ⟨![0,9,7,29],462⟩
def representative_1918 : Rep := ⟨![0,9,7,30],462⟩
def representative_1919 : Rep := ⟨![0,9,7,34],232⟩
theorem coefficient_1856 : validRep representative_1856 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1856)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1857 : validRep representative_1857 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1857)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1858 : validRep representative_1858 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1858)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1859 : validRep representative_1859 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1859)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1860 : validRep representative_1860 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1860)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1861 : validRep representative_1861 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1861)=dictionary64.getD 198 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_198]
  decide +kernel
theorem coefficient_1862 : validRep representative_1862 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1862)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1863 : validRep representative_1863 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1863)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1864 : validRep representative_1864 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1864)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1865 : validRep representative_1865 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1865)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1866 : validRep representative_1866 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1866)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1867 : validRep representative_1867 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1867)=dictionary64.getD 365 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_365]
  decide +kernel
theorem coefficient_1868 : validRep representative_1868 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1868)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1869 : validRep representative_1869 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1869)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_1870 : validRep representative_1870 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1870)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1871 : validRep representative_1871 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1871)=dictionary64.getD 175 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_175]
  decide +kernel
theorem coefficient_1872 : validRep representative_1872 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1872)=dictionary64.getD 126 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_126]
  decide +kernel
theorem coefficient_1873 : validRep representative_1873 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1873)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1874 : validRep representative_1874 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1874)=dictionary64.getD 126 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_126]
  decide +kernel
theorem coefficient_1875 : validRep representative_1875 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1875)=dictionary64.getD 300 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_300]
  decide +kernel
theorem coefficient_1876 : validRep representative_1876 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1876)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1877 : validRep representative_1877 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1877)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1878 : validRep representative_1878 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1878)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1879 : validRep representative_1879 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1879)=dictionary64.getD 141 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_141]
  decide +kernel
theorem coefficient_1880 : validRep representative_1880 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1880)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1881 : validRep representative_1881 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1881)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1882 : validRep representative_1882 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1882)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1883 : validRep representative_1883 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1883)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1884 : validRep representative_1884 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1884)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1885 : validRep representative_1885 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1885)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1886 : validRep representative_1886 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1886)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1887 : validRep representative_1887 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1887)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1888 : validRep representative_1888 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1888)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1889 : validRep representative_1889 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1889)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1890 : validRep representative_1890 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1890)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1891 : validRep representative_1891 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1891)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1892 : validRep representative_1892 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1892)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1893 : validRep representative_1893 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1893)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1894 : validRep representative_1894 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1894)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1895 : validRep representative_1895 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1895)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1896 : validRep representative_1896 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1896)=dictionary64.getD 347 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_347]
  decide +kernel
theorem coefficient_1897 : validRep representative_1897 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1897)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_1898 : validRep representative_1898 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1898)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1899 : validRep representative_1899 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1899)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1900 : validRep representative_1900 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1900)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1901 : validRep representative_1901 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1901)=dictionary64.getD 144 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_144]
  decide +kernel
theorem coefficient_1902 : validRep representative_1902 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1902)=dictionary64.getD 52 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_52]
  decide +kernel
theorem coefficient_1903 : validRep representative_1903 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1903)=dictionary64.getD 143 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_143]
  decide +kernel
theorem coefficient_1904 : validRep representative_1904 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1904)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_1905 : validRep representative_1905 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1905)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_1906 : validRep representative_1906 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1906)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_1907 : validRep representative_1907 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1907)=dictionary64.getD 422 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_422]
  decide +kernel
theorem coefficient_1908 : validRep representative_1908 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1908)=dictionary64.getD 422 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_422]
  decide +kernel
theorem coefficient_1909 : validRep representative_1909 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1909)=dictionary64.getD 100 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_100]
  decide +kernel
theorem coefficient_1910 : validRep representative_1910 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1910)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1911 : validRep representative_1911 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1911)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1912 : validRep representative_1912 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1912)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1913 : validRep representative_1913 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1913)=dictionary64.getD 134 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_134]
  decide +kernel
theorem coefficient_1914 : validRep representative_1914 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1914)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1915 : validRep representative_1915 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1915)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1916 : validRep representative_1916 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1916)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1917 : validRep representative_1917 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1917)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1918 : validRep representative_1918 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1918)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1919 : validRep representative_1919 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1919)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
def tree_029 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1888 (QuarticIntegerRepresentativeTree.Tree.branch 1872 (QuarticIntegerRepresentativeTree.Tree.branch 1864 (QuarticIntegerRepresentativeTree.Tree.branch 1860 (QuarticIntegerRepresentativeTree.Tree.branch 1858 (QuarticIntegerRepresentativeTree.Tree.branch 1857 (QuarticIntegerRepresentativeTree.Tree.leaf 1856 representative_1856) (QuarticIntegerRepresentativeTree.Tree.leaf 1857 representative_1857)) (QuarticIntegerRepresentativeTree.Tree.branch 1859 (QuarticIntegerRepresentativeTree.Tree.leaf 1858 representative_1858) (QuarticIntegerRepresentativeTree.Tree.leaf 1859 representative_1859))) (QuarticIntegerRepresentativeTree.Tree.branch 1862 (QuarticIntegerRepresentativeTree.Tree.branch 1861 (QuarticIntegerRepresentativeTree.Tree.leaf 1860 representative_1860) (QuarticIntegerRepresentativeTree.Tree.leaf 1861 representative_1861)) (QuarticIntegerRepresentativeTree.Tree.branch 1863 (QuarticIntegerRepresentativeTree.Tree.leaf 1862 representative_1862) (QuarticIntegerRepresentativeTree.Tree.leaf 1863 representative_1863)))) (QuarticIntegerRepresentativeTree.Tree.branch 1868 (QuarticIntegerRepresentativeTree.Tree.branch 1866 (QuarticIntegerRepresentativeTree.Tree.branch 1865 (QuarticIntegerRepresentativeTree.Tree.leaf 1864 representative_1864) (QuarticIntegerRepresentativeTree.Tree.leaf 1865 representative_1865)) (QuarticIntegerRepresentativeTree.Tree.branch 1867 (QuarticIntegerRepresentativeTree.Tree.leaf 1866 representative_1866) (QuarticIntegerRepresentativeTree.Tree.leaf 1867 representative_1867))) (QuarticIntegerRepresentativeTree.Tree.branch 1870 (QuarticIntegerRepresentativeTree.Tree.branch 1869 (QuarticIntegerRepresentativeTree.Tree.leaf 1868 representative_1868) (QuarticIntegerRepresentativeTree.Tree.leaf 1869 representative_1869)) (QuarticIntegerRepresentativeTree.Tree.branch 1871 (QuarticIntegerRepresentativeTree.Tree.leaf 1870 representative_1870) (QuarticIntegerRepresentativeTree.Tree.leaf 1871 representative_1871))))) (QuarticIntegerRepresentativeTree.Tree.branch 1880 (QuarticIntegerRepresentativeTree.Tree.branch 1876 (QuarticIntegerRepresentativeTree.Tree.branch 1874 (QuarticIntegerRepresentativeTree.Tree.branch 1873 (QuarticIntegerRepresentativeTree.Tree.leaf 1872 representative_1872) (QuarticIntegerRepresentativeTree.Tree.leaf 1873 representative_1873)) (QuarticIntegerRepresentativeTree.Tree.branch 1875 (QuarticIntegerRepresentativeTree.Tree.leaf 1874 representative_1874) (QuarticIntegerRepresentativeTree.Tree.leaf 1875 representative_1875))) (QuarticIntegerRepresentativeTree.Tree.branch 1878 (QuarticIntegerRepresentativeTree.Tree.branch 1877 (QuarticIntegerRepresentativeTree.Tree.leaf 1876 representative_1876) (QuarticIntegerRepresentativeTree.Tree.leaf 1877 representative_1877)) (QuarticIntegerRepresentativeTree.Tree.branch 1879 (QuarticIntegerRepresentativeTree.Tree.leaf 1878 representative_1878) (QuarticIntegerRepresentativeTree.Tree.leaf 1879 representative_1879)))) (QuarticIntegerRepresentativeTree.Tree.branch 1884 (QuarticIntegerRepresentativeTree.Tree.branch 1882 (QuarticIntegerRepresentativeTree.Tree.branch 1881 (QuarticIntegerRepresentativeTree.Tree.leaf 1880 representative_1880) (QuarticIntegerRepresentativeTree.Tree.leaf 1881 representative_1881)) (QuarticIntegerRepresentativeTree.Tree.branch 1883 (QuarticIntegerRepresentativeTree.Tree.leaf 1882 representative_1882) (QuarticIntegerRepresentativeTree.Tree.leaf 1883 representative_1883))) (QuarticIntegerRepresentativeTree.Tree.branch 1886 (QuarticIntegerRepresentativeTree.Tree.branch 1885 (QuarticIntegerRepresentativeTree.Tree.leaf 1884 representative_1884) (QuarticIntegerRepresentativeTree.Tree.leaf 1885 representative_1885)) (QuarticIntegerRepresentativeTree.Tree.branch 1887 (QuarticIntegerRepresentativeTree.Tree.leaf 1886 representative_1886) (QuarticIntegerRepresentativeTree.Tree.leaf 1887 representative_1887)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1904 (QuarticIntegerRepresentativeTree.Tree.branch 1896 (QuarticIntegerRepresentativeTree.Tree.branch 1892 (QuarticIntegerRepresentativeTree.Tree.branch 1890 (QuarticIntegerRepresentativeTree.Tree.branch 1889 (QuarticIntegerRepresentativeTree.Tree.leaf 1888 representative_1888) (QuarticIntegerRepresentativeTree.Tree.leaf 1889 representative_1889)) (QuarticIntegerRepresentativeTree.Tree.branch 1891 (QuarticIntegerRepresentativeTree.Tree.leaf 1890 representative_1890) (QuarticIntegerRepresentativeTree.Tree.leaf 1891 representative_1891))) (QuarticIntegerRepresentativeTree.Tree.branch 1894 (QuarticIntegerRepresentativeTree.Tree.branch 1893 (QuarticIntegerRepresentativeTree.Tree.leaf 1892 representative_1892) (QuarticIntegerRepresentativeTree.Tree.leaf 1893 representative_1893)) (QuarticIntegerRepresentativeTree.Tree.branch 1895 (QuarticIntegerRepresentativeTree.Tree.leaf 1894 representative_1894) (QuarticIntegerRepresentativeTree.Tree.leaf 1895 representative_1895)))) (QuarticIntegerRepresentativeTree.Tree.branch 1900 (QuarticIntegerRepresentativeTree.Tree.branch 1898 (QuarticIntegerRepresentativeTree.Tree.branch 1897 (QuarticIntegerRepresentativeTree.Tree.leaf 1896 representative_1896) (QuarticIntegerRepresentativeTree.Tree.leaf 1897 representative_1897)) (QuarticIntegerRepresentativeTree.Tree.branch 1899 (QuarticIntegerRepresentativeTree.Tree.leaf 1898 representative_1898) (QuarticIntegerRepresentativeTree.Tree.leaf 1899 representative_1899))) (QuarticIntegerRepresentativeTree.Tree.branch 1902 (QuarticIntegerRepresentativeTree.Tree.branch 1901 (QuarticIntegerRepresentativeTree.Tree.leaf 1900 representative_1900) (QuarticIntegerRepresentativeTree.Tree.leaf 1901 representative_1901)) (QuarticIntegerRepresentativeTree.Tree.branch 1903 (QuarticIntegerRepresentativeTree.Tree.leaf 1902 representative_1902) (QuarticIntegerRepresentativeTree.Tree.leaf 1903 representative_1903))))) (QuarticIntegerRepresentativeTree.Tree.branch 1912 (QuarticIntegerRepresentativeTree.Tree.branch 1908 (QuarticIntegerRepresentativeTree.Tree.branch 1906 (QuarticIntegerRepresentativeTree.Tree.branch 1905 (QuarticIntegerRepresentativeTree.Tree.leaf 1904 representative_1904) (QuarticIntegerRepresentativeTree.Tree.leaf 1905 representative_1905)) (QuarticIntegerRepresentativeTree.Tree.branch 1907 (QuarticIntegerRepresentativeTree.Tree.leaf 1906 representative_1906) (QuarticIntegerRepresentativeTree.Tree.leaf 1907 representative_1907))) (QuarticIntegerRepresentativeTree.Tree.branch 1910 (QuarticIntegerRepresentativeTree.Tree.branch 1909 (QuarticIntegerRepresentativeTree.Tree.leaf 1908 representative_1908) (QuarticIntegerRepresentativeTree.Tree.leaf 1909 representative_1909)) (QuarticIntegerRepresentativeTree.Tree.branch 1911 (QuarticIntegerRepresentativeTree.Tree.leaf 1910 representative_1910) (QuarticIntegerRepresentativeTree.Tree.leaf 1911 representative_1911)))) (QuarticIntegerRepresentativeTree.Tree.branch 1916 (QuarticIntegerRepresentativeTree.Tree.branch 1914 (QuarticIntegerRepresentativeTree.Tree.branch 1913 (QuarticIntegerRepresentativeTree.Tree.leaf 1912 representative_1912) (QuarticIntegerRepresentativeTree.Tree.leaf 1913 representative_1913)) (QuarticIntegerRepresentativeTree.Tree.branch 1915 (QuarticIntegerRepresentativeTree.Tree.leaf 1914 representative_1914) (QuarticIntegerRepresentativeTree.Tree.leaf 1915 representative_1915))) (QuarticIntegerRepresentativeTree.Tree.branch 1918 (QuarticIntegerRepresentativeTree.Tree.branch 1917 (QuarticIntegerRepresentativeTree.Tree.leaf 1916 representative_1916) (QuarticIntegerRepresentativeTree.Tree.leaf 1917 representative_1917)) (QuarticIntegerRepresentativeTree.Tree.branch 1919 (QuarticIntegerRepresentativeTree.Tree.leaf 1918 representative_1918) (QuarticIntegerRepresentativeTree.Tree.leaf 1919 representative_1919)))))))
theorem accepted_029 : All validRep tree_029 := ⟨⟨⟨⟨⟨⟨coefficient_1856,coefficient_1857⟩,⟨coefficient_1858,coefficient_1859⟩⟩,⟨⟨coefficient_1860,coefficient_1861⟩,⟨coefficient_1862,coefficient_1863⟩⟩⟩,⟨⟨⟨coefficient_1864,coefficient_1865⟩,⟨coefficient_1866,coefficient_1867⟩⟩,⟨⟨coefficient_1868,coefficient_1869⟩,⟨coefficient_1870,coefficient_1871⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1872,coefficient_1873⟩,⟨coefficient_1874,coefficient_1875⟩⟩,⟨⟨coefficient_1876,coefficient_1877⟩,⟨coefficient_1878,coefficient_1879⟩⟩⟩,⟨⟨⟨coefficient_1880,coefficient_1881⟩,⟨coefficient_1882,coefficient_1883⟩⟩,⟨⟨coefficient_1884,coefficient_1885⟩,⟨coefficient_1886,coefficient_1887⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1888,coefficient_1889⟩,⟨coefficient_1890,coefficient_1891⟩⟩,⟨⟨coefficient_1892,coefficient_1893⟩,⟨coefficient_1894,coefficient_1895⟩⟩⟩,⟨⟨⟨coefficient_1896,coefficient_1897⟩,⟨coefficient_1898,coefficient_1899⟩⟩,⟨⟨coefficient_1900,coefficient_1901⟩,⟨coefficient_1902,coefficient_1903⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1904,coefficient_1905⟩,⟨coefficient_1906,coefficient_1907⟩⟩,⟨⟨coefficient_1908,coefficient_1909⟩,⟨coefficient_1910,coefficient_1911⟩⟩⟩,⟨⟨⟨coefficient_1912,coefficient_1913⟩,⟨coefficient_1914,coefficient_1915⟩⟩,⟨⟨coefficient_1916,coefficient_1917⟩,⟨coefficient_1918,coefficient_1919⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

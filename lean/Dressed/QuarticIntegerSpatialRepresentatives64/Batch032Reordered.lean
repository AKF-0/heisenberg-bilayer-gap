import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2048 : Rep := ⟨![0,9,27,54],462⟩
def representative_2049 : Rep := ⟨![0,9,28,35],462⟩
def representative_2050 : Rep := ⟨![0,9,28,37],462⟩
def representative_2051 : Rep := ⟨![0,9,28,38],462⟩
def representative_2052 : Rep := ⟨![0,9,28,43],462⟩
def representative_2053 : Rep := ⟨![0,9,28,45],462⟩
def representative_2054 : Rep := ⟨![0,9,28,46],462⟩
def representative_2055 : Rep := ⟨![0,9,28,51],462⟩
def representative_2056 : Rep := ⟨![0,9,28,53],462⟩
def representative_2057 : Rep := ⟨![0,9,29,36],462⟩
def representative_2058 : Rep := ⟨![0,9,29,38],462⟩
def representative_2059 : Rep := ⟨![0,9,29,43],462⟩
def representative_2060 : Rep := ⟨![0,9,29,44],462⟩
def representative_2061 : Rep := ⟨![0,9,29,51],462⟩
def representative_2062 : Rep := ⟨![0,9,29,52],462⟩
def representative_2063 : Rep := ⟨![0,9,30,36],462⟩
def representative_2064 : Rep := ⟨![0,9,30,44],462⟩
def representative_2065 : Rep := ⟨![0,9,30,51],462⟩
def representative_2066 : Rep := ⟨![0,9,36,45],462⟩
def representative_2067 : Rep := ⟨![0,9,37,44],462⟩
def representative_2068 : Rep := ⟨![0,10,1,11],423⟩
def representative_2069 : Rep := ⟨![0,10,1,12],137⟩
def representative_2070 : Rep := ⟨![0,10,1,13],301⟩
def representative_2071 : Rep := ⟨![0,10,1,14],82⟩
def representative_2072 : Rep := ⟨![0,10,1,15],438⟩
def representative_2073 : Rep := ⟨![0,10,1,16],432⟩
def representative_2074 : Rep := ⟨![0,10,1,18],424⟩
def representative_2075 : Rep := ⟨![0,10,1,19],113⟩
def representative_2076 : Rep := ⟨![0,10,1,20],309⟩
def representative_2077 : Rep := ⟨![0,10,1,21],232⟩
def representative_2078 : Rep := ⟨![0,10,1,22],293⟩
def representative_2079 : Rep := ⟨![0,10,1,23],81⟩
def representative_2080 : Rep := ⟨![0,10,1,24],89⟩
def representative_2081 : Rep := ⟨![0,10,1,26],137⟩
def representative_2082 : Rep := ⟨![0,10,1,27],309⟩
def representative_2083 : Rep := ⟨![0,10,1,28],228⟩
def representative_2084 : Rep := ⟨![0,10,1,29],462⟩
def representative_2085 : Rep := ⟨![0,10,1,30],462⟩
def representative_2086 : Rep := ⟨![0,10,1,31],284⟩
def representative_2087 : Rep := ⟨![0,10,1,32],269⟩
def representative_2088 : Rep := ⟨![0,10,1,34],279⟩
def representative_2089 : Rep := ⟨![0,10,1,35],232⟩
def representative_2090 : Rep := ⟨![0,10,1,36],462⟩
def representative_2091 : Rep := ⟨![0,10,1,37],462⟩
def representative_2092 : Rep := ⟨![0,10,1,38],462⟩
def representative_2093 : Rep := ⟨![0,10,1,39],462⟩
def representative_2094 : Rep := ⟨![0,10,1,40],91⟩
def representative_2095 : Rep := ⟨![0,10,1,42],235⟩
def representative_2096 : Rep := ⟨![0,10,1,43],462⟩
def representative_2097 : Rep := ⟨![0,10,1,44],462⟩
def representative_2098 : Rep := ⟨![0,10,1,45],462⟩
def representative_2099 : Rep := ⟨![0,10,1,46],462⟩
def representative_2100 : Rep := ⟨![0,10,1,47],284⟩
def representative_2101 : Rep := ⟨![0,10,1,48],431⟩
def representative_2102 : Rep := ⟨![0,10,1,50],415⟩
def representative_2103 : Rep := ⟨![0,10,1,51],232⟩
def representative_2104 : Rep := ⟨![0,10,1,52],462⟩
def representative_2105 : Rep := ⟨![0,10,1,53],462⟩
def representative_2106 : Rep := ⟨![0,10,1,54],293⟩
def representative_2107 : Rep := ⟨![0,10,1,55],83⟩
def representative_2108 : Rep := ⟨![0,10,1,59],416⟩
def representative_2109 : Rep := ⟨![0,10,1,60],228⟩
def representative_2110 : Rep := ⟨![0,10,1,61],284⟩
def representative_2111 : Rep := ⟨![0,10,1,62],83⟩
theorem coefficient_2048 : validRep representative_2048 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2048)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2049 : validRep representative_2049 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2049)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2050 : validRep representative_2050 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2050)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2051 : validRep representative_2051 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2051)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2052 : validRep representative_2052 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2052)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2053 : validRep representative_2053 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2053)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2054 : validRep representative_2054 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2054)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2055 : validRep representative_2055 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2055)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2056 : validRep representative_2056 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2056)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2057 : validRep representative_2057 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2057)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2058 : validRep representative_2058 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2058)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2059 : validRep representative_2059 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2059)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2060 : validRep representative_2060 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2060)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2061 : validRep representative_2061 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2061)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2062 : validRep representative_2062 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2062)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2063 : validRep representative_2063 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2063)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2064 : validRep representative_2064 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2064)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2065 : validRep representative_2065 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2065)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2066 : validRep representative_2066 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2066)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2067 : validRep representative_2067 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2067)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2068 : validRep representative_2068 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2068)=dictionary64.getD 423 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_423]
  decide +kernel
theorem coefficient_2069 : validRep representative_2069 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2069)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2070 : validRep representative_2070 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2070)=dictionary64.getD 301 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_301]
  decide +kernel
theorem coefficient_2071 : validRep representative_2071 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2071)=dictionary64.getD 82 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_82]
  decide +kernel
theorem coefficient_2072 : validRep representative_2072 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2072)=dictionary64.getD 438 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_438]
  decide +kernel
theorem coefficient_2073 : validRep representative_2073 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2073)=dictionary64.getD 432 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_432]
  decide +kernel
theorem coefficient_2074 : validRep representative_2074 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2074)=dictionary64.getD 424 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_424]
  decide +kernel
theorem coefficient_2075 : validRep representative_2075 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2075)=dictionary64.getD 113 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_113]
  decide +kernel
theorem coefficient_2076 : validRep representative_2076 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2076)=dictionary64.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_2077 : validRep representative_2077 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2077)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2078 : validRep representative_2078 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2078)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_2079 : validRep representative_2079 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2079)=dictionary64.getD 81 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_81]
  decide +kernel
theorem coefficient_2080 : validRep representative_2080 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2080)=dictionary64.getD 89 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_89]
  decide +kernel
theorem coefficient_2081 : validRep representative_2081 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2081)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2082 : validRep representative_2082 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2082)=dictionary64.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_2083 : validRep representative_2083 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2083)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2084 : validRep representative_2084 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2084)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2085 : validRep representative_2085 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2085)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2086 : validRep representative_2086 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2086)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2087 : validRep representative_2087 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2087)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_2088 : validRep representative_2088 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2088)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_2089 : validRep representative_2089 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2089)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2090 : validRep representative_2090 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2090)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2091 : validRep representative_2091 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2091)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2092 : validRep representative_2092 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2092)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2093 : validRep representative_2093 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2093)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2094 : validRep representative_2094 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2094)=dictionary64.getD 91 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_91]
  decide +kernel
theorem coefficient_2095 : validRep representative_2095 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2095)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2096 : validRep representative_2096 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2096)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2097 : validRep representative_2097 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2097)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2098 : validRep representative_2098 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2098)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2099 : validRep representative_2099 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2099)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2100 : validRep representative_2100 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2100)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2101 : validRep representative_2101 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2101)=dictionary64.getD 431 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_431]
  decide +kernel
theorem coefficient_2102 : validRep representative_2102 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2102)=dictionary64.getD 415 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_415]
  decide +kernel
theorem coefficient_2103 : validRep representative_2103 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2103)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2104 : validRep representative_2104 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2104)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2105 : validRep representative_2105 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2105)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2106 : validRep representative_2106 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2106)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_2107 : validRep representative_2107 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2107)=dictionary64.getD 83 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_83]
  decide +kernel
theorem coefficient_2108 : validRep representative_2108 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2108)=dictionary64.getD 416 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_416]
  decide +kernel
theorem coefficient_2109 : validRep representative_2109 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2109)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2110 : validRep representative_2110 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2110)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2111 : validRep representative_2111 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2111)=dictionary64.getD 83 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_83]
  decide +kernel
def tree_032 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2080 (QuarticIntegerRepresentativeTree.Tree.branch 2064 (QuarticIntegerRepresentativeTree.Tree.branch 2056 (QuarticIntegerRepresentativeTree.Tree.branch 2052 (QuarticIntegerRepresentativeTree.Tree.branch 2050 (QuarticIntegerRepresentativeTree.Tree.branch 2049 (QuarticIntegerRepresentativeTree.Tree.leaf 2048 representative_2048) (QuarticIntegerRepresentativeTree.Tree.leaf 2049 representative_2049)) (QuarticIntegerRepresentativeTree.Tree.branch 2051 (QuarticIntegerRepresentativeTree.Tree.leaf 2050 representative_2050) (QuarticIntegerRepresentativeTree.Tree.leaf 2051 representative_2051))) (QuarticIntegerRepresentativeTree.Tree.branch 2054 (QuarticIntegerRepresentativeTree.Tree.branch 2053 (QuarticIntegerRepresentativeTree.Tree.leaf 2052 representative_2052) (QuarticIntegerRepresentativeTree.Tree.leaf 2053 representative_2053)) (QuarticIntegerRepresentativeTree.Tree.branch 2055 (QuarticIntegerRepresentativeTree.Tree.leaf 2054 representative_2054) (QuarticIntegerRepresentativeTree.Tree.leaf 2055 representative_2055)))) (QuarticIntegerRepresentativeTree.Tree.branch 2060 (QuarticIntegerRepresentativeTree.Tree.branch 2058 (QuarticIntegerRepresentativeTree.Tree.branch 2057 (QuarticIntegerRepresentativeTree.Tree.leaf 2056 representative_2056) (QuarticIntegerRepresentativeTree.Tree.leaf 2057 representative_2057)) (QuarticIntegerRepresentativeTree.Tree.branch 2059 (QuarticIntegerRepresentativeTree.Tree.leaf 2058 representative_2058) (QuarticIntegerRepresentativeTree.Tree.leaf 2059 representative_2059))) (QuarticIntegerRepresentativeTree.Tree.branch 2062 (QuarticIntegerRepresentativeTree.Tree.branch 2061 (QuarticIntegerRepresentativeTree.Tree.leaf 2060 representative_2060) (QuarticIntegerRepresentativeTree.Tree.leaf 2061 representative_2061)) (QuarticIntegerRepresentativeTree.Tree.branch 2063 (QuarticIntegerRepresentativeTree.Tree.leaf 2062 representative_2062) (QuarticIntegerRepresentativeTree.Tree.leaf 2063 representative_2063))))) (QuarticIntegerRepresentativeTree.Tree.branch 2072 (QuarticIntegerRepresentativeTree.Tree.branch 2068 (QuarticIntegerRepresentativeTree.Tree.branch 2066 (QuarticIntegerRepresentativeTree.Tree.branch 2065 (QuarticIntegerRepresentativeTree.Tree.leaf 2064 representative_2064) (QuarticIntegerRepresentativeTree.Tree.leaf 2065 representative_2065)) (QuarticIntegerRepresentativeTree.Tree.branch 2067 (QuarticIntegerRepresentativeTree.Tree.leaf 2066 representative_2066) (QuarticIntegerRepresentativeTree.Tree.leaf 2067 representative_2067))) (QuarticIntegerRepresentativeTree.Tree.branch 2070 (QuarticIntegerRepresentativeTree.Tree.branch 2069 (QuarticIntegerRepresentativeTree.Tree.leaf 2068 representative_2068) (QuarticIntegerRepresentativeTree.Tree.leaf 2069 representative_2069)) (QuarticIntegerRepresentativeTree.Tree.branch 2071 (QuarticIntegerRepresentativeTree.Tree.leaf 2070 representative_2070) (QuarticIntegerRepresentativeTree.Tree.leaf 2071 representative_2071)))) (QuarticIntegerRepresentativeTree.Tree.branch 2076 (QuarticIntegerRepresentativeTree.Tree.branch 2074 (QuarticIntegerRepresentativeTree.Tree.branch 2073 (QuarticIntegerRepresentativeTree.Tree.leaf 2072 representative_2072) (QuarticIntegerRepresentativeTree.Tree.leaf 2073 representative_2073)) (QuarticIntegerRepresentativeTree.Tree.branch 2075 (QuarticIntegerRepresentativeTree.Tree.leaf 2074 representative_2074) (QuarticIntegerRepresentativeTree.Tree.leaf 2075 representative_2075))) (QuarticIntegerRepresentativeTree.Tree.branch 2078 (QuarticIntegerRepresentativeTree.Tree.branch 2077 (QuarticIntegerRepresentativeTree.Tree.leaf 2076 representative_2076) (QuarticIntegerRepresentativeTree.Tree.leaf 2077 representative_2077)) (QuarticIntegerRepresentativeTree.Tree.branch 2079 (QuarticIntegerRepresentativeTree.Tree.leaf 2078 representative_2078) (QuarticIntegerRepresentativeTree.Tree.leaf 2079 representative_2079)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2096 (QuarticIntegerRepresentativeTree.Tree.branch 2088 (QuarticIntegerRepresentativeTree.Tree.branch 2084 (QuarticIntegerRepresentativeTree.Tree.branch 2082 (QuarticIntegerRepresentativeTree.Tree.branch 2081 (QuarticIntegerRepresentativeTree.Tree.leaf 2080 representative_2080) (QuarticIntegerRepresentativeTree.Tree.leaf 2081 representative_2081)) (QuarticIntegerRepresentativeTree.Tree.branch 2083 (QuarticIntegerRepresentativeTree.Tree.leaf 2082 representative_2082) (QuarticIntegerRepresentativeTree.Tree.leaf 2083 representative_2083))) (QuarticIntegerRepresentativeTree.Tree.branch 2086 (QuarticIntegerRepresentativeTree.Tree.branch 2085 (QuarticIntegerRepresentativeTree.Tree.leaf 2084 representative_2084) (QuarticIntegerRepresentativeTree.Tree.leaf 2085 representative_2085)) (QuarticIntegerRepresentativeTree.Tree.branch 2087 (QuarticIntegerRepresentativeTree.Tree.leaf 2086 representative_2086) (QuarticIntegerRepresentativeTree.Tree.leaf 2087 representative_2087)))) (QuarticIntegerRepresentativeTree.Tree.branch 2092 (QuarticIntegerRepresentativeTree.Tree.branch 2090 (QuarticIntegerRepresentativeTree.Tree.branch 2089 (QuarticIntegerRepresentativeTree.Tree.leaf 2088 representative_2088) (QuarticIntegerRepresentativeTree.Tree.leaf 2089 representative_2089)) (QuarticIntegerRepresentativeTree.Tree.branch 2091 (QuarticIntegerRepresentativeTree.Tree.leaf 2090 representative_2090) (QuarticIntegerRepresentativeTree.Tree.leaf 2091 representative_2091))) (QuarticIntegerRepresentativeTree.Tree.branch 2094 (QuarticIntegerRepresentativeTree.Tree.branch 2093 (QuarticIntegerRepresentativeTree.Tree.leaf 2092 representative_2092) (QuarticIntegerRepresentativeTree.Tree.leaf 2093 representative_2093)) (QuarticIntegerRepresentativeTree.Tree.branch 2095 (QuarticIntegerRepresentativeTree.Tree.leaf 2094 representative_2094) (QuarticIntegerRepresentativeTree.Tree.leaf 2095 representative_2095))))) (QuarticIntegerRepresentativeTree.Tree.branch 2104 (QuarticIntegerRepresentativeTree.Tree.branch 2100 (QuarticIntegerRepresentativeTree.Tree.branch 2098 (QuarticIntegerRepresentativeTree.Tree.branch 2097 (QuarticIntegerRepresentativeTree.Tree.leaf 2096 representative_2096) (QuarticIntegerRepresentativeTree.Tree.leaf 2097 representative_2097)) (QuarticIntegerRepresentativeTree.Tree.branch 2099 (QuarticIntegerRepresentativeTree.Tree.leaf 2098 representative_2098) (QuarticIntegerRepresentativeTree.Tree.leaf 2099 representative_2099))) (QuarticIntegerRepresentativeTree.Tree.branch 2102 (QuarticIntegerRepresentativeTree.Tree.branch 2101 (QuarticIntegerRepresentativeTree.Tree.leaf 2100 representative_2100) (QuarticIntegerRepresentativeTree.Tree.leaf 2101 representative_2101)) (QuarticIntegerRepresentativeTree.Tree.branch 2103 (QuarticIntegerRepresentativeTree.Tree.leaf 2102 representative_2102) (QuarticIntegerRepresentativeTree.Tree.leaf 2103 representative_2103)))) (QuarticIntegerRepresentativeTree.Tree.branch 2108 (QuarticIntegerRepresentativeTree.Tree.branch 2106 (QuarticIntegerRepresentativeTree.Tree.branch 2105 (QuarticIntegerRepresentativeTree.Tree.leaf 2104 representative_2104) (QuarticIntegerRepresentativeTree.Tree.leaf 2105 representative_2105)) (QuarticIntegerRepresentativeTree.Tree.branch 2107 (QuarticIntegerRepresentativeTree.Tree.leaf 2106 representative_2106) (QuarticIntegerRepresentativeTree.Tree.leaf 2107 representative_2107))) (QuarticIntegerRepresentativeTree.Tree.branch 2110 (QuarticIntegerRepresentativeTree.Tree.branch 2109 (QuarticIntegerRepresentativeTree.Tree.leaf 2108 representative_2108) (QuarticIntegerRepresentativeTree.Tree.leaf 2109 representative_2109)) (QuarticIntegerRepresentativeTree.Tree.branch 2111 (QuarticIntegerRepresentativeTree.Tree.leaf 2110 representative_2110) (QuarticIntegerRepresentativeTree.Tree.leaf 2111 representative_2111)))))))
theorem accepted_032 : All validRep tree_032 := ⟨⟨⟨⟨⟨⟨coefficient_2048,coefficient_2049⟩,⟨coefficient_2050,coefficient_2051⟩⟩,⟨⟨coefficient_2052,coefficient_2053⟩,⟨coefficient_2054,coefficient_2055⟩⟩⟩,⟨⟨⟨coefficient_2056,coefficient_2057⟩,⟨coefficient_2058,coefficient_2059⟩⟩,⟨⟨coefficient_2060,coefficient_2061⟩,⟨coefficient_2062,coefficient_2063⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2064,coefficient_2065⟩,⟨coefficient_2066,coefficient_2067⟩⟩,⟨⟨coefficient_2068,coefficient_2069⟩,⟨coefficient_2070,coefficient_2071⟩⟩⟩,⟨⟨⟨coefficient_2072,coefficient_2073⟩,⟨coefficient_2074,coefficient_2075⟩⟩,⟨⟨coefficient_2076,coefficient_2077⟩,⟨coefficient_2078,coefficient_2079⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2080,coefficient_2081⟩,⟨coefficient_2082,coefficient_2083⟩⟩,⟨⟨coefficient_2084,coefficient_2085⟩,⟨coefficient_2086,coefficient_2087⟩⟩⟩,⟨⟨⟨coefficient_2088,coefficient_2089⟩,⟨coefficient_2090,coefficient_2091⟩⟩,⟨⟨coefficient_2092,coefficient_2093⟩,⟨coefficient_2094,coefficient_2095⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2096,coefficient_2097⟩,⟨coefficient_2098,coefficient_2099⟩⟩,⟨⟨coefficient_2100,coefficient_2101⟩,⟨coefficient_2102,coefficient_2103⟩⟩⟩,⟨⟨⟨coefficient_2104,coefficient_2105⟩,⟨coefficient_2106,coefficient_2107⟩⟩,⟨⟨coefficient_2108,coefficient_2109⟩,⟨coefficient_2110,coefficient_2111⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

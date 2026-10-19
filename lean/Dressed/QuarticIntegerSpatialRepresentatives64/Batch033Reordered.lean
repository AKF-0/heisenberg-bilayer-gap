import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2112 : Rep := ⟨![0,10,1,63],437⟩
def representative_2113 : Rep := ⟨![0,10,2,8],433⟩
def representative_2114 : Rep := ⟨![0,10,2,12],427⟩
def representative_2115 : Rep := ⟨![0,10,2,13],93⟩
def representative_2116 : Rep := ⟨![0,10,2,14],299⟩
def representative_2117 : Rep := ⟨![0,10,2,15],92⟩
def representative_2118 : Rep := ⟨![0,10,2,16],84⟩
def representative_2119 : Rep := ⟨![0,10,2,20],86⟩
def representative_2120 : Rep := ⟨![0,10,2,21],284⟩
def representative_2121 : Rep := ⟨![0,10,2,22],234⟩
def representative_2122 : Rep := ⟨![0,10,2,23],305⟩
def representative_2123 : Rep := ⟨![0,10,2,24],302⟩
def representative_2124 : Rep := ⟨![0,10,2,25],85⟩
def representative_2125 : Rep := ⟨![0,10,2,27],86⟩
def representative_2126 : Rep := ⟨![0,10,2,28],293⟩
def representative_2127 : Rep := ⟨![0,10,2,29],462⟩
def representative_2128 : Rep := ⟨![0,10,2,30],462⟩
def representative_2129 : Rep := ⟨![0,10,2,31],235⟩
def representative_2130 : Rep := ⟨![0,10,2,32],237⟩
def representative_2131 : Rep := ⟨![0,10,2,33],284⟩
def representative_2132 : Rep := ⟨![0,10,2,35],284⟩
def representative_2133 : Rep := ⟨![0,10,2,36],462⟩
def representative_2134 : Rep := ⟨![0,10,2,37],462⟩
def representative_2135 : Rep := ⟨![0,10,2,38],462⟩
def representative_2136 : Rep := ⟨![0,10,2,39],462⟩
def representative_2137 : Rep := ⟨![0,10,2,40],266⟩
def representative_2138 : Rep := ⟨![0,10,2,41],235⟩
def representative_2139 : Rep := ⟨![0,10,2,43],462⟩
def representative_2140 : Rep := ⟨![0,10,2,44],462⟩
def representative_2141 : Rep := ⟨![0,10,2,45],462⟩
def representative_2142 : Rep := ⟨![0,10,2,46],462⟩
def representative_2143 : Rep := ⟨![0,10,2,47],235⟩
def representative_2144 : Rep := ⟨![0,10,2,48],178⟩
def representative_2145 : Rep := ⟨![0,10,2,49],392⟩
def representative_2146 : Rep := ⟨![0,10,2,51],390⟩
def representative_2147 : Rep := ⟨![0,10,2,52],462⟩
def representative_2148 : Rep := ⟨![0,10,2,53],462⟩
def representative_2149 : Rep := ⟨![0,10,2,54],234⟩
def representative_2150 : Rep := ⟨![0,10,2,55],291⟩
def representative_2151 : Rep := ⟨![0,10,2,56],414⟩
def representative_2152 : Rep := ⟨![0,10,2,60],391⟩
def representative_2153 : Rep := ⟨![0,10,2,61],235⟩
def representative_2154 : Rep := ⟨![0,10,2,62],291⟩
def representative_2155 : Rep := ⟨![0,10,2,63],137⟩
def representative_2156 : Rep := ⟨![0,10,3,13],297⟩
def representative_2157 : Rep := ⟨![0,10,3,14],229⟩
def representative_2158 : Rep := ⟨![0,10,3,15],296⟩
def representative_2159 : Rep := ⟨![0,10,3,16],318⟩
def representative_2160 : Rep := ⟨![0,10,3,17],112⟩
def representative_2161 : Rep := ⟨![0,10,3,20],320⟩
def representative_2162 : Rep := ⟨![0,10,3,21],232⟩
def representative_2163 : Rep := ⟨![0,10,3,22],244⟩
def representative_2164 : Rep := ⟨![0,10,3,23],226⟩
def representative_2165 : Rep := ⟨![0,10,3,24],226⟩
def representative_2166 : Rep := ⟨![0,10,3,25],310⟩
def representative_2167 : Rep := ⟨![0,10,3,26],137⟩
def representative_2168 : Rep := ⟨![0,10,3,28],228⟩
def representative_2169 : Rep := ⟨![0,10,3,29],462⟩
def representative_2170 : Rep := ⟨![0,10,3,30],462⟩
def representative_2171 : Rep := ⟨![0,10,3,31],243⟩
def representative_2172 : Rep := ⟨![0,10,3,32],242⟩
def representative_2173 : Rep := ⟨![0,10,3,33],232⟩
def representative_2174 : Rep := ⟨![0,10,3,34],279⟩
def representative_2175 : Rep := ⟨![0,10,3,36],462⟩
theorem coefficient_2112 : validRep representative_2112 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2112)=dictionary64.getD 437 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_437]
  decide +kernel
theorem coefficient_2113 : validRep representative_2113 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2113)=dictionary64.getD 433 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_433]
  decide +kernel
theorem coefficient_2114 : validRep representative_2114 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2114)=dictionary64.getD 427 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_427]
  decide +kernel
theorem coefficient_2115 : validRep representative_2115 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2115)=dictionary64.getD 93 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_93]
  decide +kernel
theorem coefficient_2116 : validRep representative_2116 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2116)=dictionary64.getD 299 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_299]
  decide +kernel
theorem coefficient_2117 : validRep representative_2117 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2117)=dictionary64.getD 92 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_92]
  decide +kernel
theorem coefficient_2118 : validRep representative_2118 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2118)=dictionary64.getD 84 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_84]
  decide +kernel
theorem coefficient_2119 : validRep representative_2119 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2119)=dictionary64.getD 86 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_86]
  decide +kernel
theorem coefficient_2120 : validRep representative_2120 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2120)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2121 : validRep representative_2121 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2121)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2122 : validRep representative_2122 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2122)=dictionary64.getD 305 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_305]
  decide +kernel
theorem coefficient_2123 : validRep representative_2123 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2123)=dictionary64.getD 302 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_302]
  decide +kernel
theorem coefficient_2124 : validRep representative_2124 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2124)=dictionary64.getD 85 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_85]
  decide +kernel
theorem coefficient_2125 : validRep representative_2125 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2125)=dictionary64.getD 86 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_86]
  decide +kernel
theorem coefficient_2126 : validRep representative_2126 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2126)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_2127 : validRep representative_2127 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2127)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2128 : validRep representative_2128 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2128)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2129 : validRep representative_2129 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2129)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2130 : validRep representative_2130 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2130)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2131 : validRep representative_2131 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2131)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2132 : validRep representative_2132 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2132)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2133 : validRep representative_2133 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2133)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2134 : validRep representative_2134 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2134)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2135 : validRep representative_2135 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2135)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2136 : validRep representative_2136 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2136)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2137 : validRep representative_2137 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2137)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_2138 : validRep representative_2138 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2138)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2139 : validRep representative_2139 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2139)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2140 : validRep representative_2140 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2140)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2141 : validRep representative_2141 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2141)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2142 : validRep representative_2142 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2142)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2143 : validRep representative_2143 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2143)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2144 : validRep representative_2144 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2144)=dictionary64.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_2145 : validRep representative_2145 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2145)=dictionary64.getD 392 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_392]
  decide +kernel
theorem coefficient_2146 : validRep representative_2146 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2146)=dictionary64.getD 390 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_390]
  decide +kernel
theorem coefficient_2147 : validRep representative_2147 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2147)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2148 : validRep representative_2148 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2148)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2149 : validRep representative_2149 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2149)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2150 : validRep representative_2150 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2150)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2151 : validRep representative_2151 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2151)=dictionary64.getD 414 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_414]
  decide +kernel
theorem coefficient_2152 : validRep representative_2152 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2152)=dictionary64.getD 391 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_391]
  decide +kernel
theorem coefficient_2153 : validRep representative_2153 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2153)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2154 : validRep representative_2154 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2154)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2155 : validRep representative_2155 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2155)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2156 : validRep representative_2156 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2156)=dictionary64.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_2157 : validRep representative_2157 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2157)=dictionary64.getD 229 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_229]
  decide +kernel
theorem coefficient_2158 : validRep representative_2158 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2158)=dictionary64.getD 296 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_296]
  decide +kernel
theorem coefficient_2159 : validRep representative_2159 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2159)=dictionary64.getD 318 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_318]
  decide +kernel
theorem coefficient_2160 : validRep representative_2160 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2160)=dictionary64.getD 112 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_112]
  decide +kernel
theorem coefficient_2161 : validRep representative_2161 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2161)=dictionary64.getD 320 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_320]
  decide +kernel
theorem coefficient_2162 : validRep representative_2162 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2162)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2163 : validRep representative_2163 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2163)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2164 : validRep representative_2164 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2164)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_2165 : validRep representative_2165 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2165)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_2166 : validRep representative_2166 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2166)=dictionary64.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_2167 : validRep representative_2167 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2167)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2168 : validRep representative_2168 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2168)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2169 : validRep representative_2169 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2169)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2170 : validRep representative_2170 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2170)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2171 : validRep representative_2171 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2171)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2172 : validRep representative_2172 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2172)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_2173 : validRep representative_2173 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2173)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2174 : validRep representative_2174 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2174)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_2175 : validRep representative_2175 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2175)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_033 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2144 (QuarticIntegerRepresentativeTree.Tree.branch 2128 (QuarticIntegerRepresentativeTree.Tree.branch 2120 (QuarticIntegerRepresentativeTree.Tree.branch 2116 (QuarticIntegerRepresentativeTree.Tree.branch 2114 (QuarticIntegerRepresentativeTree.Tree.branch 2113 (QuarticIntegerRepresentativeTree.Tree.leaf 2112 representative_2112) (QuarticIntegerRepresentativeTree.Tree.leaf 2113 representative_2113)) (QuarticIntegerRepresentativeTree.Tree.branch 2115 (QuarticIntegerRepresentativeTree.Tree.leaf 2114 representative_2114) (QuarticIntegerRepresentativeTree.Tree.leaf 2115 representative_2115))) (QuarticIntegerRepresentativeTree.Tree.branch 2118 (QuarticIntegerRepresentativeTree.Tree.branch 2117 (QuarticIntegerRepresentativeTree.Tree.leaf 2116 representative_2116) (QuarticIntegerRepresentativeTree.Tree.leaf 2117 representative_2117)) (QuarticIntegerRepresentativeTree.Tree.branch 2119 (QuarticIntegerRepresentativeTree.Tree.leaf 2118 representative_2118) (QuarticIntegerRepresentativeTree.Tree.leaf 2119 representative_2119)))) (QuarticIntegerRepresentativeTree.Tree.branch 2124 (QuarticIntegerRepresentativeTree.Tree.branch 2122 (QuarticIntegerRepresentativeTree.Tree.branch 2121 (QuarticIntegerRepresentativeTree.Tree.leaf 2120 representative_2120) (QuarticIntegerRepresentativeTree.Tree.leaf 2121 representative_2121)) (QuarticIntegerRepresentativeTree.Tree.branch 2123 (QuarticIntegerRepresentativeTree.Tree.leaf 2122 representative_2122) (QuarticIntegerRepresentativeTree.Tree.leaf 2123 representative_2123))) (QuarticIntegerRepresentativeTree.Tree.branch 2126 (QuarticIntegerRepresentativeTree.Tree.branch 2125 (QuarticIntegerRepresentativeTree.Tree.leaf 2124 representative_2124) (QuarticIntegerRepresentativeTree.Tree.leaf 2125 representative_2125)) (QuarticIntegerRepresentativeTree.Tree.branch 2127 (QuarticIntegerRepresentativeTree.Tree.leaf 2126 representative_2126) (QuarticIntegerRepresentativeTree.Tree.leaf 2127 representative_2127))))) (QuarticIntegerRepresentativeTree.Tree.branch 2136 (QuarticIntegerRepresentativeTree.Tree.branch 2132 (QuarticIntegerRepresentativeTree.Tree.branch 2130 (QuarticIntegerRepresentativeTree.Tree.branch 2129 (QuarticIntegerRepresentativeTree.Tree.leaf 2128 representative_2128) (QuarticIntegerRepresentativeTree.Tree.leaf 2129 representative_2129)) (QuarticIntegerRepresentativeTree.Tree.branch 2131 (QuarticIntegerRepresentativeTree.Tree.leaf 2130 representative_2130) (QuarticIntegerRepresentativeTree.Tree.leaf 2131 representative_2131))) (QuarticIntegerRepresentativeTree.Tree.branch 2134 (QuarticIntegerRepresentativeTree.Tree.branch 2133 (QuarticIntegerRepresentativeTree.Tree.leaf 2132 representative_2132) (QuarticIntegerRepresentativeTree.Tree.leaf 2133 representative_2133)) (QuarticIntegerRepresentativeTree.Tree.branch 2135 (QuarticIntegerRepresentativeTree.Tree.leaf 2134 representative_2134) (QuarticIntegerRepresentativeTree.Tree.leaf 2135 representative_2135)))) (QuarticIntegerRepresentativeTree.Tree.branch 2140 (QuarticIntegerRepresentativeTree.Tree.branch 2138 (QuarticIntegerRepresentativeTree.Tree.branch 2137 (QuarticIntegerRepresentativeTree.Tree.leaf 2136 representative_2136) (QuarticIntegerRepresentativeTree.Tree.leaf 2137 representative_2137)) (QuarticIntegerRepresentativeTree.Tree.branch 2139 (QuarticIntegerRepresentativeTree.Tree.leaf 2138 representative_2138) (QuarticIntegerRepresentativeTree.Tree.leaf 2139 representative_2139))) (QuarticIntegerRepresentativeTree.Tree.branch 2142 (QuarticIntegerRepresentativeTree.Tree.branch 2141 (QuarticIntegerRepresentativeTree.Tree.leaf 2140 representative_2140) (QuarticIntegerRepresentativeTree.Tree.leaf 2141 representative_2141)) (QuarticIntegerRepresentativeTree.Tree.branch 2143 (QuarticIntegerRepresentativeTree.Tree.leaf 2142 representative_2142) (QuarticIntegerRepresentativeTree.Tree.leaf 2143 representative_2143)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2160 (QuarticIntegerRepresentativeTree.Tree.branch 2152 (QuarticIntegerRepresentativeTree.Tree.branch 2148 (QuarticIntegerRepresentativeTree.Tree.branch 2146 (QuarticIntegerRepresentativeTree.Tree.branch 2145 (QuarticIntegerRepresentativeTree.Tree.leaf 2144 representative_2144) (QuarticIntegerRepresentativeTree.Tree.leaf 2145 representative_2145)) (QuarticIntegerRepresentativeTree.Tree.branch 2147 (QuarticIntegerRepresentativeTree.Tree.leaf 2146 representative_2146) (QuarticIntegerRepresentativeTree.Tree.leaf 2147 representative_2147))) (QuarticIntegerRepresentativeTree.Tree.branch 2150 (QuarticIntegerRepresentativeTree.Tree.branch 2149 (QuarticIntegerRepresentativeTree.Tree.leaf 2148 representative_2148) (QuarticIntegerRepresentativeTree.Tree.leaf 2149 representative_2149)) (QuarticIntegerRepresentativeTree.Tree.branch 2151 (QuarticIntegerRepresentativeTree.Tree.leaf 2150 representative_2150) (QuarticIntegerRepresentativeTree.Tree.leaf 2151 representative_2151)))) (QuarticIntegerRepresentativeTree.Tree.branch 2156 (QuarticIntegerRepresentativeTree.Tree.branch 2154 (QuarticIntegerRepresentativeTree.Tree.branch 2153 (QuarticIntegerRepresentativeTree.Tree.leaf 2152 representative_2152) (QuarticIntegerRepresentativeTree.Tree.leaf 2153 representative_2153)) (QuarticIntegerRepresentativeTree.Tree.branch 2155 (QuarticIntegerRepresentativeTree.Tree.leaf 2154 representative_2154) (QuarticIntegerRepresentativeTree.Tree.leaf 2155 representative_2155))) (QuarticIntegerRepresentativeTree.Tree.branch 2158 (QuarticIntegerRepresentativeTree.Tree.branch 2157 (QuarticIntegerRepresentativeTree.Tree.leaf 2156 representative_2156) (QuarticIntegerRepresentativeTree.Tree.leaf 2157 representative_2157)) (QuarticIntegerRepresentativeTree.Tree.branch 2159 (QuarticIntegerRepresentativeTree.Tree.leaf 2158 representative_2158) (QuarticIntegerRepresentativeTree.Tree.leaf 2159 representative_2159))))) (QuarticIntegerRepresentativeTree.Tree.branch 2168 (QuarticIntegerRepresentativeTree.Tree.branch 2164 (QuarticIntegerRepresentativeTree.Tree.branch 2162 (QuarticIntegerRepresentativeTree.Tree.branch 2161 (QuarticIntegerRepresentativeTree.Tree.leaf 2160 representative_2160) (QuarticIntegerRepresentativeTree.Tree.leaf 2161 representative_2161)) (QuarticIntegerRepresentativeTree.Tree.branch 2163 (QuarticIntegerRepresentativeTree.Tree.leaf 2162 representative_2162) (QuarticIntegerRepresentativeTree.Tree.leaf 2163 representative_2163))) (QuarticIntegerRepresentativeTree.Tree.branch 2166 (QuarticIntegerRepresentativeTree.Tree.branch 2165 (QuarticIntegerRepresentativeTree.Tree.leaf 2164 representative_2164) (QuarticIntegerRepresentativeTree.Tree.leaf 2165 representative_2165)) (QuarticIntegerRepresentativeTree.Tree.branch 2167 (QuarticIntegerRepresentativeTree.Tree.leaf 2166 representative_2166) (QuarticIntegerRepresentativeTree.Tree.leaf 2167 representative_2167)))) (QuarticIntegerRepresentativeTree.Tree.branch 2172 (QuarticIntegerRepresentativeTree.Tree.branch 2170 (QuarticIntegerRepresentativeTree.Tree.branch 2169 (QuarticIntegerRepresentativeTree.Tree.leaf 2168 representative_2168) (QuarticIntegerRepresentativeTree.Tree.leaf 2169 representative_2169)) (QuarticIntegerRepresentativeTree.Tree.branch 2171 (QuarticIntegerRepresentativeTree.Tree.leaf 2170 representative_2170) (QuarticIntegerRepresentativeTree.Tree.leaf 2171 representative_2171))) (QuarticIntegerRepresentativeTree.Tree.branch 2174 (QuarticIntegerRepresentativeTree.Tree.branch 2173 (QuarticIntegerRepresentativeTree.Tree.leaf 2172 representative_2172) (QuarticIntegerRepresentativeTree.Tree.leaf 2173 representative_2173)) (QuarticIntegerRepresentativeTree.Tree.branch 2175 (QuarticIntegerRepresentativeTree.Tree.leaf 2174 representative_2174) (QuarticIntegerRepresentativeTree.Tree.leaf 2175 representative_2175)))))))
theorem accepted_033 : All validRep tree_033 := ⟨⟨⟨⟨⟨⟨coefficient_2112,coefficient_2113⟩,⟨coefficient_2114,coefficient_2115⟩⟩,⟨⟨coefficient_2116,coefficient_2117⟩,⟨coefficient_2118,coefficient_2119⟩⟩⟩,⟨⟨⟨coefficient_2120,coefficient_2121⟩,⟨coefficient_2122,coefficient_2123⟩⟩,⟨⟨coefficient_2124,coefficient_2125⟩,⟨coefficient_2126,coefficient_2127⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2128,coefficient_2129⟩,⟨coefficient_2130,coefficient_2131⟩⟩,⟨⟨coefficient_2132,coefficient_2133⟩,⟨coefficient_2134,coefficient_2135⟩⟩⟩,⟨⟨⟨coefficient_2136,coefficient_2137⟩,⟨coefficient_2138,coefficient_2139⟩⟩,⟨⟨coefficient_2140,coefficient_2141⟩,⟨coefficient_2142,coefficient_2143⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2144,coefficient_2145⟩,⟨coefficient_2146,coefficient_2147⟩⟩,⟨⟨coefficient_2148,coefficient_2149⟩,⟨coefficient_2150,coefficient_2151⟩⟩⟩,⟨⟨⟨coefficient_2152,coefficient_2153⟩,⟨coefficient_2154,coefficient_2155⟩⟩,⟨⟨coefficient_2156,coefficient_2157⟩,⟨coefficient_2158,coefficient_2159⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2160,coefficient_2161⟩,⟨coefficient_2162,coefficient_2163⟩⟩,⟨⟨coefficient_2164,coefficient_2165⟩,⟨coefficient_2166,coefficient_2167⟩⟩⟩,⟨⟨⟨coefficient_2168,coefficient_2169⟩,⟨coefficient_2170,coefficient_2171⟩⟩,⟨⟨coefficient_2172,coefficient_2173⟩,⟨coefficient_2174,coefficient_2175⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

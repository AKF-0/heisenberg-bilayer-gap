import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2176 : Rep := ⟨![0,10,3,37],462⟩
def representative_2177 : Rep := ⟨![0,10,3,38],462⟩
def representative_2178 : Rep := ⟨![0,10,3,39],462⟩
def representative_2179 : Rep := ⟨![0,10,3,40],237⟩
def representative_2180 : Rep := ⟨![0,10,3,41],243⟩
def representative_2181 : Rep := ⟨![0,10,3,42],235⟩
def representative_2182 : Rep := ⟨![0,10,3,44],462⟩
def representative_2183 : Rep := ⟨![0,10,3,45],462⟩
def representative_2184 : Rep := ⟨![0,10,3,46],462⟩
def representative_2185 : Rep := ⟨![0,10,3,47],243⟩
def representative_2186 : Rep := ⟨![0,10,3,48],266⟩
def representative_2187 : Rep := ⟨![0,10,3,49],226⟩
def representative_2188 : Rep := ⟨![0,10,3,50],298⟩
def representative_2189 : Rep := ⟨![0,10,3,52],279⟩
def representative_2190 : Rep := ⟨![0,10,3,53],462⟩
def representative_2191 : Rep := ⟨![0,10,3,54],244⟩
def representative_2192 : Rep := ⟨![0,10,3,55],234⟩
def representative_2193 : Rep := ⟨![0,10,3,56],150⟩
def representative_2194 : Rep := ⟨![0,10,3,57],324⟩
def representative_2195 : Rep := ⟨![0,10,3,61],280⟩
def representative_2196 : Rep := ⟨![0,10,3,62],234⟩
def representative_2197 : Rep := ⟨![0,10,3,63],279⟩
def representative_2198 : Rep := ⟨![0,10,4,14],251⟩
def representative_2199 : Rep := ⟨![0,10,4,16],223⟩
def representative_2200 : Rep := ⟨![0,10,4,17],311⟩
def representative_2201 : Rep := ⟨![0,10,4,18],105⟩
def representative_2202 : Rep := ⟨![0,10,4,19],311⟩
def representative_2203 : Rep := ⟨![0,10,4,21],248⟩
def representative_2204 : Rep := ⟨![0,10,4,22],462⟩
def representative_2205 : Rep := ⟨![0,10,4,23],248⟩
def representative_2206 : Rep := ⟨![0,10,4,24],249⟩
def representative_2207 : Rep := ⟨![0,10,4,25],224⟩
def representative_2208 : Rep := ⟨![0,10,4,26],291⟩
def representative_2209 : Rep := ⟨![0,10,4,27],224⟩
def representative_2210 : Rep := ⟨![0,10,4,29],462⟩
def representative_2211 : Rep := ⟨![0,10,4,30],462⟩
def representative_2212 : Rep := ⟨![0,10,4,31],462⟩
def representative_2213 : Rep := ⟨![0,10,4,32],462⟩
def representative_2214 : Rep := ⟨![0,10,4,33],246⟩
def representative_2215 : Rep := ⟨![0,10,4,34],234⟩
def representative_2216 : Rep := ⟨![0,10,4,35],246⟩
def representative_2217 : Rep := ⟨![0,10,4,37],462⟩
def representative_2218 : Rep := ⟨![0,10,4,38],462⟩
def representative_2219 : Rep := ⟨![0,10,4,39],462⟩
def representative_2220 : Rep := ⟨![0,10,4,40],242⟩
def representative_2221 : Rep := ⟨![0,10,4,41],462⟩
def representative_2222 : Rep := ⟨![0,10,4,42],244⟩
def representative_2223 : Rep := ⟨![0,10,4,43],462⟩
def representative_2224 : Rep := ⟨![0,10,4,45],462⟩
def representative_2225 : Rep := ⟨![0,10,4,46],462⟩
def representative_2226 : Rep := ⟨![0,10,4,47],462⟩
def representative_2227 : Rep := ⟨![0,10,4,48],237⟩
def representative_2228 : Rep := ⟨![0,10,4,49],248⟩
def representative_2229 : Rep := ⟨![0,10,4,50],234⟩
def representative_2230 : Rep := ⟨![0,10,4,51],248⟩
def representative_2231 : Rep := ⟨![0,10,4,53],244⟩
def representative_2232 : Rep := ⟨![0,10,4,54],462⟩
def representative_2233 : Rep := ⟨![0,10,4,55],244⟩
def representative_2234 : Rep := ⟨![0,10,4,56],272⟩
def representative_2235 : Rep := ⟨![0,10,4,57],222⟩
def representative_2236 : Rep := ⟨![0,10,4,58],314⟩
def representative_2237 : Rep := ⟨![0,10,4,62],246⟩
def representative_2238 : Rep := ⟨![0,10,4,63],235⟩
def representative_2239 : Rep := ⟨![0,10,5,11],213⟩
theorem coefficient_2176 : validRep representative_2176 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2176)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2177 : validRep representative_2177 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2177)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2178 : validRep representative_2178 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2178)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2179 : validRep representative_2179 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2179)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2180 : validRep representative_2180 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2180)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2181 : validRep representative_2181 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2181)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2182 : validRep representative_2182 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2182)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2183 : validRep representative_2183 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2183)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2184 : validRep representative_2184 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2184)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2185 : validRep representative_2185 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2185)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2186 : validRep representative_2186 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2186)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_2187 : validRep representative_2187 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2187)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_2188 : validRep representative_2188 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2188)=dictionary64.getD 298 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_298]
  decide +kernel
theorem coefficient_2189 : validRep representative_2189 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2189)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_2190 : validRep representative_2190 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2190)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2191 : validRep representative_2191 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2191)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2192 : validRep representative_2192 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2192)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2193 : validRep representative_2193 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2193)=dictionary64.getD 150 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_150]
  decide +kernel
theorem coefficient_2194 : validRep representative_2194 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2194)=dictionary64.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_2195 : validRep representative_2195 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2195)=dictionary64.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_2196 : validRep representative_2196 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2196)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2197 : validRep representative_2197 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2197)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_2198 : validRep representative_2198 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2198)=dictionary64.getD 251 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_251]
  decide +kernel
theorem coefficient_2199 : validRep representative_2199 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2199)=dictionary64.getD 223 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_223]
  decide +kernel
theorem coefficient_2200 : validRep representative_2200 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2200)=dictionary64.getD 311 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_311]
  decide +kernel
theorem coefficient_2201 : validRep representative_2201 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2201)=dictionary64.getD 105 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_105]
  decide +kernel
theorem coefficient_2202 : validRep representative_2202 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2202)=dictionary64.getD 311 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_311]
  decide +kernel
theorem coefficient_2203 : validRep representative_2203 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2203)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2204 : validRep representative_2204 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2204)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2205 : validRep representative_2205 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2205)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2206 : validRep representative_2206 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2206)=dictionary64.getD 249 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_249]
  decide +kernel
theorem coefficient_2207 : validRep representative_2207 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2207)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2208 : validRep representative_2208 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2208)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2209 : validRep representative_2209 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2209)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2210 : validRep representative_2210 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2210)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2211 : validRep representative_2211 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2211)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2212 : validRep representative_2212 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2212)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2213 : validRep representative_2213 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2213)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2214 : validRep representative_2214 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2214)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2215 : validRep representative_2215 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2215)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2216 : validRep representative_2216 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2216)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2217 : validRep representative_2217 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2217)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2218 : validRep representative_2218 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2218)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2219 : validRep representative_2219 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2219)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2220 : validRep representative_2220 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2220)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_2221 : validRep representative_2221 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2221)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2222 : validRep representative_2222 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2222)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2223 : validRep representative_2223 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2223)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2224 : validRep representative_2224 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2224)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2225 : validRep representative_2225 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2225)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2226 : validRep representative_2226 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2226)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2227 : validRep representative_2227 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2227)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2228 : validRep representative_2228 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2228)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2229 : validRep representative_2229 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2229)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2230 : validRep representative_2230 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2230)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2231 : validRep representative_2231 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2231)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2232 : validRep representative_2232 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2232)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2233 : validRep representative_2233 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2233)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2234 : validRep representative_2234 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2234)=dictionary64.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_2235 : validRep representative_2235 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2235)=dictionary64.getD 222 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_222]
  decide +kernel
theorem coefficient_2236 : validRep representative_2236 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2236)=dictionary64.getD 314 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_314]
  decide +kernel
theorem coefficient_2237 : validRep representative_2237 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2237)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2238 : validRep representative_2238 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2238)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2239 : validRep representative_2239 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2239)=dictionary64.getD 213 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_213]
  decide +kernel
def tree_034 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2208 (QuarticIntegerRepresentativeTree.Tree.branch 2192 (QuarticIntegerRepresentativeTree.Tree.branch 2184 (QuarticIntegerRepresentativeTree.Tree.branch 2180 (QuarticIntegerRepresentativeTree.Tree.branch 2178 (QuarticIntegerRepresentativeTree.Tree.branch 2177 (QuarticIntegerRepresentativeTree.Tree.leaf 2176 representative_2176) (QuarticIntegerRepresentativeTree.Tree.leaf 2177 representative_2177)) (QuarticIntegerRepresentativeTree.Tree.branch 2179 (QuarticIntegerRepresentativeTree.Tree.leaf 2178 representative_2178) (QuarticIntegerRepresentativeTree.Tree.leaf 2179 representative_2179))) (QuarticIntegerRepresentativeTree.Tree.branch 2182 (QuarticIntegerRepresentativeTree.Tree.branch 2181 (QuarticIntegerRepresentativeTree.Tree.leaf 2180 representative_2180) (QuarticIntegerRepresentativeTree.Tree.leaf 2181 representative_2181)) (QuarticIntegerRepresentativeTree.Tree.branch 2183 (QuarticIntegerRepresentativeTree.Tree.leaf 2182 representative_2182) (QuarticIntegerRepresentativeTree.Tree.leaf 2183 representative_2183)))) (QuarticIntegerRepresentativeTree.Tree.branch 2188 (QuarticIntegerRepresentativeTree.Tree.branch 2186 (QuarticIntegerRepresentativeTree.Tree.branch 2185 (QuarticIntegerRepresentativeTree.Tree.leaf 2184 representative_2184) (QuarticIntegerRepresentativeTree.Tree.leaf 2185 representative_2185)) (QuarticIntegerRepresentativeTree.Tree.branch 2187 (QuarticIntegerRepresentativeTree.Tree.leaf 2186 representative_2186) (QuarticIntegerRepresentativeTree.Tree.leaf 2187 representative_2187))) (QuarticIntegerRepresentativeTree.Tree.branch 2190 (QuarticIntegerRepresentativeTree.Tree.branch 2189 (QuarticIntegerRepresentativeTree.Tree.leaf 2188 representative_2188) (QuarticIntegerRepresentativeTree.Tree.leaf 2189 representative_2189)) (QuarticIntegerRepresentativeTree.Tree.branch 2191 (QuarticIntegerRepresentativeTree.Tree.leaf 2190 representative_2190) (QuarticIntegerRepresentativeTree.Tree.leaf 2191 representative_2191))))) (QuarticIntegerRepresentativeTree.Tree.branch 2200 (QuarticIntegerRepresentativeTree.Tree.branch 2196 (QuarticIntegerRepresentativeTree.Tree.branch 2194 (QuarticIntegerRepresentativeTree.Tree.branch 2193 (QuarticIntegerRepresentativeTree.Tree.leaf 2192 representative_2192) (QuarticIntegerRepresentativeTree.Tree.leaf 2193 representative_2193)) (QuarticIntegerRepresentativeTree.Tree.branch 2195 (QuarticIntegerRepresentativeTree.Tree.leaf 2194 representative_2194) (QuarticIntegerRepresentativeTree.Tree.leaf 2195 representative_2195))) (QuarticIntegerRepresentativeTree.Tree.branch 2198 (QuarticIntegerRepresentativeTree.Tree.branch 2197 (QuarticIntegerRepresentativeTree.Tree.leaf 2196 representative_2196) (QuarticIntegerRepresentativeTree.Tree.leaf 2197 representative_2197)) (QuarticIntegerRepresentativeTree.Tree.branch 2199 (QuarticIntegerRepresentativeTree.Tree.leaf 2198 representative_2198) (QuarticIntegerRepresentativeTree.Tree.leaf 2199 representative_2199)))) (QuarticIntegerRepresentativeTree.Tree.branch 2204 (QuarticIntegerRepresentativeTree.Tree.branch 2202 (QuarticIntegerRepresentativeTree.Tree.branch 2201 (QuarticIntegerRepresentativeTree.Tree.leaf 2200 representative_2200) (QuarticIntegerRepresentativeTree.Tree.leaf 2201 representative_2201)) (QuarticIntegerRepresentativeTree.Tree.branch 2203 (QuarticIntegerRepresentativeTree.Tree.leaf 2202 representative_2202) (QuarticIntegerRepresentativeTree.Tree.leaf 2203 representative_2203))) (QuarticIntegerRepresentativeTree.Tree.branch 2206 (QuarticIntegerRepresentativeTree.Tree.branch 2205 (QuarticIntegerRepresentativeTree.Tree.leaf 2204 representative_2204) (QuarticIntegerRepresentativeTree.Tree.leaf 2205 representative_2205)) (QuarticIntegerRepresentativeTree.Tree.branch 2207 (QuarticIntegerRepresentativeTree.Tree.leaf 2206 representative_2206) (QuarticIntegerRepresentativeTree.Tree.leaf 2207 representative_2207)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2224 (QuarticIntegerRepresentativeTree.Tree.branch 2216 (QuarticIntegerRepresentativeTree.Tree.branch 2212 (QuarticIntegerRepresentativeTree.Tree.branch 2210 (QuarticIntegerRepresentativeTree.Tree.branch 2209 (QuarticIntegerRepresentativeTree.Tree.leaf 2208 representative_2208) (QuarticIntegerRepresentativeTree.Tree.leaf 2209 representative_2209)) (QuarticIntegerRepresentativeTree.Tree.branch 2211 (QuarticIntegerRepresentativeTree.Tree.leaf 2210 representative_2210) (QuarticIntegerRepresentativeTree.Tree.leaf 2211 representative_2211))) (QuarticIntegerRepresentativeTree.Tree.branch 2214 (QuarticIntegerRepresentativeTree.Tree.branch 2213 (QuarticIntegerRepresentativeTree.Tree.leaf 2212 representative_2212) (QuarticIntegerRepresentativeTree.Tree.leaf 2213 representative_2213)) (QuarticIntegerRepresentativeTree.Tree.branch 2215 (QuarticIntegerRepresentativeTree.Tree.leaf 2214 representative_2214) (QuarticIntegerRepresentativeTree.Tree.leaf 2215 representative_2215)))) (QuarticIntegerRepresentativeTree.Tree.branch 2220 (QuarticIntegerRepresentativeTree.Tree.branch 2218 (QuarticIntegerRepresentativeTree.Tree.branch 2217 (QuarticIntegerRepresentativeTree.Tree.leaf 2216 representative_2216) (QuarticIntegerRepresentativeTree.Tree.leaf 2217 representative_2217)) (QuarticIntegerRepresentativeTree.Tree.branch 2219 (QuarticIntegerRepresentativeTree.Tree.leaf 2218 representative_2218) (QuarticIntegerRepresentativeTree.Tree.leaf 2219 representative_2219))) (QuarticIntegerRepresentativeTree.Tree.branch 2222 (QuarticIntegerRepresentativeTree.Tree.branch 2221 (QuarticIntegerRepresentativeTree.Tree.leaf 2220 representative_2220) (QuarticIntegerRepresentativeTree.Tree.leaf 2221 representative_2221)) (QuarticIntegerRepresentativeTree.Tree.branch 2223 (QuarticIntegerRepresentativeTree.Tree.leaf 2222 representative_2222) (QuarticIntegerRepresentativeTree.Tree.leaf 2223 representative_2223))))) (QuarticIntegerRepresentativeTree.Tree.branch 2232 (QuarticIntegerRepresentativeTree.Tree.branch 2228 (QuarticIntegerRepresentativeTree.Tree.branch 2226 (QuarticIntegerRepresentativeTree.Tree.branch 2225 (QuarticIntegerRepresentativeTree.Tree.leaf 2224 representative_2224) (QuarticIntegerRepresentativeTree.Tree.leaf 2225 representative_2225)) (QuarticIntegerRepresentativeTree.Tree.branch 2227 (QuarticIntegerRepresentativeTree.Tree.leaf 2226 representative_2226) (QuarticIntegerRepresentativeTree.Tree.leaf 2227 representative_2227))) (QuarticIntegerRepresentativeTree.Tree.branch 2230 (QuarticIntegerRepresentativeTree.Tree.branch 2229 (QuarticIntegerRepresentativeTree.Tree.leaf 2228 representative_2228) (QuarticIntegerRepresentativeTree.Tree.leaf 2229 representative_2229)) (QuarticIntegerRepresentativeTree.Tree.branch 2231 (QuarticIntegerRepresentativeTree.Tree.leaf 2230 representative_2230) (QuarticIntegerRepresentativeTree.Tree.leaf 2231 representative_2231)))) (QuarticIntegerRepresentativeTree.Tree.branch 2236 (QuarticIntegerRepresentativeTree.Tree.branch 2234 (QuarticIntegerRepresentativeTree.Tree.branch 2233 (QuarticIntegerRepresentativeTree.Tree.leaf 2232 representative_2232) (QuarticIntegerRepresentativeTree.Tree.leaf 2233 representative_2233)) (QuarticIntegerRepresentativeTree.Tree.branch 2235 (QuarticIntegerRepresentativeTree.Tree.leaf 2234 representative_2234) (QuarticIntegerRepresentativeTree.Tree.leaf 2235 representative_2235))) (QuarticIntegerRepresentativeTree.Tree.branch 2238 (QuarticIntegerRepresentativeTree.Tree.branch 2237 (QuarticIntegerRepresentativeTree.Tree.leaf 2236 representative_2236) (QuarticIntegerRepresentativeTree.Tree.leaf 2237 representative_2237)) (QuarticIntegerRepresentativeTree.Tree.branch 2239 (QuarticIntegerRepresentativeTree.Tree.leaf 2238 representative_2238) (QuarticIntegerRepresentativeTree.Tree.leaf 2239 representative_2239)))))))
theorem accepted_034 : All validRep tree_034 := ⟨⟨⟨⟨⟨⟨coefficient_2176,coefficient_2177⟩,⟨coefficient_2178,coefficient_2179⟩⟩,⟨⟨coefficient_2180,coefficient_2181⟩,⟨coefficient_2182,coefficient_2183⟩⟩⟩,⟨⟨⟨coefficient_2184,coefficient_2185⟩,⟨coefficient_2186,coefficient_2187⟩⟩,⟨⟨coefficient_2188,coefficient_2189⟩,⟨coefficient_2190,coefficient_2191⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2192,coefficient_2193⟩,⟨coefficient_2194,coefficient_2195⟩⟩,⟨⟨coefficient_2196,coefficient_2197⟩,⟨coefficient_2198,coefficient_2199⟩⟩⟩,⟨⟨⟨coefficient_2200,coefficient_2201⟩,⟨coefficient_2202,coefficient_2203⟩⟩,⟨⟨coefficient_2204,coefficient_2205⟩,⟨coefficient_2206,coefficient_2207⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2208,coefficient_2209⟩,⟨coefficient_2210,coefficient_2211⟩⟩,⟨⟨coefficient_2212,coefficient_2213⟩,⟨coefficient_2214,coefficient_2215⟩⟩⟩,⟨⟨⟨coefficient_2216,coefficient_2217⟩,⟨coefficient_2218,coefficient_2219⟩⟩,⟨⟨coefficient_2220,coefficient_2221⟩,⟨coefficient_2222,coefficient_2223⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2224,coefficient_2225⟩,⟨coefficient_2226,coefficient_2227⟩⟩,⟨⟨coefficient_2228,coefficient_2229⟩,⟨coefficient_2230,coefficient_2231⟩⟩⟩,⟨⟨⟨coefficient_2232,coefficient_2233⟩,⟨coefficient_2234,coefficient_2235⟩⟩,⟨⟨coefficient_2236,coefficient_2237⟩,⟨coefficient_2238,coefficient_2239⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

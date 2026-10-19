import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2240 : Rep := ⟨![0,10,5,16],268⟩
def representative_2241 : Rep := ⟨![0,10,5,17],226⟩
def representative_2242 : Rep := ⟨![0,10,5,18],285⟩
def representative_2243 : Rep := ⟨![0,10,5,19],232⟩
def representative_2244 : Rep := ⟨![0,10,5,20],247⟩
def representative_2245 : Rep := ⟨![0,10,5,22],245⟩
def representative_2246 : Rep := ⟨![0,10,5,23],234⟩
def representative_2247 : Rep := ⟨![0,10,5,24],237⟩
def representative_2248 : Rep := ⟨![0,10,5,25],247⟩
def representative_2249 : Rep := ⟨![0,10,5,26],235⟩
def representative_2250 : Rep := ⟨![0,10,5,27],246⟩
def representative_2251 : Rep := ⟨![0,10,5,28],462⟩
def representative_2252 : Rep := ⟨![0,10,5,30],462⟩
def representative_2253 : Rep := ⟨![0,10,5,31],243⟩
def representative_2254 : Rep := ⟨![0,10,5,32],242⟩
def representative_2255 : Rep := ⟨![0,10,5,33],462⟩
def representative_2256 : Rep := ⟨![0,10,5,34],243⟩
def representative_2257 : Rep := ⟨![0,10,5,35],462⟩
def representative_2258 : Rep := ⟨![0,10,5,36],462⟩
def representative_2259 : Rep := ⟨![0,10,5,38],462⟩
def representative_2260 : Rep := ⟨![0,10,5,39],462⟩
def representative_2261 : Rep := ⟨![0,10,5,40],237⟩
def representative_2262 : Rep := ⟨![0,10,5,41],243⟩
def representative_2263 : Rep := ⟨![0,10,5,42],462⟩
def representative_2264 : Rep := ⟨![0,10,5,43],462⟩
def representative_2265 : Rep := ⟨![0,10,5,44],462⟩
def representative_2266 : Rep := ⟨![0,10,5,46],462⟩
def representative_2267 : Rep := ⟨![0,10,5,47],243⟩
def representative_2268 : Rep := ⟨![0,10,5,48],266⟩
def representative_2269 : Rep := ⟨![0,10,5,49],234⟩
def representative_2270 : Rep := ⟨![0,10,5,50],245⟩
def representative_2271 : Rep := ⟨![0,10,5,51],462⟩
def representative_2272 : Rep := ⟨![0,10,5,52],243⟩
def representative_2273 : Rep := ⟨![0,10,5,54],245⟩
def representative_2274 : Rep := ⟨![0,10,5,55],234⟩
def representative_2275 : Rep := ⟨![0,10,5,56],154⟩
def representative_2276 : Rep := ⟨![0,10,5,57],282⟩
def representative_2277 : Rep := ⟨![0,10,5,58],229⟩
def representative_2278 : Rep := ⟨![0,10,5,59],252⟩
def representative_2279 : Rep := ⟨![0,10,6,11],235⟩
def representative_2280 : Rep := ⟨![0,10,6,12],462⟩
def representative_2281 : Rep := ⟨![0,10,6,16],178⟩
def representative_2282 : Rep := ⟨![0,10,6,17],291⟩
def representative_2283 : Rep := ⟨![0,10,6,18],234⟩
def representative_2284 : Rep := ⟨![0,10,6,19],462⟩
def representative_2285 : Rep := ⟨![0,10,6,20],462⟩
def representative_2286 : Rep := ⟨![0,10,6,21],462⟩
def representative_2287 : Rep := ⟨![0,10,6,23],292⟩
def representative_2288 : Rep := ⟨![0,10,6,24],266⟩
def representative_2289 : Rep := ⟨![0,10,6,25],235⟩
def representative_2290 : Rep := ⟨![0,10,6,26],462⟩
def representative_2291 : Rep := ⟨![0,10,6,27],462⟩
def representative_2292 : Rep := ⟨![0,10,6,28],462⟩
def representative_2293 : Rep := ⟨![0,10,6,29],462⟩
def representative_2294 : Rep := ⟨![0,10,6,31],235⟩
def representative_2295 : Rep := ⟨![0,10,6,32],237⟩
def representative_2296 : Rep := ⟨![0,10,6,33],462⟩
def representative_2297 : Rep := ⟨![0,10,6,34],462⟩
def representative_2298 : Rep := ⟨![0,10,6,35],462⟩
def representative_2299 : Rep := ⟨![0,10,6,36],462⟩
def representative_2300 : Rep := ⟨![0,10,6,37],462⟩
def representative_2301 : Rep := ⟨![0,10,6,39],462⟩
def representative_2302 : Rep := ⟨![0,10,6,40],266⟩
def representative_2303 : Rep := ⟨![0,10,6,41],235⟩
theorem coefficient_2240 : validRep representative_2240 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2240)=dictionary64.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_2241 : validRep representative_2241 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2241)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_2242 : validRep representative_2242 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2242)=dictionary64.getD 285 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_285]
  decide +kernel
theorem coefficient_2243 : validRep representative_2243 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2243)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2244 : validRep representative_2244 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2244)=dictionary64.getD 247 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_247]
  decide +kernel
theorem coefficient_2245 : validRep representative_2245 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2245)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_2246 : validRep representative_2246 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2246)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2247 : validRep representative_2247 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2247)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2248 : validRep representative_2248 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2248)=dictionary64.getD 247 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_247]
  decide +kernel
theorem coefficient_2249 : validRep representative_2249 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2249)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2250 : validRep representative_2250 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2250)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2251 : validRep representative_2251 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2251)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2252 : validRep representative_2252 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2252)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2253 : validRep representative_2253 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2253)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2254 : validRep representative_2254 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2254)=dictionary64.getD 242 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_242]
  decide +kernel
theorem coefficient_2255 : validRep representative_2255 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2255)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2256 : validRep representative_2256 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2256)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2257 : validRep representative_2257 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2257)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2258 : validRep representative_2258 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2258)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2259 : validRep representative_2259 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2259)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2260 : validRep representative_2260 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2260)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2261 : validRep representative_2261 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2261)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2262 : validRep representative_2262 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2262)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2263 : validRep representative_2263 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2263)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2264 : validRep representative_2264 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2264)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2265 : validRep representative_2265 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2265)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2266 : validRep representative_2266 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2266)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2267 : validRep representative_2267 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2267)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2268 : validRep representative_2268 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2268)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_2269 : validRep representative_2269 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2269)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2270 : validRep representative_2270 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2270)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_2271 : validRep representative_2271 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2271)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2272 : validRep representative_2272 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2272)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2273 : validRep representative_2273 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2273)=dictionary64.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_2274 : validRep representative_2274 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2274)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2275 : validRep representative_2275 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2275)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_2276 : validRep representative_2276 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2276)=dictionary64.getD 282 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_282]
  decide +kernel
theorem coefficient_2277 : validRep representative_2277 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2277)=dictionary64.getD 229 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_229]
  decide +kernel
theorem coefficient_2278 : validRep representative_2278 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2278)=dictionary64.getD 252 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_252]
  decide +kernel
theorem coefficient_2279 : validRep representative_2279 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2279)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2280 : validRep representative_2280 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2280)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2281 : validRep representative_2281 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2281)=dictionary64.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_2282 : validRep representative_2282 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2282)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2283 : validRep representative_2283 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2283)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2284 : validRep representative_2284 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2284)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2285 : validRep representative_2285 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2285)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2286 : validRep representative_2286 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2286)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2287 : validRep representative_2287 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2287)=dictionary64.getD 292 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_292]
  decide +kernel
theorem coefficient_2288 : validRep representative_2288 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2288)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_2289 : validRep representative_2289 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2289)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2290 : validRep representative_2290 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2290)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2291 : validRep representative_2291 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2291)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2292 : validRep representative_2292 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2292)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2293 : validRep representative_2293 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2293)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2294 : validRep representative_2294 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2294)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2295 : validRep representative_2295 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2295)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_2296 : validRep representative_2296 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2296)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2297 : validRep representative_2297 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2297)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2298 : validRep representative_2298 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2298)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2299 : validRep representative_2299 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2299)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2300 : validRep representative_2300 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2300)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2301 : validRep representative_2301 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2301)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2302 : validRep representative_2302 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2302)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_2303 : validRep representative_2303 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2303)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
def tree_035 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2272 (QuarticIntegerRepresentativeTree.Tree.branch 2256 (QuarticIntegerRepresentativeTree.Tree.branch 2248 (QuarticIntegerRepresentativeTree.Tree.branch 2244 (QuarticIntegerRepresentativeTree.Tree.branch 2242 (QuarticIntegerRepresentativeTree.Tree.branch 2241 (QuarticIntegerRepresentativeTree.Tree.leaf 2240 representative_2240) (QuarticIntegerRepresentativeTree.Tree.leaf 2241 representative_2241)) (QuarticIntegerRepresentativeTree.Tree.branch 2243 (QuarticIntegerRepresentativeTree.Tree.leaf 2242 representative_2242) (QuarticIntegerRepresentativeTree.Tree.leaf 2243 representative_2243))) (QuarticIntegerRepresentativeTree.Tree.branch 2246 (QuarticIntegerRepresentativeTree.Tree.branch 2245 (QuarticIntegerRepresentativeTree.Tree.leaf 2244 representative_2244) (QuarticIntegerRepresentativeTree.Tree.leaf 2245 representative_2245)) (QuarticIntegerRepresentativeTree.Tree.branch 2247 (QuarticIntegerRepresentativeTree.Tree.leaf 2246 representative_2246) (QuarticIntegerRepresentativeTree.Tree.leaf 2247 representative_2247)))) (QuarticIntegerRepresentativeTree.Tree.branch 2252 (QuarticIntegerRepresentativeTree.Tree.branch 2250 (QuarticIntegerRepresentativeTree.Tree.branch 2249 (QuarticIntegerRepresentativeTree.Tree.leaf 2248 representative_2248) (QuarticIntegerRepresentativeTree.Tree.leaf 2249 representative_2249)) (QuarticIntegerRepresentativeTree.Tree.branch 2251 (QuarticIntegerRepresentativeTree.Tree.leaf 2250 representative_2250) (QuarticIntegerRepresentativeTree.Tree.leaf 2251 representative_2251))) (QuarticIntegerRepresentativeTree.Tree.branch 2254 (QuarticIntegerRepresentativeTree.Tree.branch 2253 (QuarticIntegerRepresentativeTree.Tree.leaf 2252 representative_2252) (QuarticIntegerRepresentativeTree.Tree.leaf 2253 representative_2253)) (QuarticIntegerRepresentativeTree.Tree.branch 2255 (QuarticIntegerRepresentativeTree.Tree.leaf 2254 representative_2254) (QuarticIntegerRepresentativeTree.Tree.leaf 2255 representative_2255))))) (QuarticIntegerRepresentativeTree.Tree.branch 2264 (QuarticIntegerRepresentativeTree.Tree.branch 2260 (QuarticIntegerRepresentativeTree.Tree.branch 2258 (QuarticIntegerRepresentativeTree.Tree.branch 2257 (QuarticIntegerRepresentativeTree.Tree.leaf 2256 representative_2256) (QuarticIntegerRepresentativeTree.Tree.leaf 2257 representative_2257)) (QuarticIntegerRepresentativeTree.Tree.branch 2259 (QuarticIntegerRepresentativeTree.Tree.leaf 2258 representative_2258) (QuarticIntegerRepresentativeTree.Tree.leaf 2259 representative_2259))) (QuarticIntegerRepresentativeTree.Tree.branch 2262 (QuarticIntegerRepresentativeTree.Tree.branch 2261 (QuarticIntegerRepresentativeTree.Tree.leaf 2260 representative_2260) (QuarticIntegerRepresentativeTree.Tree.leaf 2261 representative_2261)) (QuarticIntegerRepresentativeTree.Tree.branch 2263 (QuarticIntegerRepresentativeTree.Tree.leaf 2262 representative_2262) (QuarticIntegerRepresentativeTree.Tree.leaf 2263 representative_2263)))) (QuarticIntegerRepresentativeTree.Tree.branch 2268 (QuarticIntegerRepresentativeTree.Tree.branch 2266 (QuarticIntegerRepresentativeTree.Tree.branch 2265 (QuarticIntegerRepresentativeTree.Tree.leaf 2264 representative_2264) (QuarticIntegerRepresentativeTree.Tree.leaf 2265 representative_2265)) (QuarticIntegerRepresentativeTree.Tree.branch 2267 (QuarticIntegerRepresentativeTree.Tree.leaf 2266 representative_2266) (QuarticIntegerRepresentativeTree.Tree.leaf 2267 representative_2267))) (QuarticIntegerRepresentativeTree.Tree.branch 2270 (QuarticIntegerRepresentativeTree.Tree.branch 2269 (QuarticIntegerRepresentativeTree.Tree.leaf 2268 representative_2268) (QuarticIntegerRepresentativeTree.Tree.leaf 2269 representative_2269)) (QuarticIntegerRepresentativeTree.Tree.branch 2271 (QuarticIntegerRepresentativeTree.Tree.leaf 2270 representative_2270) (QuarticIntegerRepresentativeTree.Tree.leaf 2271 representative_2271)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2288 (QuarticIntegerRepresentativeTree.Tree.branch 2280 (QuarticIntegerRepresentativeTree.Tree.branch 2276 (QuarticIntegerRepresentativeTree.Tree.branch 2274 (QuarticIntegerRepresentativeTree.Tree.branch 2273 (QuarticIntegerRepresentativeTree.Tree.leaf 2272 representative_2272) (QuarticIntegerRepresentativeTree.Tree.leaf 2273 representative_2273)) (QuarticIntegerRepresentativeTree.Tree.branch 2275 (QuarticIntegerRepresentativeTree.Tree.leaf 2274 representative_2274) (QuarticIntegerRepresentativeTree.Tree.leaf 2275 representative_2275))) (QuarticIntegerRepresentativeTree.Tree.branch 2278 (QuarticIntegerRepresentativeTree.Tree.branch 2277 (QuarticIntegerRepresentativeTree.Tree.leaf 2276 representative_2276) (QuarticIntegerRepresentativeTree.Tree.leaf 2277 representative_2277)) (QuarticIntegerRepresentativeTree.Tree.branch 2279 (QuarticIntegerRepresentativeTree.Tree.leaf 2278 representative_2278) (QuarticIntegerRepresentativeTree.Tree.leaf 2279 representative_2279)))) (QuarticIntegerRepresentativeTree.Tree.branch 2284 (QuarticIntegerRepresentativeTree.Tree.branch 2282 (QuarticIntegerRepresentativeTree.Tree.branch 2281 (QuarticIntegerRepresentativeTree.Tree.leaf 2280 representative_2280) (QuarticIntegerRepresentativeTree.Tree.leaf 2281 representative_2281)) (QuarticIntegerRepresentativeTree.Tree.branch 2283 (QuarticIntegerRepresentativeTree.Tree.leaf 2282 representative_2282) (QuarticIntegerRepresentativeTree.Tree.leaf 2283 representative_2283))) (QuarticIntegerRepresentativeTree.Tree.branch 2286 (QuarticIntegerRepresentativeTree.Tree.branch 2285 (QuarticIntegerRepresentativeTree.Tree.leaf 2284 representative_2284) (QuarticIntegerRepresentativeTree.Tree.leaf 2285 representative_2285)) (QuarticIntegerRepresentativeTree.Tree.branch 2287 (QuarticIntegerRepresentativeTree.Tree.leaf 2286 representative_2286) (QuarticIntegerRepresentativeTree.Tree.leaf 2287 representative_2287))))) (QuarticIntegerRepresentativeTree.Tree.branch 2296 (QuarticIntegerRepresentativeTree.Tree.branch 2292 (QuarticIntegerRepresentativeTree.Tree.branch 2290 (QuarticIntegerRepresentativeTree.Tree.branch 2289 (QuarticIntegerRepresentativeTree.Tree.leaf 2288 representative_2288) (QuarticIntegerRepresentativeTree.Tree.leaf 2289 representative_2289)) (QuarticIntegerRepresentativeTree.Tree.branch 2291 (QuarticIntegerRepresentativeTree.Tree.leaf 2290 representative_2290) (QuarticIntegerRepresentativeTree.Tree.leaf 2291 representative_2291))) (QuarticIntegerRepresentativeTree.Tree.branch 2294 (QuarticIntegerRepresentativeTree.Tree.branch 2293 (QuarticIntegerRepresentativeTree.Tree.leaf 2292 representative_2292) (QuarticIntegerRepresentativeTree.Tree.leaf 2293 representative_2293)) (QuarticIntegerRepresentativeTree.Tree.branch 2295 (QuarticIntegerRepresentativeTree.Tree.leaf 2294 representative_2294) (QuarticIntegerRepresentativeTree.Tree.leaf 2295 representative_2295)))) (QuarticIntegerRepresentativeTree.Tree.branch 2300 (QuarticIntegerRepresentativeTree.Tree.branch 2298 (QuarticIntegerRepresentativeTree.Tree.branch 2297 (QuarticIntegerRepresentativeTree.Tree.leaf 2296 representative_2296) (QuarticIntegerRepresentativeTree.Tree.leaf 2297 representative_2297)) (QuarticIntegerRepresentativeTree.Tree.branch 2299 (QuarticIntegerRepresentativeTree.Tree.leaf 2298 representative_2298) (QuarticIntegerRepresentativeTree.Tree.leaf 2299 representative_2299))) (QuarticIntegerRepresentativeTree.Tree.branch 2302 (QuarticIntegerRepresentativeTree.Tree.branch 2301 (QuarticIntegerRepresentativeTree.Tree.leaf 2300 representative_2300) (QuarticIntegerRepresentativeTree.Tree.leaf 2301 representative_2301)) (QuarticIntegerRepresentativeTree.Tree.branch 2303 (QuarticIntegerRepresentativeTree.Tree.leaf 2302 representative_2302) (QuarticIntegerRepresentativeTree.Tree.leaf 2303 representative_2303)))))))
theorem accepted_035 : All validRep tree_035 := ⟨⟨⟨⟨⟨⟨coefficient_2240,coefficient_2241⟩,⟨coefficient_2242,coefficient_2243⟩⟩,⟨⟨coefficient_2244,coefficient_2245⟩,⟨coefficient_2246,coefficient_2247⟩⟩⟩,⟨⟨⟨coefficient_2248,coefficient_2249⟩,⟨coefficient_2250,coefficient_2251⟩⟩,⟨⟨coefficient_2252,coefficient_2253⟩,⟨coefficient_2254,coefficient_2255⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2256,coefficient_2257⟩,⟨coefficient_2258,coefficient_2259⟩⟩,⟨⟨coefficient_2260,coefficient_2261⟩,⟨coefficient_2262,coefficient_2263⟩⟩⟩,⟨⟨⟨coefficient_2264,coefficient_2265⟩,⟨coefficient_2266,coefficient_2267⟩⟩,⟨⟨coefficient_2268,coefficient_2269⟩,⟨coefficient_2270,coefficient_2271⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2272,coefficient_2273⟩,⟨coefficient_2274,coefficient_2275⟩⟩,⟨⟨coefficient_2276,coefficient_2277⟩,⟨coefficient_2278,coefficient_2279⟩⟩⟩,⟨⟨⟨coefficient_2280,coefficient_2281⟩,⟨coefficient_2282,coefficient_2283⟩⟩,⟨⟨coefficient_2284,coefficient_2285⟩,⟨coefficient_2286,coefficient_2287⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2288,coefficient_2289⟩,⟨coefficient_2290,coefficient_2291⟩⟩,⟨⟨coefficient_2292,coefficient_2293⟩,⟨coefficient_2294,coefficient_2295⟩⟩⟩,⟨⟨⟨coefficient_2296,coefficient_2297⟩,⟨coefficient_2298,coefficient_2299⟩⟩,⟨⟨coefficient_2300,coefficient_2301⟩,⟨coefficient_2302,coefficient_2303⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

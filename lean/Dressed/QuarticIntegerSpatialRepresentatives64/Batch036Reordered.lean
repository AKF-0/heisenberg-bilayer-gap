import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2304 : Rep := ⟨![0,10,6,42],462⟩
def representative_2305 : Rep := ⟨![0,10,6,43],462⟩
def representative_2306 : Rep := ⟨![0,10,6,44],462⟩
def representative_2307 : Rep := ⟨![0,10,6,45],462⟩
def representative_2308 : Rep := ⟨![0,10,6,47],235⟩
def representative_2309 : Rep := ⟨![0,10,6,48],178⟩
def representative_2310 : Rep := ⟨![0,10,6,49],291⟩
def representative_2311 : Rep := ⟨![0,10,6,50],234⟩
def representative_2312 : Rep := ⟨![0,10,6,51],462⟩
def representative_2313 : Rep := ⟨![0,10,6,52],462⟩
def representative_2314 : Rep := ⟨![0,10,6,53],462⟩
def representative_2315 : Rep := ⟨![0,10,6,55],291⟩
def representative_2316 : Rep := ⟨![0,10,6,57],137⟩
def representative_2317 : Rep := ⟨![0,10,6,58],291⟩
def representative_2318 : Rep := ⟨![0,10,6,59],235⟩
def representative_2319 : Rep := ⟨![0,10,6,60],462⟩
def representative_2320 : Rep := ⟨![0,10,7,11],303⟩
def representative_2321 : Rep := ⟨![0,10,7,17],103⟩
def representative_2322 : Rep := ⟨![0,10,7,18],307⟩
def representative_2323 : Rep := ⟨![0,10,7,19],232⟩
def representative_2324 : Rep := ⟨![0,10,7,20],246⟩
def representative_2325 : Rep := ⟨![0,10,7,21],462⟩
def representative_2326 : Rep := ⟨![0,10,7,22],214⟩
def representative_2327 : Rep := ⟨![0,10,7,24],154⟩
def representative_2328 : Rep := ⟨![0,10,7,25],286⟩
def representative_2329 : Rep := ⟨![0,10,7,26],235⟩
def representative_2330 : Rep := ⟨![0,10,7,27],246⟩
def representative_2331 : Rep := ⟨![0,10,7,28],462⟩
def representative_2332 : Rep := ⟨![0,10,7,29],462⟩
def representative_2333 : Rep := ⟨![0,10,7,30],462⟩
def representative_2334 : Rep := ⟨![0,10,7,32],269⟩
def representative_2335 : Rep := ⟨![0,10,7,33],462⟩
def representative_2336 : Rep := ⟨![0,10,7,34],243⟩
def representative_2337 : Rep := ⟨![0,10,7,35],462⟩
def representative_2338 : Rep := ⟨![0,10,7,36],462⟩
def representative_2339 : Rep := ⟨![0,10,7,37],462⟩
def representative_2340 : Rep := ⟨![0,10,7,38],462⟩
def representative_2341 : Rep := ⟨![0,10,7,40],154⟩
def representative_2342 : Rep := ⟨![0,10,7,41],284⟩
def representative_2343 : Rep := ⟨![0,10,7,42],462⟩
def representative_2344 : Rep := ⟨![0,10,7,43],462⟩
def representative_2345 : Rep := ⟨![0,10,7,44],462⟩
def representative_2346 : Rep := ⟨![0,10,7,45],462⟩
def representative_2347 : Rep := ⟨![0,10,7,46],462⟩
def representative_2348 : Rep := ⟨![0,10,7,49],105⟩
def representative_2349 : Rep := ⟨![0,10,7,50],294⟩
def representative_2350 : Rep := ⟨![0,10,7,51],462⟩
def representative_2351 : Rep := ⟨![0,10,7,52],462⟩
def representative_2352 : Rep := ⟨![0,10,7,53],462⟩
def representative_2353 : Rep := ⟨![0,10,7,54],214⟩
def representative_2354 : Rep := ⟨![0,10,7,58],104⟩
def representative_2355 : Rep := ⟨![0,10,7,59],286⟩
def representative_2356 : Rep := ⟨![0,10,7,60],462⟩
def representative_2357 : Rep := ⟨![0,10,7,61],212⟩
def representative_2358 : Rep := ⟨![0,10,16,26],313⟩
def representative_2359 : Rep := ⟨![0,10,16,27],224⟩
def representative_2360 : Rep := ⟨![0,10,16,28],248⟩
def representative_2361 : Rep := ⟨![0,10,16,29],462⟩
def representative_2362 : Rep := ⟨![0,10,16,30],291⟩
def representative_2363 : Rep := ⟨![0,10,16,34],234⟩
def representative_2364 : Rep := ⟨![0,10,16,35],246⟩
def representative_2365 : Rep := ⟨![0,10,16,36],462⟩
def representative_2366 : Rep := ⟨![0,10,16,37],462⟩
def representative_2367 : Rep := ⟨![0,10,16,38],462⟩
theorem coefficient_2304 : validRep representative_2304 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2304)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2305 : validRep representative_2305 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2305)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2306 : validRep representative_2306 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2306)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2307 : validRep representative_2307 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2307)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2308 : validRep representative_2308 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2308)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2309 : validRep representative_2309 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2309)=dictionary64.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_2310 : validRep representative_2310 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2310)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2311 : validRep representative_2311 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2311)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2312 : validRep representative_2312 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2312)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2313 : validRep representative_2313 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2313)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2314 : validRep representative_2314 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2314)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2315 : validRep representative_2315 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2315)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2316 : validRep representative_2316 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2316)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2317 : validRep representative_2317 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2317)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2318 : validRep representative_2318 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2318)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2319 : validRep representative_2319 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2319)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2320 : validRep representative_2320 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2320)=dictionary64.getD 303 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_303]
  decide +kernel
theorem coefficient_2321 : validRep representative_2321 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2321)=dictionary64.getD 103 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_103]
  decide +kernel
theorem coefficient_2322 : validRep representative_2322 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2322)=dictionary64.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_2323 : validRep representative_2323 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2323)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2324 : validRep representative_2324 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2324)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2325 : validRep representative_2325 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2325)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2326 : validRep representative_2326 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2326)=dictionary64.getD 214 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_214]
  decide +kernel
theorem coefficient_2327 : validRep representative_2327 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2327)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_2328 : validRep representative_2328 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2328)=dictionary64.getD 286 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_286]
  decide +kernel
theorem coefficient_2329 : validRep representative_2329 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2329)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2330 : validRep representative_2330 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2330)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2331 : validRep representative_2331 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2331)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2332 : validRep representative_2332 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2332)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2333 : validRep representative_2333 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2333)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2334 : validRep representative_2334 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2334)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_2335 : validRep representative_2335 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2335)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2336 : validRep representative_2336 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2336)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2337 : validRep representative_2337 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2337)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2338 : validRep representative_2338 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2338)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2339 : validRep representative_2339 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2339)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2340 : validRep representative_2340 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2340)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2341 : validRep representative_2341 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2341)=dictionary64.getD 154 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_154]
  decide +kernel
theorem coefficient_2342 : validRep representative_2342 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2342)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2343 : validRep representative_2343 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2343)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2344 : validRep representative_2344 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2344)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2345 : validRep representative_2345 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2345)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2346 : validRep representative_2346 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2346)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2347 : validRep representative_2347 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2347)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2348 : validRep representative_2348 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2348)=dictionary64.getD 105 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_105]
  decide +kernel
theorem coefficient_2349 : validRep representative_2349 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2349)=dictionary64.getD 294 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_294]
  decide +kernel
theorem coefficient_2350 : validRep representative_2350 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2350)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2351 : validRep representative_2351 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2351)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2352 : validRep representative_2352 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2352)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2353 : validRep representative_2353 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2353)=dictionary64.getD 214 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_214]
  decide +kernel
theorem coefficient_2354 : validRep representative_2354 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2354)=dictionary64.getD 104 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_104]
  decide +kernel
theorem coefficient_2355 : validRep representative_2355 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2355)=dictionary64.getD 286 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_286]
  decide +kernel
theorem coefficient_2356 : validRep representative_2356 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2356)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2357 : validRep representative_2357 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2357)=dictionary64.getD 212 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_212]
  decide +kernel
theorem coefficient_2358 : validRep representative_2358 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2358)=dictionary64.getD 313 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_313]
  decide +kernel
theorem coefficient_2359 : validRep representative_2359 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2359)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2360 : validRep representative_2360 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2360)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2361 : validRep representative_2361 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2361)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2362 : validRep representative_2362 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2362)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2363 : validRep representative_2363 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2363)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2364 : validRep representative_2364 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2364)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2365 : validRep representative_2365 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2365)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2366 : validRep representative_2366 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2366)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2367 : validRep representative_2367 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2367)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_036 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2336 (QuarticIntegerRepresentativeTree.Tree.branch 2320 (QuarticIntegerRepresentativeTree.Tree.branch 2312 (QuarticIntegerRepresentativeTree.Tree.branch 2308 (QuarticIntegerRepresentativeTree.Tree.branch 2306 (QuarticIntegerRepresentativeTree.Tree.branch 2305 (QuarticIntegerRepresentativeTree.Tree.leaf 2304 representative_2304) (QuarticIntegerRepresentativeTree.Tree.leaf 2305 representative_2305)) (QuarticIntegerRepresentativeTree.Tree.branch 2307 (QuarticIntegerRepresentativeTree.Tree.leaf 2306 representative_2306) (QuarticIntegerRepresentativeTree.Tree.leaf 2307 representative_2307))) (QuarticIntegerRepresentativeTree.Tree.branch 2310 (QuarticIntegerRepresentativeTree.Tree.branch 2309 (QuarticIntegerRepresentativeTree.Tree.leaf 2308 representative_2308) (QuarticIntegerRepresentativeTree.Tree.leaf 2309 representative_2309)) (QuarticIntegerRepresentativeTree.Tree.branch 2311 (QuarticIntegerRepresentativeTree.Tree.leaf 2310 representative_2310) (QuarticIntegerRepresentativeTree.Tree.leaf 2311 representative_2311)))) (QuarticIntegerRepresentativeTree.Tree.branch 2316 (QuarticIntegerRepresentativeTree.Tree.branch 2314 (QuarticIntegerRepresentativeTree.Tree.branch 2313 (QuarticIntegerRepresentativeTree.Tree.leaf 2312 representative_2312) (QuarticIntegerRepresentativeTree.Tree.leaf 2313 representative_2313)) (QuarticIntegerRepresentativeTree.Tree.branch 2315 (QuarticIntegerRepresentativeTree.Tree.leaf 2314 representative_2314) (QuarticIntegerRepresentativeTree.Tree.leaf 2315 representative_2315))) (QuarticIntegerRepresentativeTree.Tree.branch 2318 (QuarticIntegerRepresentativeTree.Tree.branch 2317 (QuarticIntegerRepresentativeTree.Tree.leaf 2316 representative_2316) (QuarticIntegerRepresentativeTree.Tree.leaf 2317 representative_2317)) (QuarticIntegerRepresentativeTree.Tree.branch 2319 (QuarticIntegerRepresentativeTree.Tree.leaf 2318 representative_2318) (QuarticIntegerRepresentativeTree.Tree.leaf 2319 representative_2319))))) (QuarticIntegerRepresentativeTree.Tree.branch 2328 (QuarticIntegerRepresentativeTree.Tree.branch 2324 (QuarticIntegerRepresentativeTree.Tree.branch 2322 (QuarticIntegerRepresentativeTree.Tree.branch 2321 (QuarticIntegerRepresentativeTree.Tree.leaf 2320 representative_2320) (QuarticIntegerRepresentativeTree.Tree.leaf 2321 representative_2321)) (QuarticIntegerRepresentativeTree.Tree.branch 2323 (QuarticIntegerRepresentativeTree.Tree.leaf 2322 representative_2322) (QuarticIntegerRepresentativeTree.Tree.leaf 2323 representative_2323))) (QuarticIntegerRepresentativeTree.Tree.branch 2326 (QuarticIntegerRepresentativeTree.Tree.branch 2325 (QuarticIntegerRepresentativeTree.Tree.leaf 2324 representative_2324) (QuarticIntegerRepresentativeTree.Tree.leaf 2325 representative_2325)) (QuarticIntegerRepresentativeTree.Tree.branch 2327 (QuarticIntegerRepresentativeTree.Tree.leaf 2326 representative_2326) (QuarticIntegerRepresentativeTree.Tree.leaf 2327 representative_2327)))) (QuarticIntegerRepresentativeTree.Tree.branch 2332 (QuarticIntegerRepresentativeTree.Tree.branch 2330 (QuarticIntegerRepresentativeTree.Tree.branch 2329 (QuarticIntegerRepresentativeTree.Tree.leaf 2328 representative_2328) (QuarticIntegerRepresentativeTree.Tree.leaf 2329 representative_2329)) (QuarticIntegerRepresentativeTree.Tree.branch 2331 (QuarticIntegerRepresentativeTree.Tree.leaf 2330 representative_2330) (QuarticIntegerRepresentativeTree.Tree.leaf 2331 representative_2331))) (QuarticIntegerRepresentativeTree.Tree.branch 2334 (QuarticIntegerRepresentativeTree.Tree.branch 2333 (QuarticIntegerRepresentativeTree.Tree.leaf 2332 representative_2332) (QuarticIntegerRepresentativeTree.Tree.leaf 2333 representative_2333)) (QuarticIntegerRepresentativeTree.Tree.branch 2335 (QuarticIntegerRepresentativeTree.Tree.leaf 2334 representative_2334) (QuarticIntegerRepresentativeTree.Tree.leaf 2335 representative_2335)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2352 (QuarticIntegerRepresentativeTree.Tree.branch 2344 (QuarticIntegerRepresentativeTree.Tree.branch 2340 (QuarticIntegerRepresentativeTree.Tree.branch 2338 (QuarticIntegerRepresentativeTree.Tree.branch 2337 (QuarticIntegerRepresentativeTree.Tree.leaf 2336 representative_2336) (QuarticIntegerRepresentativeTree.Tree.leaf 2337 representative_2337)) (QuarticIntegerRepresentativeTree.Tree.branch 2339 (QuarticIntegerRepresentativeTree.Tree.leaf 2338 representative_2338) (QuarticIntegerRepresentativeTree.Tree.leaf 2339 representative_2339))) (QuarticIntegerRepresentativeTree.Tree.branch 2342 (QuarticIntegerRepresentativeTree.Tree.branch 2341 (QuarticIntegerRepresentativeTree.Tree.leaf 2340 representative_2340) (QuarticIntegerRepresentativeTree.Tree.leaf 2341 representative_2341)) (QuarticIntegerRepresentativeTree.Tree.branch 2343 (QuarticIntegerRepresentativeTree.Tree.leaf 2342 representative_2342) (QuarticIntegerRepresentativeTree.Tree.leaf 2343 representative_2343)))) (QuarticIntegerRepresentativeTree.Tree.branch 2348 (QuarticIntegerRepresentativeTree.Tree.branch 2346 (QuarticIntegerRepresentativeTree.Tree.branch 2345 (QuarticIntegerRepresentativeTree.Tree.leaf 2344 representative_2344) (QuarticIntegerRepresentativeTree.Tree.leaf 2345 representative_2345)) (QuarticIntegerRepresentativeTree.Tree.branch 2347 (QuarticIntegerRepresentativeTree.Tree.leaf 2346 representative_2346) (QuarticIntegerRepresentativeTree.Tree.leaf 2347 representative_2347))) (QuarticIntegerRepresentativeTree.Tree.branch 2350 (QuarticIntegerRepresentativeTree.Tree.branch 2349 (QuarticIntegerRepresentativeTree.Tree.leaf 2348 representative_2348) (QuarticIntegerRepresentativeTree.Tree.leaf 2349 representative_2349)) (QuarticIntegerRepresentativeTree.Tree.branch 2351 (QuarticIntegerRepresentativeTree.Tree.leaf 2350 representative_2350) (QuarticIntegerRepresentativeTree.Tree.leaf 2351 representative_2351))))) (QuarticIntegerRepresentativeTree.Tree.branch 2360 (QuarticIntegerRepresentativeTree.Tree.branch 2356 (QuarticIntegerRepresentativeTree.Tree.branch 2354 (QuarticIntegerRepresentativeTree.Tree.branch 2353 (QuarticIntegerRepresentativeTree.Tree.leaf 2352 representative_2352) (QuarticIntegerRepresentativeTree.Tree.leaf 2353 representative_2353)) (QuarticIntegerRepresentativeTree.Tree.branch 2355 (QuarticIntegerRepresentativeTree.Tree.leaf 2354 representative_2354) (QuarticIntegerRepresentativeTree.Tree.leaf 2355 representative_2355))) (QuarticIntegerRepresentativeTree.Tree.branch 2358 (QuarticIntegerRepresentativeTree.Tree.branch 2357 (QuarticIntegerRepresentativeTree.Tree.leaf 2356 representative_2356) (QuarticIntegerRepresentativeTree.Tree.leaf 2357 representative_2357)) (QuarticIntegerRepresentativeTree.Tree.branch 2359 (QuarticIntegerRepresentativeTree.Tree.leaf 2358 representative_2358) (QuarticIntegerRepresentativeTree.Tree.leaf 2359 representative_2359)))) (QuarticIntegerRepresentativeTree.Tree.branch 2364 (QuarticIntegerRepresentativeTree.Tree.branch 2362 (QuarticIntegerRepresentativeTree.Tree.branch 2361 (QuarticIntegerRepresentativeTree.Tree.leaf 2360 representative_2360) (QuarticIntegerRepresentativeTree.Tree.leaf 2361 representative_2361)) (QuarticIntegerRepresentativeTree.Tree.branch 2363 (QuarticIntegerRepresentativeTree.Tree.leaf 2362 representative_2362) (QuarticIntegerRepresentativeTree.Tree.leaf 2363 representative_2363))) (QuarticIntegerRepresentativeTree.Tree.branch 2366 (QuarticIntegerRepresentativeTree.Tree.branch 2365 (QuarticIntegerRepresentativeTree.Tree.leaf 2364 representative_2364) (QuarticIntegerRepresentativeTree.Tree.leaf 2365 representative_2365)) (QuarticIntegerRepresentativeTree.Tree.branch 2367 (QuarticIntegerRepresentativeTree.Tree.leaf 2366 representative_2366) (QuarticIntegerRepresentativeTree.Tree.leaf 2367 representative_2367)))))))
theorem accepted_036 : All validRep tree_036 := ⟨⟨⟨⟨⟨⟨coefficient_2304,coefficient_2305⟩,⟨coefficient_2306,coefficient_2307⟩⟩,⟨⟨coefficient_2308,coefficient_2309⟩,⟨coefficient_2310,coefficient_2311⟩⟩⟩,⟨⟨⟨coefficient_2312,coefficient_2313⟩,⟨coefficient_2314,coefficient_2315⟩⟩,⟨⟨coefficient_2316,coefficient_2317⟩,⟨coefficient_2318,coefficient_2319⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2320,coefficient_2321⟩,⟨coefficient_2322,coefficient_2323⟩⟩,⟨⟨coefficient_2324,coefficient_2325⟩,⟨coefficient_2326,coefficient_2327⟩⟩⟩,⟨⟨⟨coefficient_2328,coefficient_2329⟩,⟨coefficient_2330,coefficient_2331⟩⟩,⟨⟨coefficient_2332,coefficient_2333⟩,⟨coefficient_2334,coefficient_2335⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2336,coefficient_2337⟩,⟨coefficient_2338,coefficient_2339⟩⟩,⟨⟨coefficient_2340,coefficient_2341⟩,⟨coefficient_2342,coefficient_2343⟩⟩⟩,⟨⟨⟨coefficient_2344,coefficient_2345⟩,⟨coefficient_2346,coefficient_2347⟩⟩,⟨⟨coefficient_2348,coefficient_2349⟩,⟨coefficient_2350,coefficient_2351⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2352,coefficient_2353⟩,⟨coefficient_2354,coefficient_2355⟩⟩,⟨⟨coefficient_2356,coefficient_2357⟩,⟨coefficient_2358,coefficient_2359⟩⟩⟩,⟨⟨⟨coefficient_2360,coefficient_2361⟩,⟨coefficient_2362,coefficient_2363⟩⟩,⟨⟨coefficient_2364,coefficient_2365⟩,⟨coefficient_2366,coefficient_2367⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2368 : Rep := ⟨![0,10,16,41],235⟩
def representative_2369 : Rep := ⟨![0,10,16,42],244⟩
def representative_2370 : Rep := ⟨![0,10,16,43],462⟩
def representative_2371 : Rep := ⟨![0,10,16,44],462⟩
def representative_2372 : Rep := ⟨![0,10,16,45],462⟩
def representative_2373 : Rep := ⟨![0,10,16,46],462⟩
def representative_2374 : Rep := ⟨![0,10,16,47],235⟩
def representative_2375 : Rep := ⟨![0,10,16,49],292⟩
def representative_2376 : Rep := ⟨![0,10,16,50],228⟩
def representative_2377 : Rep := ⟨![0,10,16,51],246⟩
def representative_2378 : Rep := ⟨![0,10,16,52],462⟩
def representative_2379 : Rep := ⟨![0,10,16,53],462⟩
def representative_2380 : Rep := ⟨![0,10,16,54],234⟩
def representative_2381 : Rep := ⟨![0,10,16,55],291⟩
def representative_2382 : Rep := ⟨![0,10,16,57],136⟩
def representative_2383 : Rep := ⟨![0,10,16,58],313⟩
def representative_2384 : Rep := ⟨![0,10,16,59],222⟩
def representative_2385 : Rep := ⟨![0,10,16,60],248⟩
def representative_2386 : Rep := ⟨![0,10,16,61],235⟩
def representative_2387 : Rep := ⟨![0,10,16,62],291⟩
def representative_2388 : Rep := ⟨![0,10,16,63],137⟩
def representative_2389 : Rep := ⟨![0,10,17,27],322⟩
def representative_2390 : Rep := ⟨![0,10,17,28],228⟩
def representative_2391 : Rep := ⟨![0,10,17,29],462⟩
def representative_2392 : Rep := ⟨![0,10,17,30],462⟩
def representative_2393 : Rep := ⟨![0,10,17,31],312⟩
def representative_2394 : Rep := ⟨![0,10,17,35],232⟩
def representative_2395 : Rep := ⟨![0,10,17,36],462⟩
def representative_2396 : Rep := ⟨![0,10,17,37],462⟩
def representative_2397 : Rep := ⟨![0,10,17,38],462⟩
def representative_2398 : Rep := ⟨![0,10,17,39],462⟩
def representative_2399 : Rep := ⟨![0,10,17,40],234⟩
def representative_2400 : Rep := ⟨![0,10,17,42],235⟩
def representative_2401 : Rep := ⟨![0,10,17,43],462⟩
def representative_2402 : Rep := ⟨![0,10,17,44],462⟩
def representative_2403 : Rep := ⟨![0,10,17,45],462⟩
def representative_2404 : Rep := ⟨![0,10,17,46],462⟩
def representative_2405 : Rep := ⟨![0,10,17,47],246⟩
def representative_2406 : Rep := ⟨![0,10,17,48],291⟩
def representative_2407 : Rep := ⟨![0,10,17,50],283⟩
def representative_2408 : Rep := ⟨![0,10,17,51],232⟩
def representative_2409 : Rep := ⟨![0,10,17,52],462⟩
def representative_2410 : Rep := ⟨![0,10,17,53],462⟩
def representative_2411 : Rep := ⟨![0,10,17,54],248⟩
def representative_2412 : Rep := ⟨![0,10,17,55],224⟩
def representative_2413 : Rep := ⟨![0,10,17,56],102⟩
def representative_2414 : Rep := ⟨![0,10,17,59],312⟩
def representative_2415 : Rep := ⟨![0,10,17,60],228⟩
def representative_2416 : Rep := ⟨![0,10,17,61],246⟩
def representative_2417 : Rep := ⟨![0,10,17,62],224⟩
def representative_2418 : Rep := ⟨![0,10,17,63],309⟩
def representative_2419 : Rep := ⟨![0,10,18,24],216⟩
def representative_2420 : Rep := ⟨![0,10,18,28],215⟩
def representative_2421 : Rep := ⟨![0,10,18,29],462⟩
def representative_2422 : Rep := ⟨![0,10,18,30],462⟩
def representative_2423 : Rep := ⟨![0,10,18,31],462⟩
def representative_2424 : Rep := ⟨![0,10,18,32],462⟩
def representative_2425 : Rep := ⟨![0,10,18,36],462⟩
def representative_2426 : Rep := ⟨![0,10,18,37],462⟩
def representative_2427 : Rep := ⟨![0,10,18,38],462⟩
def representative_2428 : Rep := ⟨![0,10,18,39],462⟩
def representative_2429 : Rep := ⟨![0,10,18,40],244⟩
def representative_2430 : Rep := ⟨![0,10,18,41],462⟩
def representative_2431 : Rep := ⟨![0,10,18,43],462⟩
theorem coefficient_2368 : validRep representative_2368 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2368)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2369 : validRep representative_2369 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2369)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2370 : validRep representative_2370 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2370)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2371 : validRep representative_2371 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2371)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2372 : validRep representative_2372 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2372)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2373 : validRep representative_2373 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2373)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2374 : validRep representative_2374 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2374)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2375 : validRep representative_2375 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2375)=dictionary64.getD 292 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_292]
  decide +kernel
theorem coefficient_2376 : validRep representative_2376 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2376)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2377 : validRep representative_2377 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2377)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2378 : validRep representative_2378 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2378)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2379 : validRep representative_2379 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2379)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2380 : validRep representative_2380 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2380)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2381 : validRep representative_2381 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2381)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2382 : validRep representative_2382 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2382)=dictionary64.getD 136 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_136]
  decide +kernel
theorem coefficient_2383 : validRep representative_2383 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2383)=dictionary64.getD 313 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_313]
  decide +kernel
theorem coefficient_2384 : validRep representative_2384 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2384)=dictionary64.getD 222 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_222]
  decide +kernel
theorem coefficient_2385 : validRep representative_2385 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2385)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2386 : validRep representative_2386 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2386)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2387 : validRep representative_2387 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2387)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2388 : validRep representative_2388 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2388)=dictionary64.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_2389 : validRep representative_2389 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2389)=dictionary64.getD 322 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_322]
  decide +kernel
theorem coefficient_2390 : validRep representative_2390 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2390)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2391 : validRep representative_2391 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2391)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2392 : validRep representative_2392 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2392)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2393 : validRep representative_2393 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2393)=dictionary64.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_2394 : validRep representative_2394 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2394)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2395 : validRep representative_2395 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2395)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2396 : validRep representative_2396 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2396)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2397 : validRep representative_2397 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2397)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2398 : validRep representative_2398 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2398)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2399 : validRep representative_2399 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2399)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2400 : validRep representative_2400 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2400)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2401 : validRep representative_2401 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2401)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2402 : validRep representative_2402 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2402)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2403 : validRep representative_2403 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2403)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2404 : validRep representative_2404 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2404)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2405 : validRep representative_2405 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2405)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2406 : validRep representative_2406 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2406)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2407 : validRep representative_2407 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2407)=dictionary64.getD 283 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_283]
  decide +kernel
theorem coefficient_2408 : validRep representative_2408 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2408)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2409 : validRep representative_2409 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2409)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2410 : validRep representative_2410 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2410)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2411 : validRep representative_2411 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2411)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2412 : validRep representative_2412 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2412)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2413 : validRep representative_2413 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2413)=dictionary64.getD 102 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_102]
  decide +kernel
theorem coefficient_2414 : validRep representative_2414 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2414)=dictionary64.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_2415 : validRep representative_2415 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2415)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2416 : validRep representative_2416 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2416)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2417 : validRep representative_2417 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2417)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2418 : validRep representative_2418 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2418)=dictionary64.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_2419 : validRep representative_2419 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2419)=dictionary64.getD 216 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_216]
  decide +kernel
theorem coefficient_2420 : validRep representative_2420 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2420)=dictionary64.getD 215 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_215]
  decide +kernel
theorem coefficient_2421 : validRep representative_2421 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2421)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2422 : validRep representative_2422 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2422)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2423 : validRep representative_2423 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2423)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2424 : validRep representative_2424 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2424)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2425 : validRep representative_2425 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2425)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2426 : validRep representative_2426 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2426)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2427 : validRep representative_2427 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2427)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2428 : validRep representative_2428 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2428)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2429 : validRep representative_2429 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2429)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2430 : validRep representative_2430 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2430)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2431 : validRep representative_2431 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2431)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_037 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2400 (QuarticIntegerRepresentativeTree.Tree.branch 2384 (QuarticIntegerRepresentativeTree.Tree.branch 2376 (QuarticIntegerRepresentativeTree.Tree.branch 2372 (QuarticIntegerRepresentativeTree.Tree.branch 2370 (QuarticIntegerRepresentativeTree.Tree.branch 2369 (QuarticIntegerRepresentativeTree.Tree.leaf 2368 representative_2368) (QuarticIntegerRepresentativeTree.Tree.leaf 2369 representative_2369)) (QuarticIntegerRepresentativeTree.Tree.branch 2371 (QuarticIntegerRepresentativeTree.Tree.leaf 2370 representative_2370) (QuarticIntegerRepresentativeTree.Tree.leaf 2371 representative_2371))) (QuarticIntegerRepresentativeTree.Tree.branch 2374 (QuarticIntegerRepresentativeTree.Tree.branch 2373 (QuarticIntegerRepresentativeTree.Tree.leaf 2372 representative_2372) (QuarticIntegerRepresentativeTree.Tree.leaf 2373 representative_2373)) (QuarticIntegerRepresentativeTree.Tree.branch 2375 (QuarticIntegerRepresentativeTree.Tree.leaf 2374 representative_2374) (QuarticIntegerRepresentativeTree.Tree.leaf 2375 representative_2375)))) (QuarticIntegerRepresentativeTree.Tree.branch 2380 (QuarticIntegerRepresentativeTree.Tree.branch 2378 (QuarticIntegerRepresentativeTree.Tree.branch 2377 (QuarticIntegerRepresentativeTree.Tree.leaf 2376 representative_2376) (QuarticIntegerRepresentativeTree.Tree.leaf 2377 representative_2377)) (QuarticIntegerRepresentativeTree.Tree.branch 2379 (QuarticIntegerRepresentativeTree.Tree.leaf 2378 representative_2378) (QuarticIntegerRepresentativeTree.Tree.leaf 2379 representative_2379))) (QuarticIntegerRepresentativeTree.Tree.branch 2382 (QuarticIntegerRepresentativeTree.Tree.branch 2381 (QuarticIntegerRepresentativeTree.Tree.leaf 2380 representative_2380) (QuarticIntegerRepresentativeTree.Tree.leaf 2381 representative_2381)) (QuarticIntegerRepresentativeTree.Tree.branch 2383 (QuarticIntegerRepresentativeTree.Tree.leaf 2382 representative_2382) (QuarticIntegerRepresentativeTree.Tree.leaf 2383 representative_2383))))) (QuarticIntegerRepresentativeTree.Tree.branch 2392 (QuarticIntegerRepresentativeTree.Tree.branch 2388 (QuarticIntegerRepresentativeTree.Tree.branch 2386 (QuarticIntegerRepresentativeTree.Tree.branch 2385 (QuarticIntegerRepresentativeTree.Tree.leaf 2384 representative_2384) (QuarticIntegerRepresentativeTree.Tree.leaf 2385 representative_2385)) (QuarticIntegerRepresentativeTree.Tree.branch 2387 (QuarticIntegerRepresentativeTree.Tree.leaf 2386 representative_2386) (QuarticIntegerRepresentativeTree.Tree.leaf 2387 representative_2387))) (QuarticIntegerRepresentativeTree.Tree.branch 2390 (QuarticIntegerRepresentativeTree.Tree.branch 2389 (QuarticIntegerRepresentativeTree.Tree.leaf 2388 representative_2388) (QuarticIntegerRepresentativeTree.Tree.leaf 2389 representative_2389)) (QuarticIntegerRepresentativeTree.Tree.branch 2391 (QuarticIntegerRepresentativeTree.Tree.leaf 2390 representative_2390) (QuarticIntegerRepresentativeTree.Tree.leaf 2391 representative_2391)))) (QuarticIntegerRepresentativeTree.Tree.branch 2396 (QuarticIntegerRepresentativeTree.Tree.branch 2394 (QuarticIntegerRepresentativeTree.Tree.branch 2393 (QuarticIntegerRepresentativeTree.Tree.leaf 2392 representative_2392) (QuarticIntegerRepresentativeTree.Tree.leaf 2393 representative_2393)) (QuarticIntegerRepresentativeTree.Tree.branch 2395 (QuarticIntegerRepresentativeTree.Tree.leaf 2394 representative_2394) (QuarticIntegerRepresentativeTree.Tree.leaf 2395 representative_2395))) (QuarticIntegerRepresentativeTree.Tree.branch 2398 (QuarticIntegerRepresentativeTree.Tree.branch 2397 (QuarticIntegerRepresentativeTree.Tree.leaf 2396 representative_2396) (QuarticIntegerRepresentativeTree.Tree.leaf 2397 representative_2397)) (QuarticIntegerRepresentativeTree.Tree.branch 2399 (QuarticIntegerRepresentativeTree.Tree.leaf 2398 representative_2398) (QuarticIntegerRepresentativeTree.Tree.leaf 2399 representative_2399)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2416 (QuarticIntegerRepresentativeTree.Tree.branch 2408 (QuarticIntegerRepresentativeTree.Tree.branch 2404 (QuarticIntegerRepresentativeTree.Tree.branch 2402 (QuarticIntegerRepresentativeTree.Tree.branch 2401 (QuarticIntegerRepresentativeTree.Tree.leaf 2400 representative_2400) (QuarticIntegerRepresentativeTree.Tree.leaf 2401 representative_2401)) (QuarticIntegerRepresentativeTree.Tree.branch 2403 (QuarticIntegerRepresentativeTree.Tree.leaf 2402 representative_2402) (QuarticIntegerRepresentativeTree.Tree.leaf 2403 representative_2403))) (QuarticIntegerRepresentativeTree.Tree.branch 2406 (QuarticIntegerRepresentativeTree.Tree.branch 2405 (QuarticIntegerRepresentativeTree.Tree.leaf 2404 representative_2404) (QuarticIntegerRepresentativeTree.Tree.leaf 2405 representative_2405)) (QuarticIntegerRepresentativeTree.Tree.branch 2407 (QuarticIntegerRepresentativeTree.Tree.leaf 2406 representative_2406) (QuarticIntegerRepresentativeTree.Tree.leaf 2407 representative_2407)))) (QuarticIntegerRepresentativeTree.Tree.branch 2412 (QuarticIntegerRepresentativeTree.Tree.branch 2410 (QuarticIntegerRepresentativeTree.Tree.branch 2409 (QuarticIntegerRepresentativeTree.Tree.leaf 2408 representative_2408) (QuarticIntegerRepresentativeTree.Tree.leaf 2409 representative_2409)) (QuarticIntegerRepresentativeTree.Tree.branch 2411 (QuarticIntegerRepresentativeTree.Tree.leaf 2410 representative_2410) (QuarticIntegerRepresentativeTree.Tree.leaf 2411 representative_2411))) (QuarticIntegerRepresentativeTree.Tree.branch 2414 (QuarticIntegerRepresentativeTree.Tree.branch 2413 (QuarticIntegerRepresentativeTree.Tree.leaf 2412 representative_2412) (QuarticIntegerRepresentativeTree.Tree.leaf 2413 representative_2413)) (QuarticIntegerRepresentativeTree.Tree.branch 2415 (QuarticIntegerRepresentativeTree.Tree.leaf 2414 representative_2414) (QuarticIntegerRepresentativeTree.Tree.leaf 2415 representative_2415))))) (QuarticIntegerRepresentativeTree.Tree.branch 2424 (QuarticIntegerRepresentativeTree.Tree.branch 2420 (QuarticIntegerRepresentativeTree.Tree.branch 2418 (QuarticIntegerRepresentativeTree.Tree.branch 2417 (QuarticIntegerRepresentativeTree.Tree.leaf 2416 representative_2416) (QuarticIntegerRepresentativeTree.Tree.leaf 2417 representative_2417)) (QuarticIntegerRepresentativeTree.Tree.branch 2419 (QuarticIntegerRepresentativeTree.Tree.leaf 2418 representative_2418) (QuarticIntegerRepresentativeTree.Tree.leaf 2419 representative_2419))) (QuarticIntegerRepresentativeTree.Tree.branch 2422 (QuarticIntegerRepresentativeTree.Tree.branch 2421 (QuarticIntegerRepresentativeTree.Tree.leaf 2420 representative_2420) (QuarticIntegerRepresentativeTree.Tree.leaf 2421 representative_2421)) (QuarticIntegerRepresentativeTree.Tree.branch 2423 (QuarticIntegerRepresentativeTree.Tree.leaf 2422 representative_2422) (QuarticIntegerRepresentativeTree.Tree.leaf 2423 representative_2423)))) (QuarticIntegerRepresentativeTree.Tree.branch 2428 (QuarticIntegerRepresentativeTree.Tree.branch 2426 (QuarticIntegerRepresentativeTree.Tree.branch 2425 (QuarticIntegerRepresentativeTree.Tree.leaf 2424 representative_2424) (QuarticIntegerRepresentativeTree.Tree.leaf 2425 representative_2425)) (QuarticIntegerRepresentativeTree.Tree.branch 2427 (QuarticIntegerRepresentativeTree.Tree.leaf 2426 representative_2426) (QuarticIntegerRepresentativeTree.Tree.leaf 2427 representative_2427))) (QuarticIntegerRepresentativeTree.Tree.branch 2430 (QuarticIntegerRepresentativeTree.Tree.branch 2429 (QuarticIntegerRepresentativeTree.Tree.leaf 2428 representative_2428) (QuarticIntegerRepresentativeTree.Tree.leaf 2429 representative_2429)) (QuarticIntegerRepresentativeTree.Tree.branch 2431 (QuarticIntegerRepresentativeTree.Tree.leaf 2430 representative_2430) (QuarticIntegerRepresentativeTree.Tree.leaf 2431 representative_2431)))))))
theorem accepted_037 : All validRep tree_037 := ⟨⟨⟨⟨⟨⟨coefficient_2368,coefficient_2369⟩,⟨coefficient_2370,coefficient_2371⟩⟩,⟨⟨coefficient_2372,coefficient_2373⟩,⟨coefficient_2374,coefficient_2375⟩⟩⟩,⟨⟨⟨coefficient_2376,coefficient_2377⟩,⟨coefficient_2378,coefficient_2379⟩⟩,⟨⟨coefficient_2380,coefficient_2381⟩,⟨coefficient_2382,coefficient_2383⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2384,coefficient_2385⟩,⟨coefficient_2386,coefficient_2387⟩⟩,⟨⟨coefficient_2388,coefficient_2389⟩,⟨coefficient_2390,coefficient_2391⟩⟩⟩,⟨⟨⟨coefficient_2392,coefficient_2393⟩,⟨coefficient_2394,coefficient_2395⟩⟩,⟨⟨coefficient_2396,coefficient_2397⟩,⟨coefficient_2398,coefficient_2399⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2400,coefficient_2401⟩,⟨coefficient_2402,coefficient_2403⟩⟩,⟨⟨coefficient_2404,coefficient_2405⟩,⟨coefficient_2406,coefficient_2407⟩⟩⟩,⟨⟨⟨coefficient_2408,coefficient_2409⟩,⟨coefficient_2410,coefficient_2411⟩⟩,⟨⟨coefficient_2412,coefficient_2413⟩,⟨coefficient_2414,coefficient_2415⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2416,coefficient_2417⟩,⟨coefficient_2418,coefficient_2419⟩⟩,⟨⟨coefficient_2420,coefficient_2421⟩,⟨coefficient_2422,coefficient_2423⟩⟩⟩,⟨⟨⟨coefficient_2424,coefficient_2425⟩,⟨coefficient_2426,coefficient_2427⟩⟩,⟨⟨coefficient_2428,coefficient_2429⟩,⟨coefficient_2430,coefficient_2431⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2432 : Rep := ⟨![0,10,18,44],462⟩
def representative_2433 : Rep := ⟨![0,10,18,45],462⟩
def representative_2434 : Rep := ⟨![0,10,18,46],462⟩
def representative_2435 : Rep := ⟨![0,10,18,47],462⟩
def representative_2436 : Rep := ⟨![0,10,18,48],234⟩
def representative_2437 : Rep := ⟨![0,10,18,49],287⟩
def representative_2438 : Rep := ⟨![0,10,18,51],284⟩
def representative_2439 : Rep := ⟨![0,10,18,52],462⟩
def representative_2440 : Rep := ⟨![0,10,18,53],462⟩
def representative_2441 : Rep := ⟨![0,10,18,54],462⟩
def representative_2442 : Rep := ⟨![0,10,18,55],248⟩
def representative_2443 : Rep := ⟨![0,10,18,56],316⟩
def representative_2444 : Rep := ⟨![0,10,18,59],105⟩
def representative_2445 : Rep := ⟨![0,10,18,60],293⟩
def representative_2446 : Rep := ⟨![0,10,18,61],462⟩
def representative_2447 : Rep := ⟨![0,10,18,62],248⟩
def representative_2448 : Rep := ⟨![0,10,18,63],228⟩
def representative_2449 : Rep := ⟨![0,10,19,24],228⟩
def representative_2450 : Rep := ⟨![0,10,19,29],462⟩
def representative_2451 : Rep := ⟨![0,10,19,30],462⟩
def representative_2452 : Rep := ⟨![0,10,19,31],462⟩
def representative_2453 : Rep := ⟨![0,10,19,32],462⟩
def representative_2454 : Rep := ⟨![0,10,19,33],232⟩
def representative_2455 : Rep := ⟨![0,10,19,36],462⟩
def representative_2456 : Rep := ⟨![0,10,19,37],462⟩
def representative_2457 : Rep := ⟨![0,10,19,38],462⟩
def representative_2458 : Rep := ⟨![0,10,19,39],462⟩
def representative_2459 : Rep := ⟨![0,10,19,40],462⟩
def representative_2460 : Rep := ⟨![0,10,19,41],462⟩
def representative_2461 : Rep := ⟨![0,10,19,42],235⟩
def representative_2462 : Rep := ⟨![0,10,19,44],462⟩
def representative_2463 : Rep := ⟨![0,10,19,45],462⟩
def representative_2464 : Rep := ⟨![0,10,19,46],462⟩
def representative_2465 : Rep := ⟨![0,10,19,47],462⟩
def representative_2466 : Rep := ⟨![0,10,19,48],462⟩
def representative_2467 : Rep := ⟨![0,10,19,49],232⟩
def representative_2468 : Rep := ⟨![0,10,19,50],279⟩
def representative_2469 : Rep := ⟨![0,10,19,52],462⟩
def representative_2470 : Rep := ⟨![0,10,19,53],462⟩
def representative_2471 : Rep := ⟨![0,10,19,54],462⟩
def representative_2472 : Rep := ⟨![0,10,19,55],462⟩
def representative_2473 : Rep := ⟨![0,10,19,60],228⟩
def representative_2474 : Rep := ⟨![0,10,19,61],462⟩
def representative_2475 : Rep := ⟨![0,10,19,62],462⟩
def representative_2476 : Rep := ⟨![0,10,19,63],462⟩
def representative_2477 : Rep := ⟨![0,10,20,24],248⟩
def representative_2478 : Rep := ⟨![0,10,20,25],224⟩
def representative_2479 : Rep := ⟨![0,10,20,30],462⟩
def representative_2480 : Rep := ⟨![0,10,20,31],462⟩
def representative_2481 : Rep := ⟨![0,10,20,32],462⟩
def representative_2482 : Rep := ⟨![0,10,20,33],246⟩
def representative_2483 : Rep := ⟨![0,10,20,34],234⟩
def representative_2484 : Rep := ⟨![0,10,20,35],246⟩
def representative_2485 : Rep := ⟨![0,10,20,37],462⟩
def representative_2486 : Rep := ⟨![0,10,20,38],462⟩
def representative_2487 : Rep := ⟨![0,10,20,39],462⟩
def representative_2488 : Rep := ⟨![0,10,20,40],462⟩
def representative_2489 : Rep := ⟨![0,10,20,41],462⟩
def representative_2490 : Rep := ⟨![0,10,20,42],244⟩
def representative_2491 : Rep := ⟨![0,10,20,43],462⟩
def representative_2492 : Rep := ⟨![0,10,20,45],462⟩
def representative_2493 : Rep := ⟨![0,10,20,46],462⟩
def representative_2494 : Rep := ⟨![0,10,20,47],462⟩
def representative_2495 : Rep := ⟨![0,10,20,48],462⟩
theorem coefficient_2432 : validRep representative_2432 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2432)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2433 : validRep representative_2433 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2433)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2434 : validRep representative_2434 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2434)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2435 : validRep representative_2435 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2435)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2436 : validRep representative_2436 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2436)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2437 : validRep representative_2437 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2437)=dictionary64.getD 287 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_287]
  decide +kernel
theorem coefficient_2438 : validRep representative_2438 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2438)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_2439 : validRep representative_2439 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2439)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2440 : validRep representative_2440 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2440)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2441 : validRep representative_2441 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2441)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2442 : validRep representative_2442 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2442)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2443 : validRep representative_2443 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2443)=dictionary64.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_2444 : validRep representative_2444 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2444)=dictionary64.getD 105 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_105]
  decide +kernel
theorem coefficient_2445 : validRep representative_2445 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2445)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_2446 : validRep representative_2446 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2446)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2447 : validRep representative_2447 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2447)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2448 : validRep representative_2448 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2448)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2449 : validRep representative_2449 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2449)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2450 : validRep representative_2450 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2450)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2451 : validRep representative_2451 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2451)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2452 : validRep representative_2452 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2452)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2453 : validRep representative_2453 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2453)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2454 : validRep representative_2454 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2454)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2455 : validRep representative_2455 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2455)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2456 : validRep representative_2456 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2456)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2457 : validRep representative_2457 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2457)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2458 : validRep representative_2458 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2458)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2459 : validRep representative_2459 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2459)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2460 : validRep representative_2460 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2460)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2461 : validRep representative_2461 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2461)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2462 : validRep representative_2462 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2462)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2463 : validRep representative_2463 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2463)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2464 : validRep representative_2464 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2464)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2465 : validRep representative_2465 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2465)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2466 : validRep representative_2466 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2466)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2467 : validRep representative_2467 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2467)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_2468 : validRep representative_2468 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2468)=dictionary64.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_2469 : validRep representative_2469 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2469)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2470 : validRep representative_2470 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2470)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2471 : validRep representative_2471 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2471)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2472 : validRep representative_2472 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2472)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2473 : validRep representative_2473 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2473)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2474 : validRep representative_2474 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2474)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2475 : validRep representative_2475 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2475)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2476 : validRep representative_2476 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2476)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2477 : validRep representative_2477 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2477)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2478 : validRep representative_2478 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2478)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2479 : validRep representative_2479 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2479)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2480 : validRep representative_2480 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2480)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2481 : validRep representative_2481 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2481)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2482 : validRep representative_2482 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2482)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2483 : validRep representative_2483 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2483)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2484 : validRep representative_2484 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2484)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2485 : validRep representative_2485 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2485)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2486 : validRep representative_2486 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2486)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2487 : validRep representative_2487 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2487)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2488 : validRep representative_2488 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2488)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2489 : validRep representative_2489 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2489)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2490 : validRep representative_2490 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2490)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2491 : validRep representative_2491 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2491)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2492 : validRep representative_2492 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2492)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2493 : validRep representative_2493 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2493)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2494 : validRep representative_2494 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2494)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2495 : validRep representative_2495 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2495)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_038 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2464 (QuarticIntegerRepresentativeTree.Tree.branch 2448 (QuarticIntegerRepresentativeTree.Tree.branch 2440 (QuarticIntegerRepresentativeTree.Tree.branch 2436 (QuarticIntegerRepresentativeTree.Tree.branch 2434 (QuarticIntegerRepresentativeTree.Tree.branch 2433 (QuarticIntegerRepresentativeTree.Tree.leaf 2432 representative_2432) (QuarticIntegerRepresentativeTree.Tree.leaf 2433 representative_2433)) (QuarticIntegerRepresentativeTree.Tree.branch 2435 (QuarticIntegerRepresentativeTree.Tree.leaf 2434 representative_2434) (QuarticIntegerRepresentativeTree.Tree.leaf 2435 representative_2435))) (QuarticIntegerRepresentativeTree.Tree.branch 2438 (QuarticIntegerRepresentativeTree.Tree.branch 2437 (QuarticIntegerRepresentativeTree.Tree.leaf 2436 representative_2436) (QuarticIntegerRepresentativeTree.Tree.leaf 2437 representative_2437)) (QuarticIntegerRepresentativeTree.Tree.branch 2439 (QuarticIntegerRepresentativeTree.Tree.leaf 2438 representative_2438) (QuarticIntegerRepresentativeTree.Tree.leaf 2439 representative_2439)))) (QuarticIntegerRepresentativeTree.Tree.branch 2444 (QuarticIntegerRepresentativeTree.Tree.branch 2442 (QuarticIntegerRepresentativeTree.Tree.branch 2441 (QuarticIntegerRepresentativeTree.Tree.leaf 2440 representative_2440) (QuarticIntegerRepresentativeTree.Tree.leaf 2441 representative_2441)) (QuarticIntegerRepresentativeTree.Tree.branch 2443 (QuarticIntegerRepresentativeTree.Tree.leaf 2442 representative_2442) (QuarticIntegerRepresentativeTree.Tree.leaf 2443 representative_2443))) (QuarticIntegerRepresentativeTree.Tree.branch 2446 (QuarticIntegerRepresentativeTree.Tree.branch 2445 (QuarticIntegerRepresentativeTree.Tree.leaf 2444 representative_2444) (QuarticIntegerRepresentativeTree.Tree.leaf 2445 representative_2445)) (QuarticIntegerRepresentativeTree.Tree.branch 2447 (QuarticIntegerRepresentativeTree.Tree.leaf 2446 representative_2446) (QuarticIntegerRepresentativeTree.Tree.leaf 2447 representative_2447))))) (QuarticIntegerRepresentativeTree.Tree.branch 2456 (QuarticIntegerRepresentativeTree.Tree.branch 2452 (QuarticIntegerRepresentativeTree.Tree.branch 2450 (QuarticIntegerRepresentativeTree.Tree.branch 2449 (QuarticIntegerRepresentativeTree.Tree.leaf 2448 representative_2448) (QuarticIntegerRepresentativeTree.Tree.leaf 2449 representative_2449)) (QuarticIntegerRepresentativeTree.Tree.branch 2451 (QuarticIntegerRepresentativeTree.Tree.leaf 2450 representative_2450) (QuarticIntegerRepresentativeTree.Tree.leaf 2451 representative_2451))) (QuarticIntegerRepresentativeTree.Tree.branch 2454 (QuarticIntegerRepresentativeTree.Tree.branch 2453 (QuarticIntegerRepresentativeTree.Tree.leaf 2452 representative_2452) (QuarticIntegerRepresentativeTree.Tree.leaf 2453 representative_2453)) (QuarticIntegerRepresentativeTree.Tree.branch 2455 (QuarticIntegerRepresentativeTree.Tree.leaf 2454 representative_2454) (QuarticIntegerRepresentativeTree.Tree.leaf 2455 representative_2455)))) (QuarticIntegerRepresentativeTree.Tree.branch 2460 (QuarticIntegerRepresentativeTree.Tree.branch 2458 (QuarticIntegerRepresentativeTree.Tree.branch 2457 (QuarticIntegerRepresentativeTree.Tree.leaf 2456 representative_2456) (QuarticIntegerRepresentativeTree.Tree.leaf 2457 representative_2457)) (QuarticIntegerRepresentativeTree.Tree.branch 2459 (QuarticIntegerRepresentativeTree.Tree.leaf 2458 representative_2458) (QuarticIntegerRepresentativeTree.Tree.leaf 2459 representative_2459))) (QuarticIntegerRepresentativeTree.Tree.branch 2462 (QuarticIntegerRepresentativeTree.Tree.branch 2461 (QuarticIntegerRepresentativeTree.Tree.leaf 2460 representative_2460) (QuarticIntegerRepresentativeTree.Tree.leaf 2461 representative_2461)) (QuarticIntegerRepresentativeTree.Tree.branch 2463 (QuarticIntegerRepresentativeTree.Tree.leaf 2462 representative_2462) (QuarticIntegerRepresentativeTree.Tree.leaf 2463 representative_2463)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2480 (QuarticIntegerRepresentativeTree.Tree.branch 2472 (QuarticIntegerRepresentativeTree.Tree.branch 2468 (QuarticIntegerRepresentativeTree.Tree.branch 2466 (QuarticIntegerRepresentativeTree.Tree.branch 2465 (QuarticIntegerRepresentativeTree.Tree.leaf 2464 representative_2464) (QuarticIntegerRepresentativeTree.Tree.leaf 2465 representative_2465)) (QuarticIntegerRepresentativeTree.Tree.branch 2467 (QuarticIntegerRepresentativeTree.Tree.leaf 2466 representative_2466) (QuarticIntegerRepresentativeTree.Tree.leaf 2467 representative_2467))) (QuarticIntegerRepresentativeTree.Tree.branch 2470 (QuarticIntegerRepresentativeTree.Tree.branch 2469 (QuarticIntegerRepresentativeTree.Tree.leaf 2468 representative_2468) (QuarticIntegerRepresentativeTree.Tree.leaf 2469 representative_2469)) (QuarticIntegerRepresentativeTree.Tree.branch 2471 (QuarticIntegerRepresentativeTree.Tree.leaf 2470 representative_2470) (QuarticIntegerRepresentativeTree.Tree.leaf 2471 representative_2471)))) (QuarticIntegerRepresentativeTree.Tree.branch 2476 (QuarticIntegerRepresentativeTree.Tree.branch 2474 (QuarticIntegerRepresentativeTree.Tree.branch 2473 (QuarticIntegerRepresentativeTree.Tree.leaf 2472 representative_2472) (QuarticIntegerRepresentativeTree.Tree.leaf 2473 representative_2473)) (QuarticIntegerRepresentativeTree.Tree.branch 2475 (QuarticIntegerRepresentativeTree.Tree.leaf 2474 representative_2474) (QuarticIntegerRepresentativeTree.Tree.leaf 2475 representative_2475))) (QuarticIntegerRepresentativeTree.Tree.branch 2478 (QuarticIntegerRepresentativeTree.Tree.branch 2477 (QuarticIntegerRepresentativeTree.Tree.leaf 2476 representative_2476) (QuarticIntegerRepresentativeTree.Tree.leaf 2477 representative_2477)) (QuarticIntegerRepresentativeTree.Tree.branch 2479 (QuarticIntegerRepresentativeTree.Tree.leaf 2478 representative_2478) (QuarticIntegerRepresentativeTree.Tree.leaf 2479 representative_2479))))) (QuarticIntegerRepresentativeTree.Tree.branch 2488 (QuarticIntegerRepresentativeTree.Tree.branch 2484 (QuarticIntegerRepresentativeTree.Tree.branch 2482 (QuarticIntegerRepresentativeTree.Tree.branch 2481 (QuarticIntegerRepresentativeTree.Tree.leaf 2480 representative_2480) (QuarticIntegerRepresentativeTree.Tree.leaf 2481 representative_2481)) (QuarticIntegerRepresentativeTree.Tree.branch 2483 (QuarticIntegerRepresentativeTree.Tree.leaf 2482 representative_2482) (QuarticIntegerRepresentativeTree.Tree.leaf 2483 representative_2483))) (QuarticIntegerRepresentativeTree.Tree.branch 2486 (QuarticIntegerRepresentativeTree.Tree.branch 2485 (QuarticIntegerRepresentativeTree.Tree.leaf 2484 representative_2484) (QuarticIntegerRepresentativeTree.Tree.leaf 2485 representative_2485)) (QuarticIntegerRepresentativeTree.Tree.branch 2487 (QuarticIntegerRepresentativeTree.Tree.leaf 2486 representative_2486) (QuarticIntegerRepresentativeTree.Tree.leaf 2487 representative_2487)))) (QuarticIntegerRepresentativeTree.Tree.branch 2492 (QuarticIntegerRepresentativeTree.Tree.branch 2490 (QuarticIntegerRepresentativeTree.Tree.branch 2489 (QuarticIntegerRepresentativeTree.Tree.leaf 2488 representative_2488) (QuarticIntegerRepresentativeTree.Tree.leaf 2489 representative_2489)) (QuarticIntegerRepresentativeTree.Tree.branch 2491 (QuarticIntegerRepresentativeTree.Tree.leaf 2490 representative_2490) (QuarticIntegerRepresentativeTree.Tree.leaf 2491 representative_2491))) (QuarticIntegerRepresentativeTree.Tree.branch 2494 (QuarticIntegerRepresentativeTree.Tree.branch 2493 (QuarticIntegerRepresentativeTree.Tree.leaf 2492 representative_2492) (QuarticIntegerRepresentativeTree.Tree.leaf 2493 representative_2493)) (QuarticIntegerRepresentativeTree.Tree.branch 2495 (QuarticIntegerRepresentativeTree.Tree.leaf 2494 representative_2494) (QuarticIntegerRepresentativeTree.Tree.leaf 2495 representative_2495)))))))
theorem accepted_038 : All validRep tree_038 := ⟨⟨⟨⟨⟨⟨coefficient_2432,coefficient_2433⟩,⟨coefficient_2434,coefficient_2435⟩⟩,⟨⟨coefficient_2436,coefficient_2437⟩,⟨coefficient_2438,coefficient_2439⟩⟩⟩,⟨⟨⟨coefficient_2440,coefficient_2441⟩,⟨coefficient_2442,coefficient_2443⟩⟩,⟨⟨coefficient_2444,coefficient_2445⟩,⟨coefficient_2446,coefficient_2447⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2448,coefficient_2449⟩,⟨coefficient_2450,coefficient_2451⟩⟩,⟨⟨coefficient_2452,coefficient_2453⟩,⟨coefficient_2454,coefficient_2455⟩⟩⟩,⟨⟨⟨coefficient_2456,coefficient_2457⟩,⟨coefficient_2458,coefficient_2459⟩⟩,⟨⟨coefficient_2460,coefficient_2461⟩,⟨coefficient_2462,coefficient_2463⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2464,coefficient_2465⟩,⟨coefficient_2466,coefficient_2467⟩⟩,⟨⟨coefficient_2468,coefficient_2469⟩,⟨coefficient_2470,coefficient_2471⟩⟩⟩,⟨⟨⟨coefficient_2472,coefficient_2473⟩,⟨coefficient_2474,coefficient_2475⟩⟩,⟨⟨coefficient_2476,coefficient_2477⟩,⟨coefficient_2478,coefficient_2479⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2480,coefficient_2481⟩,⟨coefficient_2482,coefficient_2483⟩⟩,⟨⟨coefficient_2484,coefficient_2485⟩,⟨coefficient_2486,coefficient_2487⟩⟩⟩,⟨⟨⟨coefficient_2488,coefficient_2489⟩,⟨coefficient_2490,coefficient_2491⟩⟩,⟨⟨coefficient_2492,coefficient_2493⟩,⟨coefficient_2494,coefficient_2495⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

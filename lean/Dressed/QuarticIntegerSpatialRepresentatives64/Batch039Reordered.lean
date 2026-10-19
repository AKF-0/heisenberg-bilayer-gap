import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2496 : Rep := ⟨![0,10,20,49],246⟩
def representative_2497 : Rep := ⟨![0,10,20,50],234⟩
def representative_2498 : Rep := ⟨![0,10,20,51],246⟩
def representative_2499 : Rep := ⟨![0,10,20,53],462⟩
def representative_2500 : Rep := ⟨![0,10,20,54],462⟩
def representative_2501 : Rep := ⟨![0,10,20,55],462⟩
def representative_2502 : Rep := ⟨![0,10,20,59],224⟩
def representative_2503 : Rep := ⟨![0,10,20,61],462⟩
def representative_2504 : Rep := ⟨![0,10,20,62],462⟩
def representative_2505 : Rep := ⟨![0,10,21,24],462⟩
def representative_2506 : Rep := ⟨![0,10,21,25],246⟩
def representative_2507 : Rep := ⟨![0,10,21,26],235⟩
def representative_2508 : Rep := ⟨![0,10,21,27],246⟩
def representative_2509 : Rep := ⟨![0,10,21,31],462⟩
def representative_2510 : Rep := ⟨![0,10,21,32],462⟩
def representative_2511 : Rep := ⟨![0,10,21,33],462⟩
def representative_2512 : Rep := ⟨![0,10,21,34],243⟩
def representative_2513 : Rep := ⟨![0,10,21,35],462⟩
def representative_2514 : Rep := ⟨![0,10,21,36],462⟩
def representative_2515 : Rep := ⟨![0,10,21,38],462⟩
def representative_2516 : Rep := ⟨![0,10,21,39],462⟩
def representative_2517 : Rep := ⟨![0,10,21,40],462⟩
def representative_2518 : Rep := ⟨![0,10,21,41],462⟩
def representative_2519 : Rep := ⟨![0,10,21,42],462⟩
def representative_2520 : Rep := ⟨![0,10,21,43],462⟩
def representative_2521 : Rep := ⟨![0,10,21,44],462⟩
def representative_2522 : Rep := ⟨![0,10,21,46],462⟩
def representative_2523 : Rep := ⟨![0,10,21,47],462⟩
def representative_2524 : Rep := ⟨![0,10,21,48],462⟩
def representative_2525 : Rep := ⟨![0,10,21,49],462⟩
def representative_2526 : Rep := ⟨![0,10,21,50],243⟩
def representative_2527 : Rep := ⟨![0,10,21,51],462⟩
def representative_2528 : Rep := ⟨![0,10,21,52],462⟩
def representative_2529 : Rep := ⟨![0,10,21,54],462⟩
def representative_2530 : Rep := ⟨![0,10,21,55],462⟩
def representative_2531 : Rep := ⟨![0,10,21,59],246⟩
def representative_2532 : Rep := ⟨![0,10,21,60],462⟩
def representative_2533 : Rep := ⟨![0,10,22,24],246⟩
def representative_2534 : Rep := ⟨![0,10,22,25],462⟩
def representative_2535 : Rep := ⟨![0,10,22,26],462⟩
def representative_2536 : Rep := ⟨![0,10,22,27],462⟩
def representative_2537 : Rep := ⟨![0,10,22,28],462⟩
def representative_2538 : Rep := ⟨![0,10,22,32],462⟩
def representative_2539 : Rep := ⟨![0,10,22,33],462⟩
def representative_2540 : Rep := ⟨![0,10,22,34],462⟩
def representative_2541 : Rep := ⟨![0,10,22,35],462⟩
def representative_2542 : Rep := ⟨![0,10,22,36],462⟩
def representative_2543 : Rep := ⟨![0,10,22,37],462⟩
def representative_2544 : Rep := ⟨![0,10,22,39],462⟩
def representative_2545 : Rep := ⟨![0,10,22,40],244⟩
def representative_2546 : Rep := ⟨![0,10,22,41],462⟩
def representative_2547 : Rep := ⟨![0,10,22,42],462⟩
def representative_2548 : Rep := ⟨![0,10,22,43],462⟩
def representative_2549 : Rep := ⟨![0,10,22,44],462⟩
def representative_2550 : Rep := ⟨![0,10,22,45],462⟩
def representative_2551 : Rep := ⟨![0,10,22,47],462⟩
def representative_2552 : Rep := ⟨![0,10,22,48],234⟩
def representative_2553 : Rep := ⟨![0,10,22,49],248⟩
def representative_2554 : Rep := ⟨![0,10,22,50],462⟩
def representative_2555 : Rep := ⟨![0,10,22,51],462⟩
def representative_2556 : Rep := ⟨![0,10,22,52],462⟩
def representative_2557 : Rep := ⟨![0,10,22,53],462⟩
def representative_2558 : Rep := ⟨![0,10,22,55],248⟩
def representative_2559 : Rep := ⟨![0,10,22,59],462⟩
theorem coefficient_2496 : validRep representative_2496 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2496)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2497 : validRep representative_2497 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2497)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2498 : validRep representative_2498 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2498)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2499 : validRep representative_2499 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2499)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2500 : validRep representative_2500 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2500)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2501 : validRep representative_2501 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2501)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2502 : validRep representative_2502 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2502)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2503 : validRep representative_2503 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2503)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2504 : validRep representative_2504 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2504)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2505 : validRep representative_2505 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2505)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2506 : validRep representative_2506 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2506)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2507 : validRep representative_2507 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2507)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2508 : validRep representative_2508 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2508)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2509 : validRep representative_2509 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2509)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2510 : validRep representative_2510 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2510)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2511 : validRep representative_2511 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2511)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2512 : validRep representative_2512 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2512)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2513 : validRep representative_2513 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2513)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2514 : validRep representative_2514 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2514)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2515 : validRep representative_2515 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2515)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2516 : validRep representative_2516 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2516)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2517 : validRep representative_2517 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2517)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2518 : validRep representative_2518 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2518)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2519 : validRep representative_2519 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2519)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2520 : validRep representative_2520 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2520)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2521 : validRep representative_2521 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2521)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2522 : validRep representative_2522 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2522)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2523 : validRep representative_2523 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2523)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2524 : validRep representative_2524 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2524)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2525 : validRep representative_2525 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2525)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2526 : validRep representative_2526 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2526)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2527 : validRep representative_2527 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2527)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2528 : validRep representative_2528 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2528)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2529 : validRep representative_2529 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2529)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2530 : validRep representative_2530 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2530)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2531 : validRep representative_2531 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2531)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2532 : validRep representative_2532 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2532)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2533 : validRep representative_2533 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2533)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2534 : validRep representative_2534 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2534)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2535 : validRep representative_2535 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2535)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2536 : validRep representative_2536 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2536)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2537 : validRep representative_2537 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2537)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2538 : validRep representative_2538 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2538)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2539 : validRep representative_2539 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2539)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2540 : validRep representative_2540 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2540)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2541 : validRep representative_2541 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2541)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2542 : validRep representative_2542 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2542)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2543 : validRep representative_2543 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2543)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2544 : validRep representative_2544 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2544)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2545 : validRep representative_2545 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2545)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2546 : validRep representative_2546 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2546)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2547 : validRep representative_2547 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2547)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2548 : validRep representative_2548 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2548)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2549 : validRep representative_2549 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2549)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2550 : validRep representative_2550 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2550)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2551 : validRep representative_2551 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2551)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2552 : validRep representative_2552 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2552)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2553 : validRep representative_2553 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2553)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2554 : validRep representative_2554 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2554)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2555 : validRep representative_2555 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2555)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2556 : validRep representative_2556 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2556)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2557 : validRep representative_2557 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2557)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2558 : validRep representative_2558 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2558)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2559 : validRep representative_2559 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2559)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_039 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2528 (QuarticIntegerRepresentativeTree.Tree.branch 2512 (QuarticIntegerRepresentativeTree.Tree.branch 2504 (QuarticIntegerRepresentativeTree.Tree.branch 2500 (QuarticIntegerRepresentativeTree.Tree.branch 2498 (QuarticIntegerRepresentativeTree.Tree.branch 2497 (QuarticIntegerRepresentativeTree.Tree.leaf 2496 representative_2496) (QuarticIntegerRepresentativeTree.Tree.leaf 2497 representative_2497)) (QuarticIntegerRepresentativeTree.Tree.branch 2499 (QuarticIntegerRepresentativeTree.Tree.leaf 2498 representative_2498) (QuarticIntegerRepresentativeTree.Tree.leaf 2499 representative_2499))) (QuarticIntegerRepresentativeTree.Tree.branch 2502 (QuarticIntegerRepresentativeTree.Tree.branch 2501 (QuarticIntegerRepresentativeTree.Tree.leaf 2500 representative_2500) (QuarticIntegerRepresentativeTree.Tree.leaf 2501 representative_2501)) (QuarticIntegerRepresentativeTree.Tree.branch 2503 (QuarticIntegerRepresentativeTree.Tree.leaf 2502 representative_2502) (QuarticIntegerRepresentativeTree.Tree.leaf 2503 representative_2503)))) (QuarticIntegerRepresentativeTree.Tree.branch 2508 (QuarticIntegerRepresentativeTree.Tree.branch 2506 (QuarticIntegerRepresentativeTree.Tree.branch 2505 (QuarticIntegerRepresentativeTree.Tree.leaf 2504 representative_2504) (QuarticIntegerRepresentativeTree.Tree.leaf 2505 representative_2505)) (QuarticIntegerRepresentativeTree.Tree.branch 2507 (QuarticIntegerRepresentativeTree.Tree.leaf 2506 representative_2506) (QuarticIntegerRepresentativeTree.Tree.leaf 2507 representative_2507))) (QuarticIntegerRepresentativeTree.Tree.branch 2510 (QuarticIntegerRepresentativeTree.Tree.branch 2509 (QuarticIntegerRepresentativeTree.Tree.leaf 2508 representative_2508) (QuarticIntegerRepresentativeTree.Tree.leaf 2509 representative_2509)) (QuarticIntegerRepresentativeTree.Tree.branch 2511 (QuarticIntegerRepresentativeTree.Tree.leaf 2510 representative_2510) (QuarticIntegerRepresentativeTree.Tree.leaf 2511 representative_2511))))) (QuarticIntegerRepresentativeTree.Tree.branch 2520 (QuarticIntegerRepresentativeTree.Tree.branch 2516 (QuarticIntegerRepresentativeTree.Tree.branch 2514 (QuarticIntegerRepresentativeTree.Tree.branch 2513 (QuarticIntegerRepresentativeTree.Tree.leaf 2512 representative_2512) (QuarticIntegerRepresentativeTree.Tree.leaf 2513 representative_2513)) (QuarticIntegerRepresentativeTree.Tree.branch 2515 (QuarticIntegerRepresentativeTree.Tree.leaf 2514 representative_2514) (QuarticIntegerRepresentativeTree.Tree.leaf 2515 representative_2515))) (QuarticIntegerRepresentativeTree.Tree.branch 2518 (QuarticIntegerRepresentativeTree.Tree.branch 2517 (QuarticIntegerRepresentativeTree.Tree.leaf 2516 representative_2516) (QuarticIntegerRepresentativeTree.Tree.leaf 2517 representative_2517)) (QuarticIntegerRepresentativeTree.Tree.branch 2519 (QuarticIntegerRepresentativeTree.Tree.leaf 2518 representative_2518) (QuarticIntegerRepresentativeTree.Tree.leaf 2519 representative_2519)))) (QuarticIntegerRepresentativeTree.Tree.branch 2524 (QuarticIntegerRepresentativeTree.Tree.branch 2522 (QuarticIntegerRepresentativeTree.Tree.branch 2521 (QuarticIntegerRepresentativeTree.Tree.leaf 2520 representative_2520) (QuarticIntegerRepresentativeTree.Tree.leaf 2521 representative_2521)) (QuarticIntegerRepresentativeTree.Tree.branch 2523 (QuarticIntegerRepresentativeTree.Tree.leaf 2522 representative_2522) (QuarticIntegerRepresentativeTree.Tree.leaf 2523 representative_2523))) (QuarticIntegerRepresentativeTree.Tree.branch 2526 (QuarticIntegerRepresentativeTree.Tree.branch 2525 (QuarticIntegerRepresentativeTree.Tree.leaf 2524 representative_2524) (QuarticIntegerRepresentativeTree.Tree.leaf 2525 representative_2525)) (QuarticIntegerRepresentativeTree.Tree.branch 2527 (QuarticIntegerRepresentativeTree.Tree.leaf 2526 representative_2526) (QuarticIntegerRepresentativeTree.Tree.leaf 2527 representative_2527)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2544 (QuarticIntegerRepresentativeTree.Tree.branch 2536 (QuarticIntegerRepresentativeTree.Tree.branch 2532 (QuarticIntegerRepresentativeTree.Tree.branch 2530 (QuarticIntegerRepresentativeTree.Tree.branch 2529 (QuarticIntegerRepresentativeTree.Tree.leaf 2528 representative_2528) (QuarticIntegerRepresentativeTree.Tree.leaf 2529 representative_2529)) (QuarticIntegerRepresentativeTree.Tree.branch 2531 (QuarticIntegerRepresentativeTree.Tree.leaf 2530 representative_2530) (QuarticIntegerRepresentativeTree.Tree.leaf 2531 representative_2531))) (QuarticIntegerRepresentativeTree.Tree.branch 2534 (QuarticIntegerRepresentativeTree.Tree.branch 2533 (QuarticIntegerRepresentativeTree.Tree.leaf 2532 representative_2532) (QuarticIntegerRepresentativeTree.Tree.leaf 2533 representative_2533)) (QuarticIntegerRepresentativeTree.Tree.branch 2535 (QuarticIntegerRepresentativeTree.Tree.leaf 2534 representative_2534) (QuarticIntegerRepresentativeTree.Tree.leaf 2535 representative_2535)))) (QuarticIntegerRepresentativeTree.Tree.branch 2540 (QuarticIntegerRepresentativeTree.Tree.branch 2538 (QuarticIntegerRepresentativeTree.Tree.branch 2537 (QuarticIntegerRepresentativeTree.Tree.leaf 2536 representative_2536) (QuarticIntegerRepresentativeTree.Tree.leaf 2537 representative_2537)) (QuarticIntegerRepresentativeTree.Tree.branch 2539 (QuarticIntegerRepresentativeTree.Tree.leaf 2538 representative_2538) (QuarticIntegerRepresentativeTree.Tree.leaf 2539 representative_2539))) (QuarticIntegerRepresentativeTree.Tree.branch 2542 (QuarticIntegerRepresentativeTree.Tree.branch 2541 (QuarticIntegerRepresentativeTree.Tree.leaf 2540 representative_2540) (QuarticIntegerRepresentativeTree.Tree.leaf 2541 representative_2541)) (QuarticIntegerRepresentativeTree.Tree.branch 2543 (QuarticIntegerRepresentativeTree.Tree.leaf 2542 representative_2542) (QuarticIntegerRepresentativeTree.Tree.leaf 2543 representative_2543))))) (QuarticIntegerRepresentativeTree.Tree.branch 2552 (QuarticIntegerRepresentativeTree.Tree.branch 2548 (QuarticIntegerRepresentativeTree.Tree.branch 2546 (QuarticIntegerRepresentativeTree.Tree.branch 2545 (QuarticIntegerRepresentativeTree.Tree.leaf 2544 representative_2544) (QuarticIntegerRepresentativeTree.Tree.leaf 2545 representative_2545)) (QuarticIntegerRepresentativeTree.Tree.branch 2547 (QuarticIntegerRepresentativeTree.Tree.leaf 2546 representative_2546) (QuarticIntegerRepresentativeTree.Tree.leaf 2547 representative_2547))) (QuarticIntegerRepresentativeTree.Tree.branch 2550 (QuarticIntegerRepresentativeTree.Tree.branch 2549 (QuarticIntegerRepresentativeTree.Tree.leaf 2548 representative_2548) (QuarticIntegerRepresentativeTree.Tree.leaf 2549 representative_2549)) (QuarticIntegerRepresentativeTree.Tree.branch 2551 (QuarticIntegerRepresentativeTree.Tree.leaf 2550 representative_2550) (QuarticIntegerRepresentativeTree.Tree.leaf 2551 representative_2551)))) (QuarticIntegerRepresentativeTree.Tree.branch 2556 (QuarticIntegerRepresentativeTree.Tree.branch 2554 (QuarticIntegerRepresentativeTree.Tree.branch 2553 (QuarticIntegerRepresentativeTree.Tree.leaf 2552 representative_2552) (QuarticIntegerRepresentativeTree.Tree.leaf 2553 representative_2553)) (QuarticIntegerRepresentativeTree.Tree.branch 2555 (QuarticIntegerRepresentativeTree.Tree.leaf 2554 representative_2554) (QuarticIntegerRepresentativeTree.Tree.leaf 2555 representative_2555))) (QuarticIntegerRepresentativeTree.Tree.branch 2558 (QuarticIntegerRepresentativeTree.Tree.branch 2557 (QuarticIntegerRepresentativeTree.Tree.leaf 2556 representative_2556) (QuarticIntegerRepresentativeTree.Tree.leaf 2557 representative_2557)) (QuarticIntegerRepresentativeTree.Tree.branch 2559 (QuarticIntegerRepresentativeTree.Tree.leaf 2558 representative_2558) (QuarticIntegerRepresentativeTree.Tree.leaf 2559 representative_2559)))))))
theorem accepted_039 : All validRep tree_039 := ⟨⟨⟨⟨⟨⟨coefficient_2496,coefficient_2497⟩,⟨coefficient_2498,coefficient_2499⟩⟩,⟨⟨coefficient_2500,coefficient_2501⟩,⟨coefficient_2502,coefficient_2503⟩⟩⟩,⟨⟨⟨coefficient_2504,coefficient_2505⟩,⟨coefficient_2506,coefficient_2507⟩⟩,⟨⟨coefficient_2508,coefficient_2509⟩,⟨coefficient_2510,coefficient_2511⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2512,coefficient_2513⟩,⟨coefficient_2514,coefficient_2515⟩⟩,⟨⟨coefficient_2516,coefficient_2517⟩,⟨coefficient_2518,coefficient_2519⟩⟩⟩,⟨⟨⟨coefficient_2520,coefficient_2521⟩,⟨coefficient_2522,coefficient_2523⟩⟩,⟨⟨coefficient_2524,coefficient_2525⟩,⟨coefficient_2526,coefficient_2527⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2528,coefficient_2529⟩,⟨coefficient_2530,coefficient_2531⟩⟩,⟨⟨coefficient_2532,coefficient_2533⟩,⟨coefficient_2534,coefficient_2535⟩⟩⟩,⟨⟨⟨coefficient_2536,coefficient_2537⟩,⟨coefficient_2538,coefficient_2539⟩⟩,⟨⟨coefficient_2540,coefficient_2541⟩,⟨coefficient_2542,coefficient_2543⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2544,coefficient_2545⟩,⟨coefficient_2546,coefficient_2547⟩⟩,⟨⟨coefficient_2548,coefficient_2549⟩,⟨coefficient_2550,coefficient_2551⟩⟩⟩,⟨⟨⟨coefficient_2552,coefficient_2553⟩,⟨coefficient_2554,coefficient_2555⟩⟩,⟨⟨coefficient_2556,coefficient_2557⟩,⟨coefficient_2558,coefficient_2559⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

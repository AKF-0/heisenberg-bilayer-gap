import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2560 : Rep := ⟨![0,10,22,60],462⟩
def representative_2561 : Rep := ⟨![0,10,23,25],253⟩
def representative_2562 : Rep := ⟨![0,10,23,26],235⟩
def representative_2563 : Rep := ⟨![0,10,23,27],246⟩
def representative_2564 : Rep := ⟨![0,10,23,28],462⟩
def representative_2565 : Rep := ⟨![0,10,23,33],462⟩
def representative_2566 : Rep := ⟨![0,10,23,34],243⟩
def representative_2567 : Rep := ⟨![0,10,23,35],462⟩
def representative_2568 : Rep := ⟨![0,10,23,36],462⟩
def representative_2569 : Rep := ⟨![0,10,23,37],462⟩
def representative_2570 : Rep := ⟨![0,10,23,40],234⟩
def representative_2571 : Rep := ⟨![0,10,23,41],246⟩
def representative_2572 : Rep := ⟨![0,10,23,42],462⟩
def representative_2573 : Rep := ⟨![0,10,23,43],462⟩
def representative_2574 : Rep := ⟨![0,10,23,44],462⟩
def representative_2575 : Rep := ⟨![0,10,23,45],462⟩
def representative_2576 : Rep := ⟨![0,10,23,46],462⟩
def representative_2577 : Rep := ⟨![0,10,23,48],291⟩
def representative_2578 : Rep := ⟨![0,10,23,49],224⟩
def representative_2579 : Rep := ⟨![0,10,23,50],250⟩
def representative_2580 : Rep := ⟨![0,10,23,51],462⟩
def representative_2581 : Rep := ⟨![0,10,23,52],462⟩
def representative_2582 : Rep := ⟨![0,10,23,53],462⟩
def representative_2583 : Rep := ⟨![0,10,23,54],248⟩
def representative_2584 : Rep := ⟨![0,10,23,59],251⟩
def representative_2585 : Rep := ⟨![0,10,24,34],246⟩
def representative_2586 : Rep := ⟨![0,10,24,35],462⟩
def representative_2587 : Rep := ⟨![0,10,24,36],462⟩
def representative_2588 : Rep := ⟨![0,10,24,37],462⟩
def representative_2589 : Rep := ⟨![0,10,24,38],244⟩
def representative_2590 : Rep := ⟨![0,10,24,42],462⟩
def representative_2591 : Rep := ⟨![0,10,24,43],462⟩
def representative_2592 : Rep := ⟨![0,10,24,44],462⟩
def representative_2593 : Rep := ⟨![0,10,24,45],462⟩
def representative_2594 : Rep := ⟨![0,10,24,46],462⟩
def representative_2595 : Rep := ⟨![0,10,24,49],234⟩
def representative_2596 : Rep := ⟨![0,10,24,50],246⟩
def representative_2597 : Rep := ⟨![0,10,24,51],462⟩
def representative_2598 : Rep := ⟨![0,10,24,52],462⟩
def representative_2599 : Rep := ⟨![0,10,24,53],462⟩
def representative_2600 : Rep := ⟨![0,10,24,54],244⟩
def representative_2601 : Rep := ⟨![0,10,24,55],234⟩
def representative_2602 : Rep := ⟨![0,10,25,35],251⟩
def representative_2603 : Rep := ⟨![0,10,25,36],462⟩
def representative_2604 : Rep := ⟨![0,10,25,37],462⟩
def representative_2605 : Rep := ⟨![0,10,25,38],462⟩
def representative_2606 : Rep := ⟨![0,10,25,39],246⟩
def representative_2607 : Rep := ⟨![0,10,25,43],462⟩
def representative_2608 : Rep := ⟨![0,10,25,44],462⟩
def representative_2609 : Rep := ⟨![0,10,25,45],462⟩
def representative_2610 : Rep := ⟨![0,10,25,46],462⟩
def representative_2611 : Rep := ⟨![0,10,25,47],462⟩
def representative_2612 : Rep := ⟨![0,10,25,48],235⟩
def representative_2613 : Rep := ⟨![0,10,25,51],246⟩
def representative_2614 : Rep := ⟨![0,10,25,52],462⟩
def representative_2615 : Rep := ⟨![0,10,25,53],462⟩
def representative_2616 : Rep := ⟨![0,10,25,54],462⟩
def representative_2617 : Rep := ⟨![0,10,25,55],246⟩
def representative_2618 : Rep := ⟨![0,10,26,32],462⟩
def representative_2619 : Rep := ⟨![0,10,26,36],462⟩
def representative_2620 : Rep := ⟨![0,10,26,37],462⟩
def representative_2621 : Rep := ⟨![0,10,26,38],462⟩
def representative_2622 : Rep := ⟨![0,10,26,39],462⟩
def representative_2623 : Rep := ⟨![0,10,26,40],462⟩
theorem coefficient_2560 : validRep representative_2560 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2560)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2561 : validRep representative_2561 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2561)=dictionary64.getD 253 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_253]
  decide +kernel
theorem coefficient_2562 : validRep representative_2562 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2562)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2563 : validRep representative_2563 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2563)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2564 : validRep representative_2564 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2564)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2565 : validRep representative_2565 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2565)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2566 : validRep representative_2566 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2566)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_2567 : validRep representative_2567 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2567)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2568 : validRep representative_2568 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2568)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2569 : validRep representative_2569 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2569)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2570 : validRep representative_2570 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2570)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2571 : validRep representative_2571 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2571)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2572 : validRep representative_2572 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2572)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2573 : validRep representative_2573 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2573)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2574 : validRep representative_2574 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2574)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2575 : validRep representative_2575 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2575)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2576 : validRep representative_2576 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2576)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2577 : validRep representative_2577 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2577)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_2578 : validRep representative_2578 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2578)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2579 : validRep representative_2579 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2579)=dictionary64.getD 250 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_250]
  decide +kernel
theorem coefficient_2580 : validRep representative_2580 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2580)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2581 : validRep representative_2581 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2581)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2582 : validRep representative_2582 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2582)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2583 : validRep representative_2583 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2583)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_2584 : validRep representative_2584 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2584)=dictionary64.getD 251 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_251]
  decide +kernel
theorem coefficient_2585 : validRep representative_2585 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2585)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2586 : validRep representative_2586 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2586)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2587 : validRep representative_2587 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2587)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2588 : validRep representative_2588 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2588)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2589 : validRep representative_2589 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2589)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2590 : validRep representative_2590 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2590)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2591 : validRep representative_2591 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2591)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2592 : validRep representative_2592 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2592)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2593 : validRep representative_2593 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2593)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2594 : validRep representative_2594 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2594)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2595 : validRep representative_2595 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2595)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2596 : validRep representative_2596 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2596)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2597 : validRep representative_2597 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2597)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2598 : validRep representative_2598 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2598)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2599 : validRep representative_2599 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2599)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2600 : validRep representative_2600 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2600)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_2601 : validRep representative_2601 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2601)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_2602 : validRep representative_2602 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2602)=dictionary64.getD 251 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_251]
  decide +kernel
theorem coefficient_2603 : validRep representative_2603 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2603)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2604 : validRep representative_2604 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2604)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2605 : validRep representative_2605 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2605)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2606 : validRep representative_2606 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2606)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2607 : validRep representative_2607 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2607)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2608 : validRep representative_2608 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2608)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2609 : validRep representative_2609 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2609)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2610 : validRep representative_2610 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2610)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2611 : validRep representative_2611 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2611)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2612 : validRep representative_2612 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2612)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2613 : validRep representative_2613 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2613)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2614 : validRep representative_2614 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2614)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2615 : validRep representative_2615 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2615)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2616 : validRep representative_2616 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2616)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2617 : validRep representative_2617 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2617)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_2618 : validRep representative_2618 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2618)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2619 : validRep representative_2619 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2619)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2620 : validRep representative_2620 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2620)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2621 : validRep representative_2621 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2621)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2622 : validRep representative_2622 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2622)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2623 : validRep representative_2623 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2623)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_040 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2592 (QuarticIntegerRepresentativeTree.Tree.branch 2576 (QuarticIntegerRepresentativeTree.Tree.branch 2568 (QuarticIntegerRepresentativeTree.Tree.branch 2564 (QuarticIntegerRepresentativeTree.Tree.branch 2562 (QuarticIntegerRepresentativeTree.Tree.branch 2561 (QuarticIntegerRepresentativeTree.Tree.leaf 2560 representative_2560) (QuarticIntegerRepresentativeTree.Tree.leaf 2561 representative_2561)) (QuarticIntegerRepresentativeTree.Tree.branch 2563 (QuarticIntegerRepresentativeTree.Tree.leaf 2562 representative_2562) (QuarticIntegerRepresentativeTree.Tree.leaf 2563 representative_2563))) (QuarticIntegerRepresentativeTree.Tree.branch 2566 (QuarticIntegerRepresentativeTree.Tree.branch 2565 (QuarticIntegerRepresentativeTree.Tree.leaf 2564 representative_2564) (QuarticIntegerRepresentativeTree.Tree.leaf 2565 representative_2565)) (QuarticIntegerRepresentativeTree.Tree.branch 2567 (QuarticIntegerRepresentativeTree.Tree.leaf 2566 representative_2566) (QuarticIntegerRepresentativeTree.Tree.leaf 2567 representative_2567)))) (QuarticIntegerRepresentativeTree.Tree.branch 2572 (QuarticIntegerRepresentativeTree.Tree.branch 2570 (QuarticIntegerRepresentativeTree.Tree.branch 2569 (QuarticIntegerRepresentativeTree.Tree.leaf 2568 representative_2568) (QuarticIntegerRepresentativeTree.Tree.leaf 2569 representative_2569)) (QuarticIntegerRepresentativeTree.Tree.branch 2571 (QuarticIntegerRepresentativeTree.Tree.leaf 2570 representative_2570) (QuarticIntegerRepresentativeTree.Tree.leaf 2571 representative_2571))) (QuarticIntegerRepresentativeTree.Tree.branch 2574 (QuarticIntegerRepresentativeTree.Tree.branch 2573 (QuarticIntegerRepresentativeTree.Tree.leaf 2572 representative_2572) (QuarticIntegerRepresentativeTree.Tree.leaf 2573 representative_2573)) (QuarticIntegerRepresentativeTree.Tree.branch 2575 (QuarticIntegerRepresentativeTree.Tree.leaf 2574 representative_2574) (QuarticIntegerRepresentativeTree.Tree.leaf 2575 representative_2575))))) (QuarticIntegerRepresentativeTree.Tree.branch 2584 (QuarticIntegerRepresentativeTree.Tree.branch 2580 (QuarticIntegerRepresentativeTree.Tree.branch 2578 (QuarticIntegerRepresentativeTree.Tree.branch 2577 (QuarticIntegerRepresentativeTree.Tree.leaf 2576 representative_2576) (QuarticIntegerRepresentativeTree.Tree.leaf 2577 representative_2577)) (QuarticIntegerRepresentativeTree.Tree.branch 2579 (QuarticIntegerRepresentativeTree.Tree.leaf 2578 representative_2578) (QuarticIntegerRepresentativeTree.Tree.leaf 2579 representative_2579))) (QuarticIntegerRepresentativeTree.Tree.branch 2582 (QuarticIntegerRepresentativeTree.Tree.branch 2581 (QuarticIntegerRepresentativeTree.Tree.leaf 2580 representative_2580) (QuarticIntegerRepresentativeTree.Tree.leaf 2581 representative_2581)) (QuarticIntegerRepresentativeTree.Tree.branch 2583 (QuarticIntegerRepresentativeTree.Tree.leaf 2582 representative_2582) (QuarticIntegerRepresentativeTree.Tree.leaf 2583 representative_2583)))) (QuarticIntegerRepresentativeTree.Tree.branch 2588 (QuarticIntegerRepresentativeTree.Tree.branch 2586 (QuarticIntegerRepresentativeTree.Tree.branch 2585 (QuarticIntegerRepresentativeTree.Tree.leaf 2584 representative_2584) (QuarticIntegerRepresentativeTree.Tree.leaf 2585 representative_2585)) (QuarticIntegerRepresentativeTree.Tree.branch 2587 (QuarticIntegerRepresentativeTree.Tree.leaf 2586 representative_2586) (QuarticIntegerRepresentativeTree.Tree.leaf 2587 representative_2587))) (QuarticIntegerRepresentativeTree.Tree.branch 2590 (QuarticIntegerRepresentativeTree.Tree.branch 2589 (QuarticIntegerRepresentativeTree.Tree.leaf 2588 representative_2588) (QuarticIntegerRepresentativeTree.Tree.leaf 2589 representative_2589)) (QuarticIntegerRepresentativeTree.Tree.branch 2591 (QuarticIntegerRepresentativeTree.Tree.leaf 2590 representative_2590) (QuarticIntegerRepresentativeTree.Tree.leaf 2591 representative_2591)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2608 (QuarticIntegerRepresentativeTree.Tree.branch 2600 (QuarticIntegerRepresentativeTree.Tree.branch 2596 (QuarticIntegerRepresentativeTree.Tree.branch 2594 (QuarticIntegerRepresentativeTree.Tree.branch 2593 (QuarticIntegerRepresentativeTree.Tree.leaf 2592 representative_2592) (QuarticIntegerRepresentativeTree.Tree.leaf 2593 representative_2593)) (QuarticIntegerRepresentativeTree.Tree.branch 2595 (QuarticIntegerRepresentativeTree.Tree.leaf 2594 representative_2594) (QuarticIntegerRepresentativeTree.Tree.leaf 2595 representative_2595))) (QuarticIntegerRepresentativeTree.Tree.branch 2598 (QuarticIntegerRepresentativeTree.Tree.branch 2597 (QuarticIntegerRepresentativeTree.Tree.leaf 2596 representative_2596) (QuarticIntegerRepresentativeTree.Tree.leaf 2597 representative_2597)) (QuarticIntegerRepresentativeTree.Tree.branch 2599 (QuarticIntegerRepresentativeTree.Tree.leaf 2598 representative_2598) (QuarticIntegerRepresentativeTree.Tree.leaf 2599 representative_2599)))) (QuarticIntegerRepresentativeTree.Tree.branch 2604 (QuarticIntegerRepresentativeTree.Tree.branch 2602 (QuarticIntegerRepresentativeTree.Tree.branch 2601 (QuarticIntegerRepresentativeTree.Tree.leaf 2600 representative_2600) (QuarticIntegerRepresentativeTree.Tree.leaf 2601 representative_2601)) (QuarticIntegerRepresentativeTree.Tree.branch 2603 (QuarticIntegerRepresentativeTree.Tree.leaf 2602 representative_2602) (QuarticIntegerRepresentativeTree.Tree.leaf 2603 representative_2603))) (QuarticIntegerRepresentativeTree.Tree.branch 2606 (QuarticIntegerRepresentativeTree.Tree.branch 2605 (QuarticIntegerRepresentativeTree.Tree.leaf 2604 representative_2604) (QuarticIntegerRepresentativeTree.Tree.leaf 2605 representative_2605)) (QuarticIntegerRepresentativeTree.Tree.branch 2607 (QuarticIntegerRepresentativeTree.Tree.leaf 2606 representative_2606) (QuarticIntegerRepresentativeTree.Tree.leaf 2607 representative_2607))))) (QuarticIntegerRepresentativeTree.Tree.branch 2616 (QuarticIntegerRepresentativeTree.Tree.branch 2612 (QuarticIntegerRepresentativeTree.Tree.branch 2610 (QuarticIntegerRepresentativeTree.Tree.branch 2609 (QuarticIntegerRepresentativeTree.Tree.leaf 2608 representative_2608) (QuarticIntegerRepresentativeTree.Tree.leaf 2609 representative_2609)) (QuarticIntegerRepresentativeTree.Tree.branch 2611 (QuarticIntegerRepresentativeTree.Tree.leaf 2610 representative_2610) (QuarticIntegerRepresentativeTree.Tree.leaf 2611 representative_2611))) (QuarticIntegerRepresentativeTree.Tree.branch 2614 (QuarticIntegerRepresentativeTree.Tree.branch 2613 (QuarticIntegerRepresentativeTree.Tree.leaf 2612 representative_2612) (QuarticIntegerRepresentativeTree.Tree.leaf 2613 representative_2613)) (QuarticIntegerRepresentativeTree.Tree.branch 2615 (QuarticIntegerRepresentativeTree.Tree.leaf 2614 representative_2614) (QuarticIntegerRepresentativeTree.Tree.leaf 2615 representative_2615)))) (QuarticIntegerRepresentativeTree.Tree.branch 2620 (QuarticIntegerRepresentativeTree.Tree.branch 2618 (QuarticIntegerRepresentativeTree.Tree.branch 2617 (QuarticIntegerRepresentativeTree.Tree.leaf 2616 representative_2616) (QuarticIntegerRepresentativeTree.Tree.leaf 2617 representative_2617)) (QuarticIntegerRepresentativeTree.Tree.branch 2619 (QuarticIntegerRepresentativeTree.Tree.leaf 2618 representative_2618) (QuarticIntegerRepresentativeTree.Tree.leaf 2619 representative_2619))) (QuarticIntegerRepresentativeTree.Tree.branch 2622 (QuarticIntegerRepresentativeTree.Tree.branch 2621 (QuarticIntegerRepresentativeTree.Tree.leaf 2620 representative_2620) (QuarticIntegerRepresentativeTree.Tree.leaf 2621 representative_2621)) (QuarticIntegerRepresentativeTree.Tree.branch 2623 (QuarticIntegerRepresentativeTree.Tree.leaf 2622 representative_2622) (QuarticIntegerRepresentativeTree.Tree.leaf 2623 representative_2623)))))))
theorem accepted_040 : All validRep tree_040 := ⟨⟨⟨⟨⟨⟨coefficient_2560,coefficient_2561⟩,⟨coefficient_2562,coefficient_2563⟩⟩,⟨⟨coefficient_2564,coefficient_2565⟩,⟨coefficient_2566,coefficient_2567⟩⟩⟩,⟨⟨⟨coefficient_2568,coefficient_2569⟩,⟨coefficient_2570,coefficient_2571⟩⟩,⟨⟨coefficient_2572,coefficient_2573⟩,⟨coefficient_2574,coefficient_2575⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2576,coefficient_2577⟩,⟨coefficient_2578,coefficient_2579⟩⟩,⟨⟨coefficient_2580,coefficient_2581⟩,⟨coefficient_2582,coefficient_2583⟩⟩⟩,⟨⟨⟨coefficient_2584,coefficient_2585⟩,⟨coefficient_2586,coefficient_2587⟩⟩,⟨⟨coefficient_2588,coefficient_2589⟩,⟨coefficient_2590,coefficient_2591⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2592,coefficient_2593⟩,⟨coefficient_2594,coefficient_2595⟩⟩,⟨⟨coefficient_2596,coefficient_2597⟩,⟨coefficient_2598,coefficient_2599⟩⟩⟩,⟨⟨⟨coefficient_2600,coefficient_2601⟩,⟨coefficient_2602,coefficient_2603⟩⟩,⟨⟨coefficient_2604,coefficient_2605⟩,⟨coefficient_2606,coefficient_2607⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2608,coefficient_2609⟩,⟨coefficient_2610,coefficient_2611⟩⟩,⟨⟨coefficient_2612,coefficient_2613⟩,⟨coefficient_2614,coefficient_2615⟩⟩⟩,⟨⟨⟨coefficient_2616,coefficient_2617⟩,⟨coefficient_2618,coefficient_2619⟩⟩,⟨⟨coefficient_2620,coefficient_2621⟩,⟨coefficient_2622,coefficient_2623⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

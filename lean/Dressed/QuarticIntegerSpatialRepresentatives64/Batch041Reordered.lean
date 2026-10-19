import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2624 : Rep := ⟨![0,10,26,44],462⟩
def representative_2625 : Rep := ⟨![0,10,26,45],462⟩
def representative_2626 : Rep := ⟨![0,10,26,46],462⟩
def representative_2627 : Rep := ⟨![0,10,26,47],462⟩
def representative_2628 : Rep := ⟨![0,10,26,48],462⟩
def representative_2629 : Rep := ⟨![0,10,26,51],235⟩
def representative_2630 : Rep := ⟨![0,10,26,52],462⟩
def representative_2631 : Rep := ⟨![0,10,26,53],462⟩
def representative_2632 : Rep := ⟨![0,10,26,54],462⟩
def representative_2633 : Rep := ⟨![0,10,26,55],462⟩
def representative_2634 : Rep := ⟨![0,10,27,32],462⟩
def representative_2635 : Rep := ⟨![0,10,27,37],462⟩
def representative_2636 : Rep := ⟨![0,10,27,38],462⟩
def representative_2637 : Rep := ⟨![0,10,27,39],462⟩
def representative_2638 : Rep := ⟨![0,10,27,40],462⟩
def representative_2639 : Rep := ⟨![0,10,27,41],462⟩
def representative_2640 : Rep := ⟨![0,10,27,45],462⟩
def representative_2641 : Rep := ⟨![0,10,27,46],462⟩
def representative_2642 : Rep := ⟨![0,10,27,47],462⟩
def representative_2643 : Rep := ⟨![0,10,27,52],462⟩
def representative_2644 : Rep := ⟨![0,10,27,53],462⟩
def representative_2645 : Rep := ⟨![0,10,27,54],462⟩
def representative_2646 : Rep := ⟨![0,10,27,55],462⟩
def representative_2647 : Rep := ⟨![0,10,28,32],462⟩
def representative_2648 : Rep := ⟨![0,10,28,33],462⟩
def representative_2649 : Rep := ⟨![0,10,28,38],462⟩
def representative_2650 : Rep := ⟨![0,10,28,39],462⟩
def representative_2651 : Rep := ⟨![0,10,28,40],462⟩
def representative_2652 : Rep := ⟨![0,10,28,41],462⟩
def representative_2653 : Rep := ⟨![0,10,28,42],462⟩
def representative_2654 : Rep := ⟨![0,10,28,45],462⟩
def representative_2655 : Rep := ⟨![0,10,28,46],462⟩
def representative_2656 : Rep := ⟨![0,10,28,47],462⟩
def representative_2657 : Rep := ⟨![0,10,28,51],462⟩
def representative_2658 : Rep := ⟨![0,10,28,53],462⟩
def representative_2659 : Rep := ⟨![0,10,28,54],462⟩
def representative_2660 : Rep := ⟨![0,10,29,32],462⟩
def representative_2661 : Rep := ⟨![0,10,29,33],462⟩
def representative_2662 : Rep := ⟨![0,10,29,34],462⟩
def representative_2663 : Rep := ⟨![0,10,29,35],462⟩
def representative_2664 : Rep := ⟨![0,10,29,39],462⟩
def representative_2665 : Rep := ⟨![0,10,29,40],462⟩
def representative_2666 : Rep := ⟨![0,10,29,41],462⟩
def representative_2667 : Rep := ⟨![0,10,29,42],462⟩
def representative_2668 : Rep := ⟨![0,10,29,43],462⟩
def representative_2669 : Rep := ⟨![0,10,29,44],462⟩
def representative_2670 : Rep := ⟨![0,10,29,46],462⟩
def representative_2671 : Rep := ⟨![0,10,29,47],462⟩
def representative_2672 : Rep := ⟨![0,10,29,51],462⟩
def representative_2673 : Rep := ⟨![0,10,29,52],462⟩
def representative_2674 : Rep := ⟨![0,10,30,32],462⟩
def representative_2675 : Rep := ⟨![0,10,30,33],462⟩
def representative_2676 : Rep := ⟨![0,10,30,34],462⟩
def representative_2677 : Rep := ⟨![0,10,30,35],462⟩
def representative_2678 : Rep := ⟨![0,10,30,36],462⟩
def representative_2679 : Rep := ⟨![0,10,30,40],462⟩
def representative_2680 : Rep := ⟨![0,10,30,41],462⟩
def representative_2681 : Rep := ⟨![0,10,30,42],462⟩
def representative_2682 : Rep := ⟨![0,10,30,43],462⟩
def representative_2683 : Rep := ⟨![0,10,30,44],462⟩
def representative_2684 : Rep := ⟨![0,10,30,51],462⟩
def representative_2685 : Rep := ⟨![0,10,30,52],462⟩
def representative_2686 : Rep := ⟨![0,10,31,33],462⟩
def representative_2687 : Rep := ⟨![0,10,31,34],462⟩
theorem coefficient_2624 : validRep representative_2624 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2624)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2625 : validRep representative_2625 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2625)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2626 : validRep representative_2626 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2626)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2627 : validRep representative_2627 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2627)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2628 : validRep representative_2628 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2628)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2629 : validRep representative_2629 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2629)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_2630 : validRep representative_2630 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2630)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2631 : validRep representative_2631 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2631)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2632 : validRep representative_2632 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2632)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2633 : validRep representative_2633 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2633)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2634 : validRep representative_2634 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2634)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2635 : validRep representative_2635 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2635)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2636 : validRep representative_2636 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2636)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2637 : validRep representative_2637 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2637)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2638 : validRep representative_2638 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2638)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2639 : validRep representative_2639 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2639)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2640 : validRep representative_2640 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2640)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2641 : validRep representative_2641 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2641)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2642 : validRep representative_2642 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2642)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2643 : validRep representative_2643 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2643)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2644 : validRep representative_2644 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2644)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2645 : validRep representative_2645 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2645)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2646 : validRep representative_2646 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2646)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2647 : validRep representative_2647 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2647)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2648 : validRep representative_2648 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2648)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2649 : validRep representative_2649 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2649)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2650 : validRep representative_2650 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2650)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2651 : validRep representative_2651 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2651)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2652 : validRep representative_2652 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2652)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2653 : validRep representative_2653 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2653)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2654 : validRep representative_2654 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2654)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2655 : validRep representative_2655 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2655)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2656 : validRep representative_2656 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2656)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2657 : validRep representative_2657 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2657)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2658 : validRep representative_2658 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2658)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2659 : validRep representative_2659 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2659)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2660 : validRep representative_2660 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2660)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2661 : validRep representative_2661 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2661)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2662 : validRep representative_2662 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2662)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2663 : validRep representative_2663 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2663)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2664 : validRep representative_2664 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2664)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2665 : validRep representative_2665 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2665)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2666 : validRep representative_2666 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2666)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2667 : validRep representative_2667 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2667)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2668 : validRep representative_2668 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2668)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2669 : validRep representative_2669 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2669)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2670 : validRep representative_2670 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2670)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2671 : validRep representative_2671 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2671)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2672 : validRep representative_2672 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2672)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2673 : validRep representative_2673 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2673)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2674 : validRep representative_2674 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2674)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2675 : validRep representative_2675 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2675)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2676 : validRep representative_2676 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2676)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2677 : validRep representative_2677 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2677)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2678 : validRep representative_2678 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2678)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2679 : validRep representative_2679 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2679)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2680 : validRep representative_2680 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2680)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2681 : validRep representative_2681 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2681)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2682 : validRep representative_2682 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2682)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2683 : validRep representative_2683 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2683)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2684 : validRep representative_2684 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2684)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2685 : validRep representative_2685 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2685)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2686 : validRep representative_2686 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2686)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2687 : validRep representative_2687 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2687)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_041 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2656 (QuarticIntegerRepresentativeTree.Tree.branch 2640 (QuarticIntegerRepresentativeTree.Tree.branch 2632 (QuarticIntegerRepresentativeTree.Tree.branch 2628 (QuarticIntegerRepresentativeTree.Tree.branch 2626 (QuarticIntegerRepresentativeTree.Tree.branch 2625 (QuarticIntegerRepresentativeTree.Tree.leaf 2624 representative_2624) (QuarticIntegerRepresentativeTree.Tree.leaf 2625 representative_2625)) (QuarticIntegerRepresentativeTree.Tree.branch 2627 (QuarticIntegerRepresentativeTree.Tree.leaf 2626 representative_2626) (QuarticIntegerRepresentativeTree.Tree.leaf 2627 representative_2627))) (QuarticIntegerRepresentativeTree.Tree.branch 2630 (QuarticIntegerRepresentativeTree.Tree.branch 2629 (QuarticIntegerRepresentativeTree.Tree.leaf 2628 representative_2628) (QuarticIntegerRepresentativeTree.Tree.leaf 2629 representative_2629)) (QuarticIntegerRepresentativeTree.Tree.branch 2631 (QuarticIntegerRepresentativeTree.Tree.leaf 2630 representative_2630) (QuarticIntegerRepresentativeTree.Tree.leaf 2631 representative_2631)))) (QuarticIntegerRepresentativeTree.Tree.branch 2636 (QuarticIntegerRepresentativeTree.Tree.branch 2634 (QuarticIntegerRepresentativeTree.Tree.branch 2633 (QuarticIntegerRepresentativeTree.Tree.leaf 2632 representative_2632) (QuarticIntegerRepresentativeTree.Tree.leaf 2633 representative_2633)) (QuarticIntegerRepresentativeTree.Tree.branch 2635 (QuarticIntegerRepresentativeTree.Tree.leaf 2634 representative_2634) (QuarticIntegerRepresentativeTree.Tree.leaf 2635 representative_2635))) (QuarticIntegerRepresentativeTree.Tree.branch 2638 (QuarticIntegerRepresentativeTree.Tree.branch 2637 (QuarticIntegerRepresentativeTree.Tree.leaf 2636 representative_2636) (QuarticIntegerRepresentativeTree.Tree.leaf 2637 representative_2637)) (QuarticIntegerRepresentativeTree.Tree.branch 2639 (QuarticIntegerRepresentativeTree.Tree.leaf 2638 representative_2638) (QuarticIntegerRepresentativeTree.Tree.leaf 2639 representative_2639))))) (QuarticIntegerRepresentativeTree.Tree.branch 2648 (QuarticIntegerRepresentativeTree.Tree.branch 2644 (QuarticIntegerRepresentativeTree.Tree.branch 2642 (QuarticIntegerRepresentativeTree.Tree.branch 2641 (QuarticIntegerRepresentativeTree.Tree.leaf 2640 representative_2640) (QuarticIntegerRepresentativeTree.Tree.leaf 2641 representative_2641)) (QuarticIntegerRepresentativeTree.Tree.branch 2643 (QuarticIntegerRepresentativeTree.Tree.leaf 2642 representative_2642) (QuarticIntegerRepresentativeTree.Tree.leaf 2643 representative_2643))) (QuarticIntegerRepresentativeTree.Tree.branch 2646 (QuarticIntegerRepresentativeTree.Tree.branch 2645 (QuarticIntegerRepresentativeTree.Tree.leaf 2644 representative_2644) (QuarticIntegerRepresentativeTree.Tree.leaf 2645 representative_2645)) (QuarticIntegerRepresentativeTree.Tree.branch 2647 (QuarticIntegerRepresentativeTree.Tree.leaf 2646 representative_2646) (QuarticIntegerRepresentativeTree.Tree.leaf 2647 representative_2647)))) (QuarticIntegerRepresentativeTree.Tree.branch 2652 (QuarticIntegerRepresentativeTree.Tree.branch 2650 (QuarticIntegerRepresentativeTree.Tree.branch 2649 (QuarticIntegerRepresentativeTree.Tree.leaf 2648 representative_2648) (QuarticIntegerRepresentativeTree.Tree.leaf 2649 representative_2649)) (QuarticIntegerRepresentativeTree.Tree.branch 2651 (QuarticIntegerRepresentativeTree.Tree.leaf 2650 representative_2650) (QuarticIntegerRepresentativeTree.Tree.leaf 2651 representative_2651))) (QuarticIntegerRepresentativeTree.Tree.branch 2654 (QuarticIntegerRepresentativeTree.Tree.branch 2653 (QuarticIntegerRepresentativeTree.Tree.leaf 2652 representative_2652) (QuarticIntegerRepresentativeTree.Tree.leaf 2653 representative_2653)) (QuarticIntegerRepresentativeTree.Tree.branch 2655 (QuarticIntegerRepresentativeTree.Tree.leaf 2654 representative_2654) (QuarticIntegerRepresentativeTree.Tree.leaf 2655 representative_2655)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2672 (QuarticIntegerRepresentativeTree.Tree.branch 2664 (QuarticIntegerRepresentativeTree.Tree.branch 2660 (QuarticIntegerRepresentativeTree.Tree.branch 2658 (QuarticIntegerRepresentativeTree.Tree.branch 2657 (QuarticIntegerRepresentativeTree.Tree.leaf 2656 representative_2656) (QuarticIntegerRepresentativeTree.Tree.leaf 2657 representative_2657)) (QuarticIntegerRepresentativeTree.Tree.branch 2659 (QuarticIntegerRepresentativeTree.Tree.leaf 2658 representative_2658) (QuarticIntegerRepresentativeTree.Tree.leaf 2659 representative_2659))) (QuarticIntegerRepresentativeTree.Tree.branch 2662 (QuarticIntegerRepresentativeTree.Tree.branch 2661 (QuarticIntegerRepresentativeTree.Tree.leaf 2660 representative_2660) (QuarticIntegerRepresentativeTree.Tree.leaf 2661 representative_2661)) (QuarticIntegerRepresentativeTree.Tree.branch 2663 (QuarticIntegerRepresentativeTree.Tree.leaf 2662 representative_2662) (QuarticIntegerRepresentativeTree.Tree.leaf 2663 representative_2663)))) (QuarticIntegerRepresentativeTree.Tree.branch 2668 (QuarticIntegerRepresentativeTree.Tree.branch 2666 (QuarticIntegerRepresentativeTree.Tree.branch 2665 (QuarticIntegerRepresentativeTree.Tree.leaf 2664 representative_2664) (QuarticIntegerRepresentativeTree.Tree.leaf 2665 representative_2665)) (QuarticIntegerRepresentativeTree.Tree.branch 2667 (QuarticIntegerRepresentativeTree.Tree.leaf 2666 representative_2666) (QuarticIntegerRepresentativeTree.Tree.leaf 2667 representative_2667))) (QuarticIntegerRepresentativeTree.Tree.branch 2670 (QuarticIntegerRepresentativeTree.Tree.branch 2669 (QuarticIntegerRepresentativeTree.Tree.leaf 2668 representative_2668) (QuarticIntegerRepresentativeTree.Tree.leaf 2669 representative_2669)) (QuarticIntegerRepresentativeTree.Tree.branch 2671 (QuarticIntegerRepresentativeTree.Tree.leaf 2670 representative_2670) (QuarticIntegerRepresentativeTree.Tree.leaf 2671 representative_2671))))) (QuarticIntegerRepresentativeTree.Tree.branch 2680 (QuarticIntegerRepresentativeTree.Tree.branch 2676 (QuarticIntegerRepresentativeTree.Tree.branch 2674 (QuarticIntegerRepresentativeTree.Tree.branch 2673 (QuarticIntegerRepresentativeTree.Tree.leaf 2672 representative_2672) (QuarticIntegerRepresentativeTree.Tree.leaf 2673 representative_2673)) (QuarticIntegerRepresentativeTree.Tree.branch 2675 (QuarticIntegerRepresentativeTree.Tree.leaf 2674 representative_2674) (QuarticIntegerRepresentativeTree.Tree.leaf 2675 representative_2675))) (QuarticIntegerRepresentativeTree.Tree.branch 2678 (QuarticIntegerRepresentativeTree.Tree.branch 2677 (QuarticIntegerRepresentativeTree.Tree.leaf 2676 representative_2676) (QuarticIntegerRepresentativeTree.Tree.leaf 2677 representative_2677)) (QuarticIntegerRepresentativeTree.Tree.branch 2679 (QuarticIntegerRepresentativeTree.Tree.leaf 2678 representative_2678) (QuarticIntegerRepresentativeTree.Tree.leaf 2679 representative_2679)))) (QuarticIntegerRepresentativeTree.Tree.branch 2684 (QuarticIntegerRepresentativeTree.Tree.branch 2682 (QuarticIntegerRepresentativeTree.Tree.branch 2681 (QuarticIntegerRepresentativeTree.Tree.leaf 2680 representative_2680) (QuarticIntegerRepresentativeTree.Tree.leaf 2681 representative_2681)) (QuarticIntegerRepresentativeTree.Tree.branch 2683 (QuarticIntegerRepresentativeTree.Tree.leaf 2682 representative_2682) (QuarticIntegerRepresentativeTree.Tree.leaf 2683 representative_2683))) (QuarticIntegerRepresentativeTree.Tree.branch 2686 (QuarticIntegerRepresentativeTree.Tree.branch 2685 (QuarticIntegerRepresentativeTree.Tree.leaf 2684 representative_2684) (QuarticIntegerRepresentativeTree.Tree.leaf 2685 representative_2685)) (QuarticIntegerRepresentativeTree.Tree.branch 2687 (QuarticIntegerRepresentativeTree.Tree.leaf 2686 representative_2686) (QuarticIntegerRepresentativeTree.Tree.leaf 2687 representative_2687)))))))
theorem accepted_041 : All validRep tree_041 := ⟨⟨⟨⟨⟨⟨coefficient_2624,coefficient_2625⟩,⟨coefficient_2626,coefficient_2627⟩⟩,⟨⟨coefficient_2628,coefficient_2629⟩,⟨coefficient_2630,coefficient_2631⟩⟩⟩,⟨⟨⟨coefficient_2632,coefficient_2633⟩,⟨coefficient_2634,coefficient_2635⟩⟩,⟨⟨coefficient_2636,coefficient_2637⟩,⟨coefficient_2638,coefficient_2639⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2640,coefficient_2641⟩,⟨coefficient_2642,coefficient_2643⟩⟩,⟨⟨coefficient_2644,coefficient_2645⟩,⟨coefficient_2646,coefficient_2647⟩⟩⟩,⟨⟨⟨coefficient_2648,coefficient_2649⟩,⟨coefficient_2650,coefficient_2651⟩⟩,⟨⟨coefficient_2652,coefficient_2653⟩,⟨coefficient_2654,coefficient_2655⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2656,coefficient_2657⟩,⟨coefficient_2658,coefficient_2659⟩⟩,⟨⟨coefficient_2660,coefficient_2661⟩,⟨coefficient_2662,coefficient_2663⟩⟩⟩,⟨⟨⟨coefficient_2664,coefficient_2665⟩,⟨coefficient_2666,coefficient_2667⟩⟩,⟨⟨coefficient_2668,coefficient_2669⟩,⟨coefficient_2670,coefficient_2671⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2672,coefficient_2673⟩,⟨coefficient_2674,coefficient_2675⟩⟩,⟨⟨coefficient_2676,coefficient_2677⟩,⟨coefficient_2678,coefficient_2679⟩⟩⟩,⟨⟨⟨coefficient_2680,coefficient_2681⟩,⟨coefficient_2682,coefficient_2683⟩⟩,⟨⟨coefficient_2684,coefficient_2685⟩,⟨coefficient_2686,coefficient_2687⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

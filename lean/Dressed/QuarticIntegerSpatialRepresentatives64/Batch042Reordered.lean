import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2688 : Rep := ⟨![0,10,31,35],462⟩
def representative_2689 : Rep := ⟨![0,10,31,36],462⟩
def representative_2690 : Rep := ⟨![0,10,31,41],462⟩
def representative_2691 : Rep := ⟨![0,10,31,42],462⟩
def representative_2692 : Rep := ⟨![0,10,31,43],462⟩
def representative_2693 : Rep := ⟨![0,10,31,44],462⟩
def representative_2694 : Rep := ⟨![0,10,31,45],462⟩
def representative_2695 : Rep := ⟨![0,10,31,51],462⟩
def representative_2696 : Rep := ⟨![0,10,32,42],462⟩
def representative_2697 : Rep := ⟨![0,10,32,43],462⟩
def representative_2698 : Rep := ⟨![0,10,32,44],462⟩
def representative_2699 : Rep := ⟨![0,10,32,45],462⟩
def representative_2700 : Rep := ⟨![0,10,32,46],462⟩
def representative_2701 : Rep := ⟨![0,10,33,43],462⟩
def representative_2702 : Rep := ⟨![0,10,33,44],462⟩
def representative_2703 : Rep := ⟨![0,10,33,45],462⟩
def representative_2704 : Rep := ⟨![0,10,33,46],462⟩
def representative_2705 : Rep := ⟨![0,10,33,47],462⟩
def representative_2706 : Rep := ⟨![0,10,34,40],462⟩
def representative_2707 : Rep := ⟨![0,10,34,44],462⟩
def representative_2708 : Rep := ⟨![0,10,34,45],462⟩
def representative_2709 : Rep := ⟨![0,10,34,46],462⟩
def representative_2710 : Rep := ⟨![0,10,34,47],462⟩
def representative_2711 : Rep := ⟨![0,10,35,45],462⟩
def representative_2712 : Rep := ⟨![0,10,35,46],462⟩
def representative_2713 : Rep := ⟨![0,10,35,47],462⟩
def representative_2714 : Rep := ⟨![0,10,36,46],462⟩
def representative_2715 : Rep := ⟨![0,10,37,43],462⟩
def representative_2716 : Rep := ⟨![0,10,38,43],462⟩
def representative_2717 : Rep := ⟨![0,10,38,44],462⟩
def representative_2718 : Rep := ⟨![0,10,39,43],462⟩
def representative_2719 : Rep := ⟨![0,11,1,12],462⟩
def representative_2720 : Rep := ⟨![0,11,1,13],462⟩
def representative_2721 : Rep := ⟨![0,11,1,14],11⟩
def representative_2722 : Rep := ⟨![0,11,1,19],462⟩
def representative_2723 : Rep := ⟨![0,11,1,20],462⟩
def representative_2724 : Rep := ⟨![0,11,1,21],462⟩
def representative_2725 : Rep := ⟨![0,11,1,22],462⟩
def representative_2726 : Rep := ⟨![0,11,1,23],11⟩
def representative_2727 : Rep := ⟨![0,11,1,24],10⟩
def representative_2728 : Rep := ⟨![0,11,1,26],462⟩
def representative_2729 : Rep := ⟨![0,11,1,27],462⟩
def representative_2730 : Rep := ⟨![0,11,1,28],462⟩
def representative_2731 : Rep := ⟨![0,11,1,29],462⟩
def representative_2732 : Rep := ⟨![0,11,1,30],462⟩
def representative_2733 : Rep := ⟨![0,11,1,31],462⟩
def representative_2734 : Rep := ⟨![0,11,1,32],462⟩
def representative_2735 : Rep := ⟨![0,11,1,34],462⟩
def representative_2736 : Rep := ⟨![0,11,1,35],462⟩
def representative_2737 : Rep := ⟨![0,11,1,36],462⟩
def representative_2738 : Rep := ⟨![0,11,1,37],462⟩
def representative_2739 : Rep := ⟨![0,11,1,38],462⟩
def representative_2740 : Rep := ⟨![0,11,1,39],462⟩
def representative_2741 : Rep := ⟨![0,11,1,40],10⟩
def representative_2742 : Rep := ⟨![0,11,1,42],462⟩
def representative_2743 : Rep := ⟨![0,11,1,43],462⟩
def representative_2744 : Rep := ⟨![0,11,1,44],462⟩
def representative_2745 : Rep := ⟨![0,11,1,45],462⟩
def representative_2746 : Rep := ⟨![0,11,1,46],462⟩
def representative_2747 : Rep := ⟨![0,11,1,47],462⟩
def representative_2748 : Rep := ⟨![0,11,1,51],462⟩
def representative_2749 : Rep := ⟨![0,11,1,52],462⟩
def representative_2750 : Rep := ⟨![0,11,1,53],462⟩
def representative_2751 : Rep := ⟨![0,11,1,54],462⟩
theorem coefficient_2688 : validRep representative_2688 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2688)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2689 : validRep representative_2689 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2689)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2690 : validRep representative_2690 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2690)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2691 : validRep representative_2691 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2691)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2692 : validRep representative_2692 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2692)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2693 : validRep representative_2693 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2693)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2694 : validRep representative_2694 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2694)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2695 : validRep representative_2695 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2695)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2696 : validRep representative_2696 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2696)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2697 : validRep representative_2697 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2697)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2698 : validRep representative_2698 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2698)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2699 : validRep representative_2699 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2699)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2700 : validRep representative_2700 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2700)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2701 : validRep representative_2701 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2701)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2702 : validRep representative_2702 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2702)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2703 : validRep representative_2703 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2703)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2704 : validRep representative_2704 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2704)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2705 : validRep representative_2705 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2705)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2706 : validRep representative_2706 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2706)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2707 : validRep representative_2707 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2707)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2708 : validRep representative_2708 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2708)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2709 : validRep representative_2709 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2709)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2710 : validRep representative_2710 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2710)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2711 : validRep representative_2711 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2711)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2712 : validRep representative_2712 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2712)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2713 : validRep representative_2713 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2713)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2714 : validRep representative_2714 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2714)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2715 : validRep representative_2715 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2715)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2716 : validRep representative_2716 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2716)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2717 : validRep representative_2717 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2717)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2718 : validRep representative_2718 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2718)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2719 : validRep representative_2719 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2719)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2720 : validRep representative_2720 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2720)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2721 : validRep representative_2721 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2721)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_2722 : validRep representative_2722 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2722)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2723 : validRep representative_2723 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2723)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2724 : validRep representative_2724 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2724)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2725 : validRep representative_2725 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2725)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2726 : validRep representative_2726 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2726)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_2727 : validRep representative_2727 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2727)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_2728 : validRep representative_2728 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2728)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2729 : validRep representative_2729 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2729)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2730 : validRep representative_2730 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2730)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2731 : validRep representative_2731 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2731)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2732 : validRep representative_2732 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2732)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2733 : validRep representative_2733 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2733)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2734 : validRep representative_2734 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2734)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2735 : validRep representative_2735 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2735)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2736 : validRep representative_2736 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2736)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2737 : validRep representative_2737 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2737)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2738 : validRep representative_2738 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2738)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2739 : validRep representative_2739 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2739)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2740 : validRep representative_2740 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2740)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2741 : validRep representative_2741 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2741)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_2742 : validRep representative_2742 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2742)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2743 : validRep representative_2743 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2743)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2744 : validRep representative_2744 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2744)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2745 : validRep representative_2745 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2745)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2746 : validRep representative_2746 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2746)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2747 : validRep representative_2747 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2747)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2748 : validRep representative_2748 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2748)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2749 : validRep representative_2749 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2749)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2750 : validRep representative_2750 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2750)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2751 : validRep representative_2751 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2751)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_042 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2720 (QuarticIntegerRepresentativeTree.Tree.branch 2704 (QuarticIntegerRepresentativeTree.Tree.branch 2696 (QuarticIntegerRepresentativeTree.Tree.branch 2692 (QuarticIntegerRepresentativeTree.Tree.branch 2690 (QuarticIntegerRepresentativeTree.Tree.branch 2689 (QuarticIntegerRepresentativeTree.Tree.leaf 2688 representative_2688) (QuarticIntegerRepresentativeTree.Tree.leaf 2689 representative_2689)) (QuarticIntegerRepresentativeTree.Tree.branch 2691 (QuarticIntegerRepresentativeTree.Tree.leaf 2690 representative_2690) (QuarticIntegerRepresentativeTree.Tree.leaf 2691 representative_2691))) (QuarticIntegerRepresentativeTree.Tree.branch 2694 (QuarticIntegerRepresentativeTree.Tree.branch 2693 (QuarticIntegerRepresentativeTree.Tree.leaf 2692 representative_2692) (QuarticIntegerRepresentativeTree.Tree.leaf 2693 representative_2693)) (QuarticIntegerRepresentativeTree.Tree.branch 2695 (QuarticIntegerRepresentativeTree.Tree.leaf 2694 representative_2694) (QuarticIntegerRepresentativeTree.Tree.leaf 2695 representative_2695)))) (QuarticIntegerRepresentativeTree.Tree.branch 2700 (QuarticIntegerRepresentativeTree.Tree.branch 2698 (QuarticIntegerRepresentativeTree.Tree.branch 2697 (QuarticIntegerRepresentativeTree.Tree.leaf 2696 representative_2696) (QuarticIntegerRepresentativeTree.Tree.leaf 2697 representative_2697)) (QuarticIntegerRepresentativeTree.Tree.branch 2699 (QuarticIntegerRepresentativeTree.Tree.leaf 2698 representative_2698) (QuarticIntegerRepresentativeTree.Tree.leaf 2699 representative_2699))) (QuarticIntegerRepresentativeTree.Tree.branch 2702 (QuarticIntegerRepresentativeTree.Tree.branch 2701 (QuarticIntegerRepresentativeTree.Tree.leaf 2700 representative_2700) (QuarticIntegerRepresentativeTree.Tree.leaf 2701 representative_2701)) (QuarticIntegerRepresentativeTree.Tree.branch 2703 (QuarticIntegerRepresentativeTree.Tree.leaf 2702 representative_2702) (QuarticIntegerRepresentativeTree.Tree.leaf 2703 representative_2703))))) (QuarticIntegerRepresentativeTree.Tree.branch 2712 (QuarticIntegerRepresentativeTree.Tree.branch 2708 (QuarticIntegerRepresentativeTree.Tree.branch 2706 (QuarticIntegerRepresentativeTree.Tree.branch 2705 (QuarticIntegerRepresentativeTree.Tree.leaf 2704 representative_2704) (QuarticIntegerRepresentativeTree.Tree.leaf 2705 representative_2705)) (QuarticIntegerRepresentativeTree.Tree.branch 2707 (QuarticIntegerRepresentativeTree.Tree.leaf 2706 representative_2706) (QuarticIntegerRepresentativeTree.Tree.leaf 2707 representative_2707))) (QuarticIntegerRepresentativeTree.Tree.branch 2710 (QuarticIntegerRepresentativeTree.Tree.branch 2709 (QuarticIntegerRepresentativeTree.Tree.leaf 2708 representative_2708) (QuarticIntegerRepresentativeTree.Tree.leaf 2709 representative_2709)) (QuarticIntegerRepresentativeTree.Tree.branch 2711 (QuarticIntegerRepresentativeTree.Tree.leaf 2710 representative_2710) (QuarticIntegerRepresentativeTree.Tree.leaf 2711 representative_2711)))) (QuarticIntegerRepresentativeTree.Tree.branch 2716 (QuarticIntegerRepresentativeTree.Tree.branch 2714 (QuarticIntegerRepresentativeTree.Tree.branch 2713 (QuarticIntegerRepresentativeTree.Tree.leaf 2712 representative_2712) (QuarticIntegerRepresentativeTree.Tree.leaf 2713 representative_2713)) (QuarticIntegerRepresentativeTree.Tree.branch 2715 (QuarticIntegerRepresentativeTree.Tree.leaf 2714 representative_2714) (QuarticIntegerRepresentativeTree.Tree.leaf 2715 representative_2715))) (QuarticIntegerRepresentativeTree.Tree.branch 2718 (QuarticIntegerRepresentativeTree.Tree.branch 2717 (QuarticIntegerRepresentativeTree.Tree.leaf 2716 representative_2716) (QuarticIntegerRepresentativeTree.Tree.leaf 2717 representative_2717)) (QuarticIntegerRepresentativeTree.Tree.branch 2719 (QuarticIntegerRepresentativeTree.Tree.leaf 2718 representative_2718) (QuarticIntegerRepresentativeTree.Tree.leaf 2719 representative_2719)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2736 (QuarticIntegerRepresentativeTree.Tree.branch 2728 (QuarticIntegerRepresentativeTree.Tree.branch 2724 (QuarticIntegerRepresentativeTree.Tree.branch 2722 (QuarticIntegerRepresentativeTree.Tree.branch 2721 (QuarticIntegerRepresentativeTree.Tree.leaf 2720 representative_2720) (QuarticIntegerRepresentativeTree.Tree.leaf 2721 representative_2721)) (QuarticIntegerRepresentativeTree.Tree.branch 2723 (QuarticIntegerRepresentativeTree.Tree.leaf 2722 representative_2722) (QuarticIntegerRepresentativeTree.Tree.leaf 2723 representative_2723))) (QuarticIntegerRepresentativeTree.Tree.branch 2726 (QuarticIntegerRepresentativeTree.Tree.branch 2725 (QuarticIntegerRepresentativeTree.Tree.leaf 2724 representative_2724) (QuarticIntegerRepresentativeTree.Tree.leaf 2725 representative_2725)) (QuarticIntegerRepresentativeTree.Tree.branch 2727 (QuarticIntegerRepresentativeTree.Tree.leaf 2726 representative_2726) (QuarticIntegerRepresentativeTree.Tree.leaf 2727 representative_2727)))) (QuarticIntegerRepresentativeTree.Tree.branch 2732 (QuarticIntegerRepresentativeTree.Tree.branch 2730 (QuarticIntegerRepresentativeTree.Tree.branch 2729 (QuarticIntegerRepresentativeTree.Tree.leaf 2728 representative_2728) (QuarticIntegerRepresentativeTree.Tree.leaf 2729 representative_2729)) (QuarticIntegerRepresentativeTree.Tree.branch 2731 (QuarticIntegerRepresentativeTree.Tree.leaf 2730 representative_2730) (QuarticIntegerRepresentativeTree.Tree.leaf 2731 representative_2731))) (QuarticIntegerRepresentativeTree.Tree.branch 2734 (QuarticIntegerRepresentativeTree.Tree.branch 2733 (QuarticIntegerRepresentativeTree.Tree.leaf 2732 representative_2732) (QuarticIntegerRepresentativeTree.Tree.leaf 2733 representative_2733)) (QuarticIntegerRepresentativeTree.Tree.branch 2735 (QuarticIntegerRepresentativeTree.Tree.leaf 2734 representative_2734) (QuarticIntegerRepresentativeTree.Tree.leaf 2735 representative_2735))))) (QuarticIntegerRepresentativeTree.Tree.branch 2744 (QuarticIntegerRepresentativeTree.Tree.branch 2740 (QuarticIntegerRepresentativeTree.Tree.branch 2738 (QuarticIntegerRepresentativeTree.Tree.branch 2737 (QuarticIntegerRepresentativeTree.Tree.leaf 2736 representative_2736) (QuarticIntegerRepresentativeTree.Tree.leaf 2737 representative_2737)) (QuarticIntegerRepresentativeTree.Tree.branch 2739 (QuarticIntegerRepresentativeTree.Tree.leaf 2738 representative_2738) (QuarticIntegerRepresentativeTree.Tree.leaf 2739 representative_2739))) (QuarticIntegerRepresentativeTree.Tree.branch 2742 (QuarticIntegerRepresentativeTree.Tree.branch 2741 (QuarticIntegerRepresentativeTree.Tree.leaf 2740 representative_2740) (QuarticIntegerRepresentativeTree.Tree.leaf 2741 representative_2741)) (QuarticIntegerRepresentativeTree.Tree.branch 2743 (QuarticIntegerRepresentativeTree.Tree.leaf 2742 representative_2742) (QuarticIntegerRepresentativeTree.Tree.leaf 2743 representative_2743)))) (QuarticIntegerRepresentativeTree.Tree.branch 2748 (QuarticIntegerRepresentativeTree.Tree.branch 2746 (QuarticIntegerRepresentativeTree.Tree.branch 2745 (QuarticIntegerRepresentativeTree.Tree.leaf 2744 representative_2744) (QuarticIntegerRepresentativeTree.Tree.leaf 2745 representative_2745)) (QuarticIntegerRepresentativeTree.Tree.branch 2747 (QuarticIntegerRepresentativeTree.Tree.leaf 2746 representative_2746) (QuarticIntegerRepresentativeTree.Tree.leaf 2747 representative_2747))) (QuarticIntegerRepresentativeTree.Tree.branch 2750 (QuarticIntegerRepresentativeTree.Tree.branch 2749 (QuarticIntegerRepresentativeTree.Tree.leaf 2748 representative_2748) (QuarticIntegerRepresentativeTree.Tree.leaf 2749 representative_2749)) (QuarticIntegerRepresentativeTree.Tree.branch 2751 (QuarticIntegerRepresentativeTree.Tree.leaf 2750 representative_2750) (QuarticIntegerRepresentativeTree.Tree.leaf 2751 representative_2751)))))))
theorem accepted_042 : All validRep tree_042 := ⟨⟨⟨⟨⟨⟨coefficient_2688,coefficient_2689⟩,⟨coefficient_2690,coefficient_2691⟩⟩,⟨⟨coefficient_2692,coefficient_2693⟩,⟨coefficient_2694,coefficient_2695⟩⟩⟩,⟨⟨⟨coefficient_2696,coefficient_2697⟩,⟨coefficient_2698,coefficient_2699⟩⟩,⟨⟨coefficient_2700,coefficient_2701⟩,⟨coefficient_2702,coefficient_2703⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2704,coefficient_2705⟩,⟨coefficient_2706,coefficient_2707⟩⟩,⟨⟨coefficient_2708,coefficient_2709⟩,⟨coefficient_2710,coefficient_2711⟩⟩⟩,⟨⟨⟨coefficient_2712,coefficient_2713⟩,⟨coefficient_2714,coefficient_2715⟩⟩,⟨⟨coefficient_2716,coefficient_2717⟩,⟨coefficient_2718,coefficient_2719⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2720,coefficient_2721⟩,⟨coefficient_2722,coefficient_2723⟩⟩,⟨⟨coefficient_2724,coefficient_2725⟩,⟨coefficient_2726,coefficient_2727⟩⟩⟩,⟨⟨⟨coefficient_2728,coefficient_2729⟩,⟨coefficient_2730,coefficient_2731⟩⟩,⟨⟨coefficient_2732,coefficient_2733⟩,⟨coefficient_2734,coefficient_2735⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2736,coefficient_2737⟩,⟨coefficient_2738,coefficient_2739⟩⟩,⟨⟨coefficient_2740,coefficient_2741⟩,⟨coefficient_2742,coefficient_2743⟩⟩⟩,⟨⟨⟨coefficient_2744,coefficient_2745⟩,⟨coefficient_2746,coefficient_2747⟩⟩,⟨⟨coefficient_2748,coefficient_2749⟩,⟨coefficient_2750,coefficient_2751⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

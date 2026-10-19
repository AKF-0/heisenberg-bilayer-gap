import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2752 : Rep := ⟨![0,11,1,55],11⟩
def representative_2753 : Rep := ⟨![0,11,1,60],462⟩
def representative_2754 : Rep := ⟨![0,11,1,61],462⟩
def representative_2755 : Rep := ⟨![0,11,1,62],11⟩
def representative_2756 : Rep := ⟨![0,11,2,13],462⟩
def representative_2757 : Rep := ⟨![0,11,2,14],462⟩
def representative_2758 : Rep := ⟨![0,11,2,15],462⟩
def representative_2759 : Rep := ⟨![0,11,2,16],462⟩
def representative_2760 : Rep := ⟨![0,11,2,20],462⟩
def representative_2761 : Rep := ⟨![0,11,2,21],462⟩
def representative_2762 : Rep := ⟨![0,11,2,22],462⟩
def representative_2763 : Rep := ⟨![0,11,2,23],462⟩
def representative_2764 : Rep := ⟨![0,11,2,24],462⟩
def representative_2765 : Rep := ⟨![0,11,2,25],462⟩
def representative_2766 : Rep := ⟨![0,11,2,27],462⟩
def representative_2767 : Rep := ⟨![0,11,2,28],462⟩
def representative_2768 : Rep := ⟨![0,11,2,29],462⟩
def representative_2769 : Rep := ⟨![0,11,2,30],462⟩
def representative_2770 : Rep := ⟨![0,11,2,31],462⟩
def representative_2771 : Rep := ⟨![0,11,2,32],462⟩
def representative_2772 : Rep := ⟨![0,11,2,33],462⟩
def representative_2773 : Rep := ⟨![0,11,2,35],462⟩
def representative_2774 : Rep := ⟨![0,11,2,36],462⟩
def representative_2775 : Rep := ⟨![0,11,2,37],462⟩
def representative_2776 : Rep := ⟨![0,11,2,38],462⟩
def representative_2777 : Rep := ⟨![0,11,2,39],462⟩
def representative_2778 : Rep := ⟨![0,11,2,40],462⟩
def representative_2779 : Rep := ⟨![0,11,2,41],462⟩
def representative_2780 : Rep := ⟨![0,11,2,43],462⟩
def representative_2781 : Rep := ⟨![0,11,2,44],462⟩
def representative_2782 : Rep := ⟨![0,11,2,45],462⟩
def representative_2783 : Rep := ⟨![0,11,2,46],462⟩
def representative_2784 : Rep := ⟨![0,11,2,47],462⟩
def representative_2785 : Rep := ⟨![0,11,2,48],462⟩
def representative_2786 : Rep := ⟨![0,11,2,52],462⟩
def representative_2787 : Rep := ⟨![0,11,2,53],462⟩
def representative_2788 : Rep := ⟨![0,11,2,54],462⟩
def representative_2789 : Rep := ⟨![0,11,2,55],462⟩
def representative_2790 : Rep := ⟨![0,11,2,61],462⟩
def representative_2791 : Rep := ⟨![0,11,2,62],462⟩
def representative_2792 : Rep := ⟨![0,11,2,63],462⟩
def representative_2793 : Rep := ⟨![0,11,3,8],9⟩
def representative_2794 : Rep := ⟨![0,11,3,14],8⟩
def representative_2795 : Rep := ⟨![0,11,3,15],462⟩
def representative_2796 : Rep := ⟨![0,11,3,16],462⟩
def representative_2797 : Rep := ⟨![0,11,3,17],10⟩
def representative_2798 : Rep := ⟨![0,11,3,21],10⟩
def representative_2799 : Rep := ⟨![0,11,3,22],462⟩
def representative_2800 : Rep := ⟨![0,11,3,23],462⟩
def representative_2801 : Rep := ⟨![0,11,3,24],462⟩
def representative_2802 : Rep := ⟨![0,11,3,25],462⟩
def representative_2803 : Rep := ⟨![0,11,3,29],462⟩
def representative_2804 : Rep := ⟨![0,11,3,30],462⟩
def representative_2805 : Rep := ⟨![0,11,3,31],462⟩
def representative_2806 : Rep := ⟨![0,11,3,32],462⟩
def representative_2807 : Rep := ⟨![0,11,3,33],462⟩
def representative_2808 : Rep := ⟨![0,11,3,34],462⟩
def representative_2809 : Rep := ⟨![0,11,3,36],462⟩
def representative_2810 : Rep := ⟨![0,11,3,37],462⟩
def representative_2811 : Rep := ⟨![0,11,3,38],462⟩
def representative_2812 : Rep := ⟨![0,11,3,39],462⟩
def representative_2813 : Rep := ⟨![0,11,3,40],462⟩
def representative_2814 : Rep := ⟨![0,11,3,41],462⟩
def representative_2815 : Rep := ⟨![0,11,3,42],462⟩
theorem coefficient_2752 : validRep representative_2752 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2752)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_2753 : validRep representative_2753 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2753)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2754 : validRep representative_2754 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2754)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2755 : validRep representative_2755 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2755)=dictionary64.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_2756 : validRep representative_2756 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2756)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2757 : validRep representative_2757 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2757)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2758 : validRep representative_2758 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2758)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2759 : validRep representative_2759 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2759)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2760 : validRep representative_2760 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2760)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2761 : validRep representative_2761 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2761)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2762 : validRep representative_2762 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2762)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2763 : validRep representative_2763 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2763)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2764 : validRep representative_2764 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2764)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2765 : validRep representative_2765 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2765)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2766 : validRep representative_2766 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2766)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2767 : validRep representative_2767 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2767)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2768 : validRep representative_2768 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2768)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2769 : validRep representative_2769 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2769)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2770 : validRep representative_2770 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2770)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2771 : validRep representative_2771 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2771)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2772 : validRep representative_2772 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2772)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2773 : validRep representative_2773 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2773)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2774 : validRep representative_2774 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2774)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2775 : validRep representative_2775 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2775)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2776 : validRep representative_2776 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2776)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2777 : validRep representative_2777 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2777)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2778 : validRep representative_2778 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2778)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2779 : validRep representative_2779 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2779)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2780 : validRep representative_2780 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2780)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2781 : validRep representative_2781 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2781)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2782 : validRep representative_2782 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2782)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2783 : validRep representative_2783 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2783)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2784 : validRep representative_2784 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2784)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2785 : validRep representative_2785 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2785)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2786 : validRep representative_2786 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2786)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2787 : validRep representative_2787 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2787)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2788 : validRep representative_2788 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2788)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2789 : validRep representative_2789 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2789)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2790 : validRep representative_2790 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2790)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2791 : validRep representative_2791 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2791)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2792 : validRep representative_2792 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2792)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2793 : validRep representative_2793 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2793)=dictionary64.getD 9 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_2794 : validRep representative_2794 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2794)=dictionary64.getD 8 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_8]
  decide +kernel
theorem coefficient_2795 : validRep representative_2795 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2795)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2796 : validRep representative_2796 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2796)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2797 : validRep representative_2797 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2797)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_2798 : validRep representative_2798 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2798)=dictionary64.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_2799 : validRep representative_2799 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2799)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2800 : validRep representative_2800 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2800)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2801 : validRep representative_2801 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2801)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2802 : validRep representative_2802 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2802)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2803 : validRep representative_2803 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2803)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2804 : validRep representative_2804 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2804)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2805 : validRep representative_2805 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2805)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2806 : validRep representative_2806 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2806)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2807 : validRep representative_2807 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2807)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2808 : validRep representative_2808 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2808)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2809 : validRep representative_2809 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2809)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2810 : validRep representative_2810 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2810)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2811 : validRep representative_2811 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2811)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2812 : validRep representative_2812 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2812)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2813 : validRep representative_2813 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2813)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2814 : validRep representative_2814 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2814)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2815 : validRep representative_2815 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2815)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_043 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2784 (QuarticIntegerRepresentativeTree.Tree.branch 2768 (QuarticIntegerRepresentativeTree.Tree.branch 2760 (QuarticIntegerRepresentativeTree.Tree.branch 2756 (QuarticIntegerRepresentativeTree.Tree.branch 2754 (QuarticIntegerRepresentativeTree.Tree.branch 2753 (QuarticIntegerRepresentativeTree.Tree.leaf 2752 representative_2752) (QuarticIntegerRepresentativeTree.Tree.leaf 2753 representative_2753)) (QuarticIntegerRepresentativeTree.Tree.branch 2755 (QuarticIntegerRepresentativeTree.Tree.leaf 2754 representative_2754) (QuarticIntegerRepresentativeTree.Tree.leaf 2755 representative_2755))) (QuarticIntegerRepresentativeTree.Tree.branch 2758 (QuarticIntegerRepresentativeTree.Tree.branch 2757 (QuarticIntegerRepresentativeTree.Tree.leaf 2756 representative_2756) (QuarticIntegerRepresentativeTree.Tree.leaf 2757 representative_2757)) (QuarticIntegerRepresentativeTree.Tree.branch 2759 (QuarticIntegerRepresentativeTree.Tree.leaf 2758 representative_2758) (QuarticIntegerRepresentativeTree.Tree.leaf 2759 representative_2759)))) (QuarticIntegerRepresentativeTree.Tree.branch 2764 (QuarticIntegerRepresentativeTree.Tree.branch 2762 (QuarticIntegerRepresentativeTree.Tree.branch 2761 (QuarticIntegerRepresentativeTree.Tree.leaf 2760 representative_2760) (QuarticIntegerRepresentativeTree.Tree.leaf 2761 representative_2761)) (QuarticIntegerRepresentativeTree.Tree.branch 2763 (QuarticIntegerRepresentativeTree.Tree.leaf 2762 representative_2762) (QuarticIntegerRepresentativeTree.Tree.leaf 2763 representative_2763))) (QuarticIntegerRepresentativeTree.Tree.branch 2766 (QuarticIntegerRepresentativeTree.Tree.branch 2765 (QuarticIntegerRepresentativeTree.Tree.leaf 2764 representative_2764) (QuarticIntegerRepresentativeTree.Tree.leaf 2765 representative_2765)) (QuarticIntegerRepresentativeTree.Tree.branch 2767 (QuarticIntegerRepresentativeTree.Tree.leaf 2766 representative_2766) (QuarticIntegerRepresentativeTree.Tree.leaf 2767 representative_2767))))) (QuarticIntegerRepresentativeTree.Tree.branch 2776 (QuarticIntegerRepresentativeTree.Tree.branch 2772 (QuarticIntegerRepresentativeTree.Tree.branch 2770 (QuarticIntegerRepresentativeTree.Tree.branch 2769 (QuarticIntegerRepresentativeTree.Tree.leaf 2768 representative_2768) (QuarticIntegerRepresentativeTree.Tree.leaf 2769 representative_2769)) (QuarticIntegerRepresentativeTree.Tree.branch 2771 (QuarticIntegerRepresentativeTree.Tree.leaf 2770 representative_2770) (QuarticIntegerRepresentativeTree.Tree.leaf 2771 representative_2771))) (QuarticIntegerRepresentativeTree.Tree.branch 2774 (QuarticIntegerRepresentativeTree.Tree.branch 2773 (QuarticIntegerRepresentativeTree.Tree.leaf 2772 representative_2772) (QuarticIntegerRepresentativeTree.Tree.leaf 2773 representative_2773)) (QuarticIntegerRepresentativeTree.Tree.branch 2775 (QuarticIntegerRepresentativeTree.Tree.leaf 2774 representative_2774) (QuarticIntegerRepresentativeTree.Tree.leaf 2775 representative_2775)))) (QuarticIntegerRepresentativeTree.Tree.branch 2780 (QuarticIntegerRepresentativeTree.Tree.branch 2778 (QuarticIntegerRepresentativeTree.Tree.branch 2777 (QuarticIntegerRepresentativeTree.Tree.leaf 2776 representative_2776) (QuarticIntegerRepresentativeTree.Tree.leaf 2777 representative_2777)) (QuarticIntegerRepresentativeTree.Tree.branch 2779 (QuarticIntegerRepresentativeTree.Tree.leaf 2778 representative_2778) (QuarticIntegerRepresentativeTree.Tree.leaf 2779 representative_2779))) (QuarticIntegerRepresentativeTree.Tree.branch 2782 (QuarticIntegerRepresentativeTree.Tree.branch 2781 (QuarticIntegerRepresentativeTree.Tree.leaf 2780 representative_2780) (QuarticIntegerRepresentativeTree.Tree.leaf 2781 representative_2781)) (QuarticIntegerRepresentativeTree.Tree.branch 2783 (QuarticIntegerRepresentativeTree.Tree.leaf 2782 representative_2782) (QuarticIntegerRepresentativeTree.Tree.leaf 2783 representative_2783)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2800 (QuarticIntegerRepresentativeTree.Tree.branch 2792 (QuarticIntegerRepresentativeTree.Tree.branch 2788 (QuarticIntegerRepresentativeTree.Tree.branch 2786 (QuarticIntegerRepresentativeTree.Tree.branch 2785 (QuarticIntegerRepresentativeTree.Tree.leaf 2784 representative_2784) (QuarticIntegerRepresentativeTree.Tree.leaf 2785 representative_2785)) (QuarticIntegerRepresentativeTree.Tree.branch 2787 (QuarticIntegerRepresentativeTree.Tree.leaf 2786 representative_2786) (QuarticIntegerRepresentativeTree.Tree.leaf 2787 representative_2787))) (QuarticIntegerRepresentativeTree.Tree.branch 2790 (QuarticIntegerRepresentativeTree.Tree.branch 2789 (QuarticIntegerRepresentativeTree.Tree.leaf 2788 representative_2788) (QuarticIntegerRepresentativeTree.Tree.leaf 2789 representative_2789)) (QuarticIntegerRepresentativeTree.Tree.branch 2791 (QuarticIntegerRepresentativeTree.Tree.leaf 2790 representative_2790) (QuarticIntegerRepresentativeTree.Tree.leaf 2791 representative_2791)))) (QuarticIntegerRepresentativeTree.Tree.branch 2796 (QuarticIntegerRepresentativeTree.Tree.branch 2794 (QuarticIntegerRepresentativeTree.Tree.branch 2793 (QuarticIntegerRepresentativeTree.Tree.leaf 2792 representative_2792) (QuarticIntegerRepresentativeTree.Tree.leaf 2793 representative_2793)) (QuarticIntegerRepresentativeTree.Tree.branch 2795 (QuarticIntegerRepresentativeTree.Tree.leaf 2794 representative_2794) (QuarticIntegerRepresentativeTree.Tree.leaf 2795 representative_2795))) (QuarticIntegerRepresentativeTree.Tree.branch 2798 (QuarticIntegerRepresentativeTree.Tree.branch 2797 (QuarticIntegerRepresentativeTree.Tree.leaf 2796 representative_2796) (QuarticIntegerRepresentativeTree.Tree.leaf 2797 representative_2797)) (QuarticIntegerRepresentativeTree.Tree.branch 2799 (QuarticIntegerRepresentativeTree.Tree.leaf 2798 representative_2798) (QuarticIntegerRepresentativeTree.Tree.leaf 2799 representative_2799))))) (QuarticIntegerRepresentativeTree.Tree.branch 2808 (QuarticIntegerRepresentativeTree.Tree.branch 2804 (QuarticIntegerRepresentativeTree.Tree.branch 2802 (QuarticIntegerRepresentativeTree.Tree.branch 2801 (QuarticIntegerRepresentativeTree.Tree.leaf 2800 representative_2800) (QuarticIntegerRepresentativeTree.Tree.leaf 2801 representative_2801)) (QuarticIntegerRepresentativeTree.Tree.branch 2803 (QuarticIntegerRepresentativeTree.Tree.leaf 2802 representative_2802) (QuarticIntegerRepresentativeTree.Tree.leaf 2803 representative_2803))) (QuarticIntegerRepresentativeTree.Tree.branch 2806 (QuarticIntegerRepresentativeTree.Tree.branch 2805 (QuarticIntegerRepresentativeTree.Tree.leaf 2804 representative_2804) (QuarticIntegerRepresentativeTree.Tree.leaf 2805 representative_2805)) (QuarticIntegerRepresentativeTree.Tree.branch 2807 (QuarticIntegerRepresentativeTree.Tree.leaf 2806 representative_2806) (QuarticIntegerRepresentativeTree.Tree.leaf 2807 representative_2807)))) (QuarticIntegerRepresentativeTree.Tree.branch 2812 (QuarticIntegerRepresentativeTree.Tree.branch 2810 (QuarticIntegerRepresentativeTree.Tree.branch 2809 (QuarticIntegerRepresentativeTree.Tree.leaf 2808 representative_2808) (QuarticIntegerRepresentativeTree.Tree.leaf 2809 representative_2809)) (QuarticIntegerRepresentativeTree.Tree.branch 2811 (QuarticIntegerRepresentativeTree.Tree.leaf 2810 representative_2810) (QuarticIntegerRepresentativeTree.Tree.leaf 2811 representative_2811))) (QuarticIntegerRepresentativeTree.Tree.branch 2814 (QuarticIntegerRepresentativeTree.Tree.branch 2813 (QuarticIntegerRepresentativeTree.Tree.leaf 2812 representative_2812) (QuarticIntegerRepresentativeTree.Tree.leaf 2813 representative_2813)) (QuarticIntegerRepresentativeTree.Tree.branch 2815 (QuarticIntegerRepresentativeTree.Tree.leaf 2814 representative_2814) (QuarticIntegerRepresentativeTree.Tree.leaf 2815 representative_2815)))))))
theorem accepted_043 : All validRep tree_043 := ⟨⟨⟨⟨⟨⟨coefficient_2752,coefficient_2753⟩,⟨coefficient_2754,coefficient_2755⟩⟩,⟨⟨coefficient_2756,coefficient_2757⟩,⟨coefficient_2758,coefficient_2759⟩⟩⟩,⟨⟨⟨coefficient_2760,coefficient_2761⟩,⟨coefficient_2762,coefficient_2763⟩⟩,⟨⟨coefficient_2764,coefficient_2765⟩,⟨coefficient_2766,coefficient_2767⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2768,coefficient_2769⟩,⟨coefficient_2770,coefficient_2771⟩⟩,⟨⟨coefficient_2772,coefficient_2773⟩,⟨coefficient_2774,coefficient_2775⟩⟩⟩,⟨⟨⟨coefficient_2776,coefficient_2777⟩,⟨coefficient_2778,coefficient_2779⟩⟩,⟨⟨coefficient_2780,coefficient_2781⟩,⟨coefficient_2782,coefficient_2783⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2784,coefficient_2785⟩,⟨coefficient_2786,coefficient_2787⟩⟩,⟨⟨coefficient_2788,coefficient_2789⟩,⟨coefficient_2790,coefficient_2791⟩⟩⟩,⟨⟨⟨coefficient_2792,coefficient_2793⟩,⟨coefficient_2794,coefficient_2795⟩⟩,⟨⟨coefficient_2796,coefficient_2797⟩,⟨coefficient_2798,coefficient_2799⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2800,coefficient_2801⟩,⟨coefficient_2802,coefficient_2803⟩⟩,⟨⟨coefficient_2804,coefficient_2805⟩,⟨coefficient_2806,coefficient_2807⟩⟩⟩,⟨⟨⟨coefficient_2808,coefficient_2809⟩,⟨coefficient_2810,coefficient_2811⟩⟩,⟨⟨coefficient_2812,coefficient_2813⟩,⟨coefficient_2814,coefficient_2815⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

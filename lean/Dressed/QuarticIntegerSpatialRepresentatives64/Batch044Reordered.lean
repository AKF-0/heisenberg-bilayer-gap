import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2816 : Rep := ⟨![0,11,3,44],462⟩
def representative_2817 : Rep := ⟨![0,11,3,45],462⟩
def representative_2818 : Rep := ⟨![0,11,3,46],462⟩
def representative_2819 : Rep := ⟨![0,11,3,47],462⟩
def representative_2820 : Rep := ⟨![0,11,3,48],462⟩
def representative_2821 : Rep := ⟨![0,11,3,49],462⟩
def representative_2822 : Rep := ⟨![0,11,3,53],462⟩
def representative_2823 : Rep := ⟨![0,11,3,54],462⟩
def representative_2824 : Rep := ⟨![0,11,3,55],462⟩
def representative_2825 : Rep := ⟨![0,11,3,56],462⟩
def representative_2826 : Rep := ⟨![0,11,3,62],462⟩
def representative_2827 : Rep := ⟨![0,11,3,63],462⟩
def representative_2828 : Rep := ⟨![0,11,4,15],462⟩
def representative_2829 : Rep := ⟨![0,11,4,16],462⟩
def representative_2830 : Rep := ⟨![0,11,4,17],462⟩
def representative_2831 : Rep := ⟨![0,11,4,18],462⟩
def representative_2832 : Rep := ⟨![0,11,4,22],462⟩
def representative_2833 : Rep := ⟨![0,11,4,23],462⟩
def representative_2834 : Rep := ⟨![0,11,4,24],462⟩
def representative_2835 : Rep := ⟨![0,11,4,25],462⟩
def representative_2836 : Rep := ⟨![0,11,4,26],462⟩
def representative_2837 : Rep := ⟨![0,11,4,29],462⟩
def representative_2838 : Rep := ⟨![0,11,4,30],462⟩
def representative_2839 : Rep := ⟨![0,11,4,31],462⟩
def representative_2840 : Rep := ⟨![0,11,4,32],462⟩
def representative_2841 : Rep := ⟨![0,11,4,33],462⟩
def representative_2842 : Rep := ⟨![0,11,4,34],462⟩
def representative_2843 : Rep := ⟨![0,11,4,35],462⟩
def representative_2844 : Rep := ⟨![0,11,4,37],462⟩
def representative_2845 : Rep := ⟨![0,11,4,38],462⟩
def representative_2846 : Rep := ⟨![0,11,4,39],462⟩
def representative_2847 : Rep := ⟨![0,11,4,40],462⟩
def representative_2848 : Rep := ⟨![0,11,4,41],462⟩
def representative_2849 : Rep := ⟨![0,11,4,42],462⟩
def representative_2850 : Rep := ⟨![0,11,4,43],462⟩
def representative_2851 : Rep := ⟨![0,11,4,45],462⟩
def representative_2852 : Rep := ⟨![0,11,4,46],462⟩
def representative_2853 : Rep := ⟨![0,11,4,47],462⟩
def representative_2854 : Rep := ⟨![0,11,4,48],462⟩
def representative_2855 : Rep := ⟨![0,11,4,49],462⟩
def representative_2856 : Rep := ⟨![0,11,4,50],462⟩
def representative_2857 : Rep := ⟨![0,11,4,54],462⟩
def representative_2858 : Rep := ⟨![0,11,4,55],462⟩
def representative_2859 : Rep := ⟨![0,11,4,56],462⟩
def representative_2860 : Rep := ⟨![0,11,4,57],462⟩
def representative_2861 : Rep := ⟨![0,11,4,63],462⟩
def representative_2862 : Rep := ⟨![0,11,5,16],462⟩
def representative_2863 : Rep := ⟨![0,11,5,17],462⟩
def representative_2864 : Rep := ⟨![0,11,5,18],462⟩
def representative_2865 : Rep := ⟨![0,11,5,19],462⟩
def representative_2866 : Rep := ⟨![0,11,5,23],462⟩
def representative_2867 : Rep := ⟨![0,11,5,24],462⟩
def representative_2868 : Rep := ⟨![0,11,5,25],462⟩
def representative_2869 : Rep := ⟨![0,11,5,26],462⟩
def representative_2870 : Rep := ⟨![0,11,5,27],462⟩
def representative_2871 : Rep := ⟨![0,11,5,28],462⟩
def representative_2872 : Rep := ⟨![0,11,5,30],462⟩
def representative_2873 : Rep := ⟨![0,11,5,31],462⟩
def representative_2874 : Rep := ⟨![0,11,5,32],462⟩
def representative_2875 : Rep := ⟨![0,11,5,33],462⟩
def representative_2876 : Rep := ⟨![0,11,5,34],462⟩
def representative_2877 : Rep := ⟨![0,11,5,35],462⟩
def representative_2878 : Rep := ⟨![0,11,5,36],462⟩
def representative_2879 : Rep := ⟨![0,11,5,38],462⟩
theorem coefficient_2816 : validRep representative_2816 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2816)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2817 : validRep representative_2817 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2817)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2818 : validRep representative_2818 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2818)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2819 : validRep representative_2819 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2819)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2820 : validRep representative_2820 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2820)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2821 : validRep representative_2821 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2821)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2822 : validRep representative_2822 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2822)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2823 : validRep representative_2823 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2823)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2824 : validRep representative_2824 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2824)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2825 : validRep representative_2825 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2825)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2826 : validRep representative_2826 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2826)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2827 : validRep representative_2827 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2827)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2828 : validRep representative_2828 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2828)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2829 : validRep representative_2829 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2829)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2830 : validRep representative_2830 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2830)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2831 : validRep representative_2831 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2831)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2832 : validRep representative_2832 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2832)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2833 : validRep representative_2833 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2833)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2834 : validRep representative_2834 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2834)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2835 : validRep representative_2835 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2835)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2836 : validRep representative_2836 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2836)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2837 : validRep representative_2837 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2837)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2838 : validRep representative_2838 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2838)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2839 : validRep representative_2839 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2839)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2840 : validRep representative_2840 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2840)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2841 : validRep representative_2841 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2841)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2842 : validRep representative_2842 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2842)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2843 : validRep representative_2843 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2843)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2844 : validRep representative_2844 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2844)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2845 : validRep representative_2845 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2845)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2846 : validRep representative_2846 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2846)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2847 : validRep representative_2847 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2847)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2848 : validRep representative_2848 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2848)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2849 : validRep representative_2849 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2849)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2850 : validRep representative_2850 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2850)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2851 : validRep representative_2851 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2851)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2852 : validRep representative_2852 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2852)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2853 : validRep representative_2853 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2853)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2854 : validRep representative_2854 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2854)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2855 : validRep representative_2855 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2855)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2856 : validRep representative_2856 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2856)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2857 : validRep representative_2857 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2857)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2858 : validRep representative_2858 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2858)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2859 : validRep representative_2859 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2859)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2860 : validRep representative_2860 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2860)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2861 : validRep representative_2861 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2861)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2862 : validRep representative_2862 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2862)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2863 : validRep representative_2863 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2863)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2864 : validRep representative_2864 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2864)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2865 : validRep representative_2865 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2865)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2866 : validRep representative_2866 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2866)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2867 : validRep representative_2867 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2867)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2868 : validRep representative_2868 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2868)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2869 : validRep representative_2869 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2869)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2870 : validRep representative_2870 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2870)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2871 : validRep representative_2871 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2871)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2872 : validRep representative_2872 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2872)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2873 : validRep representative_2873 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2873)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2874 : validRep representative_2874 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2874)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2875 : validRep representative_2875 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2875)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2876 : validRep representative_2876 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2876)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2877 : validRep representative_2877 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2877)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2878 : validRep representative_2878 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2878)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2879 : validRep representative_2879 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2879)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_044 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2848 (QuarticIntegerRepresentativeTree.Tree.branch 2832 (QuarticIntegerRepresentativeTree.Tree.branch 2824 (QuarticIntegerRepresentativeTree.Tree.branch 2820 (QuarticIntegerRepresentativeTree.Tree.branch 2818 (QuarticIntegerRepresentativeTree.Tree.branch 2817 (QuarticIntegerRepresentativeTree.Tree.leaf 2816 representative_2816) (QuarticIntegerRepresentativeTree.Tree.leaf 2817 representative_2817)) (QuarticIntegerRepresentativeTree.Tree.branch 2819 (QuarticIntegerRepresentativeTree.Tree.leaf 2818 representative_2818) (QuarticIntegerRepresentativeTree.Tree.leaf 2819 representative_2819))) (QuarticIntegerRepresentativeTree.Tree.branch 2822 (QuarticIntegerRepresentativeTree.Tree.branch 2821 (QuarticIntegerRepresentativeTree.Tree.leaf 2820 representative_2820) (QuarticIntegerRepresentativeTree.Tree.leaf 2821 representative_2821)) (QuarticIntegerRepresentativeTree.Tree.branch 2823 (QuarticIntegerRepresentativeTree.Tree.leaf 2822 representative_2822) (QuarticIntegerRepresentativeTree.Tree.leaf 2823 representative_2823)))) (QuarticIntegerRepresentativeTree.Tree.branch 2828 (QuarticIntegerRepresentativeTree.Tree.branch 2826 (QuarticIntegerRepresentativeTree.Tree.branch 2825 (QuarticIntegerRepresentativeTree.Tree.leaf 2824 representative_2824) (QuarticIntegerRepresentativeTree.Tree.leaf 2825 representative_2825)) (QuarticIntegerRepresentativeTree.Tree.branch 2827 (QuarticIntegerRepresentativeTree.Tree.leaf 2826 representative_2826) (QuarticIntegerRepresentativeTree.Tree.leaf 2827 representative_2827))) (QuarticIntegerRepresentativeTree.Tree.branch 2830 (QuarticIntegerRepresentativeTree.Tree.branch 2829 (QuarticIntegerRepresentativeTree.Tree.leaf 2828 representative_2828) (QuarticIntegerRepresentativeTree.Tree.leaf 2829 representative_2829)) (QuarticIntegerRepresentativeTree.Tree.branch 2831 (QuarticIntegerRepresentativeTree.Tree.leaf 2830 representative_2830) (QuarticIntegerRepresentativeTree.Tree.leaf 2831 representative_2831))))) (QuarticIntegerRepresentativeTree.Tree.branch 2840 (QuarticIntegerRepresentativeTree.Tree.branch 2836 (QuarticIntegerRepresentativeTree.Tree.branch 2834 (QuarticIntegerRepresentativeTree.Tree.branch 2833 (QuarticIntegerRepresentativeTree.Tree.leaf 2832 representative_2832) (QuarticIntegerRepresentativeTree.Tree.leaf 2833 representative_2833)) (QuarticIntegerRepresentativeTree.Tree.branch 2835 (QuarticIntegerRepresentativeTree.Tree.leaf 2834 representative_2834) (QuarticIntegerRepresentativeTree.Tree.leaf 2835 representative_2835))) (QuarticIntegerRepresentativeTree.Tree.branch 2838 (QuarticIntegerRepresentativeTree.Tree.branch 2837 (QuarticIntegerRepresentativeTree.Tree.leaf 2836 representative_2836) (QuarticIntegerRepresentativeTree.Tree.leaf 2837 representative_2837)) (QuarticIntegerRepresentativeTree.Tree.branch 2839 (QuarticIntegerRepresentativeTree.Tree.leaf 2838 representative_2838) (QuarticIntegerRepresentativeTree.Tree.leaf 2839 representative_2839)))) (QuarticIntegerRepresentativeTree.Tree.branch 2844 (QuarticIntegerRepresentativeTree.Tree.branch 2842 (QuarticIntegerRepresentativeTree.Tree.branch 2841 (QuarticIntegerRepresentativeTree.Tree.leaf 2840 representative_2840) (QuarticIntegerRepresentativeTree.Tree.leaf 2841 representative_2841)) (QuarticIntegerRepresentativeTree.Tree.branch 2843 (QuarticIntegerRepresentativeTree.Tree.leaf 2842 representative_2842) (QuarticIntegerRepresentativeTree.Tree.leaf 2843 representative_2843))) (QuarticIntegerRepresentativeTree.Tree.branch 2846 (QuarticIntegerRepresentativeTree.Tree.branch 2845 (QuarticIntegerRepresentativeTree.Tree.leaf 2844 representative_2844) (QuarticIntegerRepresentativeTree.Tree.leaf 2845 representative_2845)) (QuarticIntegerRepresentativeTree.Tree.branch 2847 (QuarticIntegerRepresentativeTree.Tree.leaf 2846 representative_2846) (QuarticIntegerRepresentativeTree.Tree.leaf 2847 representative_2847)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2864 (QuarticIntegerRepresentativeTree.Tree.branch 2856 (QuarticIntegerRepresentativeTree.Tree.branch 2852 (QuarticIntegerRepresentativeTree.Tree.branch 2850 (QuarticIntegerRepresentativeTree.Tree.branch 2849 (QuarticIntegerRepresentativeTree.Tree.leaf 2848 representative_2848) (QuarticIntegerRepresentativeTree.Tree.leaf 2849 representative_2849)) (QuarticIntegerRepresentativeTree.Tree.branch 2851 (QuarticIntegerRepresentativeTree.Tree.leaf 2850 representative_2850) (QuarticIntegerRepresentativeTree.Tree.leaf 2851 representative_2851))) (QuarticIntegerRepresentativeTree.Tree.branch 2854 (QuarticIntegerRepresentativeTree.Tree.branch 2853 (QuarticIntegerRepresentativeTree.Tree.leaf 2852 representative_2852) (QuarticIntegerRepresentativeTree.Tree.leaf 2853 representative_2853)) (QuarticIntegerRepresentativeTree.Tree.branch 2855 (QuarticIntegerRepresentativeTree.Tree.leaf 2854 representative_2854) (QuarticIntegerRepresentativeTree.Tree.leaf 2855 representative_2855)))) (QuarticIntegerRepresentativeTree.Tree.branch 2860 (QuarticIntegerRepresentativeTree.Tree.branch 2858 (QuarticIntegerRepresentativeTree.Tree.branch 2857 (QuarticIntegerRepresentativeTree.Tree.leaf 2856 representative_2856) (QuarticIntegerRepresentativeTree.Tree.leaf 2857 representative_2857)) (QuarticIntegerRepresentativeTree.Tree.branch 2859 (QuarticIntegerRepresentativeTree.Tree.leaf 2858 representative_2858) (QuarticIntegerRepresentativeTree.Tree.leaf 2859 representative_2859))) (QuarticIntegerRepresentativeTree.Tree.branch 2862 (QuarticIntegerRepresentativeTree.Tree.branch 2861 (QuarticIntegerRepresentativeTree.Tree.leaf 2860 representative_2860) (QuarticIntegerRepresentativeTree.Tree.leaf 2861 representative_2861)) (QuarticIntegerRepresentativeTree.Tree.branch 2863 (QuarticIntegerRepresentativeTree.Tree.leaf 2862 representative_2862) (QuarticIntegerRepresentativeTree.Tree.leaf 2863 representative_2863))))) (QuarticIntegerRepresentativeTree.Tree.branch 2872 (QuarticIntegerRepresentativeTree.Tree.branch 2868 (QuarticIntegerRepresentativeTree.Tree.branch 2866 (QuarticIntegerRepresentativeTree.Tree.branch 2865 (QuarticIntegerRepresentativeTree.Tree.leaf 2864 representative_2864) (QuarticIntegerRepresentativeTree.Tree.leaf 2865 representative_2865)) (QuarticIntegerRepresentativeTree.Tree.branch 2867 (QuarticIntegerRepresentativeTree.Tree.leaf 2866 representative_2866) (QuarticIntegerRepresentativeTree.Tree.leaf 2867 representative_2867))) (QuarticIntegerRepresentativeTree.Tree.branch 2870 (QuarticIntegerRepresentativeTree.Tree.branch 2869 (QuarticIntegerRepresentativeTree.Tree.leaf 2868 representative_2868) (QuarticIntegerRepresentativeTree.Tree.leaf 2869 representative_2869)) (QuarticIntegerRepresentativeTree.Tree.branch 2871 (QuarticIntegerRepresentativeTree.Tree.leaf 2870 representative_2870) (QuarticIntegerRepresentativeTree.Tree.leaf 2871 representative_2871)))) (QuarticIntegerRepresentativeTree.Tree.branch 2876 (QuarticIntegerRepresentativeTree.Tree.branch 2874 (QuarticIntegerRepresentativeTree.Tree.branch 2873 (QuarticIntegerRepresentativeTree.Tree.leaf 2872 representative_2872) (QuarticIntegerRepresentativeTree.Tree.leaf 2873 representative_2873)) (QuarticIntegerRepresentativeTree.Tree.branch 2875 (QuarticIntegerRepresentativeTree.Tree.leaf 2874 representative_2874) (QuarticIntegerRepresentativeTree.Tree.leaf 2875 representative_2875))) (QuarticIntegerRepresentativeTree.Tree.branch 2878 (QuarticIntegerRepresentativeTree.Tree.branch 2877 (QuarticIntegerRepresentativeTree.Tree.leaf 2876 representative_2876) (QuarticIntegerRepresentativeTree.Tree.leaf 2877 representative_2877)) (QuarticIntegerRepresentativeTree.Tree.branch 2879 (QuarticIntegerRepresentativeTree.Tree.leaf 2878 representative_2878) (QuarticIntegerRepresentativeTree.Tree.leaf 2879 representative_2879)))))))
theorem accepted_044 : All validRep tree_044 := ⟨⟨⟨⟨⟨⟨coefficient_2816,coefficient_2817⟩,⟨coefficient_2818,coefficient_2819⟩⟩,⟨⟨coefficient_2820,coefficient_2821⟩,⟨coefficient_2822,coefficient_2823⟩⟩⟩,⟨⟨⟨coefficient_2824,coefficient_2825⟩,⟨coefficient_2826,coefficient_2827⟩⟩,⟨⟨coefficient_2828,coefficient_2829⟩,⟨coefficient_2830,coefficient_2831⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2832,coefficient_2833⟩,⟨coefficient_2834,coefficient_2835⟩⟩,⟨⟨coefficient_2836,coefficient_2837⟩,⟨coefficient_2838,coefficient_2839⟩⟩⟩,⟨⟨⟨coefficient_2840,coefficient_2841⟩,⟨coefficient_2842,coefficient_2843⟩⟩,⟨⟨coefficient_2844,coefficient_2845⟩,⟨coefficient_2846,coefficient_2847⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2848,coefficient_2849⟩,⟨coefficient_2850,coefficient_2851⟩⟩,⟨⟨coefficient_2852,coefficient_2853⟩,⟨coefficient_2854,coefficient_2855⟩⟩⟩,⟨⟨⟨coefficient_2856,coefficient_2857⟩,⟨coefficient_2858,coefficient_2859⟩⟩,⟨⟨coefficient_2860,coefficient_2861⟩,⟨coefficient_2862,coefficient_2863⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2864,coefficient_2865⟩,⟨coefficient_2866,coefficient_2867⟩⟩,⟨⟨coefficient_2868,coefficient_2869⟩,⟨coefficient_2870,coefficient_2871⟩⟩⟩,⟨⟨⟨coefficient_2872,coefficient_2873⟩,⟨coefficient_2874,coefficient_2875⟩⟩,⟨⟨coefficient_2876,coefficient_2877⟩,⟨coefficient_2878,coefficient_2879⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

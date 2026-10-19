import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2880 : Rep := ⟨![0,11,5,39],462⟩
def representative_2881 : Rep := ⟨![0,11,5,40],462⟩
def representative_2882 : Rep := ⟨![0,11,5,41],462⟩
def representative_2883 : Rep := ⟨![0,11,5,42],462⟩
def representative_2884 : Rep := ⟨![0,11,5,43],462⟩
def representative_2885 : Rep := ⟨![0,11,5,44],462⟩
def representative_2886 : Rep := ⟨![0,11,5,46],462⟩
def representative_2887 : Rep := ⟨![0,11,5,47],462⟩
def representative_2888 : Rep := ⟨![0,11,5,48],462⟩
def representative_2889 : Rep := ⟨![0,11,5,49],462⟩
def representative_2890 : Rep := ⟨![0,11,5,50],462⟩
def representative_2891 : Rep := ⟨![0,11,5,51],462⟩
def representative_2892 : Rep := ⟨![0,11,5,55],462⟩
def representative_2893 : Rep := ⟨![0,11,5,57],462⟩
def representative_2894 : Rep := ⟨![0,11,5,58],462⟩
def representative_2895 : Rep := ⟨![0,11,6,16],462⟩
def representative_2896 : Rep := ⟨![0,11,6,17],462⟩
def representative_2897 : Rep := ⟨![0,11,6,18],462⟩
def representative_2898 : Rep := ⟨![0,11,6,19],462⟩
def representative_2899 : Rep := ⟨![0,11,6,20],462⟩
def representative_2900 : Rep := ⟨![0,11,6,24],462⟩
def representative_2901 : Rep := ⟨![0,11,6,25],462⟩
def representative_2902 : Rep := ⟨![0,11,6,26],462⟩
def representative_2903 : Rep := ⟨![0,11,6,27],462⟩
def representative_2904 : Rep := ⟨![0,11,6,28],462⟩
def representative_2905 : Rep := ⟨![0,11,6,29],462⟩
def representative_2906 : Rep := ⟨![0,11,6,31],462⟩
def representative_2907 : Rep := ⟨![0,11,6,32],462⟩
def representative_2908 : Rep := ⟨![0,11,6,33],462⟩
def representative_2909 : Rep := ⟨![0,11,6,34],462⟩
def representative_2910 : Rep := ⟨![0,11,6,35],462⟩
def representative_2911 : Rep := ⟨![0,11,6,36],462⟩
def representative_2912 : Rep := ⟨![0,11,6,37],462⟩
def representative_2913 : Rep := ⟨![0,11,6,39],462⟩
def representative_2914 : Rep := ⟨![0,11,6,40],462⟩
def representative_2915 : Rep := ⟨![0,11,6,41],462⟩
def representative_2916 : Rep := ⟨![0,11,6,42],462⟩
def representative_2917 : Rep := ⟨![0,11,6,43],462⟩
def representative_2918 : Rep := ⟨![0,11,6,44],462⟩
def representative_2919 : Rep := ⟨![0,11,6,45],462⟩
def representative_2920 : Rep := ⟨![0,11,6,47],462⟩
def representative_2921 : Rep := ⟨![0,11,6,48],462⟩
def representative_2922 : Rep := ⟨![0,11,6,49],462⟩
def representative_2923 : Rep := ⟨![0,11,6,50],462⟩
def representative_2924 : Rep := ⟨![0,11,6,51],462⟩
def representative_2925 : Rep := ⟨![0,11,6,52],462⟩
def representative_2926 : Rep := ⟨![0,11,6,58],462⟩
def representative_2927 : Rep := ⟨![0,11,6,59],462⟩
def representative_2928 : Rep := ⟨![0,11,7,12],462⟩
def representative_2929 : Rep := ⟨![0,11,7,17],462⟩
def representative_2930 : Rep := ⟨![0,11,7,18],462⟩
def representative_2931 : Rep := ⟨![0,11,7,19],462⟩
def representative_2932 : Rep := ⟨![0,11,7,20],462⟩
def representative_2933 : Rep := ⟨![0,11,7,21],462⟩
def representative_2934 : Rep := ⟨![0,11,7,25],462⟩
def representative_2935 : Rep := ⟨![0,11,7,26],462⟩
def representative_2936 : Rep := ⟨![0,11,7,27],462⟩
def representative_2937 : Rep := ⟨![0,11,7,28],462⟩
def representative_2938 : Rep := ⟨![0,11,7,29],462⟩
def representative_2939 : Rep := ⟨![0,11,7,30],462⟩
def representative_2940 : Rep := ⟨![0,11,7,32],462⟩
def representative_2941 : Rep := ⟨![0,11,7,33],462⟩
def representative_2942 : Rep := ⟨![0,11,7,34],462⟩
def representative_2943 : Rep := ⟨![0,11,7,35],462⟩
theorem coefficient_2880 : validRep representative_2880 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2880)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2881 : validRep representative_2881 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2881)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2882 : validRep representative_2882 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2882)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2883 : validRep representative_2883 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2883)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2884 : validRep representative_2884 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2884)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2885 : validRep representative_2885 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2885)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2886 : validRep representative_2886 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2886)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2887 : validRep representative_2887 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2887)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2888 : validRep representative_2888 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2888)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2889 : validRep representative_2889 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2889)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2890 : validRep representative_2890 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2890)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2891 : validRep representative_2891 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2891)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2892 : validRep representative_2892 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2892)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2893 : validRep representative_2893 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2893)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2894 : validRep representative_2894 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2894)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2895 : validRep representative_2895 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2895)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2896 : validRep representative_2896 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2896)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2897 : validRep representative_2897 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2897)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2898 : validRep representative_2898 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2898)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2899 : validRep representative_2899 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2899)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2900 : validRep representative_2900 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2900)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2901 : validRep representative_2901 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2901)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2902 : validRep representative_2902 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2902)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2903 : validRep representative_2903 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2903)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2904 : validRep representative_2904 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2904)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2905 : validRep representative_2905 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2905)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2906 : validRep representative_2906 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2906)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2907 : validRep representative_2907 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2907)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2908 : validRep representative_2908 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2908)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2909 : validRep representative_2909 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2909)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2910 : validRep representative_2910 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2910)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2911 : validRep representative_2911 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2911)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2912 : validRep representative_2912 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2912)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2913 : validRep representative_2913 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2913)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2914 : validRep representative_2914 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2914)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2915 : validRep representative_2915 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2915)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2916 : validRep representative_2916 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2916)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2917 : validRep representative_2917 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2917)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2918 : validRep representative_2918 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2918)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2919 : validRep representative_2919 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2919)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2920 : validRep representative_2920 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2920)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2921 : validRep representative_2921 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2921)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2922 : validRep representative_2922 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2922)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2923 : validRep representative_2923 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2923)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2924 : validRep representative_2924 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2924)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2925 : validRep representative_2925 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2925)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2926 : validRep representative_2926 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2926)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2927 : validRep representative_2927 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2927)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2928 : validRep representative_2928 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2928)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2929 : validRep representative_2929 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2929)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2930 : validRep representative_2930 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2930)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2931 : validRep representative_2931 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2931)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2932 : validRep representative_2932 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2932)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2933 : validRep representative_2933 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2933)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2934 : validRep representative_2934 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2934)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2935 : validRep representative_2935 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2935)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2936 : validRep representative_2936 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2936)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2937 : validRep representative_2937 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2937)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2938 : validRep representative_2938 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2938)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2939 : validRep representative_2939 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2939)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2940 : validRep representative_2940 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2940)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2941 : validRep representative_2941 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2941)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2942 : validRep representative_2942 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2942)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2943 : validRep representative_2943 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2943)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_045 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2912 (QuarticIntegerRepresentativeTree.Tree.branch 2896 (QuarticIntegerRepresentativeTree.Tree.branch 2888 (QuarticIntegerRepresentativeTree.Tree.branch 2884 (QuarticIntegerRepresentativeTree.Tree.branch 2882 (QuarticIntegerRepresentativeTree.Tree.branch 2881 (QuarticIntegerRepresentativeTree.Tree.leaf 2880 representative_2880) (QuarticIntegerRepresentativeTree.Tree.leaf 2881 representative_2881)) (QuarticIntegerRepresentativeTree.Tree.branch 2883 (QuarticIntegerRepresentativeTree.Tree.leaf 2882 representative_2882) (QuarticIntegerRepresentativeTree.Tree.leaf 2883 representative_2883))) (QuarticIntegerRepresentativeTree.Tree.branch 2886 (QuarticIntegerRepresentativeTree.Tree.branch 2885 (QuarticIntegerRepresentativeTree.Tree.leaf 2884 representative_2884) (QuarticIntegerRepresentativeTree.Tree.leaf 2885 representative_2885)) (QuarticIntegerRepresentativeTree.Tree.branch 2887 (QuarticIntegerRepresentativeTree.Tree.leaf 2886 representative_2886) (QuarticIntegerRepresentativeTree.Tree.leaf 2887 representative_2887)))) (QuarticIntegerRepresentativeTree.Tree.branch 2892 (QuarticIntegerRepresentativeTree.Tree.branch 2890 (QuarticIntegerRepresentativeTree.Tree.branch 2889 (QuarticIntegerRepresentativeTree.Tree.leaf 2888 representative_2888) (QuarticIntegerRepresentativeTree.Tree.leaf 2889 representative_2889)) (QuarticIntegerRepresentativeTree.Tree.branch 2891 (QuarticIntegerRepresentativeTree.Tree.leaf 2890 representative_2890) (QuarticIntegerRepresentativeTree.Tree.leaf 2891 representative_2891))) (QuarticIntegerRepresentativeTree.Tree.branch 2894 (QuarticIntegerRepresentativeTree.Tree.branch 2893 (QuarticIntegerRepresentativeTree.Tree.leaf 2892 representative_2892) (QuarticIntegerRepresentativeTree.Tree.leaf 2893 representative_2893)) (QuarticIntegerRepresentativeTree.Tree.branch 2895 (QuarticIntegerRepresentativeTree.Tree.leaf 2894 representative_2894) (QuarticIntegerRepresentativeTree.Tree.leaf 2895 representative_2895))))) (QuarticIntegerRepresentativeTree.Tree.branch 2904 (QuarticIntegerRepresentativeTree.Tree.branch 2900 (QuarticIntegerRepresentativeTree.Tree.branch 2898 (QuarticIntegerRepresentativeTree.Tree.branch 2897 (QuarticIntegerRepresentativeTree.Tree.leaf 2896 representative_2896) (QuarticIntegerRepresentativeTree.Tree.leaf 2897 representative_2897)) (QuarticIntegerRepresentativeTree.Tree.branch 2899 (QuarticIntegerRepresentativeTree.Tree.leaf 2898 representative_2898) (QuarticIntegerRepresentativeTree.Tree.leaf 2899 representative_2899))) (QuarticIntegerRepresentativeTree.Tree.branch 2902 (QuarticIntegerRepresentativeTree.Tree.branch 2901 (QuarticIntegerRepresentativeTree.Tree.leaf 2900 representative_2900) (QuarticIntegerRepresentativeTree.Tree.leaf 2901 representative_2901)) (QuarticIntegerRepresentativeTree.Tree.branch 2903 (QuarticIntegerRepresentativeTree.Tree.leaf 2902 representative_2902) (QuarticIntegerRepresentativeTree.Tree.leaf 2903 representative_2903)))) (QuarticIntegerRepresentativeTree.Tree.branch 2908 (QuarticIntegerRepresentativeTree.Tree.branch 2906 (QuarticIntegerRepresentativeTree.Tree.branch 2905 (QuarticIntegerRepresentativeTree.Tree.leaf 2904 representative_2904) (QuarticIntegerRepresentativeTree.Tree.leaf 2905 representative_2905)) (QuarticIntegerRepresentativeTree.Tree.branch 2907 (QuarticIntegerRepresentativeTree.Tree.leaf 2906 representative_2906) (QuarticIntegerRepresentativeTree.Tree.leaf 2907 representative_2907))) (QuarticIntegerRepresentativeTree.Tree.branch 2910 (QuarticIntegerRepresentativeTree.Tree.branch 2909 (QuarticIntegerRepresentativeTree.Tree.leaf 2908 representative_2908) (QuarticIntegerRepresentativeTree.Tree.leaf 2909 representative_2909)) (QuarticIntegerRepresentativeTree.Tree.branch 2911 (QuarticIntegerRepresentativeTree.Tree.leaf 2910 representative_2910) (QuarticIntegerRepresentativeTree.Tree.leaf 2911 representative_2911)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2928 (QuarticIntegerRepresentativeTree.Tree.branch 2920 (QuarticIntegerRepresentativeTree.Tree.branch 2916 (QuarticIntegerRepresentativeTree.Tree.branch 2914 (QuarticIntegerRepresentativeTree.Tree.branch 2913 (QuarticIntegerRepresentativeTree.Tree.leaf 2912 representative_2912) (QuarticIntegerRepresentativeTree.Tree.leaf 2913 representative_2913)) (QuarticIntegerRepresentativeTree.Tree.branch 2915 (QuarticIntegerRepresentativeTree.Tree.leaf 2914 representative_2914) (QuarticIntegerRepresentativeTree.Tree.leaf 2915 representative_2915))) (QuarticIntegerRepresentativeTree.Tree.branch 2918 (QuarticIntegerRepresentativeTree.Tree.branch 2917 (QuarticIntegerRepresentativeTree.Tree.leaf 2916 representative_2916) (QuarticIntegerRepresentativeTree.Tree.leaf 2917 representative_2917)) (QuarticIntegerRepresentativeTree.Tree.branch 2919 (QuarticIntegerRepresentativeTree.Tree.leaf 2918 representative_2918) (QuarticIntegerRepresentativeTree.Tree.leaf 2919 representative_2919)))) (QuarticIntegerRepresentativeTree.Tree.branch 2924 (QuarticIntegerRepresentativeTree.Tree.branch 2922 (QuarticIntegerRepresentativeTree.Tree.branch 2921 (QuarticIntegerRepresentativeTree.Tree.leaf 2920 representative_2920) (QuarticIntegerRepresentativeTree.Tree.leaf 2921 representative_2921)) (QuarticIntegerRepresentativeTree.Tree.branch 2923 (QuarticIntegerRepresentativeTree.Tree.leaf 2922 representative_2922) (QuarticIntegerRepresentativeTree.Tree.leaf 2923 representative_2923))) (QuarticIntegerRepresentativeTree.Tree.branch 2926 (QuarticIntegerRepresentativeTree.Tree.branch 2925 (QuarticIntegerRepresentativeTree.Tree.leaf 2924 representative_2924) (QuarticIntegerRepresentativeTree.Tree.leaf 2925 representative_2925)) (QuarticIntegerRepresentativeTree.Tree.branch 2927 (QuarticIntegerRepresentativeTree.Tree.leaf 2926 representative_2926) (QuarticIntegerRepresentativeTree.Tree.leaf 2927 representative_2927))))) (QuarticIntegerRepresentativeTree.Tree.branch 2936 (QuarticIntegerRepresentativeTree.Tree.branch 2932 (QuarticIntegerRepresentativeTree.Tree.branch 2930 (QuarticIntegerRepresentativeTree.Tree.branch 2929 (QuarticIntegerRepresentativeTree.Tree.leaf 2928 representative_2928) (QuarticIntegerRepresentativeTree.Tree.leaf 2929 representative_2929)) (QuarticIntegerRepresentativeTree.Tree.branch 2931 (QuarticIntegerRepresentativeTree.Tree.leaf 2930 representative_2930) (QuarticIntegerRepresentativeTree.Tree.leaf 2931 representative_2931))) (QuarticIntegerRepresentativeTree.Tree.branch 2934 (QuarticIntegerRepresentativeTree.Tree.branch 2933 (QuarticIntegerRepresentativeTree.Tree.leaf 2932 representative_2932) (QuarticIntegerRepresentativeTree.Tree.leaf 2933 representative_2933)) (QuarticIntegerRepresentativeTree.Tree.branch 2935 (QuarticIntegerRepresentativeTree.Tree.leaf 2934 representative_2934) (QuarticIntegerRepresentativeTree.Tree.leaf 2935 representative_2935)))) (QuarticIntegerRepresentativeTree.Tree.branch 2940 (QuarticIntegerRepresentativeTree.Tree.branch 2938 (QuarticIntegerRepresentativeTree.Tree.branch 2937 (QuarticIntegerRepresentativeTree.Tree.leaf 2936 representative_2936) (QuarticIntegerRepresentativeTree.Tree.leaf 2937 representative_2937)) (QuarticIntegerRepresentativeTree.Tree.branch 2939 (QuarticIntegerRepresentativeTree.Tree.leaf 2938 representative_2938) (QuarticIntegerRepresentativeTree.Tree.leaf 2939 representative_2939))) (QuarticIntegerRepresentativeTree.Tree.branch 2942 (QuarticIntegerRepresentativeTree.Tree.branch 2941 (QuarticIntegerRepresentativeTree.Tree.leaf 2940 representative_2940) (QuarticIntegerRepresentativeTree.Tree.leaf 2941 representative_2941)) (QuarticIntegerRepresentativeTree.Tree.branch 2943 (QuarticIntegerRepresentativeTree.Tree.leaf 2942 representative_2942) (QuarticIntegerRepresentativeTree.Tree.leaf 2943 representative_2943)))))))
theorem accepted_045 : All validRep tree_045 := ⟨⟨⟨⟨⟨⟨coefficient_2880,coefficient_2881⟩,⟨coefficient_2882,coefficient_2883⟩⟩,⟨⟨coefficient_2884,coefficient_2885⟩,⟨coefficient_2886,coefficient_2887⟩⟩⟩,⟨⟨⟨coefficient_2888,coefficient_2889⟩,⟨coefficient_2890,coefficient_2891⟩⟩,⟨⟨coefficient_2892,coefficient_2893⟩,⟨coefficient_2894,coefficient_2895⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2896,coefficient_2897⟩,⟨coefficient_2898,coefficient_2899⟩⟩,⟨⟨coefficient_2900,coefficient_2901⟩,⟨coefficient_2902,coefficient_2903⟩⟩⟩,⟨⟨⟨coefficient_2904,coefficient_2905⟩,⟨coefficient_2906,coefficient_2907⟩⟩,⟨⟨coefficient_2908,coefficient_2909⟩,⟨coefficient_2910,coefficient_2911⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2912,coefficient_2913⟩,⟨coefficient_2914,coefficient_2915⟩⟩,⟨⟨coefficient_2916,coefficient_2917⟩,⟨coefficient_2918,coefficient_2919⟩⟩⟩,⟨⟨⟨coefficient_2920,coefficient_2921⟩,⟨coefficient_2922,coefficient_2923⟩⟩,⟨⟨coefficient_2924,coefficient_2925⟩,⟨coefficient_2926,coefficient_2927⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2928,coefficient_2929⟩,⟨coefficient_2930,coefficient_2931⟩⟩,⟨⟨coefficient_2932,coefficient_2933⟩,⟨coefficient_2934,coefficient_2935⟩⟩⟩,⟨⟨⟨coefficient_2936,coefficient_2937⟩,⟨coefficient_2938,coefficient_2939⟩⟩,⟨⟨coefficient_2940,coefficient_2941⟩,⟨coefficient_2942,coefficient_2943⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

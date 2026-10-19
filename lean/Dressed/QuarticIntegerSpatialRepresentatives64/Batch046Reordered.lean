import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_2944 : Rep := ⟨![0,11,7,36],462⟩
def representative_2945 : Rep := ⟨![0,11,7,37],462⟩
def representative_2946 : Rep := ⟨![0,11,7,38],462⟩
def representative_2947 : Rep := ⟨![0,11,7,41],462⟩
def representative_2948 : Rep := ⟨![0,11,7,42],462⟩
def representative_2949 : Rep := ⟨![0,11,7,43],462⟩
def representative_2950 : Rep := ⟨![0,11,7,44],462⟩
def representative_2951 : Rep := ⟨![0,11,7,45],462⟩
def representative_2952 : Rep := ⟨![0,11,7,46],462⟩
def representative_2953 : Rep := ⟨![0,11,7,49],462⟩
def representative_2954 : Rep := ⟨![0,11,7,50],462⟩
def representative_2955 : Rep := ⟨![0,11,7,51],462⟩
def representative_2956 : Rep := ⟨![0,11,7,52],462⟩
def representative_2957 : Rep := ⟨![0,11,7,53],462⟩
def representative_2958 : Rep := ⟨![0,11,7,59],462⟩
def representative_2959 : Rep := ⟨![0,11,7,60],462⟩
def representative_2960 : Rep := ⟨![0,11,16,27],462⟩
def representative_2961 : Rep := ⟨![0,11,16,28],462⟩
def representative_2962 : Rep := ⟨![0,11,16,29],462⟩
def representative_2963 : Rep := ⟨![0,11,16,34],462⟩
def representative_2964 : Rep := ⟨![0,11,16,35],462⟩
def representative_2965 : Rep := ⟨![0,11,16,36],462⟩
def representative_2966 : Rep := ⟨![0,11,16,37],462⟩
def representative_2967 : Rep := ⟨![0,11,16,38],462⟩
def representative_2968 : Rep := ⟨![0,11,16,42],462⟩
def representative_2969 : Rep := ⟨![0,11,16,43],462⟩
def representative_2970 : Rep := ⟨![0,11,16,44],462⟩
def representative_2971 : Rep := ⟨![0,11,16,45],462⟩
def representative_2972 : Rep := ⟨![0,11,16,46],462⟩
def representative_2973 : Rep := ⟨![0,11,16,49],462⟩
def representative_2974 : Rep := ⟨![0,11,16,50],462⟩
def representative_2975 : Rep := ⟨![0,11,16,51],462⟩
def representative_2976 : Rep := ⟨![0,11,16,52],462⟩
def representative_2977 : Rep := ⟨![0,11,16,53],462⟩
def representative_2978 : Rep := ⟨![0,11,16,54],462⟩
def representative_2979 : Rep := ⟨![0,11,16,55],462⟩
def representative_2980 : Rep := ⟨![0,11,16,58],462⟩
def representative_2981 : Rep := ⟨![0,11,16,59],462⟩
def representative_2982 : Rep := ⟨![0,11,16,60],462⟩
def representative_2983 : Rep := ⟨![0,11,16,61],462⟩
def representative_2984 : Rep := ⟨![0,11,16,62],462⟩
def representative_2985 : Rep := ⟨![0,11,17,28],462⟩
def representative_2986 : Rep := ⟨![0,11,17,29],462⟩
def representative_2987 : Rep := ⟨![0,11,17,30],462⟩
def representative_2988 : Rep := ⟨![0,11,17,35],462⟩
def representative_2989 : Rep := ⟨![0,11,17,36],462⟩
def representative_2990 : Rep := ⟨![0,11,17,37],462⟩
def representative_2991 : Rep := ⟨![0,11,17,38],462⟩
def representative_2992 : Rep := ⟨![0,11,17,39],462⟩
def representative_2993 : Rep := ⟨![0,11,17,42],462⟩
def representative_2994 : Rep := ⟨![0,11,17,43],462⟩
def representative_2995 : Rep := ⟨![0,11,17,44],462⟩
def representative_2996 : Rep := ⟨![0,11,17,45],462⟩
def representative_2997 : Rep := ⟨![0,11,17,46],462⟩
def representative_2998 : Rep := ⟨![0,11,17,47],462⟩
def representative_2999 : Rep := ⟨![0,11,17,48],462⟩
def representative_3000 : Rep := ⟨![0,11,17,50],462⟩
def representative_3001 : Rep := ⟨![0,11,17,51],462⟩
def representative_3002 : Rep := ⟨![0,11,17,52],462⟩
def representative_3003 : Rep := ⟨![0,11,17,53],462⟩
def representative_3004 : Rep := ⟨![0,11,17,54],462⟩
def representative_3005 : Rep := ⟨![0,11,17,55],462⟩
def representative_3006 : Rep := ⟨![0,11,17,58],462⟩
def representative_3007 : Rep := ⟨![0,11,17,60],462⟩
theorem coefficient_2944 : validRep representative_2944 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2944)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2945 : validRep representative_2945 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2945)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2946 : validRep representative_2946 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2946)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2947 : validRep representative_2947 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2947)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2948 : validRep representative_2948 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2948)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2949 : validRep representative_2949 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2949)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2950 : validRep representative_2950 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2950)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2951 : validRep representative_2951 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2951)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2952 : validRep representative_2952 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2952)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2953 : validRep representative_2953 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2953)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2954 : validRep representative_2954 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2954)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2955 : validRep representative_2955 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2955)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2956 : validRep representative_2956 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2956)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2957 : validRep representative_2957 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2957)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2958 : validRep representative_2958 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2958)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2959 : validRep representative_2959 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2959)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2960 : validRep representative_2960 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2960)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2961 : validRep representative_2961 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2961)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2962 : validRep representative_2962 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2962)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2963 : validRep representative_2963 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2963)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2964 : validRep representative_2964 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2964)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2965 : validRep representative_2965 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2965)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2966 : validRep representative_2966 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2966)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2967 : validRep representative_2967 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2967)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2968 : validRep representative_2968 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2968)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2969 : validRep representative_2969 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2969)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2970 : validRep representative_2970 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2970)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2971 : validRep representative_2971 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2971)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2972 : validRep representative_2972 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2972)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2973 : validRep representative_2973 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2973)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2974 : validRep representative_2974 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2974)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2975 : validRep representative_2975 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2975)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2976 : validRep representative_2976 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2976)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2977 : validRep representative_2977 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2977)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2978 : validRep representative_2978 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2978)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2979 : validRep representative_2979 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2979)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2980 : validRep representative_2980 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2980)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2981 : validRep representative_2981 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2981)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2982 : validRep representative_2982 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2982)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2983 : validRep representative_2983 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2983)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2984 : validRep representative_2984 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2984)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2985 : validRep representative_2985 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2985)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2986 : validRep representative_2986 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2986)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2987 : validRep representative_2987 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2987)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2988 : validRep representative_2988 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2988)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2989 : validRep representative_2989 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2989)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2990 : validRep representative_2990 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2990)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2991 : validRep representative_2991 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2991)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2992 : validRep representative_2992 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2992)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2993 : validRep representative_2993 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2993)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2994 : validRep representative_2994 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2994)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2995 : validRep representative_2995 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2995)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2996 : validRep representative_2996 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2996)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2997 : validRep representative_2997 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2997)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2998 : validRep representative_2998 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2998)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2999 : validRep representative_2999 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2999)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3000 : validRep representative_3000 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3000)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3001 : validRep representative_3001 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3001)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3002 : validRep representative_3002 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3002)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3003 : validRep representative_3003 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3003)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3004 : validRep representative_3004 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3004)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3005 : validRep representative_3005 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3005)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3006 : validRep representative_3006 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3006)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_3007 : validRep representative_3007 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_3007)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_046 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2976 (QuarticIntegerRepresentativeTree.Tree.branch 2960 (QuarticIntegerRepresentativeTree.Tree.branch 2952 (QuarticIntegerRepresentativeTree.Tree.branch 2948 (QuarticIntegerRepresentativeTree.Tree.branch 2946 (QuarticIntegerRepresentativeTree.Tree.branch 2945 (QuarticIntegerRepresentativeTree.Tree.leaf 2944 representative_2944) (QuarticIntegerRepresentativeTree.Tree.leaf 2945 representative_2945)) (QuarticIntegerRepresentativeTree.Tree.branch 2947 (QuarticIntegerRepresentativeTree.Tree.leaf 2946 representative_2946) (QuarticIntegerRepresentativeTree.Tree.leaf 2947 representative_2947))) (QuarticIntegerRepresentativeTree.Tree.branch 2950 (QuarticIntegerRepresentativeTree.Tree.branch 2949 (QuarticIntegerRepresentativeTree.Tree.leaf 2948 representative_2948) (QuarticIntegerRepresentativeTree.Tree.leaf 2949 representative_2949)) (QuarticIntegerRepresentativeTree.Tree.branch 2951 (QuarticIntegerRepresentativeTree.Tree.leaf 2950 representative_2950) (QuarticIntegerRepresentativeTree.Tree.leaf 2951 representative_2951)))) (QuarticIntegerRepresentativeTree.Tree.branch 2956 (QuarticIntegerRepresentativeTree.Tree.branch 2954 (QuarticIntegerRepresentativeTree.Tree.branch 2953 (QuarticIntegerRepresentativeTree.Tree.leaf 2952 representative_2952) (QuarticIntegerRepresentativeTree.Tree.leaf 2953 representative_2953)) (QuarticIntegerRepresentativeTree.Tree.branch 2955 (QuarticIntegerRepresentativeTree.Tree.leaf 2954 representative_2954) (QuarticIntegerRepresentativeTree.Tree.leaf 2955 representative_2955))) (QuarticIntegerRepresentativeTree.Tree.branch 2958 (QuarticIntegerRepresentativeTree.Tree.branch 2957 (QuarticIntegerRepresentativeTree.Tree.leaf 2956 representative_2956) (QuarticIntegerRepresentativeTree.Tree.leaf 2957 representative_2957)) (QuarticIntegerRepresentativeTree.Tree.branch 2959 (QuarticIntegerRepresentativeTree.Tree.leaf 2958 representative_2958) (QuarticIntegerRepresentativeTree.Tree.leaf 2959 representative_2959))))) (QuarticIntegerRepresentativeTree.Tree.branch 2968 (QuarticIntegerRepresentativeTree.Tree.branch 2964 (QuarticIntegerRepresentativeTree.Tree.branch 2962 (QuarticIntegerRepresentativeTree.Tree.branch 2961 (QuarticIntegerRepresentativeTree.Tree.leaf 2960 representative_2960) (QuarticIntegerRepresentativeTree.Tree.leaf 2961 representative_2961)) (QuarticIntegerRepresentativeTree.Tree.branch 2963 (QuarticIntegerRepresentativeTree.Tree.leaf 2962 representative_2962) (QuarticIntegerRepresentativeTree.Tree.leaf 2963 representative_2963))) (QuarticIntegerRepresentativeTree.Tree.branch 2966 (QuarticIntegerRepresentativeTree.Tree.branch 2965 (QuarticIntegerRepresentativeTree.Tree.leaf 2964 representative_2964) (QuarticIntegerRepresentativeTree.Tree.leaf 2965 representative_2965)) (QuarticIntegerRepresentativeTree.Tree.branch 2967 (QuarticIntegerRepresentativeTree.Tree.leaf 2966 representative_2966) (QuarticIntegerRepresentativeTree.Tree.leaf 2967 representative_2967)))) (QuarticIntegerRepresentativeTree.Tree.branch 2972 (QuarticIntegerRepresentativeTree.Tree.branch 2970 (QuarticIntegerRepresentativeTree.Tree.branch 2969 (QuarticIntegerRepresentativeTree.Tree.leaf 2968 representative_2968) (QuarticIntegerRepresentativeTree.Tree.leaf 2969 representative_2969)) (QuarticIntegerRepresentativeTree.Tree.branch 2971 (QuarticIntegerRepresentativeTree.Tree.leaf 2970 representative_2970) (QuarticIntegerRepresentativeTree.Tree.leaf 2971 representative_2971))) (QuarticIntegerRepresentativeTree.Tree.branch 2974 (QuarticIntegerRepresentativeTree.Tree.branch 2973 (QuarticIntegerRepresentativeTree.Tree.leaf 2972 representative_2972) (QuarticIntegerRepresentativeTree.Tree.leaf 2973 representative_2973)) (QuarticIntegerRepresentativeTree.Tree.branch 2975 (QuarticIntegerRepresentativeTree.Tree.leaf 2974 representative_2974) (QuarticIntegerRepresentativeTree.Tree.leaf 2975 representative_2975)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2992 (QuarticIntegerRepresentativeTree.Tree.branch 2984 (QuarticIntegerRepresentativeTree.Tree.branch 2980 (QuarticIntegerRepresentativeTree.Tree.branch 2978 (QuarticIntegerRepresentativeTree.Tree.branch 2977 (QuarticIntegerRepresentativeTree.Tree.leaf 2976 representative_2976) (QuarticIntegerRepresentativeTree.Tree.leaf 2977 representative_2977)) (QuarticIntegerRepresentativeTree.Tree.branch 2979 (QuarticIntegerRepresentativeTree.Tree.leaf 2978 representative_2978) (QuarticIntegerRepresentativeTree.Tree.leaf 2979 representative_2979))) (QuarticIntegerRepresentativeTree.Tree.branch 2982 (QuarticIntegerRepresentativeTree.Tree.branch 2981 (QuarticIntegerRepresentativeTree.Tree.leaf 2980 representative_2980) (QuarticIntegerRepresentativeTree.Tree.leaf 2981 representative_2981)) (QuarticIntegerRepresentativeTree.Tree.branch 2983 (QuarticIntegerRepresentativeTree.Tree.leaf 2982 representative_2982) (QuarticIntegerRepresentativeTree.Tree.leaf 2983 representative_2983)))) (QuarticIntegerRepresentativeTree.Tree.branch 2988 (QuarticIntegerRepresentativeTree.Tree.branch 2986 (QuarticIntegerRepresentativeTree.Tree.branch 2985 (QuarticIntegerRepresentativeTree.Tree.leaf 2984 representative_2984) (QuarticIntegerRepresentativeTree.Tree.leaf 2985 representative_2985)) (QuarticIntegerRepresentativeTree.Tree.branch 2987 (QuarticIntegerRepresentativeTree.Tree.leaf 2986 representative_2986) (QuarticIntegerRepresentativeTree.Tree.leaf 2987 representative_2987))) (QuarticIntegerRepresentativeTree.Tree.branch 2990 (QuarticIntegerRepresentativeTree.Tree.branch 2989 (QuarticIntegerRepresentativeTree.Tree.leaf 2988 representative_2988) (QuarticIntegerRepresentativeTree.Tree.leaf 2989 representative_2989)) (QuarticIntegerRepresentativeTree.Tree.branch 2991 (QuarticIntegerRepresentativeTree.Tree.leaf 2990 representative_2990) (QuarticIntegerRepresentativeTree.Tree.leaf 2991 representative_2991))))) (QuarticIntegerRepresentativeTree.Tree.branch 3000 (QuarticIntegerRepresentativeTree.Tree.branch 2996 (QuarticIntegerRepresentativeTree.Tree.branch 2994 (QuarticIntegerRepresentativeTree.Tree.branch 2993 (QuarticIntegerRepresentativeTree.Tree.leaf 2992 representative_2992) (QuarticIntegerRepresentativeTree.Tree.leaf 2993 representative_2993)) (QuarticIntegerRepresentativeTree.Tree.branch 2995 (QuarticIntegerRepresentativeTree.Tree.leaf 2994 representative_2994) (QuarticIntegerRepresentativeTree.Tree.leaf 2995 representative_2995))) (QuarticIntegerRepresentativeTree.Tree.branch 2998 (QuarticIntegerRepresentativeTree.Tree.branch 2997 (QuarticIntegerRepresentativeTree.Tree.leaf 2996 representative_2996) (QuarticIntegerRepresentativeTree.Tree.leaf 2997 representative_2997)) (QuarticIntegerRepresentativeTree.Tree.branch 2999 (QuarticIntegerRepresentativeTree.Tree.leaf 2998 representative_2998) (QuarticIntegerRepresentativeTree.Tree.leaf 2999 representative_2999)))) (QuarticIntegerRepresentativeTree.Tree.branch 3004 (QuarticIntegerRepresentativeTree.Tree.branch 3002 (QuarticIntegerRepresentativeTree.Tree.branch 3001 (QuarticIntegerRepresentativeTree.Tree.leaf 3000 representative_3000) (QuarticIntegerRepresentativeTree.Tree.leaf 3001 representative_3001)) (QuarticIntegerRepresentativeTree.Tree.branch 3003 (QuarticIntegerRepresentativeTree.Tree.leaf 3002 representative_3002) (QuarticIntegerRepresentativeTree.Tree.leaf 3003 representative_3003))) (QuarticIntegerRepresentativeTree.Tree.branch 3006 (QuarticIntegerRepresentativeTree.Tree.branch 3005 (QuarticIntegerRepresentativeTree.Tree.leaf 3004 representative_3004) (QuarticIntegerRepresentativeTree.Tree.leaf 3005 representative_3005)) (QuarticIntegerRepresentativeTree.Tree.branch 3007 (QuarticIntegerRepresentativeTree.Tree.leaf 3006 representative_3006) (QuarticIntegerRepresentativeTree.Tree.leaf 3007 representative_3007)))))))
theorem accepted_046 : All validRep tree_046 := ⟨⟨⟨⟨⟨⟨coefficient_2944,coefficient_2945⟩,⟨coefficient_2946,coefficient_2947⟩⟩,⟨⟨coefficient_2948,coefficient_2949⟩,⟨coefficient_2950,coefficient_2951⟩⟩⟩,⟨⟨⟨coefficient_2952,coefficient_2953⟩,⟨coefficient_2954,coefficient_2955⟩⟩,⟨⟨coefficient_2956,coefficient_2957⟩,⟨coefficient_2958,coefficient_2959⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2960,coefficient_2961⟩,⟨coefficient_2962,coefficient_2963⟩⟩,⟨⟨coefficient_2964,coefficient_2965⟩,⟨coefficient_2966,coefficient_2967⟩⟩⟩,⟨⟨⟨coefficient_2968,coefficient_2969⟩,⟨coefficient_2970,coefficient_2971⟩⟩,⟨⟨coefficient_2972,coefficient_2973⟩,⟨coefficient_2974,coefficient_2975⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2976,coefficient_2977⟩,⟨coefficient_2978,coefficient_2979⟩⟩,⟨⟨coefficient_2980,coefficient_2981⟩,⟨coefficient_2982,coefficient_2983⟩⟩⟩,⟨⟨⟨coefficient_2984,coefficient_2985⟩,⟨coefficient_2986,coefficient_2987⟩⟩,⟨⟨coefficient_2988,coefficient_2989⟩,⟨coefficient_2990,coefficient_2991⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2992,coefficient_2993⟩,⟨coefficient_2994,coefficient_2995⟩⟩,⟨⟨coefficient_2996,coefficient_2997⟩,⟨coefficient_2998,coefficient_2999⟩⟩⟩,⟨⟨⟨coefficient_3000,coefficient_3001⟩,⟨coefficient_3002,coefficient_3003⟩⟩,⟨⟨coefficient_3004,coefficient_3005⟩,⟨coefficient_3006,coefficient_3007⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

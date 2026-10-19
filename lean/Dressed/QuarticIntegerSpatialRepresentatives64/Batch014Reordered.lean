import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_896 : Rep := ⟨![0,2,19,54],462⟩
def representative_897 : Rep := ⟨![0,2,19,55],462⟩
def representative_898 : Rep := ⟨![0,2,20,22],462⟩
def representative_899 : Rep := ⟨![0,2,20,24],462⟩
def representative_900 : Rep := ⟨![0,2,20,25],462⟩
def representative_901 : Rep := ⟨![0,2,20,26],237⟩
def representative_902 : Rep := ⟨![0,2,20,27],462⟩
def representative_903 : Rep := ⟨![0,2,20,29],462⟩
def representative_904 : Rep := ⟨![0,2,20,30],462⟩
def representative_905 : Rep := ⟨![0,2,20,31],462⟩
def representative_906 : Rep := ⟨![0,2,20,32],462⟩
def representative_907 : Rep := ⟨![0,2,20,33],462⟩
def representative_908 : Rep := ⟨![0,2,20,34],462⟩
def representative_909 : Rep := ⟨![0,2,20,35],462⟩
def representative_910 : Rep := ⟨![0,2,20,36],462⟩
def representative_911 : Rep := ⟨![0,2,20,37],462⟩
def representative_912 : Rep := ⟨![0,2,20,38],462⟩
def representative_913 : Rep := ⟨![0,2,20,39],462⟩
def representative_914 : Rep := ⟨![0,2,20,40],462⟩
def representative_915 : Rep := ⟨![0,2,20,41],462⟩
def representative_916 : Rep := ⟨![0,2,20,42],237⟩
def representative_917 : Rep := ⟨![0,2,20,43],462⟩
def representative_918 : Rep := ⟨![0,2,20,44],462⟩
def representative_919 : Rep := ⟨![0,2,20,45],462⟩
def representative_920 : Rep := ⟨![0,2,20,46],462⟩
def representative_921 : Rep := ⟨![0,2,20,47],462⟩
def representative_922 : Rep := ⟨![0,2,20,52],462⟩
def representative_923 : Rep := ⟨![0,2,20,53],462⟩
def representative_924 : Rep := ⟨![0,2,20,54],462⟩
def representative_925 : Rep := ⟨![0,2,21,24],462⟩
def representative_926 : Rep := ⟨![0,2,21,25],462⟩
def representative_927 : Rep := ⟨![0,2,21,27],462⟩
def representative_928 : Rep := ⟨![0,2,21,28],462⟩
def representative_929 : Rep := ⟨![0,2,21,32],462⟩
def representative_930 : Rep := ⟨![0,2,21,33],462⟩
def representative_931 : Rep := ⟨![0,2,21,35],462⟩
def representative_932 : Rep := ⟨![0,2,21,36],462⟩
def representative_933 : Rep := ⟨![0,2,21,37],462⟩
def representative_934 : Rep := ⟨![0,2,21,40],462⟩
def representative_935 : Rep := ⟨![0,2,21,41],462⟩
def representative_936 : Rep := ⟨![0,2,21,43],462⟩
def representative_937 : Rep := ⟨![0,2,21,44],462⟩
def representative_938 : Rep := ⟨![0,2,21,45],462⟩
def representative_939 : Rep := ⟨![0,2,21,53],462⟩
def representative_940 : Rep := ⟨![0,2,24,26],462⟩
def representative_941 : Rep := ⟨![0,2,24,27],462⟩
def representative_942 : Rep := ⟨![0,2,24,28],462⟩
def representative_943 : Rep := ⟨![0,2,24,29],462⟩
def representative_944 : Rep := ⟨![0,2,24,30],462⟩
def representative_945 : Rep := ⟨![0,2,24,33],462⟩
def representative_946 : Rep := ⟨![0,2,24,34],462⟩
def representative_947 : Rep := ⟨![0,2,24,35],462⟩
def representative_948 : Rep := ⟨![0,2,24,36],462⟩
def representative_949 : Rep := ⟨![0,2,24,37],462⟩
def representative_950 : Rep := ⟨![0,2,24,38],462⟩
def representative_951 : Rep := ⟨![0,2,24,39],462⟩
def representative_952 : Rep := ⟨![0,2,24,41],238⟩
def representative_953 : Rep := ⟨![0,2,24,42],462⟩
def representative_954 : Rep := ⟨![0,2,24,43],462⟩
def representative_955 : Rep := ⟨![0,2,24,44],462⟩
def representative_956 : Rep := ⟨![0,2,24,45],462⟩
def representative_957 : Rep := ⟨![0,2,24,46],462⟩
def representative_958 : Rep := ⟨![0,2,24,47],238⟩
def representative_959 : Rep := ⟨![0,2,25,27],462⟩
theorem coefficient_896 : validRep representative_896 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_896)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_897 : validRep representative_897 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_897)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_898 : validRep representative_898 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_898)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_899 : validRep representative_899 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_899)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_900 : validRep representative_900 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_900)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_901 : validRep representative_901 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_901)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_902 : validRep representative_902 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_902)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_903 : validRep representative_903 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_903)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_904 : validRep representative_904 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_904)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_905 : validRep representative_905 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_905)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_906 : validRep representative_906 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_906)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_907 : validRep representative_907 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_907)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_908 : validRep representative_908 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_908)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_909 : validRep representative_909 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_909)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_910 : validRep representative_910 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_910)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_911 : validRep representative_911 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_911)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_912 : validRep representative_912 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_912)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_913 : validRep representative_913 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_913)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_914 : validRep representative_914 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_914)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_915 : validRep representative_915 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_915)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_916 : validRep representative_916 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_916)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_917 : validRep representative_917 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_917)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_918 : validRep representative_918 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_918)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_919 : validRep representative_919 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_919)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_920 : validRep representative_920 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_920)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_921 : validRep representative_921 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_921)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_922 : validRep representative_922 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_922)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_923 : validRep representative_923 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_923)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_924 : validRep representative_924 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_924)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_925 : validRep representative_925 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_925)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_926 : validRep representative_926 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_926)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_927 : validRep representative_927 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_927)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_928 : validRep representative_928 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_928)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_929 : validRep representative_929 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_929)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_930 : validRep representative_930 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_930)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_931 : validRep representative_931 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_931)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_932 : validRep representative_932 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_932)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_933 : validRep representative_933 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_933)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_934 : validRep representative_934 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_934)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_935 : validRep representative_935 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_935)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_936 : validRep representative_936 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_936)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_937 : validRep representative_937 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_937)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_938 : validRep representative_938 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_938)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_939 : validRep representative_939 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_939)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_940 : validRep representative_940 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_940)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_941 : validRep representative_941 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_941)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_942 : validRep representative_942 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_942)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_943 : validRep representative_943 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_943)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_944 : validRep representative_944 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_944)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_945 : validRep representative_945 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_945)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_946 : validRep representative_946 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_946)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_947 : validRep representative_947 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_947)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_948 : validRep representative_948 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_948)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_949 : validRep representative_949 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_949)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_950 : validRep representative_950 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_950)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_951 : validRep representative_951 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_951)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_952 : validRep representative_952 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_952)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_953 : validRep representative_953 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_953)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_954 : validRep representative_954 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_954)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_955 : validRep representative_955 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_955)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_956 : validRep representative_956 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_956)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_957 : validRep representative_957 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_957)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_958 : validRep representative_958 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_958)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_959 : validRep representative_959 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_959)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_014 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 928 (QuarticIntegerRepresentativeTree.Tree.branch 912 (QuarticIntegerRepresentativeTree.Tree.branch 904 (QuarticIntegerRepresentativeTree.Tree.branch 900 (QuarticIntegerRepresentativeTree.Tree.branch 898 (QuarticIntegerRepresentativeTree.Tree.branch 897 (QuarticIntegerRepresentativeTree.Tree.leaf 896 representative_896) (QuarticIntegerRepresentativeTree.Tree.leaf 897 representative_897)) (QuarticIntegerRepresentativeTree.Tree.branch 899 (QuarticIntegerRepresentativeTree.Tree.leaf 898 representative_898) (QuarticIntegerRepresentativeTree.Tree.leaf 899 representative_899))) (QuarticIntegerRepresentativeTree.Tree.branch 902 (QuarticIntegerRepresentativeTree.Tree.branch 901 (QuarticIntegerRepresentativeTree.Tree.leaf 900 representative_900) (QuarticIntegerRepresentativeTree.Tree.leaf 901 representative_901)) (QuarticIntegerRepresentativeTree.Tree.branch 903 (QuarticIntegerRepresentativeTree.Tree.leaf 902 representative_902) (QuarticIntegerRepresentativeTree.Tree.leaf 903 representative_903)))) (QuarticIntegerRepresentativeTree.Tree.branch 908 (QuarticIntegerRepresentativeTree.Tree.branch 906 (QuarticIntegerRepresentativeTree.Tree.branch 905 (QuarticIntegerRepresentativeTree.Tree.leaf 904 representative_904) (QuarticIntegerRepresentativeTree.Tree.leaf 905 representative_905)) (QuarticIntegerRepresentativeTree.Tree.branch 907 (QuarticIntegerRepresentativeTree.Tree.leaf 906 representative_906) (QuarticIntegerRepresentativeTree.Tree.leaf 907 representative_907))) (QuarticIntegerRepresentativeTree.Tree.branch 910 (QuarticIntegerRepresentativeTree.Tree.branch 909 (QuarticIntegerRepresentativeTree.Tree.leaf 908 representative_908) (QuarticIntegerRepresentativeTree.Tree.leaf 909 representative_909)) (QuarticIntegerRepresentativeTree.Tree.branch 911 (QuarticIntegerRepresentativeTree.Tree.leaf 910 representative_910) (QuarticIntegerRepresentativeTree.Tree.leaf 911 representative_911))))) (QuarticIntegerRepresentativeTree.Tree.branch 920 (QuarticIntegerRepresentativeTree.Tree.branch 916 (QuarticIntegerRepresentativeTree.Tree.branch 914 (QuarticIntegerRepresentativeTree.Tree.branch 913 (QuarticIntegerRepresentativeTree.Tree.leaf 912 representative_912) (QuarticIntegerRepresentativeTree.Tree.leaf 913 representative_913)) (QuarticIntegerRepresentativeTree.Tree.branch 915 (QuarticIntegerRepresentativeTree.Tree.leaf 914 representative_914) (QuarticIntegerRepresentativeTree.Tree.leaf 915 representative_915))) (QuarticIntegerRepresentativeTree.Tree.branch 918 (QuarticIntegerRepresentativeTree.Tree.branch 917 (QuarticIntegerRepresentativeTree.Tree.leaf 916 representative_916) (QuarticIntegerRepresentativeTree.Tree.leaf 917 representative_917)) (QuarticIntegerRepresentativeTree.Tree.branch 919 (QuarticIntegerRepresentativeTree.Tree.leaf 918 representative_918) (QuarticIntegerRepresentativeTree.Tree.leaf 919 representative_919)))) (QuarticIntegerRepresentativeTree.Tree.branch 924 (QuarticIntegerRepresentativeTree.Tree.branch 922 (QuarticIntegerRepresentativeTree.Tree.branch 921 (QuarticIntegerRepresentativeTree.Tree.leaf 920 representative_920) (QuarticIntegerRepresentativeTree.Tree.leaf 921 representative_921)) (QuarticIntegerRepresentativeTree.Tree.branch 923 (QuarticIntegerRepresentativeTree.Tree.leaf 922 representative_922) (QuarticIntegerRepresentativeTree.Tree.leaf 923 representative_923))) (QuarticIntegerRepresentativeTree.Tree.branch 926 (QuarticIntegerRepresentativeTree.Tree.branch 925 (QuarticIntegerRepresentativeTree.Tree.leaf 924 representative_924) (QuarticIntegerRepresentativeTree.Tree.leaf 925 representative_925)) (QuarticIntegerRepresentativeTree.Tree.branch 927 (QuarticIntegerRepresentativeTree.Tree.leaf 926 representative_926) (QuarticIntegerRepresentativeTree.Tree.leaf 927 representative_927)))))) (QuarticIntegerRepresentativeTree.Tree.branch 944 (QuarticIntegerRepresentativeTree.Tree.branch 936 (QuarticIntegerRepresentativeTree.Tree.branch 932 (QuarticIntegerRepresentativeTree.Tree.branch 930 (QuarticIntegerRepresentativeTree.Tree.branch 929 (QuarticIntegerRepresentativeTree.Tree.leaf 928 representative_928) (QuarticIntegerRepresentativeTree.Tree.leaf 929 representative_929)) (QuarticIntegerRepresentativeTree.Tree.branch 931 (QuarticIntegerRepresentativeTree.Tree.leaf 930 representative_930) (QuarticIntegerRepresentativeTree.Tree.leaf 931 representative_931))) (QuarticIntegerRepresentativeTree.Tree.branch 934 (QuarticIntegerRepresentativeTree.Tree.branch 933 (QuarticIntegerRepresentativeTree.Tree.leaf 932 representative_932) (QuarticIntegerRepresentativeTree.Tree.leaf 933 representative_933)) (QuarticIntegerRepresentativeTree.Tree.branch 935 (QuarticIntegerRepresentativeTree.Tree.leaf 934 representative_934) (QuarticIntegerRepresentativeTree.Tree.leaf 935 representative_935)))) (QuarticIntegerRepresentativeTree.Tree.branch 940 (QuarticIntegerRepresentativeTree.Tree.branch 938 (QuarticIntegerRepresentativeTree.Tree.branch 937 (QuarticIntegerRepresentativeTree.Tree.leaf 936 representative_936) (QuarticIntegerRepresentativeTree.Tree.leaf 937 representative_937)) (QuarticIntegerRepresentativeTree.Tree.branch 939 (QuarticIntegerRepresentativeTree.Tree.leaf 938 representative_938) (QuarticIntegerRepresentativeTree.Tree.leaf 939 representative_939))) (QuarticIntegerRepresentativeTree.Tree.branch 942 (QuarticIntegerRepresentativeTree.Tree.branch 941 (QuarticIntegerRepresentativeTree.Tree.leaf 940 representative_940) (QuarticIntegerRepresentativeTree.Tree.leaf 941 representative_941)) (QuarticIntegerRepresentativeTree.Tree.branch 943 (QuarticIntegerRepresentativeTree.Tree.leaf 942 representative_942) (QuarticIntegerRepresentativeTree.Tree.leaf 943 representative_943))))) (QuarticIntegerRepresentativeTree.Tree.branch 952 (QuarticIntegerRepresentativeTree.Tree.branch 948 (QuarticIntegerRepresentativeTree.Tree.branch 946 (QuarticIntegerRepresentativeTree.Tree.branch 945 (QuarticIntegerRepresentativeTree.Tree.leaf 944 representative_944) (QuarticIntegerRepresentativeTree.Tree.leaf 945 representative_945)) (QuarticIntegerRepresentativeTree.Tree.branch 947 (QuarticIntegerRepresentativeTree.Tree.leaf 946 representative_946) (QuarticIntegerRepresentativeTree.Tree.leaf 947 representative_947))) (QuarticIntegerRepresentativeTree.Tree.branch 950 (QuarticIntegerRepresentativeTree.Tree.branch 949 (QuarticIntegerRepresentativeTree.Tree.leaf 948 representative_948) (QuarticIntegerRepresentativeTree.Tree.leaf 949 representative_949)) (QuarticIntegerRepresentativeTree.Tree.branch 951 (QuarticIntegerRepresentativeTree.Tree.leaf 950 representative_950) (QuarticIntegerRepresentativeTree.Tree.leaf 951 representative_951)))) (QuarticIntegerRepresentativeTree.Tree.branch 956 (QuarticIntegerRepresentativeTree.Tree.branch 954 (QuarticIntegerRepresentativeTree.Tree.branch 953 (QuarticIntegerRepresentativeTree.Tree.leaf 952 representative_952) (QuarticIntegerRepresentativeTree.Tree.leaf 953 representative_953)) (QuarticIntegerRepresentativeTree.Tree.branch 955 (QuarticIntegerRepresentativeTree.Tree.leaf 954 representative_954) (QuarticIntegerRepresentativeTree.Tree.leaf 955 representative_955))) (QuarticIntegerRepresentativeTree.Tree.branch 958 (QuarticIntegerRepresentativeTree.Tree.branch 957 (QuarticIntegerRepresentativeTree.Tree.leaf 956 representative_956) (QuarticIntegerRepresentativeTree.Tree.leaf 957 representative_957)) (QuarticIntegerRepresentativeTree.Tree.branch 959 (QuarticIntegerRepresentativeTree.Tree.leaf 958 representative_958) (QuarticIntegerRepresentativeTree.Tree.leaf 959 representative_959)))))))
theorem accepted_014 : All validRep tree_014 := ⟨⟨⟨⟨⟨⟨coefficient_896,coefficient_897⟩,⟨coefficient_898,coefficient_899⟩⟩,⟨⟨coefficient_900,coefficient_901⟩,⟨coefficient_902,coefficient_903⟩⟩⟩,⟨⟨⟨coefficient_904,coefficient_905⟩,⟨coefficient_906,coefficient_907⟩⟩,⟨⟨coefficient_908,coefficient_909⟩,⟨coefficient_910,coefficient_911⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_912,coefficient_913⟩,⟨coefficient_914,coefficient_915⟩⟩,⟨⟨coefficient_916,coefficient_917⟩,⟨coefficient_918,coefficient_919⟩⟩⟩,⟨⟨⟨coefficient_920,coefficient_921⟩,⟨coefficient_922,coefficient_923⟩⟩,⟨⟨coefficient_924,coefficient_925⟩,⟨coefficient_926,coefficient_927⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_928,coefficient_929⟩,⟨coefficient_930,coefficient_931⟩⟩,⟨⟨coefficient_932,coefficient_933⟩,⟨coefficient_934,coefficient_935⟩⟩⟩,⟨⟨⟨coefficient_936,coefficient_937⟩,⟨coefficient_938,coefficient_939⟩⟩,⟨⟨coefficient_940,coefficient_941⟩,⟨coefficient_942,coefficient_943⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_944,coefficient_945⟩,⟨coefficient_946,coefficient_947⟩⟩,⟨⟨coefficient_948,coefficient_949⟩,⟨coefficient_950,coefficient_951⟩⟩⟩,⟨⟨⟨coefficient_952,coefficient_953⟩,⟨coefficient_954,coefficient_955⟩⟩,⟨⟨coefficient_956,coefficient_957⟩,⟨coefficient_958,coefficient_959⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

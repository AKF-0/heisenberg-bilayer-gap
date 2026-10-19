import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_960 : Rep := ⟨![0,2,25,28],462⟩
def representative_961 : Rep := ⟨![0,2,25,29],462⟩
def representative_962 : Rep := ⟨![0,2,25,32],462⟩
def representative_963 : Rep := ⟨![0,2,25,35],462⟩
def representative_964 : Rep := ⟨![0,2,25,36],462⟩
def representative_965 : Rep := ⟨![0,2,25,37],462⟩
def representative_966 : Rep := ⟨![0,2,25,43],462⟩
def representative_967 : Rep := ⟨![0,2,25,44],462⟩
def representative_968 : Rep := ⟨![0,2,25,45],462⟩
def representative_969 : Rep := ⟨![0,2,27,29],462⟩
def representative_970 : Rep := ⟨![0,2,27,30],462⟩
def representative_971 : Rep := ⟨![0,2,27,31],462⟩
def representative_972 : Rep := ⟨![0,2,27,32],462⟩
def representative_973 : Rep := ⟨![0,2,27,33],462⟩
def representative_974 : Rep := ⟨![0,2,27,34],462⟩
def representative_975 : Rep := ⟨![0,2,27,36],462⟩
def representative_976 : Rep := ⟨![0,2,27,37],462⟩
def representative_977 : Rep := ⟨![0,2,27,38],462⟩
def representative_978 : Rep := ⟨![0,2,27,39],462⟩
def representative_979 : Rep := ⟨![0,2,27,44],462⟩
def representative_980 : Rep := ⟨![0,2,27,45],462⟩
def representative_981 : Rep := ⟨![0,2,27,46],462⟩
def representative_982 : Rep := ⟨![0,2,27,47],462⟩
def representative_983 : Rep := ⟨![0,2,28,30],462⟩
def representative_984 : Rep := ⟨![0,2,28,32],462⟩
def representative_985 : Rep := ⟨![0,2,28,33],462⟩
def representative_986 : Rep := ⟨![0,2,28,34],462⟩
def representative_987 : Rep := ⟨![0,2,28,35],462⟩
def representative_988 : Rep := ⟨![0,2,28,37],462⟩
def representative_989 : Rep := ⟨![0,2,28,38],462⟩
def representative_990 : Rep := ⟨![0,2,28,39],462⟩
def representative_991 : Rep := ⟨![0,2,28,45],462⟩
def representative_992 : Rep := ⟨![0,2,28,46],462⟩
def representative_993 : Rep := ⟨![0,2,29,32],462⟩
def representative_994 : Rep := ⟨![0,2,29,33],462⟩
def representative_995 : Rep := ⟨![0,2,29,35],462⟩
def representative_996 : Rep := ⟨![0,2,29,36],462⟩
def representative_997 : Rep := ⟨![0,2,29,45],462⟩
def representative_998 : Rep := ⟨![0,2,32,34],462⟩
def representative_999 : Rep := ⟨![0,2,32,35],462⟩
def representative_1000 : Rep := ⟨![0,2,32,36],462⟩
def representative_1001 : Rep := ⟨![0,2,32,37],462⟩
def representative_1002 : Rep := ⟨![0,2,32,38],462⟩
def representative_1003 : Rep := ⟨![0,2,33,35],462⟩
def representative_1004 : Rep := ⟨![0,2,33,36],462⟩
def representative_1005 : Rep := ⟨![0,2,33,37],462⟩
def representative_1006 : Rep := ⟨![0,2,35,37],462⟩
def representative_1007 : Rep := ⟨![0,2,35,38],462⟩
def representative_1008 : Rep := ⟨![0,2,35,39],462⟩
def representative_1009 : Rep := ⟨![0,2,36,38],462⟩
def representative_1010 : Rep := ⟨![0,3,1,4],374⟩
def representative_1011 : Rep := ⟨![0,3,1,5],96⟩
def representative_1012 : Rep := ⟨![0,3,1,6],425⟩
def representative_1013 : Rep := ⟨![0,3,1,8],29⟩
def representative_1014 : Rep := ⟨![0,3,1,10],51⟩
def representative_1015 : Rep := ⟨![0,3,1,11],400⟩
def representative_1016 : Rep := ⟨![0,3,1,12],190⟩
def representative_1017 : Rep := ⟨![0,3,1,13],277⟩
def representative_1018 : Rep := ⟨![0,3,1,14],87⟩
def representative_1019 : Rep := ⟨![0,3,1,15],430⟩
def representative_1020 : Rep := ⟨![0,3,1,16],426⟩
def representative_1021 : Rep := ⟨![0,3,1,18],393⟩
def representative_1022 : Rep := ⟨![0,3,1,19],206⟩
def representative_1023 : Rep := ⟨![0,3,1,20],266⟩
theorem coefficient_960 : validRep representative_960 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_960)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_961 : validRep representative_961 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_961)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_962 : validRep representative_962 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_962)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_963 : validRep representative_963 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_963)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_964 : validRep representative_964 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_964)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_965 : validRep representative_965 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_965)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_966 : validRep representative_966 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_966)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_967 : validRep representative_967 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_967)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_968 : validRep representative_968 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_968)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_969 : validRep representative_969 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_969)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_970 : validRep representative_970 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_970)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_971 : validRep representative_971 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_971)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_972 : validRep representative_972 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_972)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_973 : validRep representative_973 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_973)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_974 : validRep representative_974 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_974)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_975 : validRep representative_975 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_975)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_976 : validRep representative_976 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_976)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_977 : validRep representative_977 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_977)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_978 : validRep representative_978 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_978)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_979 : validRep representative_979 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_979)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_980 : validRep representative_980 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_980)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_981 : validRep representative_981 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_981)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_982 : validRep representative_982 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_982)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_983 : validRep representative_983 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_983)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_984 : validRep representative_984 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_984)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_985 : validRep representative_985 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_985)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_986 : validRep representative_986 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_986)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_987 : validRep representative_987 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_987)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_988 : validRep representative_988 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_988)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_989 : validRep representative_989 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_989)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_990 : validRep representative_990 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_990)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_991 : validRep representative_991 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_991)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_992 : validRep representative_992 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_992)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_993 : validRep representative_993 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_993)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_994 : validRep representative_994 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_994)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_995 : validRep representative_995 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_995)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_996 : validRep representative_996 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_996)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_997 : validRep representative_997 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_997)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_998 : validRep representative_998 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_998)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_999 : validRep representative_999 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_999)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1000 : validRep representative_1000 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1000)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1001 : validRep representative_1001 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1001)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1002 : validRep representative_1002 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1002)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1003 : validRep representative_1003 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1003)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1004 : validRep representative_1004 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1004)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1005 : validRep representative_1005 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1005)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1006 : validRep representative_1006 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1006)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1007 : validRep representative_1007 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1007)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1008 : validRep representative_1008 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1008)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1009 : validRep representative_1009 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1009)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1010 : validRep representative_1010 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1010)=dictionary64.getD 374 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_374]
  decide +kernel
theorem coefficient_1011 : validRep representative_1011 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1011)=dictionary64.getD 96 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_96]
  decide +kernel
theorem coefficient_1012 : validRep representative_1012 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1012)=dictionary64.getD 425 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_425]
  decide +kernel
theorem coefficient_1013 : validRep representative_1013 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1013)=dictionary64.getD 29 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_29]
  decide +kernel
theorem coefficient_1014 : validRep representative_1014 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1014)=dictionary64.getD 51 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_51]
  decide +kernel
theorem coefficient_1015 : validRep representative_1015 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1015)=dictionary64.getD 400 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_400]
  decide +kernel
theorem coefficient_1016 : validRep representative_1016 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1016)=dictionary64.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_1017 : validRep representative_1017 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1017)=dictionary64.getD 277 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_277]
  decide +kernel
theorem coefficient_1018 : validRep representative_1018 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1018)=dictionary64.getD 87 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_87]
  decide +kernel
theorem coefficient_1019 : validRep representative_1019 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1019)=dictionary64.getD 430 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_430]
  decide +kernel
theorem coefficient_1020 : validRep representative_1020 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1020)=dictionary64.getD 426 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_426]
  decide +kernel
theorem coefficient_1021 : validRep representative_1021 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1021)=dictionary64.getD 393 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_393]
  decide +kernel
theorem coefficient_1022 : validRep representative_1022 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1022)=dictionary64.getD 206 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_206]
  decide +kernel
theorem coefficient_1023 : validRep representative_1023 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1023)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
def tree_015 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 992 (QuarticIntegerRepresentativeTree.Tree.branch 976 (QuarticIntegerRepresentativeTree.Tree.branch 968 (QuarticIntegerRepresentativeTree.Tree.branch 964 (QuarticIntegerRepresentativeTree.Tree.branch 962 (QuarticIntegerRepresentativeTree.Tree.branch 961 (QuarticIntegerRepresentativeTree.Tree.leaf 960 representative_960) (QuarticIntegerRepresentativeTree.Tree.leaf 961 representative_961)) (QuarticIntegerRepresentativeTree.Tree.branch 963 (QuarticIntegerRepresentativeTree.Tree.leaf 962 representative_962) (QuarticIntegerRepresentativeTree.Tree.leaf 963 representative_963))) (QuarticIntegerRepresentativeTree.Tree.branch 966 (QuarticIntegerRepresentativeTree.Tree.branch 965 (QuarticIntegerRepresentativeTree.Tree.leaf 964 representative_964) (QuarticIntegerRepresentativeTree.Tree.leaf 965 representative_965)) (QuarticIntegerRepresentativeTree.Tree.branch 967 (QuarticIntegerRepresentativeTree.Tree.leaf 966 representative_966) (QuarticIntegerRepresentativeTree.Tree.leaf 967 representative_967)))) (QuarticIntegerRepresentativeTree.Tree.branch 972 (QuarticIntegerRepresentativeTree.Tree.branch 970 (QuarticIntegerRepresentativeTree.Tree.branch 969 (QuarticIntegerRepresentativeTree.Tree.leaf 968 representative_968) (QuarticIntegerRepresentativeTree.Tree.leaf 969 representative_969)) (QuarticIntegerRepresentativeTree.Tree.branch 971 (QuarticIntegerRepresentativeTree.Tree.leaf 970 representative_970) (QuarticIntegerRepresentativeTree.Tree.leaf 971 representative_971))) (QuarticIntegerRepresentativeTree.Tree.branch 974 (QuarticIntegerRepresentativeTree.Tree.branch 973 (QuarticIntegerRepresentativeTree.Tree.leaf 972 representative_972) (QuarticIntegerRepresentativeTree.Tree.leaf 973 representative_973)) (QuarticIntegerRepresentativeTree.Tree.branch 975 (QuarticIntegerRepresentativeTree.Tree.leaf 974 representative_974) (QuarticIntegerRepresentativeTree.Tree.leaf 975 representative_975))))) (QuarticIntegerRepresentativeTree.Tree.branch 984 (QuarticIntegerRepresentativeTree.Tree.branch 980 (QuarticIntegerRepresentativeTree.Tree.branch 978 (QuarticIntegerRepresentativeTree.Tree.branch 977 (QuarticIntegerRepresentativeTree.Tree.leaf 976 representative_976) (QuarticIntegerRepresentativeTree.Tree.leaf 977 representative_977)) (QuarticIntegerRepresentativeTree.Tree.branch 979 (QuarticIntegerRepresentativeTree.Tree.leaf 978 representative_978) (QuarticIntegerRepresentativeTree.Tree.leaf 979 representative_979))) (QuarticIntegerRepresentativeTree.Tree.branch 982 (QuarticIntegerRepresentativeTree.Tree.branch 981 (QuarticIntegerRepresentativeTree.Tree.leaf 980 representative_980) (QuarticIntegerRepresentativeTree.Tree.leaf 981 representative_981)) (QuarticIntegerRepresentativeTree.Tree.branch 983 (QuarticIntegerRepresentativeTree.Tree.leaf 982 representative_982) (QuarticIntegerRepresentativeTree.Tree.leaf 983 representative_983)))) (QuarticIntegerRepresentativeTree.Tree.branch 988 (QuarticIntegerRepresentativeTree.Tree.branch 986 (QuarticIntegerRepresentativeTree.Tree.branch 985 (QuarticIntegerRepresentativeTree.Tree.leaf 984 representative_984) (QuarticIntegerRepresentativeTree.Tree.leaf 985 representative_985)) (QuarticIntegerRepresentativeTree.Tree.branch 987 (QuarticIntegerRepresentativeTree.Tree.leaf 986 representative_986) (QuarticIntegerRepresentativeTree.Tree.leaf 987 representative_987))) (QuarticIntegerRepresentativeTree.Tree.branch 990 (QuarticIntegerRepresentativeTree.Tree.branch 989 (QuarticIntegerRepresentativeTree.Tree.leaf 988 representative_988) (QuarticIntegerRepresentativeTree.Tree.leaf 989 representative_989)) (QuarticIntegerRepresentativeTree.Tree.branch 991 (QuarticIntegerRepresentativeTree.Tree.leaf 990 representative_990) (QuarticIntegerRepresentativeTree.Tree.leaf 991 representative_991)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1008 (QuarticIntegerRepresentativeTree.Tree.branch 1000 (QuarticIntegerRepresentativeTree.Tree.branch 996 (QuarticIntegerRepresentativeTree.Tree.branch 994 (QuarticIntegerRepresentativeTree.Tree.branch 993 (QuarticIntegerRepresentativeTree.Tree.leaf 992 representative_992) (QuarticIntegerRepresentativeTree.Tree.leaf 993 representative_993)) (QuarticIntegerRepresentativeTree.Tree.branch 995 (QuarticIntegerRepresentativeTree.Tree.leaf 994 representative_994) (QuarticIntegerRepresentativeTree.Tree.leaf 995 representative_995))) (QuarticIntegerRepresentativeTree.Tree.branch 998 (QuarticIntegerRepresentativeTree.Tree.branch 997 (QuarticIntegerRepresentativeTree.Tree.leaf 996 representative_996) (QuarticIntegerRepresentativeTree.Tree.leaf 997 representative_997)) (QuarticIntegerRepresentativeTree.Tree.branch 999 (QuarticIntegerRepresentativeTree.Tree.leaf 998 representative_998) (QuarticIntegerRepresentativeTree.Tree.leaf 999 representative_999)))) (QuarticIntegerRepresentativeTree.Tree.branch 1004 (QuarticIntegerRepresentativeTree.Tree.branch 1002 (QuarticIntegerRepresentativeTree.Tree.branch 1001 (QuarticIntegerRepresentativeTree.Tree.leaf 1000 representative_1000) (QuarticIntegerRepresentativeTree.Tree.leaf 1001 representative_1001)) (QuarticIntegerRepresentativeTree.Tree.branch 1003 (QuarticIntegerRepresentativeTree.Tree.leaf 1002 representative_1002) (QuarticIntegerRepresentativeTree.Tree.leaf 1003 representative_1003))) (QuarticIntegerRepresentativeTree.Tree.branch 1006 (QuarticIntegerRepresentativeTree.Tree.branch 1005 (QuarticIntegerRepresentativeTree.Tree.leaf 1004 representative_1004) (QuarticIntegerRepresentativeTree.Tree.leaf 1005 representative_1005)) (QuarticIntegerRepresentativeTree.Tree.branch 1007 (QuarticIntegerRepresentativeTree.Tree.leaf 1006 representative_1006) (QuarticIntegerRepresentativeTree.Tree.leaf 1007 representative_1007))))) (QuarticIntegerRepresentativeTree.Tree.branch 1016 (QuarticIntegerRepresentativeTree.Tree.branch 1012 (QuarticIntegerRepresentativeTree.Tree.branch 1010 (QuarticIntegerRepresentativeTree.Tree.branch 1009 (QuarticIntegerRepresentativeTree.Tree.leaf 1008 representative_1008) (QuarticIntegerRepresentativeTree.Tree.leaf 1009 representative_1009)) (QuarticIntegerRepresentativeTree.Tree.branch 1011 (QuarticIntegerRepresentativeTree.Tree.leaf 1010 representative_1010) (QuarticIntegerRepresentativeTree.Tree.leaf 1011 representative_1011))) (QuarticIntegerRepresentativeTree.Tree.branch 1014 (QuarticIntegerRepresentativeTree.Tree.branch 1013 (QuarticIntegerRepresentativeTree.Tree.leaf 1012 representative_1012) (QuarticIntegerRepresentativeTree.Tree.leaf 1013 representative_1013)) (QuarticIntegerRepresentativeTree.Tree.branch 1015 (QuarticIntegerRepresentativeTree.Tree.leaf 1014 representative_1014) (QuarticIntegerRepresentativeTree.Tree.leaf 1015 representative_1015)))) (QuarticIntegerRepresentativeTree.Tree.branch 1020 (QuarticIntegerRepresentativeTree.Tree.branch 1018 (QuarticIntegerRepresentativeTree.Tree.branch 1017 (QuarticIntegerRepresentativeTree.Tree.leaf 1016 representative_1016) (QuarticIntegerRepresentativeTree.Tree.leaf 1017 representative_1017)) (QuarticIntegerRepresentativeTree.Tree.branch 1019 (QuarticIntegerRepresentativeTree.Tree.leaf 1018 representative_1018) (QuarticIntegerRepresentativeTree.Tree.leaf 1019 representative_1019))) (QuarticIntegerRepresentativeTree.Tree.branch 1022 (QuarticIntegerRepresentativeTree.Tree.branch 1021 (QuarticIntegerRepresentativeTree.Tree.leaf 1020 representative_1020) (QuarticIntegerRepresentativeTree.Tree.leaf 1021 representative_1021)) (QuarticIntegerRepresentativeTree.Tree.branch 1023 (QuarticIntegerRepresentativeTree.Tree.leaf 1022 representative_1022) (QuarticIntegerRepresentativeTree.Tree.leaf 1023 representative_1023)))))))
theorem accepted_015 : All validRep tree_015 := ⟨⟨⟨⟨⟨⟨coefficient_960,coefficient_961⟩,⟨coefficient_962,coefficient_963⟩⟩,⟨⟨coefficient_964,coefficient_965⟩,⟨coefficient_966,coefficient_967⟩⟩⟩,⟨⟨⟨coefficient_968,coefficient_969⟩,⟨coefficient_970,coefficient_971⟩⟩,⟨⟨coefficient_972,coefficient_973⟩,⟨coefficient_974,coefficient_975⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_976,coefficient_977⟩,⟨coefficient_978,coefficient_979⟩⟩,⟨⟨coefficient_980,coefficient_981⟩,⟨coefficient_982,coefficient_983⟩⟩⟩,⟨⟨⟨coefficient_984,coefficient_985⟩,⟨coefficient_986,coefficient_987⟩⟩,⟨⟨coefficient_988,coefficient_989⟩,⟨coefficient_990,coefficient_991⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_992,coefficient_993⟩,⟨coefficient_994,coefficient_995⟩⟩,⟨⟨coefficient_996,coefficient_997⟩,⟨coefficient_998,coefficient_999⟩⟩⟩,⟨⟨⟨coefficient_1000,coefficient_1001⟩,⟨coefficient_1002,coefficient_1003⟩⟩,⟨⟨coefficient_1004,coefficient_1005⟩,⟨coefficient_1006,coefficient_1007⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1008,coefficient_1009⟩,⟨coefficient_1010,coefficient_1011⟩⟩,⟨⟨coefficient_1012,coefficient_1013⟩,⟨coefficient_1014,coefficient_1015⟩⟩⟩,⟨⟨⟨coefficient_1016,coefficient_1017⟩,⟨coefficient_1018,coefficient_1019⟩⟩,⟨⟨coefficient_1020,coefficient_1021⟩,⟨coefficient_1022,coefficient_1023⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

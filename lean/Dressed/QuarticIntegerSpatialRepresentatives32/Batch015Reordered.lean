import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_960 : Rep := ⟨![0,12,6,16],304⟩
def representative_961 : Rep := ⟨![0,12,6,17],268⟩
def representative_962 : Rep := ⟨![0,12,6,18],280⟩
def representative_963 : Rep := ⟨![0,12,6,20],268⟩
def representative_964 : Rep := ⟨![0,12,6,21],277⟩
def representative_965 : Rep := ⟨![0,12,6,22],508⟩
def representative_966 : Rep := ⟨![0,12,6,24],300⟩
def representative_967 : Rep := ⟨![0,12,6,25],265⟩
def representative_968 : Rep := ⟨![0,12,6,26],280⟩
def representative_969 : Rep := ⟨![0,12,16,28],250⟩
def representative_970 : Rep := ⟨![0,12,16,29],273⟩
def representative_971 : Rep := ⟨![0,12,16,30],274⟩
def representative_972 : Rep := ⟨![0,12,17,29],508⟩
def representative_973 : Rep := ⟨![0,12,17,30],508⟩
def representative_974 : Rep := ⟨![0,12,17,31],508⟩
def representative_975 : Rep := ⟨![0,12,18,30],508⟩
def representative_976 : Rep := ⟨![0,13,1,12],10⟩
def representative_977 : Rep := ⟨![0,13,1,14],508⟩
def representative_978 : Rep := ⟨![0,13,1,15],508⟩
def representative_979 : Rep := ⟨![0,13,1,16],508⟩
def representative_980 : Rep := ⟨![0,13,1,17],508⟩
def representative_981 : Rep := ⟨![0,13,1,18],508⟩
def representative_982 : Rep := ⟨![0,13,1,19],508⟩
def representative_983 : Rep := ⟨![0,13,1,20],9⟩
def representative_984 : Rep := ⟨![0,13,1,22],508⟩
def representative_985 : Rep := ⟨![0,13,1,23],508⟩
def representative_986 : Rep := ⟨![0,13,2,15],508⟩
def representative_987 : Rep := ⟨![0,13,2,16],508⟩
def representative_988 : Rep := ⟨![0,13,2,17],508⟩
def representative_989 : Rep := ⟨![0,13,2,18],508⟩
def representative_990 : Rep := ⟨![0,13,2,19],508⟩
def representative_991 : Rep := ⟨![0,13,2,20],508⟩
def representative_992 : Rep := ⟨![0,13,2,21],508⟩
def representative_993 : Rep := ⟨![0,13,2,23],508⟩
def representative_994 : Rep := ⟨![0,13,3,14],508⟩
def representative_995 : Rep := ⟨![0,13,3,16],508⟩
def representative_996 : Rep := ⟨![0,13,3,17],508⟩
def representative_997 : Rep := ⟨![0,13,3,18],508⟩
def representative_998 : Rep := ⟨![0,13,3,19],508⟩
def representative_999 : Rep := ⟨![0,13,3,21],508⟩
def representative_1000 : Rep := ⟨![0,13,3,22],508⟩
def representative_1001 : Rep := ⟨![0,13,4,17],508⟩
def representative_1002 : Rep := ⟨![0,13,4,18],508⟩
def representative_1003 : Rep := ⟨![0,13,4,19],508⟩
def representative_1004 : Rep := ⟨![0,13,4,20],11⟩
def representative_1005 : Rep := ⟨![0,13,4,21],508⟩
def representative_1006 : Rep := ⟨![0,13,4,22],508⟩
def representative_1007 : Rep := ⟨![0,13,4,23],508⟩
def representative_1008 : Rep := ⟨![0,13,4,25],13⟩
def representative_1009 : Rep := ⟨![0,13,4,26],508⟩
def representative_1010 : Rep := ⟨![0,13,4,27],13⟩
def representative_1011 : Rep := ⟨![0,13,5,16],508⟩
def representative_1012 : Rep := ⟨![0,13,5,18],508⟩
def representative_1013 : Rep := ⟨![0,13,5,19],508⟩
def representative_1014 : Rep := ⟨![0,13,5,20],508⟩
def representative_1015 : Rep := ⟨![0,13,5,21],508⟩
def representative_1016 : Rep := ⟨![0,13,5,22],508⟩
def representative_1017 : Rep := ⟨![0,13,5,23],508⟩
def representative_1018 : Rep := ⟨![0,13,5,24],508⟩
def representative_1019 : Rep := ⟨![0,13,5,26],508⟩
def representative_1020 : Rep := ⟨![0,13,5,27],508⟩
def representative_1021 : Rep := ⟨![0,13,6,16],508⟩
def representative_1022 : Rep := ⟨![0,13,6,19],508⟩
def representative_1023 : Rep := ⟨![0,13,6,20],508⟩
theorem coefficient_960 : validRep representative_960 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_960)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_961 : validRep representative_961 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_961)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_962 : validRep representative_962 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_962)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_963 : validRep representative_963 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_963)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_964 : validRep representative_964 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_964)=dictionary32.getD 277 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_277]
  decide +kernel
theorem coefficient_965 : validRep representative_965 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_965)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_966 : validRep representative_966 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_966)=dictionary32.getD 300 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_300]
  decide +kernel
theorem coefficient_967 : validRep representative_967 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_967)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_968 : validRep representative_968 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_968)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_969 : validRep representative_969 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_969)=dictionary32.getD 250 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_250]
  decide +kernel
theorem coefficient_970 : validRep representative_970 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_970)=dictionary32.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_971 : validRep representative_971 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_971)=dictionary32.getD 274 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_274]
  decide +kernel
theorem coefficient_972 : validRep representative_972 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_972)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_973 : validRep representative_973 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_973)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_974 : validRep representative_974 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_974)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_975 : validRep representative_975 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_975)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_976 : validRep representative_976 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_976)=dictionary32.getD 10 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_10]
  decide +kernel
theorem coefficient_977 : validRep representative_977 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_977)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_978 : validRep representative_978 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_978)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_979 : validRep representative_979 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_979)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_980 : validRep representative_980 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_980)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_981 : validRep representative_981 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_981)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_982 : validRep representative_982 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_982)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_983 : validRep representative_983 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_983)=dictionary32.getD 9 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_984 : validRep representative_984 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_984)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_985 : validRep representative_985 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_985)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_986 : validRep representative_986 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_986)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_987 : validRep representative_987 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_987)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_988 : validRep representative_988 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_988)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_989 : validRep representative_989 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_989)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_990 : validRep representative_990 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_990)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_991 : validRep representative_991 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_991)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_992 : validRep representative_992 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_992)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_993 : validRep representative_993 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_993)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_994 : validRep representative_994 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_994)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_995 : validRep representative_995 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_995)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_996 : validRep representative_996 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_996)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_997 : validRep representative_997 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_997)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_998 : validRep representative_998 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_998)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_999 : validRep representative_999 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_999)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1000 : validRep representative_1000 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1000)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1001 : validRep representative_1001 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1001)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1002 : validRep representative_1002 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1002)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1003 : validRep representative_1003 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1003)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1004 : validRep representative_1004 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1004)=dictionary32.getD 11 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_11]
  decide +kernel
theorem coefficient_1005 : validRep representative_1005 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1005)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1006 : validRep representative_1006 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1006)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1007 : validRep representative_1007 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1007)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1008 : validRep representative_1008 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1008)=dictionary32.getD 13 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_1009 : validRep representative_1009 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1009)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1010 : validRep representative_1010 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1010)=dictionary32.getD 13 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_1011 : validRep representative_1011 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1011)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1012 : validRep representative_1012 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1012)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1013 : validRep representative_1013 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1013)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1014 : validRep representative_1014 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1014)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1015 : validRep representative_1015 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1015)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1016 : validRep representative_1016 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1016)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1017 : validRep representative_1017 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1017)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1018 : validRep representative_1018 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1018)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1019 : validRep representative_1019 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1019)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1020 : validRep representative_1020 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1020)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1021 : validRep representative_1021 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1021)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1022 : validRep representative_1022 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1022)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1023 : validRep representative_1023 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_1023)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_015 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 992 (QuarticIntegerRepresentativeTree.Tree.branch 976 (QuarticIntegerRepresentativeTree.Tree.branch 968 (QuarticIntegerRepresentativeTree.Tree.branch 964 (QuarticIntegerRepresentativeTree.Tree.branch 962 (QuarticIntegerRepresentativeTree.Tree.branch 961 (QuarticIntegerRepresentativeTree.Tree.leaf 960 representative_960) (QuarticIntegerRepresentativeTree.Tree.leaf 961 representative_961)) (QuarticIntegerRepresentativeTree.Tree.branch 963 (QuarticIntegerRepresentativeTree.Tree.leaf 962 representative_962) (QuarticIntegerRepresentativeTree.Tree.leaf 963 representative_963))) (QuarticIntegerRepresentativeTree.Tree.branch 966 (QuarticIntegerRepresentativeTree.Tree.branch 965 (QuarticIntegerRepresentativeTree.Tree.leaf 964 representative_964) (QuarticIntegerRepresentativeTree.Tree.leaf 965 representative_965)) (QuarticIntegerRepresentativeTree.Tree.branch 967 (QuarticIntegerRepresentativeTree.Tree.leaf 966 representative_966) (QuarticIntegerRepresentativeTree.Tree.leaf 967 representative_967)))) (QuarticIntegerRepresentativeTree.Tree.branch 972 (QuarticIntegerRepresentativeTree.Tree.branch 970 (QuarticIntegerRepresentativeTree.Tree.branch 969 (QuarticIntegerRepresentativeTree.Tree.leaf 968 representative_968) (QuarticIntegerRepresentativeTree.Tree.leaf 969 representative_969)) (QuarticIntegerRepresentativeTree.Tree.branch 971 (QuarticIntegerRepresentativeTree.Tree.leaf 970 representative_970) (QuarticIntegerRepresentativeTree.Tree.leaf 971 representative_971))) (QuarticIntegerRepresentativeTree.Tree.branch 974 (QuarticIntegerRepresentativeTree.Tree.branch 973 (QuarticIntegerRepresentativeTree.Tree.leaf 972 representative_972) (QuarticIntegerRepresentativeTree.Tree.leaf 973 representative_973)) (QuarticIntegerRepresentativeTree.Tree.branch 975 (QuarticIntegerRepresentativeTree.Tree.leaf 974 representative_974) (QuarticIntegerRepresentativeTree.Tree.leaf 975 representative_975))))) (QuarticIntegerRepresentativeTree.Tree.branch 984 (QuarticIntegerRepresentativeTree.Tree.branch 980 (QuarticIntegerRepresentativeTree.Tree.branch 978 (QuarticIntegerRepresentativeTree.Tree.branch 977 (QuarticIntegerRepresentativeTree.Tree.leaf 976 representative_976) (QuarticIntegerRepresentativeTree.Tree.leaf 977 representative_977)) (QuarticIntegerRepresentativeTree.Tree.branch 979 (QuarticIntegerRepresentativeTree.Tree.leaf 978 representative_978) (QuarticIntegerRepresentativeTree.Tree.leaf 979 representative_979))) (QuarticIntegerRepresentativeTree.Tree.branch 982 (QuarticIntegerRepresentativeTree.Tree.branch 981 (QuarticIntegerRepresentativeTree.Tree.leaf 980 representative_980) (QuarticIntegerRepresentativeTree.Tree.leaf 981 representative_981)) (QuarticIntegerRepresentativeTree.Tree.branch 983 (QuarticIntegerRepresentativeTree.Tree.leaf 982 representative_982) (QuarticIntegerRepresentativeTree.Tree.leaf 983 representative_983)))) (QuarticIntegerRepresentativeTree.Tree.branch 988 (QuarticIntegerRepresentativeTree.Tree.branch 986 (QuarticIntegerRepresentativeTree.Tree.branch 985 (QuarticIntegerRepresentativeTree.Tree.leaf 984 representative_984) (QuarticIntegerRepresentativeTree.Tree.leaf 985 representative_985)) (QuarticIntegerRepresentativeTree.Tree.branch 987 (QuarticIntegerRepresentativeTree.Tree.leaf 986 representative_986) (QuarticIntegerRepresentativeTree.Tree.leaf 987 representative_987))) (QuarticIntegerRepresentativeTree.Tree.branch 990 (QuarticIntegerRepresentativeTree.Tree.branch 989 (QuarticIntegerRepresentativeTree.Tree.leaf 988 representative_988) (QuarticIntegerRepresentativeTree.Tree.leaf 989 representative_989)) (QuarticIntegerRepresentativeTree.Tree.branch 991 (QuarticIntegerRepresentativeTree.Tree.leaf 990 representative_990) (QuarticIntegerRepresentativeTree.Tree.leaf 991 representative_991)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1008 (QuarticIntegerRepresentativeTree.Tree.branch 1000 (QuarticIntegerRepresentativeTree.Tree.branch 996 (QuarticIntegerRepresentativeTree.Tree.branch 994 (QuarticIntegerRepresentativeTree.Tree.branch 993 (QuarticIntegerRepresentativeTree.Tree.leaf 992 representative_992) (QuarticIntegerRepresentativeTree.Tree.leaf 993 representative_993)) (QuarticIntegerRepresentativeTree.Tree.branch 995 (QuarticIntegerRepresentativeTree.Tree.leaf 994 representative_994) (QuarticIntegerRepresentativeTree.Tree.leaf 995 representative_995))) (QuarticIntegerRepresentativeTree.Tree.branch 998 (QuarticIntegerRepresentativeTree.Tree.branch 997 (QuarticIntegerRepresentativeTree.Tree.leaf 996 representative_996) (QuarticIntegerRepresentativeTree.Tree.leaf 997 representative_997)) (QuarticIntegerRepresentativeTree.Tree.branch 999 (QuarticIntegerRepresentativeTree.Tree.leaf 998 representative_998) (QuarticIntegerRepresentativeTree.Tree.leaf 999 representative_999)))) (QuarticIntegerRepresentativeTree.Tree.branch 1004 (QuarticIntegerRepresentativeTree.Tree.branch 1002 (QuarticIntegerRepresentativeTree.Tree.branch 1001 (QuarticIntegerRepresentativeTree.Tree.leaf 1000 representative_1000) (QuarticIntegerRepresentativeTree.Tree.leaf 1001 representative_1001)) (QuarticIntegerRepresentativeTree.Tree.branch 1003 (QuarticIntegerRepresentativeTree.Tree.leaf 1002 representative_1002) (QuarticIntegerRepresentativeTree.Tree.leaf 1003 representative_1003))) (QuarticIntegerRepresentativeTree.Tree.branch 1006 (QuarticIntegerRepresentativeTree.Tree.branch 1005 (QuarticIntegerRepresentativeTree.Tree.leaf 1004 representative_1004) (QuarticIntegerRepresentativeTree.Tree.leaf 1005 representative_1005)) (QuarticIntegerRepresentativeTree.Tree.branch 1007 (QuarticIntegerRepresentativeTree.Tree.leaf 1006 representative_1006) (QuarticIntegerRepresentativeTree.Tree.leaf 1007 representative_1007))))) (QuarticIntegerRepresentativeTree.Tree.branch 1016 (QuarticIntegerRepresentativeTree.Tree.branch 1012 (QuarticIntegerRepresentativeTree.Tree.branch 1010 (QuarticIntegerRepresentativeTree.Tree.branch 1009 (QuarticIntegerRepresentativeTree.Tree.leaf 1008 representative_1008) (QuarticIntegerRepresentativeTree.Tree.leaf 1009 representative_1009)) (QuarticIntegerRepresentativeTree.Tree.branch 1011 (QuarticIntegerRepresentativeTree.Tree.leaf 1010 representative_1010) (QuarticIntegerRepresentativeTree.Tree.leaf 1011 representative_1011))) (QuarticIntegerRepresentativeTree.Tree.branch 1014 (QuarticIntegerRepresentativeTree.Tree.branch 1013 (QuarticIntegerRepresentativeTree.Tree.leaf 1012 representative_1012) (QuarticIntegerRepresentativeTree.Tree.leaf 1013 representative_1013)) (QuarticIntegerRepresentativeTree.Tree.branch 1015 (QuarticIntegerRepresentativeTree.Tree.leaf 1014 representative_1014) (QuarticIntegerRepresentativeTree.Tree.leaf 1015 representative_1015)))) (QuarticIntegerRepresentativeTree.Tree.branch 1020 (QuarticIntegerRepresentativeTree.Tree.branch 1018 (QuarticIntegerRepresentativeTree.Tree.branch 1017 (QuarticIntegerRepresentativeTree.Tree.leaf 1016 representative_1016) (QuarticIntegerRepresentativeTree.Tree.leaf 1017 representative_1017)) (QuarticIntegerRepresentativeTree.Tree.branch 1019 (QuarticIntegerRepresentativeTree.Tree.leaf 1018 representative_1018) (QuarticIntegerRepresentativeTree.Tree.leaf 1019 representative_1019))) (QuarticIntegerRepresentativeTree.Tree.branch 1022 (QuarticIntegerRepresentativeTree.Tree.branch 1021 (QuarticIntegerRepresentativeTree.Tree.leaf 1020 representative_1020) (QuarticIntegerRepresentativeTree.Tree.leaf 1021 representative_1021)) (QuarticIntegerRepresentativeTree.Tree.branch 1023 (QuarticIntegerRepresentativeTree.Tree.leaf 1022 representative_1022) (QuarticIntegerRepresentativeTree.Tree.leaf 1023 representative_1023)))))))
theorem accepted_015 : All validRep tree_015 := ⟨⟨⟨⟨⟨⟨coefficient_960,coefficient_961⟩,⟨coefficient_962,coefficient_963⟩⟩,⟨⟨coefficient_964,coefficient_965⟩,⟨coefficient_966,coefficient_967⟩⟩⟩,⟨⟨⟨coefficient_968,coefficient_969⟩,⟨coefficient_970,coefficient_971⟩⟩,⟨⟨coefficient_972,coefficient_973⟩,⟨coefficient_974,coefficient_975⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_976,coefficient_977⟩,⟨coefficient_978,coefficient_979⟩⟩,⟨⟨coefficient_980,coefficient_981⟩,⟨coefficient_982,coefficient_983⟩⟩⟩,⟨⟨⟨coefficient_984,coefficient_985⟩,⟨coefficient_986,coefficient_987⟩⟩,⟨⟨coefficient_988,coefficient_989⟩,⟨coefficient_990,coefficient_991⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_992,coefficient_993⟩,⟨coefficient_994,coefficient_995⟩⟩,⟨⟨coefficient_996,coefficient_997⟩,⟨coefficient_998,coefficient_999⟩⟩⟩,⟨⟨⟨coefficient_1000,coefficient_1001⟩,⟨coefficient_1002,coefficient_1003⟩⟩,⟨⟨coefficient_1004,coefficient_1005⟩,⟨coefficient_1006,coefficient_1007⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1008,coefficient_1009⟩,⟨coefficient_1010,coefficient_1011⟩⟩,⟨⟨coefficient_1012,coefficient_1013⟩,⟨coefficient_1014,coefficient_1015⟩⟩⟩,⟨⟨⟨coefficient_1016,coefficient_1017⟩,⟨coefficient_1018,coefficient_1019⟩⟩,⟨⟨coefficient_1020,coefficient_1021⟩,⟨coefficient_1022,coefficient_1023⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

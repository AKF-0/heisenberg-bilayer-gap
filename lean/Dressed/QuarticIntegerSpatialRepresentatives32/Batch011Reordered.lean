import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_704 : Rep := ⟨![0,8,13,24],290⟩
def representative_705 : Rep := ⟨![0,8,13,25],269⟩
def representative_706 : Rep := ⟨![0,8,13,26],508⟩
def representative_707 : Rep := ⟨![0,8,13,27],271⟩
def representative_708 : Rep := ⟨![0,8,13,29],307⟩
def representative_709 : Rep := ⟨![0,8,13,30],268⟩
def representative_710 : Rep := ⟨![0,8,13,31],307⟩
def representative_711 : Rep := ⟨![0,8,14,20],297⟩
def representative_712 : Rep := ⟨![0,8,14,21],268⟩
def representative_713 : Rep := ⟨![0,8,14,22],508⟩
def representative_714 : Rep := ⟨![0,8,14,24],271⟩
def representative_715 : Rep := ⟨![0,8,14,25],508⟩
def representative_716 : Rep := ⟨![0,8,14,26],508⟩
def representative_717 : Rep := ⟨![0,8,14,30],508⟩
def representative_718 : Rep := ⟨![0,8,16,24],290⟩
def representative_719 : Rep := ⟨![0,8,16,25],271⟩
def representative_720 : Rep := ⟨![0,8,16,26],508⟩
def representative_721 : Rep := ⟨![0,8,17,25],508⟩
def representative_722 : Rep := ⟨![0,8,17,26],508⟩
def representative_723 : Rep := ⟨![0,8,17,27],508⟩
def representative_724 : Rep := ⟨![0,8,18,26],508⟩
def representative_725 : Rep := ⟨![0,9,1,8],457⟩
def representative_726 : Rep := ⟨![0,9,1,10],419⟩
def representative_727 : Rep := ⟨![0,9,1,11],115⟩
def representative_728 : Rep := ⟨![0,9,1,12],122⟩
def representative_729 : Rep := ⟨![0,9,1,13],406⟩
def representative_730 : Rep := ⟨![0,9,1,14],188⟩
def representative_731 : Rep := ⟨![0,9,1,15],329⟩
def representative_732 : Rep := ⟨![0,9,1,16],314⟩
def representative_733 : Rep := ⟨![0,9,1,17],223⟩
def representative_734 : Rep := ⟨![0,9,1,18],309⟩
def representative_735 : Rep := ⟨![0,9,1,19],265⟩
def representative_736 : Rep := ⟨![0,9,1,20],123⟩
def representative_737 : Rep := ⟨![0,9,1,21],356⟩
def representative_738 : Rep := ⟨![0,9,1,22],271⟩
def representative_739 : Rep := ⟨![0,9,1,23],304⟩
def representative_740 : Rep := ⟨![0,9,1,24],450⟩
def representative_741 : Rep := ⟨![0,9,1,26],394⟩
def representative_742 : Rep := ⟨![0,9,1,27],116⟩
def representative_743 : Rep := ⟨![0,9,2,11],343⟩
def representative_744 : Rep := ⟨![0,9,2,12],328⟩
def representative_745 : Rep := ⟨![0,9,2,13],149⟩
def representative_746 : Rep := ⟨![0,9,2,14],328⟩
def representative_747 : Rep := ⟨![0,9,2,15],254⟩
def representative_748 : Rep := ⟨![0,9,2,16],259⟩
def representative_749 : Rep := ⟨![0,9,2,17],309⟩
def representative_750 : Rep := ⟨![0,9,2,18],261⟩
def representative_751 : Rep := ⟨![0,9,2,19],279⟩
def representative_752 : Rep := ⟨![0,9,2,20],301⟩
def representative_753 : Rep := ⟨![0,9,2,21],263⟩
def representative_754 : Rep := ⟨![0,9,2,22],301⟩
def representative_755 : Rep := ⟨![0,9,2,23],268⟩
def representative_756 : Rep := ⟨![0,9,2,24],187⟩
def representative_757 : Rep := ⟨![0,9,2,25],337⟩
def representative_758 : Rep := ⟨![0,9,2,27],336⟩
def representative_759 : Rep := ⟨![0,9,3,10],333⟩
def representative_760 : Rep := ⟨![0,9,3,12],198⟩
def representative_761 : Rep := ⟨![0,9,3,13],330⟩
def representative_762 : Rep := ⟨![0,9,3,14],258⟩
def representative_763 : Rep := ⟨![0,9,3,15],294⟩
def representative_764 : Rep := ⟨![0,9,3,16],289⟩
def representative_765 : Rep := ⟨![0,9,3,17],265⟩
def representative_766 : Rep := ⟨![0,9,3,18],279⟩
def representative_767 : Rep := ⟨![0,9,3,19],508⟩
theorem coefficient_704 : validRep representative_704 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_704)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_705 : validRep representative_705 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_705)=dictionary32.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_706 : validRep representative_706 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_706)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_707 : validRep representative_707 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_707)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_708 : validRep representative_708 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_708)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_709 : validRep representative_709 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_709)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_710 : validRep representative_710 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_710)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_711 : validRep representative_711 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_711)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_712 : validRep representative_712 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_712)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_713 : validRep representative_713 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_713)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_714 : validRep representative_714 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_714)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_715 : validRep representative_715 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_715)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_716 : validRep representative_716 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_716)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_717 : validRep representative_717 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_717)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_718 : validRep representative_718 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_718)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_719 : validRep representative_719 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_719)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_720 : validRep representative_720 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_720)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_721 : validRep representative_721 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_721)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_722 : validRep representative_722 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_722)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_723 : validRep representative_723 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_723)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_724 : validRep representative_724 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_724)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_725 : validRep representative_725 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_725)=dictionary32.getD 457 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_457]
  decide +kernel
theorem coefficient_726 : validRep representative_726 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_726)=dictionary32.getD 419 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_419]
  decide +kernel
theorem coefficient_727 : validRep representative_727 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_727)=dictionary32.getD 115 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_115]
  decide +kernel
theorem coefficient_728 : validRep representative_728 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_728)=dictionary32.getD 122 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_122]
  decide +kernel
theorem coefficient_729 : validRep representative_729 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_729)=dictionary32.getD 406 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_406]
  decide +kernel
theorem coefficient_730 : validRep representative_730 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_730)=dictionary32.getD 188 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_188]
  decide +kernel
theorem coefficient_731 : validRep representative_731 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_731)=dictionary32.getD 329 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_329]
  decide +kernel
theorem coefficient_732 : validRep representative_732 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_732)=dictionary32.getD 314 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_314]
  decide +kernel
theorem coefficient_733 : validRep representative_733 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_733)=dictionary32.getD 223 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_223]
  decide +kernel
theorem coefficient_734 : validRep representative_734 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_734)=dictionary32.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_735 : validRep representative_735 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_735)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_736 : validRep representative_736 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_736)=dictionary32.getD 123 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_123]
  decide +kernel
theorem coefficient_737 : validRep representative_737 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_737)=dictionary32.getD 356 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_356]
  decide +kernel
theorem coefficient_738 : validRep representative_738 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_738)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_739 : validRep representative_739 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_739)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_740 : validRep representative_740 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_740)=dictionary32.getD 450 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_450]
  decide +kernel
theorem coefficient_741 : validRep representative_741 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_741)=dictionary32.getD 394 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_394]
  decide +kernel
theorem coefficient_742 : validRep representative_742 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_742)=dictionary32.getD 116 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_116]
  decide +kernel
theorem coefficient_743 : validRep representative_743 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_743)=dictionary32.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_744 : validRep representative_744 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_744)=dictionary32.getD 328 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_328]
  decide +kernel
theorem coefficient_745 : validRep representative_745 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_745)=dictionary32.getD 149 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_149]
  decide +kernel
theorem coefficient_746 : validRep representative_746 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_746)=dictionary32.getD 328 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_328]
  decide +kernel
theorem coefficient_747 : validRep representative_747 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_747)=dictionary32.getD 254 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_254]
  decide +kernel
theorem coefficient_748 : validRep representative_748 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_748)=dictionary32.getD 259 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_259]
  decide +kernel
theorem coefficient_749 : validRep representative_749 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_749)=dictionary32.getD 309 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_309]
  decide +kernel
theorem coefficient_750 : validRep representative_750 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_750)=dictionary32.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_751 : validRep representative_751 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_751)=dictionary32.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_752 : validRep representative_752 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_752)=dictionary32.getD 301 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_301]
  decide +kernel
theorem coefficient_753 : validRep representative_753 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_753)=dictionary32.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_754 : validRep representative_754 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_754)=dictionary32.getD 301 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_301]
  decide +kernel
theorem coefficient_755 : validRep representative_755 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_755)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_756 : validRep representative_756 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_756)=dictionary32.getD 187 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_187]
  decide +kernel
theorem coefficient_757 : validRep representative_757 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_757)=dictionary32.getD 337 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_337]
  decide +kernel
theorem coefficient_758 : validRep representative_758 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_758)=dictionary32.getD 336 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_336]
  decide +kernel
theorem coefficient_759 : validRep representative_759 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_759)=dictionary32.getD 333 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_333]
  decide +kernel
theorem coefficient_760 : validRep representative_760 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_760)=dictionary32.getD 198 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_198]
  decide +kernel
theorem coefficient_761 : validRep representative_761 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_761)=dictionary32.getD 330 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_330]
  decide +kernel
theorem coefficient_762 : validRep representative_762 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_762)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_763 : validRep representative_763 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_763)=dictionary32.getD 294 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_294]
  decide +kernel
theorem coefficient_764 : validRep representative_764 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_764)=dictionary32.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_765 : validRep representative_765 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_765)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_766 : validRep representative_766 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_766)=dictionary32.getD 279 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_279]
  decide +kernel
theorem coefficient_767 : validRep representative_767 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_767)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_011 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 736 (QuarticIntegerRepresentativeTree.Tree.branch 720 (QuarticIntegerRepresentativeTree.Tree.branch 712 (QuarticIntegerRepresentativeTree.Tree.branch 708 (QuarticIntegerRepresentativeTree.Tree.branch 706 (QuarticIntegerRepresentativeTree.Tree.branch 705 (QuarticIntegerRepresentativeTree.Tree.leaf 704 representative_704) (QuarticIntegerRepresentativeTree.Tree.leaf 705 representative_705)) (QuarticIntegerRepresentativeTree.Tree.branch 707 (QuarticIntegerRepresentativeTree.Tree.leaf 706 representative_706) (QuarticIntegerRepresentativeTree.Tree.leaf 707 representative_707))) (QuarticIntegerRepresentativeTree.Tree.branch 710 (QuarticIntegerRepresentativeTree.Tree.branch 709 (QuarticIntegerRepresentativeTree.Tree.leaf 708 representative_708) (QuarticIntegerRepresentativeTree.Tree.leaf 709 representative_709)) (QuarticIntegerRepresentativeTree.Tree.branch 711 (QuarticIntegerRepresentativeTree.Tree.leaf 710 representative_710) (QuarticIntegerRepresentativeTree.Tree.leaf 711 representative_711)))) (QuarticIntegerRepresentativeTree.Tree.branch 716 (QuarticIntegerRepresentativeTree.Tree.branch 714 (QuarticIntegerRepresentativeTree.Tree.branch 713 (QuarticIntegerRepresentativeTree.Tree.leaf 712 representative_712) (QuarticIntegerRepresentativeTree.Tree.leaf 713 representative_713)) (QuarticIntegerRepresentativeTree.Tree.branch 715 (QuarticIntegerRepresentativeTree.Tree.leaf 714 representative_714) (QuarticIntegerRepresentativeTree.Tree.leaf 715 representative_715))) (QuarticIntegerRepresentativeTree.Tree.branch 718 (QuarticIntegerRepresentativeTree.Tree.branch 717 (QuarticIntegerRepresentativeTree.Tree.leaf 716 representative_716) (QuarticIntegerRepresentativeTree.Tree.leaf 717 representative_717)) (QuarticIntegerRepresentativeTree.Tree.branch 719 (QuarticIntegerRepresentativeTree.Tree.leaf 718 representative_718) (QuarticIntegerRepresentativeTree.Tree.leaf 719 representative_719))))) (QuarticIntegerRepresentativeTree.Tree.branch 728 (QuarticIntegerRepresentativeTree.Tree.branch 724 (QuarticIntegerRepresentativeTree.Tree.branch 722 (QuarticIntegerRepresentativeTree.Tree.branch 721 (QuarticIntegerRepresentativeTree.Tree.leaf 720 representative_720) (QuarticIntegerRepresentativeTree.Tree.leaf 721 representative_721)) (QuarticIntegerRepresentativeTree.Tree.branch 723 (QuarticIntegerRepresentativeTree.Tree.leaf 722 representative_722) (QuarticIntegerRepresentativeTree.Tree.leaf 723 representative_723))) (QuarticIntegerRepresentativeTree.Tree.branch 726 (QuarticIntegerRepresentativeTree.Tree.branch 725 (QuarticIntegerRepresentativeTree.Tree.leaf 724 representative_724) (QuarticIntegerRepresentativeTree.Tree.leaf 725 representative_725)) (QuarticIntegerRepresentativeTree.Tree.branch 727 (QuarticIntegerRepresentativeTree.Tree.leaf 726 representative_726) (QuarticIntegerRepresentativeTree.Tree.leaf 727 representative_727)))) (QuarticIntegerRepresentativeTree.Tree.branch 732 (QuarticIntegerRepresentativeTree.Tree.branch 730 (QuarticIntegerRepresentativeTree.Tree.branch 729 (QuarticIntegerRepresentativeTree.Tree.leaf 728 representative_728) (QuarticIntegerRepresentativeTree.Tree.leaf 729 representative_729)) (QuarticIntegerRepresentativeTree.Tree.branch 731 (QuarticIntegerRepresentativeTree.Tree.leaf 730 representative_730) (QuarticIntegerRepresentativeTree.Tree.leaf 731 representative_731))) (QuarticIntegerRepresentativeTree.Tree.branch 734 (QuarticIntegerRepresentativeTree.Tree.branch 733 (QuarticIntegerRepresentativeTree.Tree.leaf 732 representative_732) (QuarticIntegerRepresentativeTree.Tree.leaf 733 representative_733)) (QuarticIntegerRepresentativeTree.Tree.branch 735 (QuarticIntegerRepresentativeTree.Tree.leaf 734 representative_734) (QuarticIntegerRepresentativeTree.Tree.leaf 735 representative_735)))))) (QuarticIntegerRepresentativeTree.Tree.branch 752 (QuarticIntegerRepresentativeTree.Tree.branch 744 (QuarticIntegerRepresentativeTree.Tree.branch 740 (QuarticIntegerRepresentativeTree.Tree.branch 738 (QuarticIntegerRepresentativeTree.Tree.branch 737 (QuarticIntegerRepresentativeTree.Tree.leaf 736 representative_736) (QuarticIntegerRepresentativeTree.Tree.leaf 737 representative_737)) (QuarticIntegerRepresentativeTree.Tree.branch 739 (QuarticIntegerRepresentativeTree.Tree.leaf 738 representative_738) (QuarticIntegerRepresentativeTree.Tree.leaf 739 representative_739))) (QuarticIntegerRepresentativeTree.Tree.branch 742 (QuarticIntegerRepresentativeTree.Tree.branch 741 (QuarticIntegerRepresentativeTree.Tree.leaf 740 representative_740) (QuarticIntegerRepresentativeTree.Tree.leaf 741 representative_741)) (QuarticIntegerRepresentativeTree.Tree.branch 743 (QuarticIntegerRepresentativeTree.Tree.leaf 742 representative_742) (QuarticIntegerRepresentativeTree.Tree.leaf 743 representative_743)))) (QuarticIntegerRepresentativeTree.Tree.branch 748 (QuarticIntegerRepresentativeTree.Tree.branch 746 (QuarticIntegerRepresentativeTree.Tree.branch 745 (QuarticIntegerRepresentativeTree.Tree.leaf 744 representative_744) (QuarticIntegerRepresentativeTree.Tree.leaf 745 representative_745)) (QuarticIntegerRepresentativeTree.Tree.branch 747 (QuarticIntegerRepresentativeTree.Tree.leaf 746 representative_746) (QuarticIntegerRepresentativeTree.Tree.leaf 747 representative_747))) (QuarticIntegerRepresentativeTree.Tree.branch 750 (QuarticIntegerRepresentativeTree.Tree.branch 749 (QuarticIntegerRepresentativeTree.Tree.leaf 748 representative_748) (QuarticIntegerRepresentativeTree.Tree.leaf 749 representative_749)) (QuarticIntegerRepresentativeTree.Tree.branch 751 (QuarticIntegerRepresentativeTree.Tree.leaf 750 representative_750) (QuarticIntegerRepresentativeTree.Tree.leaf 751 representative_751))))) (QuarticIntegerRepresentativeTree.Tree.branch 760 (QuarticIntegerRepresentativeTree.Tree.branch 756 (QuarticIntegerRepresentativeTree.Tree.branch 754 (QuarticIntegerRepresentativeTree.Tree.branch 753 (QuarticIntegerRepresentativeTree.Tree.leaf 752 representative_752) (QuarticIntegerRepresentativeTree.Tree.leaf 753 representative_753)) (QuarticIntegerRepresentativeTree.Tree.branch 755 (QuarticIntegerRepresentativeTree.Tree.leaf 754 representative_754) (QuarticIntegerRepresentativeTree.Tree.leaf 755 representative_755))) (QuarticIntegerRepresentativeTree.Tree.branch 758 (QuarticIntegerRepresentativeTree.Tree.branch 757 (QuarticIntegerRepresentativeTree.Tree.leaf 756 representative_756) (QuarticIntegerRepresentativeTree.Tree.leaf 757 representative_757)) (QuarticIntegerRepresentativeTree.Tree.branch 759 (QuarticIntegerRepresentativeTree.Tree.leaf 758 representative_758) (QuarticIntegerRepresentativeTree.Tree.leaf 759 representative_759)))) (QuarticIntegerRepresentativeTree.Tree.branch 764 (QuarticIntegerRepresentativeTree.Tree.branch 762 (QuarticIntegerRepresentativeTree.Tree.branch 761 (QuarticIntegerRepresentativeTree.Tree.leaf 760 representative_760) (QuarticIntegerRepresentativeTree.Tree.leaf 761 representative_761)) (QuarticIntegerRepresentativeTree.Tree.branch 763 (QuarticIntegerRepresentativeTree.Tree.leaf 762 representative_762) (QuarticIntegerRepresentativeTree.Tree.leaf 763 representative_763))) (QuarticIntegerRepresentativeTree.Tree.branch 766 (QuarticIntegerRepresentativeTree.Tree.branch 765 (QuarticIntegerRepresentativeTree.Tree.leaf 764 representative_764) (QuarticIntegerRepresentativeTree.Tree.leaf 765 representative_765)) (QuarticIntegerRepresentativeTree.Tree.branch 767 (QuarticIntegerRepresentativeTree.Tree.leaf 766 representative_766) (QuarticIntegerRepresentativeTree.Tree.leaf 767 representative_767)))))))
theorem accepted_011 : All validRep tree_011 := ⟨⟨⟨⟨⟨⟨coefficient_704,coefficient_705⟩,⟨coefficient_706,coefficient_707⟩⟩,⟨⟨coefficient_708,coefficient_709⟩,⟨coefficient_710,coefficient_711⟩⟩⟩,⟨⟨⟨coefficient_712,coefficient_713⟩,⟨coefficient_714,coefficient_715⟩⟩,⟨⟨coefficient_716,coefficient_717⟩,⟨coefficient_718,coefficient_719⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_720,coefficient_721⟩,⟨coefficient_722,coefficient_723⟩⟩,⟨⟨coefficient_724,coefficient_725⟩,⟨coefficient_726,coefficient_727⟩⟩⟩,⟨⟨⟨coefficient_728,coefficient_729⟩,⟨coefficient_730,coefficient_731⟩⟩,⟨⟨coefficient_732,coefficient_733⟩,⟨coefficient_734,coefficient_735⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_736,coefficient_737⟩,⟨coefficient_738,coefficient_739⟩⟩,⟨⟨coefficient_740,coefficient_741⟩,⟨coefficient_742,coefficient_743⟩⟩⟩,⟨⟨⟨coefficient_744,coefficient_745⟩,⟨coefficient_746,coefficient_747⟩⟩,⟨⟨coefficient_748,coefficient_749⟩,⟨coefficient_750,coefficient_751⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_752,coefficient_753⟩,⟨coefficient_754,coefficient_755⟩⟩,⟨⟨coefficient_756,coefficient_757⟩,⟨coefficient_758,coefficient_759⟩⟩⟩,⟨⟨⟨coefficient_760,coefficient_761⟩,⟨coefficient_762,coefficient_763⟩⟩,⟨⟨coefficient_764,coefficient_765⟩,⟨coefficient_766,coefficient_767⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_704 : Rep := ⟨![0,2,11,18],351⟩
def representative_705 : Rep := ⟨![0,2,11,20],300⟩
def representative_706 : Rep := ⟨![0,2,11,21],232⟩
def representative_707 : Rep := ⟨![0,2,11,22],462⟩
def representative_708 : Rep := ⟨![0,2,11,23],235⟩
def representative_709 : Rep := ⟨![0,2,11,24],238⟩
def representative_710 : Rep := ⟨![0,2,11,25],273⟩
def representative_711 : Rep := ⟨![0,2,11,26],197⟩
def representative_712 : Rep := ⟨![0,2,11,27],288⟩
def representative_713 : Rep := ⟨![0,2,11,28],232⟩
def representative_714 : Rep := ⟨![0,2,11,29],462⟩
def representative_715 : Rep := ⟨![0,2,11,30],462⟩
def representative_716 : Rep := ⟨![0,2,11,31],462⟩
def representative_717 : Rep := ⟨![0,2,11,32],462⟩
def representative_718 : Rep := ⟨![0,2,11,33],462⟩
def representative_719 : Rep := ⟨![0,2,11,34],261⟩
def representative_720 : Rep := ⟨![0,2,11,35],236⟩
def representative_721 : Rep := ⟨![0,2,11,36],462⟩
def representative_722 : Rep := ⟨![0,2,11,37],462⟩
def representative_723 : Rep := ⟨![0,2,11,38],462⟩
def representative_724 : Rep := ⟨![0,2,11,39],462⟩
def representative_725 : Rep := ⟨![0,2,11,40],238⟩
def representative_726 : Rep := ⟨![0,2,11,41],273⟩
def representative_727 : Rep := ⟨![0,2,11,42],199⟩
def representative_728 : Rep := ⟨![0,2,11,43],273⟩
def representative_729 : Rep := ⟨![0,2,11,44],462⟩
def representative_730 : Rep := ⟨![0,2,11,45],462⟩
def representative_731 : Rep := ⟨![0,2,11,46],462⟩
def representative_732 : Rep := ⟨![0,2,11,47],462⟩
def representative_733 : Rep := ⟨![0,2,11,48],288⟩
def representative_734 : Rep := ⟨![0,2,11,49],147⟩
def representative_735 : Rep := ⟨![0,2,11,50],345⟩
def representative_736 : Rep := ⟨![0,2,11,51],148⟩
def representative_737 : Rep := ⟨![0,2,11,52],278⟩
def representative_738 : Rep := ⟨![0,2,11,53],462⟩
def representative_739 : Rep := ⟨![0,2,11,54],462⟩
def representative_740 : Rep := ⟨![0,2,11,55],235⟩
def representative_741 : Rep := ⟨![0,2,11,60],146⟩
def representative_742 : Rep := ⟨![0,2,11,61],273⟩
def representative_743 : Rep := ⟨![0,2,11,62],235⟩
def representative_744 : Rep := ⟨![0,2,11,63],288⟩
def representative_745 : Rep := ⟨![0,2,12,14],462⟩
def representative_746 : Rep := ⟨![0,2,12,16],234⟩
def representative_747 : Rep := ⟨![0,2,12,17],289⟩
def representative_748 : Rep := ⟨![0,2,12,18],182⟩
def representative_749 : Rep := ⟨![0,2,12,19],289⟩
def representative_750 : Rep := ⟨![0,2,12,21],462⟩
def representative_751 : Rep := ⟨![0,2,12,22],462⟩
def representative_752 : Rep := ⟨![0,2,12,23],462⟩
def representative_753 : Rep := ⟨![0,2,12,24],462⟩
def representative_754 : Rep := ⟨![0,2,12,25],235⟩
def representative_755 : Rep := ⟨![0,2,12,26],265⟩
def representative_756 : Rep := ⟨![0,2,12,27],235⟩
def representative_757 : Rep := ⟨![0,2,12,28],462⟩
def representative_758 : Rep := ⟨![0,2,12,29],462⟩
def representative_759 : Rep := ⟨![0,2,12,30],462⟩
def representative_760 : Rep := ⟨![0,2,12,31],462⟩
def representative_761 : Rep := ⟨![0,2,12,32],462⟩
def representative_762 : Rep := ⟨![0,2,12,33],462⟩
def representative_763 : Rep := ⟨![0,2,12,34],237⟩
def representative_764 : Rep := ⟨![0,2,12,35],462⟩
def representative_765 : Rep := ⟨![0,2,12,36],462⟩
def representative_766 : Rep := ⟨![0,2,12,37],462⟩
def representative_767 : Rep := ⟨![0,2,12,38],462⟩
theorem coefficient_704 : validRep representative_704 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_704)=dictionary64.getD 351 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_351]
  decide +kernel
theorem coefficient_705 : validRep representative_705 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_705)=dictionary64.getD 300 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_300]
  decide +kernel
theorem coefficient_706 : validRep representative_706 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_706)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_707 : validRep representative_707 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_707)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_708 : validRep representative_708 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_708)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_709 : validRep representative_709 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_709)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_710 : validRep representative_710 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_710)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_711 : validRep representative_711 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_711)=dictionary64.getD 197 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_197]
  decide +kernel
theorem coefficient_712 : validRep representative_712 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_712)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_713 : validRep representative_713 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_713)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_714 : validRep representative_714 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_714)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_715 : validRep representative_715 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_715)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_716 : validRep representative_716 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_716)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_717 : validRep representative_717 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_717)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_718 : validRep representative_718 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_718)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_719 : validRep representative_719 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_719)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_720 : validRep representative_720 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_720)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_721 : validRep representative_721 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_721)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_722 : validRep representative_722 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_722)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_723 : validRep representative_723 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_723)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_724 : validRep representative_724 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_724)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_725 : validRep representative_725 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_725)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_726 : validRep representative_726 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_726)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_727 : validRep representative_727 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_727)=dictionary64.getD 199 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_199]
  decide +kernel
theorem coefficient_728 : validRep representative_728 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_728)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_729 : validRep representative_729 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_729)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_730 : validRep representative_730 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_730)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_731 : validRep representative_731 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_731)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_732 : validRep representative_732 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_732)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_733 : validRep representative_733 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_733)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_734 : validRep representative_734 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_734)=dictionary64.getD 147 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_147]
  decide +kernel
theorem coefficient_735 : validRep representative_735 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_735)=dictionary64.getD 345 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_345]
  decide +kernel
theorem coefficient_736 : validRep representative_736 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_736)=dictionary64.getD 148 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_148]
  decide +kernel
theorem coefficient_737 : validRep representative_737 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_737)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_738 : validRep representative_738 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_738)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_739 : validRep representative_739 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_739)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_740 : validRep representative_740 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_740)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_741 : validRep representative_741 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_741)=dictionary64.getD 146 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_146]
  decide +kernel
theorem coefficient_742 : validRep representative_742 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_742)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_743 : validRep representative_743 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_743)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_744 : validRep representative_744 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_744)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_745 : validRep representative_745 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_745)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_746 : validRep representative_746 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_746)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_747 : validRep representative_747 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_747)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_748 : validRep representative_748 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_748)=dictionary64.getD 182 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_182]
  decide +kernel
theorem coefficient_749 : validRep representative_749 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_749)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_750 : validRep representative_750 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_750)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_751 : validRep representative_751 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_751)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_752 : validRep representative_752 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_752)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_753 : validRep representative_753 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_753)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_754 : validRep representative_754 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_754)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_755 : validRep representative_755 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_755)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_756 : validRep representative_756 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_756)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_757 : validRep representative_757 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_757)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_758 : validRep representative_758 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_758)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_759 : validRep representative_759 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_759)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_760 : validRep representative_760 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_760)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_761 : validRep representative_761 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_761)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_762 : validRep representative_762 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_762)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_763 : validRep representative_763 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_763)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_764 : validRep representative_764 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_764)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_765 : validRep representative_765 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_765)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_766 : validRep representative_766 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_766)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_767 : validRep representative_767 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_767)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_011 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 736 (QuarticIntegerRepresentativeTree.Tree.branch 720 (QuarticIntegerRepresentativeTree.Tree.branch 712 (QuarticIntegerRepresentativeTree.Tree.branch 708 (QuarticIntegerRepresentativeTree.Tree.branch 706 (QuarticIntegerRepresentativeTree.Tree.branch 705 (QuarticIntegerRepresentativeTree.Tree.leaf 704 representative_704) (QuarticIntegerRepresentativeTree.Tree.leaf 705 representative_705)) (QuarticIntegerRepresentativeTree.Tree.branch 707 (QuarticIntegerRepresentativeTree.Tree.leaf 706 representative_706) (QuarticIntegerRepresentativeTree.Tree.leaf 707 representative_707))) (QuarticIntegerRepresentativeTree.Tree.branch 710 (QuarticIntegerRepresentativeTree.Tree.branch 709 (QuarticIntegerRepresentativeTree.Tree.leaf 708 representative_708) (QuarticIntegerRepresentativeTree.Tree.leaf 709 representative_709)) (QuarticIntegerRepresentativeTree.Tree.branch 711 (QuarticIntegerRepresentativeTree.Tree.leaf 710 representative_710) (QuarticIntegerRepresentativeTree.Tree.leaf 711 representative_711)))) (QuarticIntegerRepresentativeTree.Tree.branch 716 (QuarticIntegerRepresentativeTree.Tree.branch 714 (QuarticIntegerRepresentativeTree.Tree.branch 713 (QuarticIntegerRepresentativeTree.Tree.leaf 712 representative_712) (QuarticIntegerRepresentativeTree.Tree.leaf 713 representative_713)) (QuarticIntegerRepresentativeTree.Tree.branch 715 (QuarticIntegerRepresentativeTree.Tree.leaf 714 representative_714) (QuarticIntegerRepresentativeTree.Tree.leaf 715 representative_715))) (QuarticIntegerRepresentativeTree.Tree.branch 718 (QuarticIntegerRepresentativeTree.Tree.branch 717 (QuarticIntegerRepresentativeTree.Tree.leaf 716 representative_716) (QuarticIntegerRepresentativeTree.Tree.leaf 717 representative_717)) (QuarticIntegerRepresentativeTree.Tree.branch 719 (QuarticIntegerRepresentativeTree.Tree.leaf 718 representative_718) (QuarticIntegerRepresentativeTree.Tree.leaf 719 representative_719))))) (QuarticIntegerRepresentativeTree.Tree.branch 728 (QuarticIntegerRepresentativeTree.Tree.branch 724 (QuarticIntegerRepresentativeTree.Tree.branch 722 (QuarticIntegerRepresentativeTree.Tree.branch 721 (QuarticIntegerRepresentativeTree.Tree.leaf 720 representative_720) (QuarticIntegerRepresentativeTree.Tree.leaf 721 representative_721)) (QuarticIntegerRepresentativeTree.Tree.branch 723 (QuarticIntegerRepresentativeTree.Tree.leaf 722 representative_722) (QuarticIntegerRepresentativeTree.Tree.leaf 723 representative_723))) (QuarticIntegerRepresentativeTree.Tree.branch 726 (QuarticIntegerRepresentativeTree.Tree.branch 725 (QuarticIntegerRepresentativeTree.Tree.leaf 724 representative_724) (QuarticIntegerRepresentativeTree.Tree.leaf 725 representative_725)) (QuarticIntegerRepresentativeTree.Tree.branch 727 (QuarticIntegerRepresentativeTree.Tree.leaf 726 representative_726) (QuarticIntegerRepresentativeTree.Tree.leaf 727 representative_727)))) (QuarticIntegerRepresentativeTree.Tree.branch 732 (QuarticIntegerRepresentativeTree.Tree.branch 730 (QuarticIntegerRepresentativeTree.Tree.branch 729 (QuarticIntegerRepresentativeTree.Tree.leaf 728 representative_728) (QuarticIntegerRepresentativeTree.Tree.leaf 729 representative_729)) (QuarticIntegerRepresentativeTree.Tree.branch 731 (QuarticIntegerRepresentativeTree.Tree.leaf 730 representative_730) (QuarticIntegerRepresentativeTree.Tree.leaf 731 representative_731))) (QuarticIntegerRepresentativeTree.Tree.branch 734 (QuarticIntegerRepresentativeTree.Tree.branch 733 (QuarticIntegerRepresentativeTree.Tree.leaf 732 representative_732) (QuarticIntegerRepresentativeTree.Tree.leaf 733 representative_733)) (QuarticIntegerRepresentativeTree.Tree.branch 735 (QuarticIntegerRepresentativeTree.Tree.leaf 734 representative_734) (QuarticIntegerRepresentativeTree.Tree.leaf 735 representative_735)))))) (QuarticIntegerRepresentativeTree.Tree.branch 752 (QuarticIntegerRepresentativeTree.Tree.branch 744 (QuarticIntegerRepresentativeTree.Tree.branch 740 (QuarticIntegerRepresentativeTree.Tree.branch 738 (QuarticIntegerRepresentativeTree.Tree.branch 737 (QuarticIntegerRepresentativeTree.Tree.leaf 736 representative_736) (QuarticIntegerRepresentativeTree.Tree.leaf 737 representative_737)) (QuarticIntegerRepresentativeTree.Tree.branch 739 (QuarticIntegerRepresentativeTree.Tree.leaf 738 representative_738) (QuarticIntegerRepresentativeTree.Tree.leaf 739 representative_739))) (QuarticIntegerRepresentativeTree.Tree.branch 742 (QuarticIntegerRepresentativeTree.Tree.branch 741 (QuarticIntegerRepresentativeTree.Tree.leaf 740 representative_740) (QuarticIntegerRepresentativeTree.Tree.leaf 741 representative_741)) (QuarticIntegerRepresentativeTree.Tree.branch 743 (QuarticIntegerRepresentativeTree.Tree.leaf 742 representative_742) (QuarticIntegerRepresentativeTree.Tree.leaf 743 representative_743)))) (QuarticIntegerRepresentativeTree.Tree.branch 748 (QuarticIntegerRepresentativeTree.Tree.branch 746 (QuarticIntegerRepresentativeTree.Tree.branch 745 (QuarticIntegerRepresentativeTree.Tree.leaf 744 representative_744) (QuarticIntegerRepresentativeTree.Tree.leaf 745 representative_745)) (QuarticIntegerRepresentativeTree.Tree.branch 747 (QuarticIntegerRepresentativeTree.Tree.leaf 746 representative_746) (QuarticIntegerRepresentativeTree.Tree.leaf 747 representative_747))) (QuarticIntegerRepresentativeTree.Tree.branch 750 (QuarticIntegerRepresentativeTree.Tree.branch 749 (QuarticIntegerRepresentativeTree.Tree.leaf 748 representative_748) (QuarticIntegerRepresentativeTree.Tree.leaf 749 representative_749)) (QuarticIntegerRepresentativeTree.Tree.branch 751 (QuarticIntegerRepresentativeTree.Tree.leaf 750 representative_750) (QuarticIntegerRepresentativeTree.Tree.leaf 751 representative_751))))) (QuarticIntegerRepresentativeTree.Tree.branch 760 (QuarticIntegerRepresentativeTree.Tree.branch 756 (QuarticIntegerRepresentativeTree.Tree.branch 754 (QuarticIntegerRepresentativeTree.Tree.branch 753 (QuarticIntegerRepresentativeTree.Tree.leaf 752 representative_752) (QuarticIntegerRepresentativeTree.Tree.leaf 753 representative_753)) (QuarticIntegerRepresentativeTree.Tree.branch 755 (QuarticIntegerRepresentativeTree.Tree.leaf 754 representative_754) (QuarticIntegerRepresentativeTree.Tree.leaf 755 representative_755))) (QuarticIntegerRepresentativeTree.Tree.branch 758 (QuarticIntegerRepresentativeTree.Tree.branch 757 (QuarticIntegerRepresentativeTree.Tree.leaf 756 representative_756) (QuarticIntegerRepresentativeTree.Tree.leaf 757 representative_757)) (QuarticIntegerRepresentativeTree.Tree.branch 759 (QuarticIntegerRepresentativeTree.Tree.leaf 758 representative_758) (QuarticIntegerRepresentativeTree.Tree.leaf 759 representative_759)))) (QuarticIntegerRepresentativeTree.Tree.branch 764 (QuarticIntegerRepresentativeTree.Tree.branch 762 (QuarticIntegerRepresentativeTree.Tree.branch 761 (QuarticIntegerRepresentativeTree.Tree.leaf 760 representative_760) (QuarticIntegerRepresentativeTree.Tree.leaf 761 representative_761)) (QuarticIntegerRepresentativeTree.Tree.branch 763 (QuarticIntegerRepresentativeTree.Tree.leaf 762 representative_762) (QuarticIntegerRepresentativeTree.Tree.leaf 763 representative_763))) (QuarticIntegerRepresentativeTree.Tree.branch 766 (QuarticIntegerRepresentativeTree.Tree.branch 765 (QuarticIntegerRepresentativeTree.Tree.leaf 764 representative_764) (QuarticIntegerRepresentativeTree.Tree.leaf 765 representative_765)) (QuarticIntegerRepresentativeTree.Tree.branch 767 (QuarticIntegerRepresentativeTree.Tree.leaf 766 representative_766) (QuarticIntegerRepresentativeTree.Tree.leaf 767 representative_767)))))))
theorem accepted_011 : All validRep tree_011 := ⟨⟨⟨⟨⟨⟨coefficient_704,coefficient_705⟩,⟨coefficient_706,coefficient_707⟩⟩,⟨⟨coefficient_708,coefficient_709⟩,⟨coefficient_710,coefficient_711⟩⟩⟩,⟨⟨⟨coefficient_712,coefficient_713⟩,⟨coefficient_714,coefficient_715⟩⟩,⟨⟨coefficient_716,coefficient_717⟩,⟨coefficient_718,coefficient_719⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_720,coefficient_721⟩,⟨coefficient_722,coefficient_723⟩⟩,⟨⟨coefficient_724,coefficient_725⟩,⟨coefficient_726,coefficient_727⟩⟩⟩,⟨⟨⟨coefficient_728,coefficient_729⟩,⟨coefficient_730,coefficient_731⟩⟩,⟨⟨coefficient_732,coefficient_733⟩,⟨coefficient_734,coefficient_735⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_736,coefficient_737⟩,⟨coefficient_738,coefficient_739⟩⟩,⟨⟨coefficient_740,coefficient_741⟩,⟨coefficient_742,coefficient_743⟩⟩⟩,⟨⟨⟨coefficient_744,coefficient_745⟩,⟨coefficient_746,coefficient_747⟩⟩,⟨⟨coefficient_748,coefficient_749⟩,⟨coefficient_750,coefficient_751⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_752,coefficient_753⟩,⟨coefficient_754,coefficient_755⟩⟩,⟨⟨coefficient_756,coefficient_757⟩,⟨coefficient_758,coefficient_759⟩⟩⟩,⟨⟨⟨coefficient_760,coefficient_761⟩,⟨coefficient_762,coefficient_763⟩⟩,⟨⟨coefficient_764,coefficient_765⟩,⟨coefficient_766,coefficient_767⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

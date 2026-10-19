import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_768 : Rep := ⟨![0,2,12,39],462⟩
def representative_769 : Rep := ⟨![0,2,12,40],462⟩
def representative_770 : Rep := ⟨![0,2,12,41],235⟩
def representative_771 : Rep := ⟨![0,2,12,42],265⟩
def representative_772 : Rep := ⟨![0,2,12,43],235⟩
def representative_773 : Rep := ⟨![0,2,12,44],462⟩
def representative_774 : Rep := ⟨![0,2,12,45],462⟩
def representative_775 : Rep := ⟨![0,2,12,46],462⟩
def representative_776 : Rep := ⟨![0,2,12,47],462⟩
def representative_777 : Rep := ⟨![0,2,12,48],234⟩
def representative_778 : Rep := ⟨![0,2,12,49],289⟩
def representative_779 : Rep := ⟨![0,2,12,50],184⟩
def representative_780 : Rep := ⟨![0,2,12,51],289⟩
def representative_781 : Rep := ⟨![0,2,12,52],234⟩
def representative_782 : Rep := ⟨![0,2,12,53],462⟩
def representative_783 : Rep := ⟨![0,2,12,54],462⟩
def representative_784 : Rep := ⟨![0,2,12,55],462⟩
def representative_785 : Rep := ⟨![0,2,12,60],289⟩
def representative_786 : Rep := ⟨![0,2,12,61],235⟩
def representative_787 : Rep := ⟨![0,2,12,62],462⟩
def representative_788 : Rep := ⟨![0,2,13,16],261⟩
def representative_789 : Rep := ⟨![0,2,13,17],232⟩
def representative_790 : Rep := ⟨![0,2,13,19],235⟩
def representative_791 : Rep := ⟨![0,2,13,20],462⟩
def representative_792 : Rep := ⟨![0,2,13,24],238⟩
def representative_793 : Rep := ⟨![0,2,13,25],462⟩
def representative_794 : Rep := ⟨![0,2,13,27],462⟩
def representative_795 : Rep := ⟨![0,2,13,28],462⟩
def representative_796 : Rep := ⟨![0,2,13,29],462⟩
def representative_797 : Rep := ⟨![0,2,13,32],462⟩
def representative_798 : Rep := ⟨![0,2,13,33],462⟩
def representative_799 : Rep := ⟨![0,2,13,35],462⟩
def representative_800 : Rep := ⟨![0,2,13,36],462⟩
def representative_801 : Rep := ⟨![0,2,13,37],462⟩
def representative_802 : Rep := ⟨![0,2,13,40],238⟩
def representative_803 : Rep := ⟨![0,2,13,41],462⟩
def representative_804 : Rep := ⟨![0,2,13,43],462⟩
def representative_805 : Rep := ⟨![0,2,13,44],462⟩
def representative_806 : Rep := ⟨![0,2,13,45],462⟩
def representative_807 : Rep := ⟨![0,2,13,48],261⟩
def representative_808 : Rep := ⟨![0,2,13,49],232⟩
def representative_809 : Rep := ⟨![0,2,13,51],235⟩
def representative_810 : Rep := ⟨![0,2,13,52],462⟩
def representative_811 : Rep := ⟨![0,2,13,53],462⟩
def representative_812 : Rep := ⟨![0,2,13,61],462⟩
def representative_813 : Rep := ⟨![0,2,16,18],295⟩
def representative_814 : Rep := ⟨![0,2,16,19],232⟩
def representative_815 : Rep := ⟨![0,2,16,20],462⟩
def representative_816 : Rep := ⟨![0,2,16,21],237⟩
def representative_817 : Rep := ⟨![0,2,16,22],278⟩
def representative_818 : Rep := ⟨![0,2,16,25],288⟩
def representative_819 : Rep := ⟨![0,2,16,26],232⟩
def representative_820 : Rep := ⟨![0,2,16,27],462⟩
def representative_821 : Rep := ⟨![0,2,16,28],462⟩
def representative_822 : Rep := ⟨![0,2,16,29],462⟩
def representative_823 : Rep := ⟨![0,2,16,30],234⟩
def representative_824 : Rep := ⟨![0,2,16,31],288⟩
def representative_825 : Rep := ⟨![0,2,16,33],234⟩
def representative_826 : Rep := ⟨![0,2,16,34],462⟩
def representative_827 : Rep := ⟨![0,2,16,35],462⟩
def representative_828 : Rep := ⟨![0,2,16,36],462⟩
def representative_829 : Rep := ⟨![0,2,16,37],462⟩
def representative_830 : Rep := ⟨![0,2,16,38],462⟩
def representative_831 : Rep := ⟨![0,2,16,39],234⟩
theorem coefficient_768 : validRep representative_768 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_768)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_769 : validRep representative_769 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_769)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_770 : validRep representative_770 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_770)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_771 : validRep representative_771 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_771)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_772 : validRep representative_772 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_772)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_773 : validRep representative_773 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_773)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_774 : validRep representative_774 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_774)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_775 : validRep representative_775 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_775)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_776 : validRep representative_776 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_776)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_777 : validRep representative_777 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_777)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_778 : validRep representative_778 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_778)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_779 : validRep representative_779 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_779)=dictionary64.getD 184 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_184]
  decide +kernel
theorem coefficient_780 : validRep representative_780 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_780)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_781 : validRep representative_781 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_781)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_782 : validRep representative_782 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_782)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_783 : validRep representative_783 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_783)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_784 : validRep representative_784 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_784)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_785 : validRep representative_785 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_785)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_786 : validRep representative_786 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_786)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_787 : validRep representative_787 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_787)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_788 : validRep representative_788 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_788)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_789 : validRep representative_789 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_789)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_790 : validRep representative_790 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_790)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_791 : validRep representative_791 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_791)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_792 : validRep representative_792 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_792)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_793 : validRep representative_793 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_793)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_794 : validRep representative_794 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_794)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_795 : validRep representative_795 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_795)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_796 : validRep representative_796 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_796)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_797 : validRep representative_797 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_797)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_798 : validRep representative_798 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_798)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_799 : validRep representative_799 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_799)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_800 : validRep representative_800 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_800)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_801 : validRep representative_801 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_801)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_802 : validRep representative_802 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_802)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_803 : validRep representative_803 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_803)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_804 : validRep representative_804 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_804)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_805 : validRep representative_805 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_805)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_806 : validRep representative_806 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_806)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_807 : validRep representative_807 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_807)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_808 : validRep representative_808 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_808)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_809 : validRep representative_809 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_809)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_810 : validRep representative_810 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_810)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_811 : validRep representative_811 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_811)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_812 : validRep representative_812 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_812)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_813 : validRep representative_813 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_813)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_814 : validRep representative_814 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_814)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_815 : validRep representative_815 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_815)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_816 : validRep representative_816 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_816)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_817 : validRep representative_817 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_817)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_818 : validRep representative_818 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_818)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_819 : validRep representative_819 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_819)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_820 : validRep representative_820 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_820)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_821 : validRep representative_821 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_821)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_822 : validRep representative_822 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_822)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_823 : validRep representative_823 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_823)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_824 : validRep representative_824 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_824)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_825 : validRep representative_825 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_825)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_826 : validRep representative_826 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_826)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_827 : validRep representative_827 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_827)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_828 : validRep representative_828 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_828)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_829 : validRep representative_829 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_829)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_830 : validRep representative_830 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_830)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_831 : validRep representative_831 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_831)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
def tree_012 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 800 (QuarticIntegerRepresentativeTree.Tree.branch 784 (QuarticIntegerRepresentativeTree.Tree.branch 776 (QuarticIntegerRepresentativeTree.Tree.branch 772 (QuarticIntegerRepresentativeTree.Tree.branch 770 (QuarticIntegerRepresentativeTree.Tree.branch 769 (QuarticIntegerRepresentativeTree.Tree.leaf 768 representative_768) (QuarticIntegerRepresentativeTree.Tree.leaf 769 representative_769)) (QuarticIntegerRepresentativeTree.Tree.branch 771 (QuarticIntegerRepresentativeTree.Tree.leaf 770 representative_770) (QuarticIntegerRepresentativeTree.Tree.leaf 771 representative_771))) (QuarticIntegerRepresentativeTree.Tree.branch 774 (QuarticIntegerRepresentativeTree.Tree.branch 773 (QuarticIntegerRepresentativeTree.Tree.leaf 772 representative_772) (QuarticIntegerRepresentativeTree.Tree.leaf 773 representative_773)) (QuarticIntegerRepresentativeTree.Tree.branch 775 (QuarticIntegerRepresentativeTree.Tree.leaf 774 representative_774) (QuarticIntegerRepresentativeTree.Tree.leaf 775 representative_775)))) (QuarticIntegerRepresentativeTree.Tree.branch 780 (QuarticIntegerRepresentativeTree.Tree.branch 778 (QuarticIntegerRepresentativeTree.Tree.branch 777 (QuarticIntegerRepresentativeTree.Tree.leaf 776 representative_776) (QuarticIntegerRepresentativeTree.Tree.leaf 777 representative_777)) (QuarticIntegerRepresentativeTree.Tree.branch 779 (QuarticIntegerRepresentativeTree.Tree.leaf 778 representative_778) (QuarticIntegerRepresentativeTree.Tree.leaf 779 representative_779))) (QuarticIntegerRepresentativeTree.Tree.branch 782 (QuarticIntegerRepresentativeTree.Tree.branch 781 (QuarticIntegerRepresentativeTree.Tree.leaf 780 representative_780) (QuarticIntegerRepresentativeTree.Tree.leaf 781 representative_781)) (QuarticIntegerRepresentativeTree.Tree.branch 783 (QuarticIntegerRepresentativeTree.Tree.leaf 782 representative_782) (QuarticIntegerRepresentativeTree.Tree.leaf 783 representative_783))))) (QuarticIntegerRepresentativeTree.Tree.branch 792 (QuarticIntegerRepresentativeTree.Tree.branch 788 (QuarticIntegerRepresentativeTree.Tree.branch 786 (QuarticIntegerRepresentativeTree.Tree.branch 785 (QuarticIntegerRepresentativeTree.Tree.leaf 784 representative_784) (QuarticIntegerRepresentativeTree.Tree.leaf 785 representative_785)) (QuarticIntegerRepresentativeTree.Tree.branch 787 (QuarticIntegerRepresentativeTree.Tree.leaf 786 representative_786) (QuarticIntegerRepresentativeTree.Tree.leaf 787 representative_787))) (QuarticIntegerRepresentativeTree.Tree.branch 790 (QuarticIntegerRepresentativeTree.Tree.branch 789 (QuarticIntegerRepresentativeTree.Tree.leaf 788 representative_788) (QuarticIntegerRepresentativeTree.Tree.leaf 789 representative_789)) (QuarticIntegerRepresentativeTree.Tree.branch 791 (QuarticIntegerRepresentativeTree.Tree.leaf 790 representative_790) (QuarticIntegerRepresentativeTree.Tree.leaf 791 representative_791)))) (QuarticIntegerRepresentativeTree.Tree.branch 796 (QuarticIntegerRepresentativeTree.Tree.branch 794 (QuarticIntegerRepresentativeTree.Tree.branch 793 (QuarticIntegerRepresentativeTree.Tree.leaf 792 representative_792) (QuarticIntegerRepresentativeTree.Tree.leaf 793 representative_793)) (QuarticIntegerRepresentativeTree.Tree.branch 795 (QuarticIntegerRepresentativeTree.Tree.leaf 794 representative_794) (QuarticIntegerRepresentativeTree.Tree.leaf 795 representative_795))) (QuarticIntegerRepresentativeTree.Tree.branch 798 (QuarticIntegerRepresentativeTree.Tree.branch 797 (QuarticIntegerRepresentativeTree.Tree.leaf 796 representative_796) (QuarticIntegerRepresentativeTree.Tree.leaf 797 representative_797)) (QuarticIntegerRepresentativeTree.Tree.branch 799 (QuarticIntegerRepresentativeTree.Tree.leaf 798 representative_798) (QuarticIntegerRepresentativeTree.Tree.leaf 799 representative_799)))))) (QuarticIntegerRepresentativeTree.Tree.branch 816 (QuarticIntegerRepresentativeTree.Tree.branch 808 (QuarticIntegerRepresentativeTree.Tree.branch 804 (QuarticIntegerRepresentativeTree.Tree.branch 802 (QuarticIntegerRepresentativeTree.Tree.branch 801 (QuarticIntegerRepresentativeTree.Tree.leaf 800 representative_800) (QuarticIntegerRepresentativeTree.Tree.leaf 801 representative_801)) (QuarticIntegerRepresentativeTree.Tree.branch 803 (QuarticIntegerRepresentativeTree.Tree.leaf 802 representative_802) (QuarticIntegerRepresentativeTree.Tree.leaf 803 representative_803))) (QuarticIntegerRepresentativeTree.Tree.branch 806 (QuarticIntegerRepresentativeTree.Tree.branch 805 (QuarticIntegerRepresentativeTree.Tree.leaf 804 representative_804) (QuarticIntegerRepresentativeTree.Tree.leaf 805 representative_805)) (QuarticIntegerRepresentativeTree.Tree.branch 807 (QuarticIntegerRepresentativeTree.Tree.leaf 806 representative_806) (QuarticIntegerRepresentativeTree.Tree.leaf 807 representative_807)))) (QuarticIntegerRepresentativeTree.Tree.branch 812 (QuarticIntegerRepresentativeTree.Tree.branch 810 (QuarticIntegerRepresentativeTree.Tree.branch 809 (QuarticIntegerRepresentativeTree.Tree.leaf 808 representative_808) (QuarticIntegerRepresentativeTree.Tree.leaf 809 representative_809)) (QuarticIntegerRepresentativeTree.Tree.branch 811 (QuarticIntegerRepresentativeTree.Tree.leaf 810 representative_810) (QuarticIntegerRepresentativeTree.Tree.leaf 811 representative_811))) (QuarticIntegerRepresentativeTree.Tree.branch 814 (QuarticIntegerRepresentativeTree.Tree.branch 813 (QuarticIntegerRepresentativeTree.Tree.leaf 812 representative_812) (QuarticIntegerRepresentativeTree.Tree.leaf 813 representative_813)) (QuarticIntegerRepresentativeTree.Tree.branch 815 (QuarticIntegerRepresentativeTree.Tree.leaf 814 representative_814) (QuarticIntegerRepresentativeTree.Tree.leaf 815 representative_815))))) (QuarticIntegerRepresentativeTree.Tree.branch 824 (QuarticIntegerRepresentativeTree.Tree.branch 820 (QuarticIntegerRepresentativeTree.Tree.branch 818 (QuarticIntegerRepresentativeTree.Tree.branch 817 (QuarticIntegerRepresentativeTree.Tree.leaf 816 representative_816) (QuarticIntegerRepresentativeTree.Tree.leaf 817 representative_817)) (QuarticIntegerRepresentativeTree.Tree.branch 819 (QuarticIntegerRepresentativeTree.Tree.leaf 818 representative_818) (QuarticIntegerRepresentativeTree.Tree.leaf 819 representative_819))) (QuarticIntegerRepresentativeTree.Tree.branch 822 (QuarticIntegerRepresentativeTree.Tree.branch 821 (QuarticIntegerRepresentativeTree.Tree.leaf 820 representative_820) (QuarticIntegerRepresentativeTree.Tree.leaf 821 representative_821)) (QuarticIntegerRepresentativeTree.Tree.branch 823 (QuarticIntegerRepresentativeTree.Tree.leaf 822 representative_822) (QuarticIntegerRepresentativeTree.Tree.leaf 823 representative_823)))) (QuarticIntegerRepresentativeTree.Tree.branch 828 (QuarticIntegerRepresentativeTree.Tree.branch 826 (QuarticIntegerRepresentativeTree.Tree.branch 825 (QuarticIntegerRepresentativeTree.Tree.leaf 824 representative_824) (QuarticIntegerRepresentativeTree.Tree.leaf 825 representative_825)) (QuarticIntegerRepresentativeTree.Tree.branch 827 (QuarticIntegerRepresentativeTree.Tree.leaf 826 representative_826) (QuarticIntegerRepresentativeTree.Tree.leaf 827 representative_827))) (QuarticIntegerRepresentativeTree.Tree.branch 830 (QuarticIntegerRepresentativeTree.Tree.branch 829 (QuarticIntegerRepresentativeTree.Tree.leaf 828 representative_828) (QuarticIntegerRepresentativeTree.Tree.leaf 829 representative_829)) (QuarticIntegerRepresentativeTree.Tree.branch 831 (QuarticIntegerRepresentativeTree.Tree.leaf 830 representative_830) (QuarticIntegerRepresentativeTree.Tree.leaf 831 representative_831)))))))
theorem accepted_012 : All validRep tree_012 := ⟨⟨⟨⟨⟨⟨coefficient_768,coefficient_769⟩,⟨coefficient_770,coefficient_771⟩⟩,⟨⟨coefficient_772,coefficient_773⟩,⟨coefficient_774,coefficient_775⟩⟩⟩,⟨⟨⟨coefficient_776,coefficient_777⟩,⟨coefficient_778,coefficient_779⟩⟩,⟨⟨coefficient_780,coefficient_781⟩,⟨coefficient_782,coefficient_783⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_784,coefficient_785⟩,⟨coefficient_786,coefficient_787⟩⟩,⟨⟨coefficient_788,coefficient_789⟩,⟨coefficient_790,coefficient_791⟩⟩⟩,⟨⟨⟨coefficient_792,coefficient_793⟩,⟨coefficient_794,coefficient_795⟩⟩,⟨⟨coefficient_796,coefficient_797⟩,⟨coefficient_798,coefficient_799⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_800,coefficient_801⟩,⟨coefficient_802,coefficient_803⟩⟩,⟨⟨coefficient_804,coefficient_805⟩,⟨coefficient_806,coefficient_807⟩⟩⟩,⟨⟨⟨coefficient_808,coefficient_809⟩,⟨coefficient_810,coefficient_811⟩⟩,⟨⟨coefficient_812,coefficient_813⟩,⟨coefficient_814,coefficient_815⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_816,coefficient_817⟩,⟨coefficient_818,coefficient_819⟩⟩,⟨⟨coefficient_820,coefficient_821⟩,⟨coefficient_822,coefficient_823⟩⟩⟩,⟨⟨⟨coefficient_824,coefficient_825⟩,⟨coefficient_826,coefficient_827⟩⟩,⟨⟨coefficient_828,coefficient_829⟩,⟨coefficient_830,coefficient_831⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

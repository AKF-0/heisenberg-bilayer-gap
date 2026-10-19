import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_768 : Rep := ⟨![0,9,3,20],201⟩
def representative_769 : Rep := ⟨![0,9,3,21],305⟩
def representative_770 : Rep := ⟨![0,9,3,22],508⟩
def representative_771 : Rep := ⟨![0,9,3,23],293⟩
def representative_772 : Rep := ⟨![0,9,3,25],150⟩
def representative_773 : Rep := ⟨![0,9,3,26],320⟩
def representative_774 : Rep := ⟨![0,9,4,13],436⟩
def representative_775 : Rep := ⟨![0,9,4,14],162⟩
def representative_776 : Rep := ⟨![0,9,4,15],423⟩
def representative_777 : Rep := ⟨![0,9,4,16],383⟩
def representative_778 : Rep := ⟨![0,9,4,17],188⟩
def representative_779 : Rep := ⟨![0,9,4,18],323⟩
def representative_780 : Rep := ⟨![0,9,4,19],258⟩
def representative_781 : Rep := ⟨![0,9,4,20],121⟩
def representative_782 : Rep := ⟨![0,9,4,21],315⟩
def representative_783 : Rep := ⟨![0,9,4,22],268⟩
def representative_784 : Rep := ⟨![0,9,4,23],303⟩
def representative_785 : Rep := ⟨![0,9,4,24],454⟩
def representative_786 : Rep := ⟨![0,9,4,25],112⟩
def representative_787 : Rep := ⟨![0,9,4,26],326⟩
def representative_788 : Rep := ⟨![0,9,4,27],113⟩
def representative_789 : Rep := ⟨![0,9,4,29],464⟩
def representative_790 : Rep := ⟨![0,9,4,30],108⟩
def representative_791 : Rep := ⟨![0,9,4,31],463⟩
def representative_792 : Rep := ⟨![0,9,6,12],160⟩
def representative_793 : Rep := ⟨![0,9,6,15],343⟩
def representative_794 : Rep := ⟨![0,9,6,16],324⟩
def representative_795 : Rep := ⟨![0,9,6,17],188⟩
def representative_796 : Rep := ⟨![0,9,6,18],334⟩
def representative_797 : Rep := ⟨![0,9,6,19],258⟩
def representative_798 : Rep := ⟨![0,9,6,20],260⟩
def representative_799 : Rep := ⟨![0,9,6,21],302⟩
def representative_800 : Rep := ⟨![0,9,6,22],268⟩
def representative_801 : Rep := ⟨![0,9,6,23],278⟩
def representative_802 : Rep := ⟨![0,9,6,24],324⟩
def representative_803 : Rep := ⟨![0,9,6,25],255⟩
def representative_804 : Rep := ⟨![0,9,6,26],313⟩
def representative_805 : Rep := ⟨![0,9,6,27],256⟩
def representative_806 : Rep := ⟨![0,9,6,28],132⟩
def representative_807 : Rep := ⟨![0,9,6,29],346⟩
def representative_808 : Rep := ⟨![0,9,6,31],342⟩
def representative_809 : Rep := ⟨![0,9,12,21],312⟩
def representative_810 : Rep := ⟨![0,9,12,22],268⟩
def representative_811 : Rep := ⟨![0,9,12,23],299⟩
def representative_812 : Rep := ⟨![0,9,12,24],295⟩
def representative_813 : Rep := ⟨![0,9,12,25],266⟩
def representative_814 : Rep := ⟨![0,9,12,26],276⟩
def representative_815 : Rep := ⟨![0,9,12,27],270⟩
def representative_816 : Rep := ⟨![0,9,12,28],199⟩
def representative_817 : Rep := ⟨![0,9,12,29],311⟩
def representative_818 : Rep := ⟨![0,9,12,30],260⟩
def representative_819 : Rep := ⟨![0,9,12,31],298⟩
def representative_820 : Rep := ⟨![0,9,13,20],247⟩
def representative_821 : Rep := ⟨![0,9,13,22],246⟩
def representative_822 : Rep := ⟨![0,9,13,23],508⟩
def representative_823 : Rep := ⟨![0,9,13,24],271⟩
def representative_824 : Rep := ⟨![0,9,13,25],249⟩
def representative_825 : Rep := ⟨![0,9,13,26],508⟩
def representative_826 : Rep := ⟨![0,9,13,27],276⟩
def representative_827 : Rep := ⟨![0,9,13,28],316⟩
def representative_828 : Rep := ⟨![0,9,13,30],306⟩
def representative_829 : Rep := ⟨![0,9,13,31],268⟩
def representative_830 : Rep := ⟨![0,9,14,20],268⟩
def representative_831 : Rep := ⟨![0,9,14,23],508⟩
theorem coefficient_768 : validRep representative_768 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_768)=dictionary32.getD 201 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_201]
  decide +kernel
theorem coefficient_769 : validRep representative_769 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_769)=dictionary32.getD 305 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_305]
  decide +kernel
theorem coefficient_770 : validRep representative_770 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_770)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_771 : validRep representative_771 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_771)=dictionary32.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_772 : validRep representative_772 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_772)=dictionary32.getD 150 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_150]
  decide +kernel
theorem coefficient_773 : validRep representative_773 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_773)=dictionary32.getD 320 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_320]
  decide +kernel
theorem coefficient_774 : validRep representative_774 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_774)=dictionary32.getD 436 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_436]
  decide +kernel
theorem coefficient_775 : validRep representative_775 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_775)=dictionary32.getD 162 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_162]
  decide +kernel
theorem coefficient_776 : validRep representative_776 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_776)=dictionary32.getD 423 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_423]
  decide +kernel
theorem coefficient_777 : validRep representative_777 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_777)=dictionary32.getD 383 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_383]
  decide +kernel
theorem coefficient_778 : validRep representative_778 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_778)=dictionary32.getD 188 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_188]
  decide +kernel
theorem coefficient_779 : validRep representative_779 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_779)=dictionary32.getD 323 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_323]
  decide +kernel
theorem coefficient_780 : validRep representative_780 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_780)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_781 : validRep representative_781 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_781)=dictionary32.getD 121 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_121]
  decide +kernel
theorem coefficient_782 : validRep representative_782 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_782)=dictionary32.getD 315 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_315]
  decide +kernel
theorem coefficient_783 : validRep representative_783 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_783)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_784 : validRep representative_784 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_784)=dictionary32.getD 303 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_303]
  decide +kernel
theorem coefficient_785 : validRep representative_785 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_785)=dictionary32.getD 454 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_454]
  decide +kernel
theorem coefficient_786 : validRep representative_786 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_786)=dictionary32.getD 112 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_112]
  decide +kernel
theorem coefficient_787 : validRep representative_787 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_787)=dictionary32.getD 326 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_326]
  decide +kernel
theorem coefficient_788 : validRep representative_788 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_788)=dictionary32.getD 113 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_113]
  decide +kernel
theorem coefficient_789 : validRep representative_789 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_789)=dictionary32.getD 464 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_464]
  decide +kernel
theorem coefficient_790 : validRep representative_790 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_790)=dictionary32.getD 108 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_108]
  decide +kernel
theorem coefficient_791 : validRep representative_791 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_791)=dictionary32.getD 463 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_463]
  decide +kernel
theorem coefficient_792 : validRep representative_792 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_792)=dictionary32.getD 160 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_160]
  decide +kernel
theorem coefficient_793 : validRep representative_793 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_793)=dictionary32.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_794 : validRep representative_794 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_794)=dictionary32.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_795 : validRep representative_795 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_795)=dictionary32.getD 188 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_188]
  decide +kernel
theorem coefficient_796 : validRep representative_796 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_796)=dictionary32.getD 334 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_334]
  decide +kernel
theorem coefficient_797 : validRep representative_797 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_797)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_798 : validRep representative_798 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_798)=dictionary32.getD 260 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_260]
  decide +kernel
theorem coefficient_799 : validRep representative_799 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_799)=dictionary32.getD 302 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_302]
  decide +kernel
theorem coefficient_800 : validRep representative_800 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_800)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_801 : validRep representative_801 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_801)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_802 : validRep representative_802 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_802)=dictionary32.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_803 : validRep representative_803 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_803)=dictionary32.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_804 : validRep representative_804 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_804)=dictionary32.getD 313 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_313]
  decide +kernel
theorem coefficient_805 : validRep representative_805 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_805)=dictionary32.getD 256 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_256]
  decide +kernel
theorem coefficient_806 : validRep representative_806 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_806)=dictionary32.getD 132 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_132]
  decide +kernel
theorem coefficient_807 : validRep representative_807 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_807)=dictionary32.getD 346 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_346]
  decide +kernel
theorem coefficient_808 : validRep representative_808 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_808)=dictionary32.getD 342 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_342]
  decide +kernel
theorem coefficient_809 : validRep representative_809 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_809)=dictionary32.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_810 : validRep representative_810 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_810)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_811 : validRep representative_811 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_811)=dictionary32.getD 299 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_299]
  decide +kernel
theorem coefficient_812 : validRep representative_812 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_812)=dictionary32.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_813 : validRep representative_813 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_813)=dictionary32.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_814 : validRep representative_814 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_814)=dictionary32.getD 276 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_276]
  decide +kernel
theorem coefficient_815 : validRep representative_815 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_815)=dictionary32.getD 270 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_270]
  decide +kernel
theorem coefficient_816 : validRep representative_816 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_816)=dictionary32.getD 199 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_199]
  decide +kernel
theorem coefficient_817 : validRep representative_817 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_817)=dictionary32.getD 311 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_311]
  decide +kernel
theorem coefficient_818 : validRep representative_818 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_818)=dictionary32.getD 260 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_260]
  decide +kernel
theorem coefficient_819 : validRep representative_819 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_819)=dictionary32.getD 298 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_298]
  decide +kernel
theorem coefficient_820 : validRep representative_820 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_820)=dictionary32.getD 247 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_247]
  decide +kernel
theorem coefficient_821 : validRep representative_821 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_821)=dictionary32.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_822 : validRep representative_822 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_822)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_823 : validRep representative_823 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_823)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_824 : validRep representative_824 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_824)=dictionary32.getD 249 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_249]
  decide +kernel
theorem coefficient_825 : validRep representative_825 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_825)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_826 : validRep representative_826 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_826)=dictionary32.getD 276 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_276]
  decide +kernel
theorem coefficient_827 : validRep representative_827 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_827)=dictionary32.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_828 : validRep representative_828 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_828)=dictionary32.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_829 : validRep representative_829 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_829)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_830 : validRep representative_830 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_830)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_831 : validRep representative_831 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_831)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_012 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 800 (QuarticIntegerRepresentativeTree.Tree.branch 784 (QuarticIntegerRepresentativeTree.Tree.branch 776 (QuarticIntegerRepresentativeTree.Tree.branch 772 (QuarticIntegerRepresentativeTree.Tree.branch 770 (QuarticIntegerRepresentativeTree.Tree.branch 769 (QuarticIntegerRepresentativeTree.Tree.leaf 768 representative_768) (QuarticIntegerRepresentativeTree.Tree.leaf 769 representative_769)) (QuarticIntegerRepresentativeTree.Tree.branch 771 (QuarticIntegerRepresentativeTree.Tree.leaf 770 representative_770) (QuarticIntegerRepresentativeTree.Tree.leaf 771 representative_771))) (QuarticIntegerRepresentativeTree.Tree.branch 774 (QuarticIntegerRepresentativeTree.Tree.branch 773 (QuarticIntegerRepresentativeTree.Tree.leaf 772 representative_772) (QuarticIntegerRepresentativeTree.Tree.leaf 773 representative_773)) (QuarticIntegerRepresentativeTree.Tree.branch 775 (QuarticIntegerRepresentativeTree.Tree.leaf 774 representative_774) (QuarticIntegerRepresentativeTree.Tree.leaf 775 representative_775)))) (QuarticIntegerRepresentativeTree.Tree.branch 780 (QuarticIntegerRepresentativeTree.Tree.branch 778 (QuarticIntegerRepresentativeTree.Tree.branch 777 (QuarticIntegerRepresentativeTree.Tree.leaf 776 representative_776) (QuarticIntegerRepresentativeTree.Tree.leaf 777 representative_777)) (QuarticIntegerRepresentativeTree.Tree.branch 779 (QuarticIntegerRepresentativeTree.Tree.leaf 778 representative_778) (QuarticIntegerRepresentativeTree.Tree.leaf 779 representative_779))) (QuarticIntegerRepresentativeTree.Tree.branch 782 (QuarticIntegerRepresentativeTree.Tree.branch 781 (QuarticIntegerRepresentativeTree.Tree.leaf 780 representative_780) (QuarticIntegerRepresentativeTree.Tree.leaf 781 representative_781)) (QuarticIntegerRepresentativeTree.Tree.branch 783 (QuarticIntegerRepresentativeTree.Tree.leaf 782 representative_782) (QuarticIntegerRepresentativeTree.Tree.leaf 783 representative_783))))) (QuarticIntegerRepresentativeTree.Tree.branch 792 (QuarticIntegerRepresentativeTree.Tree.branch 788 (QuarticIntegerRepresentativeTree.Tree.branch 786 (QuarticIntegerRepresentativeTree.Tree.branch 785 (QuarticIntegerRepresentativeTree.Tree.leaf 784 representative_784) (QuarticIntegerRepresentativeTree.Tree.leaf 785 representative_785)) (QuarticIntegerRepresentativeTree.Tree.branch 787 (QuarticIntegerRepresentativeTree.Tree.leaf 786 representative_786) (QuarticIntegerRepresentativeTree.Tree.leaf 787 representative_787))) (QuarticIntegerRepresentativeTree.Tree.branch 790 (QuarticIntegerRepresentativeTree.Tree.branch 789 (QuarticIntegerRepresentativeTree.Tree.leaf 788 representative_788) (QuarticIntegerRepresentativeTree.Tree.leaf 789 representative_789)) (QuarticIntegerRepresentativeTree.Tree.branch 791 (QuarticIntegerRepresentativeTree.Tree.leaf 790 representative_790) (QuarticIntegerRepresentativeTree.Tree.leaf 791 representative_791)))) (QuarticIntegerRepresentativeTree.Tree.branch 796 (QuarticIntegerRepresentativeTree.Tree.branch 794 (QuarticIntegerRepresentativeTree.Tree.branch 793 (QuarticIntegerRepresentativeTree.Tree.leaf 792 representative_792) (QuarticIntegerRepresentativeTree.Tree.leaf 793 representative_793)) (QuarticIntegerRepresentativeTree.Tree.branch 795 (QuarticIntegerRepresentativeTree.Tree.leaf 794 representative_794) (QuarticIntegerRepresentativeTree.Tree.leaf 795 representative_795))) (QuarticIntegerRepresentativeTree.Tree.branch 798 (QuarticIntegerRepresentativeTree.Tree.branch 797 (QuarticIntegerRepresentativeTree.Tree.leaf 796 representative_796) (QuarticIntegerRepresentativeTree.Tree.leaf 797 representative_797)) (QuarticIntegerRepresentativeTree.Tree.branch 799 (QuarticIntegerRepresentativeTree.Tree.leaf 798 representative_798) (QuarticIntegerRepresentativeTree.Tree.leaf 799 representative_799)))))) (QuarticIntegerRepresentativeTree.Tree.branch 816 (QuarticIntegerRepresentativeTree.Tree.branch 808 (QuarticIntegerRepresentativeTree.Tree.branch 804 (QuarticIntegerRepresentativeTree.Tree.branch 802 (QuarticIntegerRepresentativeTree.Tree.branch 801 (QuarticIntegerRepresentativeTree.Tree.leaf 800 representative_800) (QuarticIntegerRepresentativeTree.Tree.leaf 801 representative_801)) (QuarticIntegerRepresentativeTree.Tree.branch 803 (QuarticIntegerRepresentativeTree.Tree.leaf 802 representative_802) (QuarticIntegerRepresentativeTree.Tree.leaf 803 representative_803))) (QuarticIntegerRepresentativeTree.Tree.branch 806 (QuarticIntegerRepresentativeTree.Tree.branch 805 (QuarticIntegerRepresentativeTree.Tree.leaf 804 representative_804) (QuarticIntegerRepresentativeTree.Tree.leaf 805 representative_805)) (QuarticIntegerRepresentativeTree.Tree.branch 807 (QuarticIntegerRepresentativeTree.Tree.leaf 806 representative_806) (QuarticIntegerRepresentativeTree.Tree.leaf 807 representative_807)))) (QuarticIntegerRepresentativeTree.Tree.branch 812 (QuarticIntegerRepresentativeTree.Tree.branch 810 (QuarticIntegerRepresentativeTree.Tree.branch 809 (QuarticIntegerRepresentativeTree.Tree.leaf 808 representative_808) (QuarticIntegerRepresentativeTree.Tree.leaf 809 representative_809)) (QuarticIntegerRepresentativeTree.Tree.branch 811 (QuarticIntegerRepresentativeTree.Tree.leaf 810 representative_810) (QuarticIntegerRepresentativeTree.Tree.leaf 811 representative_811))) (QuarticIntegerRepresentativeTree.Tree.branch 814 (QuarticIntegerRepresentativeTree.Tree.branch 813 (QuarticIntegerRepresentativeTree.Tree.leaf 812 representative_812) (QuarticIntegerRepresentativeTree.Tree.leaf 813 representative_813)) (QuarticIntegerRepresentativeTree.Tree.branch 815 (QuarticIntegerRepresentativeTree.Tree.leaf 814 representative_814) (QuarticIntegerRepresentativeTree.Tree.leaf 815 representative_815))))) (QuarticIntegerRepresentativeTree.Tree.branch 824 (QuarticIntegerRepresentativeTree.Tree.branch 820 (QuarticIntegerRepresentativeTree.Tree.branch 818 (QuarticIntegerRepresentativeTree.Tree.branch 817 (QuarticIntegerRepresentativeTree.Tree.leaf 816 representative_816) (QuarticIntegerRepresentativeTree.Tree.leaf 817 representative_817)) (QuarticIntegerRepresentativeTree.Tree.branch 819 (QuarticIntegerRepresentativeTree.Tree.leaf 818 representative_818) (QuarticIntegerRepresentativeTree.Tree.leaf 819 representative_819))) (QuarticIntegerRepresentativeTree.Tree.branch 822 (QuarticIntegerRepresentativeTree.Tree.branch 821 (QuarticIntegerRepresentativeTree.Tree.leaf 820 representative_820) (QuarticIntegerRepresentativeTree.Tree.leaf 821 representative_821)) (QuarticIntegerRepresentativeTree.Tree.branch 823 (QuarticIntegerRepresentativeTree.Tree.leaf 822 representative_822) (QuarticIntegerRepresentativeTree.Tree.leaf 823 representative_823)))) (QuarticIntegerRepresentativeTree.Tree.branch 828 (QuarticIntegerRepresentativeTree.Tree.branch 826 (QuarticIntegerRepresentativeTree.Tree.branch 825 (QuarticIntegerRepresentativeTree.Tree.leaf 824 representative_824) (QuarticIntegerRepresentativeTree.Tree.leaf 825 representative_825)) (QuarticIntegerRepresentativeTree.Tree.branch 827 (QuarticIntegerRepresentativeTree.Tree.leaf 826 representative_826) (QuarticIntegerRepresentativeTree.Tree.leaf 827 representative_827))) (QuarticIntegerRepresentativeTree.Tree.branch 830 (QuarticIntegerRepresentativeTree.Tree.branch 829 (QuarticIntegerRepresentativeTree.Tree.leaf 828 representative_828) (QuarticIntegerRepresentativeTree.Tree.leaf 829 representative_829)) (QuarticIntegerRepresentativeTree.Tree.branch 831 (QuarticIntegerRepresentativeTree.Tree.leaf 830 representative_830) (QuarticIntegerRepresentativeTree.Tree.leaf 831 representative_831)))))))
theorem accepted_012 : All validRep tree_012 := ⟨⟨⟨⟨⟨⟨coefficient_768,coefficient_769⟩,⟨coefficient_770,coefficient_771⟩⟩,⟨⟨coefficient_772,coefficient_773⟩,⟨coefficient_774,coefficient_775⟩⟩⟩,⟨⟨⟨coefficient_776,coefficient_777⟩,⟨coefficient_778,coefficient_779⟩⟩,⟨⟨coefficient_780,coefficient_781⟩,⟨coefficient_782,coefficient_783⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_784,coefficient_785⟩,⟨coefficient_786,coefficient_787⟩⟩,⟨⟨coefficient_788,coefficient_789⟩,⟨coefficient_790,coefficient_791⟩⟩⟩,⟨⟨⟨coefficient_792,coefficient_793⟩,⟨coefficient_794,coefficient_795⟩⟩,⟨⟨coefficient_796,coefficient_797⟩,⟨coefficient_798,coefficient_799⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_800,coefficient_801⟩,⟨coefficient_802,coefficient_803⟩⟩,⟨⟨coefficient_804,coefficient_805⟩,⟨coefficient_806,coefficient_807⟩⟩⟩,⟨⟨⟨coefficient_808,coefficient_809⟩,⟨coefficient_810,coefficient_811⟩⟩,⟨⟨coefficient_812,coefficient_813⟩,⟨coefficient_814,coefficient_815⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_816,coefficient_817⟩,⟨coefficient_818,coefficient_819⟩⟩,⟨⟨coefficient_820,coefficient_821⟩,⟨coefficient_822,coefficient_823⟩⟩⟩,⟨⟨⟨coefficient_824,coefficient_825⟩,⟨coefficient_826,coefficient_827⟩⟩,⟨⟨coefficient_828,coefficient_829⟩,⟨coefficient_830,coefficient_831⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

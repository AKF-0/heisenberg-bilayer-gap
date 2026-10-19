import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_832 : Rep := ⟨![0,2,16,40],209⟩
def representative_833 : Rep := ⟨![0,2,16,41],261⟩
def representative_834 : Rep := ⟨![0,2,16,42],237⟩
def representative_835 : Rep := ⟨![0,2,16,43],462⟩
def representative_836 : Rep := ⟨![0,2,16,44],462⟩
def representative_837 : Rep := ⟨![0,2,16,45],462⟩
def representative_838 : Rep := ⟨![0,2,16,46],462⟩
def representative_839 : Rep := ⟨![0,2,16,47],261⟩
def representative_840 : Rep := ⟨![0,2,16,48],327⟩
def representative_841 : Rep := ⟨![0,2,16,49],182⟩
def representative_842 : Rep := ⟨![0,2,16,50],278⟩
def representative_843 : Rep := ⟨![0,2,16,51],234⟩
def representative_844 : Rep := ⟨![0,2,16,52],462⟩
def representative_845 : Rep := ⟨![0,2,16,53],462⟩
def representative_846 : Rep := ⟨![0,2,16,54],265⟩
def representative_847 : Rep := ⟨![0,2,16,55],184⟩
def representative_848 : Rep := ⟨![0,2,17,19],306⟩
def representative_849 : Rep := ⟨![0,2,17,20],228⟩
def representative_850 : Rep := ⟨![0,2,17,21],462⟩
def representative_851 : Rep := ⟨![0,2,17,24],315⟩
def representative_852 : Rep := ⟨![0,2,17,27],222⟩
def representative_853 : Rep := ⟨![0,2,17,28],462⟩
def representative_854 : Rep := ⟨![0,2,17,29],462⟩
def representative_855 : Rep := ⟨![0,2,17,32],223⟩
def representative_856 : Rep := ⟨![0,2,17,35],462⟩
def representative_857 : Rep := ⟨![0,2,17,36],462⟩
def representative_858 : Rep := ⟨![0,2,17,37],462⟩
def representative_859 : Rep := ⟨![0,2,17,40],265⟩
def representative_860 : Rep := ⟨![0,2,17,41],226⟩
def representative_861 : Rep := ⟨![0,2,17,43],235⟩
def representative_862 : Rep := ⟨![0,2,17,44],462⟩
def representative_863 : Rep := ⟨![0,2,17,45],462⟩
def representative_864 : Rep := ⟨![0,2,17,49],306⟩
def representative_865 : Rep := ⟨![0,2,17,51],289⟩
def representative_866 : Rep := ⟨![0,2,17,52],234⟩
def representative_867 : Rep := ⟨![0,2,17,53],462⟩
def representative_868 : Rep := ⟨![0,2,19,21],462⟩
def representative_869 : Rep := ⟨![0,2,19,22],462⟩
def representative_870 : Rep := ⟨![0,2,19,23],462⟩
def representative_871 : Rep := ⟨![0,2,19,24],462⟩
def representative_872 : Rep := ⟨![0,2,19,25],235⟩
def representative_873 : Rep := ⟨![0,2,19,26],265⟩
def representative_874 : Rep := ⟨![0,2,19,28],462⟩
def representative_875 : Rep := ⟨![0,2,19,29],462⟩
def representative_876 : Rep := ⟨![0,2,19,30],462⟩
def representative_877 : Rep := ⟨![0,2,19,31],462⟩
def representative_878 : Rep := ⟨![0,2,19,32],462⟩
def representative_879 : Rep := ⟨![0,2,19,33],462⟩
def representative_880 : Rep := ⟨![0,2,19,34],237⟩
def representative_881 : Rep := ⟨![0,2,19,36],462⟩
def representative_882 : Rep := ⟨![0,2,19,37],462⟩
def representative_883 : Rep := ⟨![0,2,19,38],462⟩
def representative_884 : Rep := ⟨![0,2,19,39],462⟩
def representative_885 : Rep := ⟨![0,2,19,40],462⟩
def representative_886 : Rep := ⟨![0,2,19,41],235⟩
def representative_887 : Rep := ⟨![0,2,19,42],265⟩
def representative_888 : Rep := ⟨![0,2,19,43],235⟩
def representative_889 : Rep := ⟨![0,2,19,44],462⟩
def representative_890 : Rep := ⟨![0,2,19,45],462⟩
def representative_891 : Rep := ⟨![0,2,19,46],462⟩
def representative_892 : Rep := ⟨![0,2,19,47],462⟩
def representative_893 : Rep := ⟨![0,2,19,51],289⟩
def representative_894 : Rep := ⟨![0,2,19,52],234⟩
def representative_895 : Rep := ⟨![0,2,19,53],462⟩
theorem coefficient_832 : validRep representative_832 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_832)=dictionary64.getD 209 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_209]
  decide +kernel
theorem coefficient_833 : validRep representative_833 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_833)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_834 : validRep representative_834 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_834)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_835 : validRep representative_835 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_835)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_836 : validRep representative_836 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_836)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_837 : validRep representative_837 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_837)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_838 : validRep representative_838 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_838)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_839 : validRep representative_839 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_839)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_840 : validRep representative_840 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_840)=dictionary64.getD 327 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_327]
  decide +kernel
theorem coefficient_841 : validRep representative_841 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_841)=dictionary64.getD 182 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_182]
  decide +kernel
theorem coefficient_842 : validRep representative_842 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_842)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_843 : validRep representative_843 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_843)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_844 : validRep representative_844 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_844)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_845 : validRep representative_845 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_845)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_846 : validRep representative_846 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_846)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_847 : validRep representative_847 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_847)=dictionary64.getD 184 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_184]
  decide +kernel
theorem coefficient_848 : validRep representative_848 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_848)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_849 : validRep representative_849 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_849)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_850 : validRep representative_850 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_850)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_851 : validRep representative_851 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_851)=dictionary64.getD 315 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_315]
  decide +kernel
theorem coefficient_852 : validRep representative_852 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_852)=dictionary64.getD 222 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_222]
  decide +kernel
theorem coefficient_853 : validRep representative_853 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_853)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_854 : validRep representative_854 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_854)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_855 : validRep representative_855 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_855)=dictionary64.getD 223 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_223]
  decide +kernel
theorem coefficient_856 : validRep representative_856 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_856)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_857 : validRep representative_857 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_857)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_858 : validRep representative_858 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_858)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_859 : validRep representative_859 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_859)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_860 : validRep representative_860 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_860)=dictionary64.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_861 : validRep representative_861 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_861)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_862 : validRep representative_862 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_862)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_863 : validRep representative_863 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_863)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_864 : validRep representative_864 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_864)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_865 : validRep representative_865 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_865)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_866 : validRep representative_866 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_866)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_867 : validRep representative_867 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_867)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_868 : validRep representative_868 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_868)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_869 : validRep representative_869 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_869)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_870 : validRep representative_870 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_870)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_871 : validRep representative_871 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_871)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_872 : validRep representative_872 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_872)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_873 : validRep representative_873 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_873)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_874 : validRep representative_874 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_874)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_875 : validRep representative_875 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_875)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_876 : validRep representative_876 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_876)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_877 : validRep representative_877 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_877)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_878 : validRep representative_878 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_878)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_879 : validRep representative_879 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_879)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_880 : validRep representative_880 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_880)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_881 : validRep representative_881 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_881)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_882 : validRep representative_882 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_882)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_883 : validRep representative_883 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_883)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_884 : validRep representative_884 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_884)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_885 : validRep representative_885 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_885)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_886 : validRep representative_886 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_886)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_887 : validRep representative_887 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_887)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_888 : validRep representative_888 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_888)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_889 : validRep representative_889 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_889)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_890 : validRep representative_890 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_890)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_891 : validRep representative_891 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_891)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_892 : validRep representative_892 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_892)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_893 : validRep representative_893 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_893)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_894 : validRep representative_894 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_894)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_895 : validRep representative_895 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_895)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_013 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 864 (QuarticIntegerRepresentativeTree.Tree.branch 848 (QuarticIntegerRepresentativeTree.Tree.branch 840 (QuarticIntegerRepresentativeTree.Tree.branch 836 (QuarticIntegerRepresentativeTree.Tree.branch 834 (QuarticIntegerRepresentativeTree.Tree.branch 833 (QuarticIntegerRepresentativeTree.Tree.leaf 832 representative_832) (QuarticIntegerRepresentativeTree.Tree.leaf 833 representative_833)) (QuarticIntegerRepresentativeTree.Tree.branch 835 (QuarticIntegerRepresentativeTree.Tree.leaf 834 representative_834) (QuarticIntegerRepresentativeTree.Tree.leaf 835 representative_835))) (QuarticIntegerRepresentativeTree.Tree.branch 838 (QuarticIntegerRepresentativeTree.Tree.branch 837 (QuarticIntegerRepresentativeTree.Tree.leaf 836 representative_836) (QuarticIntegerRepresentativeTree.Tree.leaf 837 representative_837)) (QuarticIntegerRepresentativeTree.Tree.branch 839 (QuarticIntegerRepresentativeTree.Tree.leaf 838 representative_838) (QuarticIntegerRepresentativeTree.Tree.leaf 839 representative_839)))) (QuarticIntegerRepresentativeTree.Tree.branch 844 (QuarticIntegerRepresentativeTree.Tree.branch 842 (QuarticIntegerRepresentativeTree.Tree.branch 841 (QuarticIntegerRepresentativeTree.Tree.leaf 840 representative_840) (QuarticIntegerRepresentativeTree.Tree.leaf 841 representative_841)) (QuarticIntegerRepresentativeTree.Tree.branch 843 (QuarticIntegerRepresentativeTree.Tree.leaf 842 representative_842) (QuarticIntegerRepresentativeTree.Tree.leaf 843 representative_843))) (QuarticIntegerRepresentativeTree.Tree.branch 846 (QuarticIntegerRepresentativeTree.Tree.branch 845 (QuarticIntegerRepresentativeTree.Tree.leaf 844 representative_844) (QuarticIntegerRepresentativeTree.Tree.leaf 845 representative_845)) (QuarticIntegerRepresentativeTree.Tree.branch 847 (QuarticIntegerRepresentativeTree.Tree.leaf 846 representative_846) (QuarticIntegerRepresentativeTree.Tree.leaf 847 representative_847))))) (QuarticIntegerRepresentativeTree.Tree.branch 856 (QuarticIntegerRepresentativeTree.Tree.branch 852 (QuarticIntegerRepresentativeTree.Tree.branch 850 (QuarticIntegerRepresentativeTree.Tree.branch 849 (QuarticIntegerRepresentativeTree.Tree.leaf 848 representative_848) (QuarticIntegerRepresentativeTree.Tree.leaf 849 representative_849)) (QuarticIntegerRepresentativeTree.Tree.branch 851 (QuarticIntegerRepresentativeTree.Tree.leaf 850 representative_850) (QuarticIntegerRepresentativeTree.Tree.leaf 851 representative_851))) (QuarticIntegerRepresentativeTree.Tree.branch 854 (QuarticIntegerRepresentativeTree.Tree.branch 853 (QuarticIntegerRepresentativeTree.Tree.leaf 852 representative_852) (QuarticIntegerRepresentativeTree.Tree.leaf 853 representative_853)) (QuarticIntegerRepresentativeTree.Tree.branch 855 (QuarticIntegerRepresentativeTree.Tree.leaf 854 representative_854) (QuarticIntegerRepresentativeTree.Tree.leaf 855 representative_855)))) (QuarticIntegerRepresentativeTree.Tree.branch 860 (QuarticIntegerRepresentativeTree.Tree.branch 858 (QuarticIntegerRepresentativeTree.Tree.branch 857 (QuarticIntegerRepresentativeTree.Tree.leaf 856 representative_856) (QuarticIntegerRepresentativeTree.Tree.leaf 857 representative_857)) (QuarticIntegerRepresentativeTree.Tree.branch 859 (QuarticIntegerRepresentativeTree.Tree.leaf 858 representative_858) (QuarticIntegerRepresentativeTree.Tree.leaf 859 representative_859))) (QuarticIntegerRepresentativeTree.Tree.branch 862 (QuarticIntegerRepresentativeTree.Tree.branch 861 (QuarticIntegerRepresentativeTree.Tree.leaf 860 representative_860) (QuarticIntegerRepresentativeTree.Tree.leaf 861 representative_861)) (QuarticIntegerRepresentativeTree.Tree.branch 863 (QuarticIntegerRepresentativeTree.Tree.leaf 862 representative_862) (QuarticIntegerRepresentativeTree.Tree.leaf 863 representative_863)))))) (QuarticIntegerRepresentativeTree.Tree.branch 880 (QuarticIntegerRepresentativeTree.Tree.branch 872 (QuarticIntegerRepresentativeTree.Tree.branch 868 (QuarticIntegerRepresentativeTree.Tree.branch 866 (QuarticIntegerRepresentativeTree.Tree.branch 865 (QuarticIntegerRepresentativeTree.Tree.leaf 864 representative_864) (QuarticIntegerRepresentativeTree.Tree.leaf 865 representative_865)) (QuarticIntegerRepresentativeTree.Tree.branch 867 (QuarticIntegerRepresentativeTree.Tree.leaf 866 representative_866) (QuarticIntegerRepresentativeTree.Tree.leaf 867 representative_867))) (QuarticIntegerRepresentativeTree.Tree.branch 870 (QuarticIntegerRepresentativeTree.Tree.branch 869 (QuarticIntegerRepresentativeTree.Tree.leaf 868 representative_868) (QuarticIntegerRepresentativeTree.Tree.leaf 869 representative_869)) (QuarticIntegerRepresentativeTree.Tree.branch 871 (QuarticIntegerRepresentativeTree.Tree.leaf 870 representative_870) (QuarticIntegerRepresentativeTree.Tree.leaf 871 representative_871)))) (QuarticIntegerRepresentativeTree.Tree.branch 876 (QuarticIntegerRepresentativeTree.Tree.branch 874 (QuarticIntegerRepresentativeTree.Tree.branch 873 (QuarticIntegerRepresentativeTree.Tree.leaf 872 representative_872) (QuarticIntegerRepresentativeTree.Tree.leaf 873 representative_873)) (QuarticIntegerRepresentativeTree.Tree.branch 875 (QuarticIntegerRepresentativeTree.Tree.leaf 874 representative_874) (QuarticIntegerRepresentativeTree.Tree.leaf 875 representative_875))) (QuarticIntegerRepresentativeTree.Tree.branch 878 (QuarticIntegerRepresentativeTree.Tree.branch 877 (QuarticIntegerRepresentativeTree.Tree.leaf 876 representative_876) (QuarticIntegerRepresentativeTree.Tree.leaf 877 representative_877)) (QuarticIntegerRepresentativeTree.Tree.branch 879 (QuarticIntegerRepresentativeTree.Tree.leaf 878 representative_878) (QuarticIntegerRepresentativeTree.Tree.leaf 879 representative_879))))) (QuarticIntegerRepresentativeTree.Tree.branch 888 (QuarticIntegerRepresentativeTree.Tree.branch 884 (QuarticIntegerRepresentativeTree.Tree.branch 882 (QuarticIntegerRepresentativeTree.Tree.branch 881 (QuarticIntegerRepresentativeTree.Tree.leaf 880 representative_880) (QuarticIntegerRepresentativeTree.Tree.leaf 881 representative_881)) (QuarticIntegerRepresentativeTree.Tree.branch 883 (QuarticIntegerRepresentativeTree.Tree.leaf 882 representative_882) (QuarticIntegerRepresentativeTree.Tree.leaf 883 representative_883))) (QuarticIntegerRepresentativeTree.Tree.branch 886 (QuarticIntegerRepresentativeTree.Tree.branch 885 (QuarticIntegerRepresentativeTree.Tree.leaf 884 representative_884) (QuarticIntegerRepresentativeTree.Tree.leaf 885 representative_885)) (QuarticIntegerRepresentativeTree.Tree.branch 887 (QuarticIntegerRepresentativeTree.Tree.leaf 886 representative_886) (QuarticIntegerRepresentativeTree.Tree.leaf 887 representative_887)))) (QuarticIntegerRepresentativeTree.Tree.branch 892 (QuarticIntegerRepresentativeTree.Tree.branch 890 (QuarticIntegerRepresentativeTree.Tree.branch 889 (QuarticIntegerRepresentativeTree.Tree.leaf 888 representative_888) (QuarticIntegerRepresentativeTree.Tree.leaf 889 representative_889)) (QuarticIntegerRepresentativeTree.Tree.branch 891 (QuarticIntegerRepresentativeTree.Tree.leaf 890 representative_890) (QuarticIntegerRepresentativeTree.Tree.leaf 891 representative_891))) (QuarticIntegerRepresentativeTree.Tree.branch 894 (QuarticIntegerRepresentativeTree.Tree.branch 893 (QuarticIntegerRepresentativeTree.Tree.leaf 892 representative_892) (QuarticIntegerRepresentativeTree.Tree.leaf 893 representative_893)) (QuarticIntegerRepresentativeTree.Tree.branch 895 (QuarticIntegerRepresentativeTree.Tree.leaf 894 representative_894) (QuarticIntegerRepresentativeTree.Tree.leaf 895 representative_895)))))))
theorem accepted_013 : All validRep tree_013 := ⟨⟨⟨⟨⟨⟨coefficient_832,coefficient_833⟩,⟨coefficient_834,coefficient_835⟩⟩,⟨⟨coefficient_836,coefficient_837⟩,⟨coefficient_838,coefficient_839⟩⟩⟩,⟨⟨⟨coefficient_840,coefficient_841⟩,⟨coefficient_842,coefficient_843⟩⟩,⟨⟨coefficient_844,coefficient_845⟩,⟨coefficient_846,coefficient_847⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_848,coefficient_849⟩,⟨coefficient_850,coefficient_851⟩⟩,⟨⟨coefficient_852,coefficient_853⟩,⟨coefficient_854,coefficient_855⟩⟩⟩,⟨⟨⟨coefficient_856,coefficient_857⟩,⟨coefficient_858,coefficient_859⟩⟩,⟨⟨coefficient_860,coefficient_861⟩,⟨coefficient_862,coefficient_863⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_864,coefficient_865⟩,⟨coefficient_866,coefficient_867⟩⟩,⟨⟨coefficient_868,coefficient_869⟩,⟨coefficient_870,coefficient_871⟩⟩⟩,⟨⟨⟨coefficient_872,coefficient_873⟩,⟨coefficient_874,coefficient_875⟩⟩,⟨⟨coefficient_876,coefficient_877⟩,⟨coefficient_878,coefficient_879⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_880,coefficient_881⟩,⟨coefficient_882,coefficient_883⟩⟩,⟨⟨coefficient_884,coefficient_885⟩,⟨coefficient_886,coefficient_887⟩⟩⟩,⟨⟨⟨coefficient_888,coefficient_889⟩,⟨coefficient_890,coefficient_891⟩⟩,⟨⟨coefficient_892,coefficient_893⟩,⟨coefficient_894,coefficient_895⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

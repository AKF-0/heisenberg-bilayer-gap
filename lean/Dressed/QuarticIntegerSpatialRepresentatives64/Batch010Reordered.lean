import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_640 : Rep := ⟨![0,2,8,35],462⟩
def representative_641 : Rep := ⟨![0,2,8,36],462⟩
def representative_642 : Rep := ⟨![0,2,8,37],462⟩
def representative_643 : Rep := ⟨![0,2,8,38],462⟩
def representative_644 : Rep := ⟨![0,2,8,39],462⟩
def representative_645 : Rep := ⟨![0,2,8,40],339⟩
def representative_646 : Rep := ⟨![0,2,8,41],191⟩
def representative_647 : Rep := ⟨![0,2,8,42],265⟩
def representative_648 : Rep := ⟨![0,2,8,43],235⟩
def representative_649 : Rep := ⟨![0,2,8,44],462⟩
def representative_650 : Rep := ⟨![0,2,8,45],462⟩
def representative_651 : Rep := ⟨![0,2,8,46],462⟩
def representative_652 : Rep := ⟨![0,2,8,47],193⟩
def representative_653 : Rep := ⟨![0,2,8,48],68⟩
def representative_654 : Rep := ⟨![0,2,8,49],388⟩
def representative_655 : Rep := ⟨![0,2,8,50],140⟩
def representative_656 : Rep := ⟨![0,2,8,51],289⟩
def representative_657 : Rep := ⟨![0,2,8,52],234⟩
def representative_658 : Rep := ⟨![0,2,8,53],462⟩
def representative_659 : Rep := ⟨![0,2,8,54],180⟩
def representative_660 : Rep := ⟨![0,2,8,55],387⟩
def representative_661 : Rep := ⟨![0,2,8,57],48⟩
def representative_662 : Rep := ⟨![0,2,8,58],409⟩
def representative_663 : Rep := ⟨![0,2,8,59],133⟩
def representative_664 : Rep := ⟨![0,2,8,60],289⟩
def representative_665 : Rep := ⟨![0,2,8,61],191⟩
def representative_666 : Rep := ⟨![0,2,8,62],387⟩
def representative_667 : Rep := ⟨![0,2,8,63],49⟩
def representative_668 : Rep := ⟨![0,2,9,11],402⟩
def representative_669 : Rep := ⟨![0,2,9,12],126⟩
def representative_670 : Rep := ⟨![0,2,9,13],288⟩
def representative_671 : Rep := ⟨![0,2,9,16],406⟩
def representative_672 : Rep := ⟨![0,2,9,19],98⟩
def representative_673 : Rep := ⟨![0,2,9,20],278⟩
def representative_674 : Rep := ⟨![0,2,9,21],462⟩
def representative_675 : Rep := ⟨![0,2,9,24],109⟩
def representative_676 : Rep := ⟨![0,2,9,25],379⟩
def representative_677 : Rep := ⟨![0,2,9,27],273⟩
def representative_678 : Rep := ⟨![0,2,9,28],462⟩
def representative_679 : Rep := ⟨![0,2,9,29],462⟩
def representative_680 : Rep := ⟨![0,2,9,32],261⟩
def representative_681 : Rep := ⟨![0,2,9,33],161⟩
def representative_682 : Rep := ⟨![0,2,9,35],462⟩
def representative_683 : Rep := ⟨![0,2,9,36],462⟩
def representative_684 : Rep := ⟨![0,2,9,37],462⟩
def representative_685 : Rep := ⟨![0,2,9,40],199⟩
def representative_686 : Rep := ⟨![0,2,9,41],288⟩
def representative_687 : Rep := ⟨![0,2,9,43],273⟩
def representative_688 : Rep := ⟨![0,2,9,44],462⟩
def representative_689 : Rep := ⟨![0,2,9,45],462⟩
def representative_690 : Rep := ⟨![0,2,9,48],348⟩
def representative_691 : Rep := ⟨![0,2,9,49],107⟩
def representative_692 : Rep := ⟨![0,2,9,51],149⟩
def representative_693 : Rep := ⟨![0,2,9,52],278⟩
def representative_694 : Rep := ⟨![0,2,9,53],462⟩
def representative_695 : Rep := ⟨![0,2,9,57],420⟩
def representative_696 : Rep := ⟨![0,2,9,59],378⟩
def representative_697 : Rep := ⟨![0,2,9,60],149⟩
def representative_698 : Rep := ⟨![0,2,9,61],288⟩
def representative_699 : Rep := ⟨![0,2,11,13],288⟩
def representative_700 : Rep := ⟨![0,2,11,14],233⟩
def representative_701 : Rep := ⟨![0,2,11,15],288⟩
def representative_702 : Rep := ⟨![0,2,11,16],288⟩
def representative_703 : Rep := ⟨![0,2,11,17],142⟩
theorem coefficient_640 : validRep representative_640 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_640)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_641 : validRep representative_641 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_641)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_642 : validRep representative_642 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_642)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_643 : validRep representative_643 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_643)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_644 : validRep representative_644 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_644)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_645 : validRep representative_645 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_645)=dictionary64.getD 339 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_339]
  decide +kernel
theorem coefficient_646 : validRep representative_646 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_646)=dictionary64.getD 191 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_191]
  decide +kernel
theorem coefficient_647 : validRep representative_647 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_647)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_648 : validRep representative_648 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_648)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_649 : validRep representative_649 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_649)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_650 : validRep representative_650 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_650)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_651 : validRep representative_651 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_651)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_652 : validRep representative_652 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_652)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_653 : validRep representative_653 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_653)=dictionary64.getD 68 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_68]
  decide +kernel
theorem coefficient_654 : validRep representative_654 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_654)=dictionary64.getD 388 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_388]
  decide +kernel
theorem coefficient_655 : validRep representative_655 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_655)=dictionary64.getD 140 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_140]
  decide +kernel
theorem coefficient_656 : validRep representative_656 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_656)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_657 : validRep representative_657 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_657)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_658 : validRep representative_658 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_658)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_659 : validRep representative_659 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_659)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_660 : validRep representative_660 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_660)=dictionary64.getD 387 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_387]
  decide +kernel
theorem coefficient_661 : validRep representative_661 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_661)=dictionary64.getD 48 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_48]
  decide +kernel
theorem coefficient_662 : validRep representative_662 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_662)=dictionary64.getD 409 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_409]
  decide +kernel
theorem coefficient_663 : validRep representative_663 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_663)=dictionary64.getD 133 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_133]
  decide +kernel
theorem coefficient_664 : validRep representative_664 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_664)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_665 : validRep representative_665 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_665)=dictionary64.getD 191 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_191]
  decide +kernel
theorem coefficient_666 : validRep representative_666 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_666)=dictionary64.getD 387 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_387]
  decide +kernel
theorem coefficient_667 : validRep representative_667 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_667)=dictionary64.getD 49 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_49]
  decide +kernel
theorem coefficient_668 : validRep representative_668 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_668)=dictionary64.getD 402 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_402]
  decide +kernel
theorem coefficient_669 : validRep representative_669 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_669)=dictionary64.getD 126 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_126]
  decide +kernel
theorem coefficient_670 : validRep representative_670 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_670)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_671 : validRep representative_671 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_671)=dictionary64.getD 406 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_406]
  decide +kernel
theorem coefficient_672 : validRep representative_672 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_672)=dictionary64.getD 98 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_98]
  decide +kernel
theorem coefficient_673 : validRep representative_673 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_673)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_674 : validRep representative_674 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_674)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_675 : validRep representative_675 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_675)=dictionary64.getD 109 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_109]
  decide +kernel
theorem coefficient_676 : validRep representative_676 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_676)=dictionary64.getD 379 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_379]
  decide +kernel
theorem coefficient_677 : validRep representative_677 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_677)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_678 : validRep representative_678 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_678)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_679 : validRep representative_679 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_679)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_680 : validRep representative_680 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_680)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_681 : validRep representative_681 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_681)=dictionary64.getD 161 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_161]
  decide +kernel
theorem coefficient_682 : validRep representative_682 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_682)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_683 : validRep representative_683 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_683)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_684 : validRep representative_684 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_684)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_685 : validRep representative_685 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_685)=dictionary64.getD 199 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_199]
  decide +kernel
theorem coefficient_686 : validRep representative_686 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_686)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_687 : validRep representative_687 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_687)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_688 : validRep representative_688 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_688)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_689 : validRep representative_689 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_689)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_690 : validRep representative_690 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_690)=dictionary64.getD 348 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_348]
  decide +kernel
theorem coefficient_691 : validRep representative_691 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_691)=dictionary64.getD 107 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_107]
  decide +kernel
theorem coefficient_692 : validRep representative_692 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_692)=dictionary64.getD 149 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_149]
  decide +kernel
theorem coefficient_693 : validRep representative_693 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_693)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_694 : validRep representative_694 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_694)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_695 : validRep representative_695 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_695)=dictionary64.getD 420 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_420]
  decide +kernel
theorem coefficient_696 : validRep representative_696 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_696)=dictionary64.getD 378 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_378]
  decide +kernel
theorem coefficient_697 : validRep representative_697 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_697)=dictionary64.getD 149 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_149]
  decide +kernel
theorem coefficient_698 : validRep representative_698 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_698)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_699 : validRep representative_699 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_699)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_700 : validRep representative_700 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_700)=dictionary64.getD 233 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_233]
  decide +kernel
theorem coefficient_701 : validRep representative_701 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_701)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_702 : validRep representative_702 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_702)=dictionary64.getD 288 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_288]
  decide +kernel
theorem coefficient_703 : validRep representative_703 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_703)=dictionary64.getD 142 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_142]
  decide +kernel
def tree_010 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 672 (QuarticIntegerRepresentativeTree.Tree.branch 656 (QuarticIntegerRepresentativeTree.Tree.branch 648 (QuarticIntegerRepresentativeTree.Tree.branch 644 (QuarticIntegerRepresentativeTree.Tree.branch 642 (QuarticIntegerRepresentativeTree.Tree.branch 641 (QuarticIntegerRepresentativeTree.Tree.leaf 640 representative_640) (QuarticIntegerRepresentativeTree.Tree.leaf 641 representative_641)) (QuarticIntegerRepresentativeTree.Tree.branch 643 (QuarticIntegerRepresentativeTree.Tree.leaf 642 representative_642) (QuarticIntegerRepresentativeTree.Tree.leaf 643 representative_643))) (QuarticIntegerRepresentativeTree.Tree.branch 646 (QuarticIntegerRepresentativeTree.Tree.branch 645 (QuarticIntegerRepresentativeTree.Tree.leaf 644 representative_644) (QuarticIntegerRepresentativeTree.Tree.leaf 645 representative_645)) (QuarticIntegerRepresentativeTree.Tree.branch 647 (QuarticIntegerRepresentativeTree.Tree.leaf 646 representative_646) (QuarticIntegerRepresentativeTree.Tree.leaf 647 representative_647)))) (QuarticIntegerRepresentativeTree.Tree.branch 652 (QuarticIntegerRepresentativeTree.Tree.branch 650 (QuarticIntegerRepresentativeTree.Tree.branch 649 (QuarticIntegerRepresentativeTree.Tree.leaf 648 representative_648) (QuarticIntegerRepresentativeTree.Tree.leaf 649 representative_649)) (QuarticIntegerRepresentativeTree.Tree.branch 651 (QuarticIntegerRepresentativeTree.Tree.leaf 650 representative_650) (QuarticIntegerRepresentativeTree.Tree.leaf 651 representative_651))) (QuarticIntegerRepresentativeTree.Tree.branch 654 (QuarticIntegerRepresentativeTree.Tree.branch 653 (QuarticIntegerRepresentativeTree.Tree.leaf 652 representative_652) (QuarticIntegerRepresentativeTree.Tree.leaf 653 representative_653)) (QuarticIntegerRepresentativeTree.Tree.branch 655 (QuarticIntegerRepresentativeTree.Tree.leaf 654 representative_654) (QuarticIntegerRepresentativeTree.Tree.leaf 655 representative_655))))) (QuarticIntegerRepresentativeTree.Tree.branch 664 (QuarticIntegerRepresentativeTree.Tree.branch 660 (QuarticIntegerRepresentativeTree.Tree.branch 658 (QuarticIntegerRepresentativeTree.Tree.branch 657 (QuarticIntegerRepresentativeTree.Tree.leaf 656 representative_656) (QuarticIntegerRepresentativeTree.Tree.leaf 657 representative_657)) (QuarticIntegerRepresentativeTree.Tree.branch 659 (QuarticIntegerRepresentativeTree.Tree.leaf 658 representative_658) (QuarticIntegerRepresentativeTree.Tree.leaf 659 representative_659))) (QuarticIntegerRepresentativeTree.Tree.branch 662 (QuarticIntegerRepresentativeTree.Tree.branch 661 (QuarticIntegerRepresentativeTree.Tree.leaf 660 representative_660) (QuarticIntegerRepresentativeTree.Tree.leaf 661 representative_661)) (QuarticIntegerRepresentativeTree.Tree.branch 663 (QuarticIntegerRepresentativeTree.Tree.leaf 662 representative_662) (QuarticIntegerRepresentativeTree.Tree.leaf 663 representative_663)))) (QuarticIntegerRepresentativeTree.Tree.branch 668 (QuarticIntegerRepresentativeTree.Tree.branch 666 (QuarticIntegerRepresentativeTree.Tree.branch 665 (QuarticIntegerRepresentativeTree.Tree.leaf 664 representative_664) (QuarticIntegerRepresentativeTree.Tree.leaf 665 representative_665)) (QuarticIntegerRepresentativeTree.Tree.branch 667 (QuarticIntegerRepresentativeTree.Tree.leaf 666 representative_666) (QuarticIntegerRepresentativeTree.Tree.leaf 667 representative_667))) (QuarticIntegerRepresentativeTree.Tree.branch 670 (QuarticIntegerRepresentativeTree.Tree.branch 669 (QuarticIntegerRepresentativeTree.Tree.leaf 668 representative_668) (QuarticIntegerRepresentativeTree.Tree.leaf 669 representative_669)) (QuarticIntegerRepresentativeTree.Tree.branch 671 (QuarticIntegerRepresentativeTree.Tree.leaf 670 representative_670) (QuarticIntegerRepresentativeTree.Tree.leaf 671 representative_671)))))) (QuarticIntegerRepresentativeTree.Tree.branch 688 (QuarticIntegerRepresentativeTree.Tree.branch 680 (QuarticIntegerRepresentativeTree.Tree.branch 676 (QuarticIntegerRepresentativeTree.Tree.branch 674 (QuarticIntegerRepresentativeTree.Tree.branch 673 (QuarticIntegerRepresentativeTree.Tree.leaf 672 representative_672) (QuarticIntegerRepresentativeTree.Tree.leaf 673 representative_673)) (QuarticIntegerRepresentativeTree.Tree.branch 675 (QuarticIntegerRepresentativeTree.Tree.leaf 674 representative_674) (QuarticIntegerRepresentativeTree.Tree.leaf 675 representative_675))) (QuarticIntegerRepresentativeTree.Tree.branch 678 (QuarticIntegerRepresentativeTree.Tree.branch 677 (QuarticIntegerRepresentativeTree.Tree.leaf 676 representative_676) (QuarticIntegerRepresentativeTree.Tree.leaf 677 representative_677)) (QuarticIntegerRepresentativeTree.Tree.branch 679 (QuarticIntegerRepresentativeTree.Tree.leaf 678 representative_678) (QuarticIntegerRepresentativeTree.Tree.leaf 679 representative_679)))) (QuarticIntegerRepresentativeTree.Tree.branch 684 (QuarticIntegerRepresentativeTree.Tree.branch 682 (QuarticIntegerRepresentativeTree.Tree.branch 681 (QuarticIntegerRepresentativeTree.Tree.leaf 680 representative_680) (QuarticIntegerRepresentativeTree.Tree.leaf 681 representative_681)) (QuarticIntegerRepresentativeTree.Tree.branch 683 (QuarticIntegerRepresentativeTree.Tree.leaf 682 representative_682) (QuarticIntegerRepresentativeTree.Tree.leaf 683 representative_683))) (QuarticIntegerRepresentativeTree.Tree.branch 686 (QuarticIntegerRepresentativeTree.Tree.branch 685 (QuarticIntegerRepresentativeTree.Tree.leaf 684 representative_684) (QuarticIntegerRepresentativeTree.Tree.leaf 685 representative_685)) (QuarticIntegerRepresentativeTree.Tree.branch 687 (QuarticIntegerRepresentativeTree.Tree.leaf 686 representative_686) (QuarticIntegerRepresentativeTree.Tree.leaf 687 representative_687))))) (QuarticIntegerRepresentativeTree.Tree.branch 696 (QuarticIntegerRepresentativeTree.Tree.branch 692 (QuarticIntegerRepresentativeTree.Tree.branch 690 (QuarticIntegerRepresentativeTree.Tree.branch 689 (QuarticIntegerRepresentativeTree.Tree.leaf 688 representative_688) (QuarticIntegerRepresentativeTree.Tree.leaf 689 representative_689)) (QuarticIntegerRepresentativeTree.Tree.branch 691 (QuarticIntegerRepresentativeTree.Tree.leaf 690 representative_690) (QuarticIntegerRepresentativeTree.Tree.leaf 691 representative_691))) (QuarticIntegerRepresentativeTree.Tree.branch 694 (QuarticIntegerRepresentativeTree.Tree.branch 693 (QuarticIntegerRepresentativeTree.Tree.leaf 692 representative_692) (QuarticIntegerRepresentativeTree.Tree.leaf 693 representative_693)) (QuarticIntegerRepresentativeTree.Tree.branch 695 (QuarticIntegerRepresentativeTree.Tree.leaf 694 representative_694) (QuarticIntegerRepresentativeTree.Tree.leaf 695 representative_695)))) (QuarticIntegerRepresentativeTree.Tree.branch 700 (QuarticIntegerRepresentativeTree.Tree.branch 698 (QuarticIntegerRepresentativeTree.Tree.branch 697 (QuarticIntegerRepresentativeTree.Tree.leaf 696 representative_696) (QuarticIntegerRepresentativeTree.Tree.leaf 697 representative_697)) (QuarticIntegerRepresentativeTree.Tree.branch 699 (QuarticIntegerRepresentativeTree.Tree.leaf 698 representative_698) (QuarticIntegerRepresentativeTree.Tree.leaf 699 representative_699))) (QuarticIntegerRepresentativeTree.Tree.branch 702 (QuarticIntegerRepresentativeTree.Tree.branch 701 (QuarticIntegerRepresentativeTree.Tree.leaf 700 representative_700) (QuarticIntegerRepresentativeTree.Tree.leaf 701 representative_701)) (QuarticIntegerRepresentativeTree.Tree.branch 703 (QuarticIntegerRepresentativeTree.Tree.leaf 702 representative_702) (QuarticIntegerRepresentativeTree.Tree.leaf 703 representative_703)))))))
theorem accepted_010 : All validRep tree_010 := ⟨⟨⟨⟨⟨⟨coefficient_640,coefficient_641⟩,⟨coefficient_642,coefficient_643⟩⟩,⟨⟨coefficient_644,coefficient_645⟩,⟨coefficient_646,coefficient_647⟩⟩⟩,⟨⟨⟨coefficient_648,coefficient_649⟩,⟨coefficient_650,coefficient_651⟩⟩,⟨⟨coefficient_652,coefficient_653⟩,⟨coefficient_654,coefficient_655⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_656,coefficient_657⟩,⟨coefficient_658,coefficient_659⟩⟩,⟨⟨coefficient_660,coefficient_661⟩,⟨coefficient_662,coefficient_663⟩⟩⟩,⟨⟨⟨coefficient_664,coefficient_665⟩,⟨coefficient_666,coefficient_667⟩⟩,⟨⟨coefficient_668,coefficient_669⟩,⟨coefficient_670,coefficient_671⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_672,coefficient_673⟩,⟨coefficient_674,coefficient_675⟩⟩,⟨⟨coefficient_676,coefficient_677⟩,⟨coefficient_678,coefficient_679⟩⟩⟩,⟨⟨⟨coefficient_680,coefficient_681⟩,⟨coefficient_682,coefficient_683⟩⟩,⟨⟨coefficient_684,coefficient_685⟩,⟨coefficient_686,coefficient_687⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_688,coefficient_689⟩,⟨coefficient_690,coefficient_691⟩⟩,⟨⟨coefficient_692,coefficient_693⟩,⟨coefficient_694,coefficient_695⟩⟩⟩,⟨⟨⟨coefficient_696,coefficient_697⟩,⟨coefficient_698,coefficient_699⟩⟩,⟨⟨coefficient_700,coefficient_701⟩,⟨coefficient_702,coefficient_703⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

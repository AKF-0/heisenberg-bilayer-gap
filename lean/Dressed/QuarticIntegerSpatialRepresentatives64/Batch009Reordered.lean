import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_576 : Rep := ⟨![0,2,4,17],183⟩
def representative_577 : Rep := ⟨![0,2,4,18],327⟩
def representative_578 : Rep := ⟨![0,2,4,19],183⟩
def representative_579 : Rep := ⟨![0,2,4,20],273⟩
def representative_580 : Rep := ⟨![0,2,4,21],237⟩
def representative_581 : Rep := ⟨![0,2,4,22],462⟩
def representative_582 : Rep := ⟨![0,2,4,23],237⟩
def representative_583 : Rep := ⟨![0,2,4,24],239⟩
def representative_584 : Rep := ⟨![0,2,4,25],261⟩
def representative_585 : Rep := ⟨![0,2,4,26],210⟩
def representative_586 : Rep := ⟨![0,2,4,27],261⟩
def representative_587 : Rep := ⟨![0,2,4,28],239⟩
def representative_588 : Rep := ⟨![0,2,4,29],462⟩
def representative_589 : Rep := ⟨![0,2,4,30],462⟩
def representative_590 : Rep := ⟨![0,2,4,31],462⟩
def representative_591 : Rep := ⟨![0,2,4,32],462⟩
def representative_592 : Rep := ⟨![0,2,4,33],462⟩
def representative_593 : Rep := ⟨![0,2,4,34],255⟩
def representative_594 : Rep := ⟨![0,2,4,35],462⟩
def representative_595 : Rep := ⟨![0,2,4,36],462⟩
def representative_596 : Rep := ⟨![0,2,4,37],462⟩
def representative_597 : Rep := ⟨![0,2,4,38],462⟩
def representative_598 : Rep := ⟨![0,2,4,39],462⟩
def representative_599 : Rep := ⟨![0,2,5,8],340⟩
def representative_600 : Rep := ⟨![0,2,5,9],176⟩
def representative_601 : Rep := ⟨![0,2,5,11],195⟩
def representative_602 : Rep := ⟨![0,2,5,12],275⟩
def representative_603 : Rep := ⟨![0,2,5,16],209⟩
def representative_604 : Rep := ⟨![0,2,5,17],278⟩
def representative_605 : Rep := ⟨![0,2,5,19],265⟩
def representative_606 : Rep := ⟨![0,2,5,20],235⟩
def representative_607 : Rep := ⟨![0,2,5,21],255⟩
def representative_608 : Rep := ⟨![0,2,5,24],255⟩
def representative_609 : Rep := ⟨![0,2,5,25],236⟩
def representative_610 : Rep := ⟨![0,2,5,27],238⟩
def representative_611 : Rep := ⟨![0,2,5,28],462⟩
def representative_612 : Rep := ⟨![0,2,5,29],239⟩
def representative_613 : Rep := ⟨![0,2,5,32],239⟩
def representative_614 : Rep := ⟨![0,2,5,33],462⟩
def representative_615 : Rep := ⟨![0,2,5,35],462⟩
def representative_616 : Rep := ⟨![0,2,5,36],462⟩
def representative_617 : Rep := ⟨![0,2,5,37],462⟩
def representative_618 : Rep := ⟨![0,2,8,10],419⟩
def representative_619 : Rep := ⟨![0,2,8,11],123⟩
def representative_620 : Rep := ⟨![0,2,8,12],289⟩
def representative_621 : Rep := ⟨![0,2,8,13],155⟩
def representative_622 : Rep := ⟨![0,2,8,14],401⟩
def representative_623 : Rep := ⟨![0,2,8,17],411⟩
def representative_624 : Rep := ⟨![0,2,8,18],108⟩
def representative_625 : Rep := ⟨![0,2,8,19],289⟩
def representative_626 : Rep := ⟨![0,2,8,20],234⟩
def representative_627 : Rep := ⟨![0,2,8,21],462⟩
def representative_628 : Rep := ⟨![0,2,8,22],114⟩
def representative_629 : Rep := ⟨![0,2,8,23],410⟩
def representative_630 : Rep := ⟨![0,2,8,25],121⟩
def representative_631 : Rep := ⟨![0,2,8,26],265⟩
def representative_632 : Rep := ⟨![0,2,8,27],235⟩
def representative_633 : Rep := ⟨![0,2,8,28],462⟩
def representative_634 : Rep := ⟨![0,2,8,29],462⟩
def representative_635 : Rep := ⟨![0,2,8,30],462⟩
def representative_636 : Rep := ⟨![0,2,8,31],122⟩
def representative_637 : Rep := ⟨![0,2,8,32],168⟩
def representative_638 : Rep := ⟨![0,2,8,33],462⟩
def representative_639 : Rep := ⟨![0,2,8,34],237⟩
theorem coefficient_576 : validRep representative_576 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_576)=dictionary64.getD 183 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_183]
  decide +kernel
theorem coefficient_577 : validRep representative_577 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_577)=dictionary64.getD 327 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_327]
  decide +kernel
theorem coefficient_578 : validRep representative_578 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_578)=dictionary64.getD 183 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_183]
  decide +kernel
theorem coefficient_579 : validRep representative_579 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_579)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_580 : validRep representative_580 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_580)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_581 : validRep representative_581 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_581)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_582 : validRep representative_582 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_582)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_583 : validRep representative_583 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_583)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_584 : validRep representative_584 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_584)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_585 : validRep representative_585 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_585)=dictionary64.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_210]
  decide +kernel
theorem coefficient_586 : validRep representative_586 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_586)=dictionary64.getD 261 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_261]
  decide +kernel
theorem coefficient_587 : validRep representative_587 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_587)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_588 : validRep representative_588 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_588)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_589 : validRep representative_589 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_589)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_590 : validRep representative_590 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_590)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_591 : validRep representative_591 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_591)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_592 : validRep representative_592 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_592)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_593 : validRep representative_593 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_593)=dictionary64.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_594 : validRep representative_594 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_594)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_595 : validRep representative_595 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_595)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_596 : validRep representative_596 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_596)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_597 : validRep representative_597 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_597)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_598 : validRep representative_598 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_598)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_599 : validRep representative_599 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_599)=dictionary64.getD 340 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_340]
  decide +kernel
theorem coefficient_600 : validRep representative_600 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_600)=dictionary64.getD 176 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_176]
  decide +kernel
theorem coefficient_601 : validRep representative_601 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_601)=dictionary64.getD 195 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_195]
  decide +kernel
theorem coefficient_602 : validRep representative_602 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_602)=dictionary64.getD 275 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_275]
  decide +kernel
theorem coefficient_603 : validRep representative_603 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_603)=dictionary64.getD 209 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_209]
  decide +kernel
theorem coefficient_604 : validRep representative_604 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_604)=dictionary64.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_605 : validRep representative_605 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_605)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_606 : validRep representative_606 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_606)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_607 : validRep representative_607 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_607)=dictionary64.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_608 : validRep representative_608 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_608)=dictionary64.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_609 : validRep representative_609 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_609)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_610 : validRep representative_610 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_610)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_611 : validRep representative_611 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_611)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_612 : validRep representative_612 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_612)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_613 : validRep representative_613 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_613)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_614 : validRep representative_614 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_614)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_615 : validRep representative_615 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_615)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_616 : validRep representative_616 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_616)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_617 : validRep representative_617 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_617)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_618 : validRep representative_618 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_618)=dictionary64.getD 419 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_419]
  decide +kernel
theorem coefficient_619 : validRep representative_619 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_619)=dictionary64.getD 123 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_123]
  decide +kernel
theorem coefficient_620 : validRep representative_620 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_620)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_621 : validRep representative_621 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_621)=dictionary64.getD 155 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_155]
  decide +kernel
theorem coefficient_622 : validRep representative_622 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_622)=dictionary64.getD 401 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_401]
  decide +kernel
theorem coefficient_623 : validRep representative_623 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_623)=dictionary64.getD 411 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_411]
  decide +kernel
theorem coefficient_624 : validRep representative_624 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_624)=dictionary64.getD 108 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_108]
  decide +kernel
theorem coefficient_625 : validRep representative_625 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_625)=dictionary64.getD 289 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_289]
  decide +kernel
theorem coefficient_626 : validRep representative_626 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_626)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_627 : validRep representative_627 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_627)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_628 : validRep representative_628 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_628)=dictionary64.getD 114 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_114]
  decide +kernel
theorem coefficient_629 : validRep representative_629 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_629)=dictionary64.getD 410 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_410]
  decide +kernel
theorem coefficient_630 : validRep representative_630 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_630)=dictionary64.getD 121 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_121]
  decide +kernel
theorem coefficient_631 : validRep representative_631 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_631)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_632 : validRep representative_632 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_632)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_633 : validRep representative_633 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_633)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_634 : validRep representative_634 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_634)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_635 : validRep representative_635 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_635)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_636 : validRep representative_636 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_636)=dictionary64.getD 122 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_122]
  decide +kernel
theorem coefficient_637 : validRep representative_637 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_637)=dictionary64.getD 168 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_168]
  decide +kernel
theorem coefficient_638 : validRep representative_638 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_638)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_639 : validRep representative_639 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_639)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
def tree_009 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 608 (QuarticIntegerRepresentativeTree.Tree.branch 592 (QuarticIntegerRepresentativeTree.Tree.branch 584 (QuarticIntegerRepresentativeTree.Tree.branch 580 (QuarticIntegerRepresentativeTree.Tree.branch 578 (QuarticIntegerRepresentativeTree.Tree.branch 577 (QuarticIntegerRepresentativeTree.Tree.leaf 576 representative_576) (QuarticIntegerRepresentativeTree.Tree.leaf 577 representative_577)) (QuarticIntegerRepresentativeTree.Tree.branch 579 (QuarticIntegerRepresentativeTree.Tree.leaf 578 representative_578) (QuarticIntegerRepresentativeTree.Tree.leaf 579 representative_579))) (QuarticIntegerRepresentativeTree.Tree.branch 582 (QuarticIntegerRepresentativeTree.Tree.branch 581 (QuarticIntegerRepresentativeTree.Tree.leaf 580 representative_580) (QuarticIntegerRepresentativeTree.Tree.leaf 581 representative_581)) (QuarticIntegerRepresentativeTree.Tree.branch 583 (QuarticIntegerRepresentativeTree.Tree.leaf 582 representative_582) (QuarticIntegerRepresentativeTree.Tree.leaf 583 representative_583)))) (QuarticIntegerRepresentativeTree.Tree.branch 588 (QuarticIntegerRepresentativeTree.Tree.branch 586 (QuarticIntegerRepresentativeTree.Tree.branch 585 (QuarticIntegerRepresentativeTree.Tree.leaf 584 representative_584) (QuarticIntegerRepresentativeTree.Tree.leaf 585 representative_585)) (QuarticIntegerRepresentativeTree.Tree.branch 587 (QuarticIntegerRepresentativeTree.Tree.leaf 586 representative_586) (QuarticIntegerRepresentativeTree.Tree.leaf 587 representative_587))) (QuarticIntegerRepresentativeTree.Tree.branch 590 (QuarticIntegerRepresentativeTree.Tree.branch 589 (QuarticIntegerRepresentativeTree.Tree.leaf 588 representative_588) (QuarticIntegerRepresentativeTree.Tree.leaf 589 representative_589)) (QuarticIntegerRepresentativeTree.Tree.branch 591 (QuarticIntegerRepresentativeTree.Tree.leaf 590 representative_590) (QuarticIntegerRepresentativeTree.Tree.leaf 591 representative_591))))) (QuarticIntegerRepresentativeTree.Tree.branch 600 (QuarticIntegerRepresentativeTree.Tree.branch 596 (QuarticIntegerRepresentativeTree.Tree.branch 594 (QuarticIntegerRepresentativeTree.Tree.branch 593 (QuarticIntegerRepresentativeTree.Tree.leaf 592 representative_592) (QuarticIntegerRepresentativeTree.Tree.leaf 593 representative_593)) (QuarticIntegerRepresentativeTree.Tree.branch 595 (QuarticIntegerRepresentativeTree.Tree.leaf 594 representative_594) (QuarticIntegerRepresentativeTree.Tree.leaf 595 representative_595))) (QuarticIntegerRepresentativeTree.Tree.branch 598 (QuarticIntegerRepresentativeTree.Tree.branch 597 (QuarticIntegerRepresentativeTree.Tree.leaf 596 representative_596) (QuarticIntegerRepresentativeTree.Tree.leaf 597 representative_597)) (QuarticIntegerRepresentativeTree.Tree.branch 599 (QuarticIntegerRepresentativeTree.Tree.leaf 598 representative_598) (QuarticIntegerRepresentativeTree.Tree.leaf 599 representative_599)))) (QuarticIntegerRepresentativeTree.Tree.branch 604 (QuarticIntegerRepresentativeTree.Tree.branch 602 (QuarticIntegerRepresentativeTree.Tree.branch 601 (QuarticIntegerRepresentativeTree.Tree.leaf 600 representative_600) (QuarticIntegerRepresentativeTree.Tree.leaf 601 representative_601)) (QuarticIntegerRepresentativeTree.Tree.branch 603 (QuarticIntegerRepresentativeTree.Tree.leaf 602 representative_602) (QuarticIntegerRepresentativeTree.Tree.leaf 603 representative_603))) (QuarticIntegerRepresentativeTree.Tree.branch 606 (QuarticIntegerRepresentativeTree.Tree.branch 605 (QuarticIntegerRepresentativeTree.Tree.leaf 604 representative_604) (QuarticIntegerRepresentativeTree.Tree.leaf 605 representative_605)) (QuarticIntegerRepresentativeTree.Tree.branch 607 (QuarticIntegerRepresentativeTree.Tree.leaf 606 representative_606) (QuarticIntegerRepresentativeTree.Tree.leaf 607 representative_607)))))) (QuarticIntegerRepresentativeTree.Tree.branch 624 (QuarticIntegerRepresentativeTree.Tree.branch 616 (QuarticIntegerRepresentativeTree.Tree.branch 612 (QuarticIntegerRepresentativeTree.Tree.branch 610 (QuarticIntegerRepresentativeTree.Tree.branch 609 (QuarticIntegerRepresentativeTree.Tree.leaf 608 representative_608) (QuarticIntegerRepresentativeTree.Tree.leaf 609 representative_609)) (QuarticIntegerRepresentativeTree.Tree.branch 611 (QuarticIntegerRepresentativeTree.Tree.leaf 610 representative_610) (QuarticIntegerRepresentativeTree.Tree.leaf 611 representative_611))) (QuarticIntegerRepresentativeTree.Tree.branch 614 (QuarticIntegerRepresentativeTree.Tree.branch 613 (QuarticIntegerRepresentativeTree.Tree.leaf 612 representative_612) (QuarticIntegerRepresentativeTree.Tree.leaf 613 representative_613)) (QuarticIntegerRepresentativeTree.Tree.branch 615 (QuarticIntegerRepresentativeTree.Tree.leaf 614 representative_614) (QuarticIntegerRepresentativeTree.Tree.leaf 615 representative_615)))) (QuarticIntegerRepresentativeTree.Tree.branch 620 (QuarticIntegerRepresentativeTree.Tree.branch 618 (QuarticIntegerRepresentativeTree.Tree.branch 617 (QuarticIntegerRepresentativeTree.Tree.leaf 616 representative_616) (QuarticIntegerRepresentativeTree.Tree.leaf 617 representative_617)) (QuarticIntegerRepresentativeTree.Tree.branch 619 (QuarticIntegerRepresentativeTree.Tree.leaf 618 representative_618) (QuarticIntegerRepresentativeTree.Tree.leaf 619 representative_619))) (QuarticIntegerRepresentativeTree.Tree.branch 622 (QuarticIntegerRepresentativeTree.Tree.branch 621 (QuarticIntegerRepresentativeTree.Tree.leaf 620 representative_620) (QuarticIntegerRepresentativeTree.Tree.leaf 621 representative_621)) (QuarticIntegerRepresentativeTree.Tree.branch 623 (QuarticIntegerRepresentativeTree.Tree.leaf 622 representative_622) (QuarticIntegerRepresentativeTree.Tree.leaf 623 representative_623))))) (QuarticIntegerRepresentativeTree.Tree.branch 632 (QuarticIntegerRepresentativeTree.Tree.branch 628 (QuarticIntegerRepresentativeTree.Tree.branch 626 (QuarticIntegerRepresentativeTree.Tree.branch 625 (QuarticIntegerRepresentativeTree.Tree.leaf 624 representative_624) (QuarticIntegerRepresentativeTree.Tree.leaf 625 representative_625)) (QuarticIntegerRepresentativeTree.Tree.branch 627 (QuarticIntegerRepresentativeTree.Tree.leaf 626 representative_626) (QuarticIntegerRepresentativeTree.Tree.leaf 627 representative_627))) (QuarticIntegerRepresentativeTree.Tree.branch 630 (QuarticIntegerRepresentativeTree.Tree.branch 629 (QuarticIntegerRepresentativeTree.Tree.leaf 628 representative_628) (QuarticIntegerRepresentativeTree.Tree.leaf 629 representative_629)) (QuarticIntegerRepresentativeTree.Tree.branch 631 (QuarticIntegerRepresentativeTree.Tree.leaf 630 representative_630) (QuarticIntegerRepresentativeTree.Tree.leaf 631 representative_631)))) (QuarticIntegerRepresentativeTree.Tree.branch 636 (QuarticIntegerRepresentativeTree.Tree.branch 634 (QuarticIntegerRepresentativeTree.Tree.branch 633 (QuarticIntegerRepresentativeTree.Tree.leaf 632 representative_632) (QuarticIntegerRepresentativeTree.Tree.leaf 633 representative_633)) (QuarticIntegerRepresentativeTree.Tree.branch 635 (QuarticIntegerRepresentativeTree.Tree.leaf 634 representative_634) (QuarticIntegerRepresentativeTree.Tree.leaf 635 representative_635))) (QuarticIntegerRepresentativeTree.Tree.branch 638 (QuarticIntegerRepresentativeTree.Tree.branch 637 (QuarticIntegerRepresentativeTree.Tree.leaf 636 representative_636) (QuarticIntegerRepresentativeTree.Tree.leaf 637 representative_637)) (QuarticIntegerRepresentativeTree.Tree.branch 639 (QuarticIntegerRepresentativeTree.Tree.leaf 638 representative_638) (QuarticIntegerRepresentativeTree.Tree.leaf 639 representative_639)))))))
theorem accepted_009 : All validRep tree_009 := ⟨⟨⟨⟨⟨⟨coefficient_576,coefficient_577⟩,⟨coefficient_578,coefficient_579⟩⟩,⟨⟨coefficient_580,coefficient_581⟩,⟨coefficient_582,coefficient_583⟩⟩⟩,⟨⟨⟨coefficient_584,coefficient_585⟩,⟨coefficient_586,coefficient_587⟩⟩,⟨⟨coefficient_588,coefficient_589⟩,⟨coefficient_590,coefficient_591⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_592,coefficient_593⟩,⟨coefficient_594,coefficient_595⟩⟩,⟨⟨coefficient_596,coefficient_597⟩,⟨coefficient_598,coefficient_599⟩⟩⟩,⟨⟨⟨coefficient_600,coefficient_601⟩,⟨coefficient_602,coefficient_603⟩⟩,⟨⟨coefficient_604,coefficient_605⟩,⟨coefficient_606,coefficient_607⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_608,coefficient_609⟩,⟨coefficient_610,coefficient_611⟩⟩,⟨⟨coefficient_612,coefficient_613⟩,⟨coefficient_614,coefficient_615⟩⟩⟩,⟨⟨⟨coefficient_616,coefficient_617⟩,⟨coefficient_618,coefficient_619⟩⟩,⟨⟨coefficient_620,coefficient_621⟩,⟨coefficient_622,coefficient_623⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_624,coefficient_625⟩,⟨coefficient_626,coefficient_627⟩⟩,⟨⟨coefficient_628,coefficient_629⟩,⟨coefficient_630,coefficient_631⟩⟩⟩,⟨⟨⟨coefficient_632,coefficient_633⟩,⟨coefficient_634,coefficient_635⟩⟩,⟨⟨coefficient_636,coefficient_637⟩,⟨coefficient_638,coefficient_639⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

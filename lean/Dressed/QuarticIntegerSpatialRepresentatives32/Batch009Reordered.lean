import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_576 : Rep := ⟨![0,6,8,28],420⟩
def representative_577 : Rep := ⟨![0,6,8,29],158⟩
def representative_578 : Rep := ⟨![0,6,8,30],343⟩
def representative_579 : Rep := ⟨![0,6,9,15],343⟩
def representative_580 : Rep := ⟨![0,6,9,16],324⟩
def representative_581 : Rep := ⟨![0,6,9,17],194⟩
def representative_582 : Rep := ⟨![0,6,9,18],334⟩
def representative_583 : Rep := ⟨![0,6,9,19],262⟩
def representative_584 : Rep := ⟨![0,6,9,20],265⟩
def representative_585 : Rep := ⟨![0,6,9,21],302⟩
def representative_586 : Rep := ⟨![0,6,9,22],268⟩
def representative_587 : Rep := ⟨![0,6,9,23],278⟩
def representative_588 : Rep := ⟨![0,6,9,24],324⟩
def representative_589 : Rep := ⟨![0,6,9,25],252⟩
def representative_590 : Rep := ⟨![0,6,9,26],313⟩
def representative_591 : Rep := ⟨![0,6,9,27],252⟩
def representative_592 : Rep := ⟨![0,6,9,28],131⟩
def representative_593 : Rep := ⟨![0,6,9,29],346⟩
def representative_594 : Rep := ⟨![0,6,9,31],342⟩
def representative_595 : Rep := ⟨![0,6,10,12],244⟩
def representative_596 : Rep := ⟨![0,6,10,16],508⟩
def representative_597 : Rep := ⟨![0,6,10,17],245⟩
def representative_598 : Rep := ⟨![0,6,10,18],240⟩
def representative_599 : Rep := ⟨![0,6,10,20],278⟩
def representative_600 : Rep := ⟨![0,6,10,21],508⟩
def representative_601 : Rep := ⟨![0,6,10,22],248⟩
def representative_602 : Rep := ⟨![0,6,10,24],258⟩
def representative_603 : Rep := ⟨![0,6,10,25],318⟩
def representative_604 : Rep := ⟨![0,6,10,26],170⟩
def representative_605 : Rep := ⟨![0,6,10,28],345⟩
def representative_606 : Rep := ⟨![0,6,12,18],280⟩
def representative_607 : Rep := ⟨![0,6,12,20],268⟩
def representative_608 : Rep := ⟨![0,6,12,21],277⟩
def representative_609 : Rep := ⟨![0,6,12,22],508⟩
def representative_610 : Rep := ⟨![0,6,12,24],300⟩
def representative_611 : Rep := ⟨![0,6,12,25],265⟩
def representative_612 : Rep := ⟨![0,6,12,26],280⟩
def representative_613 : Rep := ⟨![0,6,13,19],280⟩
def representative_614 : Rep := ⟨![0,6,13,20],277⟩
def representative_615 : Rep := ⟨![0,6,13,21],271⟩
def representative_616 : Rep := ⟨![0,6,13,22],278⟩
def representative_617 : Rep := ⟨![0,6,13,23],508⟩
def representative_618 : Rep := ⟨![0,6,13,24],268⟩
def representative_619 : Rep := ⟨![0,6,13,25],281⟩
def representative_620 : Rep := ⟨![0,6,13,27],280⟩
def representative_621 : Rep := ⟨![0,6,14,16],508⟩
def representative_622 : Rep := ⟨![0,6,14,20],508⟩
def representative_623 : Rep := ⟨![0,6,14,21],508⟩
def representative_624 : Rep := ⟨![0,6,14,22],271⟩
def representative_625 : Rep := ⟨![0,6,14,24],508⟩
def representative_626 : Rep := ⟨![0,6,16,22],508⟩
def representative_627 : Rep := ⟨![0,6,17,23],508⟩
def representative_628 : Rep := ⟨![0,6,18,20],508⟩
def representative_629 : Rep := ⟨![0,8,1,9],429⟩
def representative_630 : Rep := ⟨![0,8,1,10],146⟩
def representative_631 : Rep := ⟨![0,8,1,11],414⟩
def representative_632 : Rep := ⟨![0,8,1,12],400⟩
def representative_633 : Rep := ⟨![0,8,1,13],171⟩
def representative_634 : Rep := ⟨![0,8,1,14],321⟩
def representative_635 : Rep := ⟨![0,8,1,15],186⟩
def representative_636 : Rep := ⟨![0,8,1,16],218⟩
def representative_637 : Rep := ⟨![0,8,1,17],308⟩
def representative_638 : Rep := ⟨![0,8,1,18],265⟩
def representative_639 : Rep := ⟨![0,8,1,19],308⟩
theorem coefficient_576 : validRep representative_576 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_576)=dictionary32.getD 420 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_420]
  decide +kernel
theorem coefficient_577 : validRep representative_577 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_577)=dictionary32.getD 158 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_158]
  decide +kernel
theorem coefficient_578 : validRep representative_578 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_578)=dictionary32.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_579 : validRep representative_579 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_579)=dictionary32.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_580 : validRep representative_580 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_580)=dictionary32.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_581 : validRep representative_581 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_581)=dictionary32.getD 194 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_194]
  decide +kernel
theorem coefficient_582 : validRep representative_582 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_582)=dictionary32.getD 334 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_334]
  decide +kernel
theorem coefficient_583 : validRep representative_583 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_583)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_584 : validRep representative_584 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_584)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_585 : validRep representative_585 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_585)=dictionary32.getD 302 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_302]
  decide +kernel
theorem coefficient_586 : validRep representative_586 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_586)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_587 : validRep representative_587 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_587)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_588 : validRep representative_588 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_588)=dictionary32.getD 324 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_324]
  decide +kernel
theorem coefficient_589 : validRep representative_589 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_589)=dictionary32.getD 252 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_252]
  decide +kernel
theorem coefficient_590 : validRep representative_590 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_590)=dictionary32.getD 313 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_313]
  decide +kernel
theorem coefficient_591 : validRep representative_591 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_591)=dictionary32.getD 252 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_252]
  decide +kernel
theorem coefficient_592 : validRep representative_592 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_592)=dictionary32.getD 131 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_131]
  decide +kernel
theorem coefficient_593 : validRep representative_593 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_593)=dictionary32.getD 346 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_346]
  decide +kernel
theorem coefficient_594 : validRep representative_594 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_594)=dictionary32.getD 342 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_342]
  decide +kernel
theorem coefficient_595 : validRep representative_595 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_595)=dictionary32.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_596 : validRep representative_596 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_596)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_597 : validRep representative_597 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_597)=dictionary32.getD 245 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_245]
  decide +kernel
theorem coefficient_598 : validRep representative_598 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_598)=dictionary32.getD 240 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_240]
  decide +kernel
theorem coefficient_599 : validRep representative_599 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_599)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_600 : validRep representative_600 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_600)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_601 : validRep representative_601 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_601)=dictionary32.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_602 : validRep representative_602 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_602)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_603 : validRep representative_603 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_603)=dictionary32.getD 318 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_318]
  decide +kernel
theorem coefficient_604 : validRep representative_604 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_604)=dictionary32.getD 170 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_170]
  decide +kernel
theorem coefficient_605 : validRep representative_605 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_605)=dictionary32.getD 345 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_345]
  decide +kernel
theorem coefficient_606 : validRep representative_606 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_606)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_607 : validRep representative_607 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_607)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_608 : validRep representative_608 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_608)=dictionary32.getD 277 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_277]
  decide +kernel
theorem coefficient_609 : validRep representative_609 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_609)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_610 : validRep representative_610 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_610)=dictionary32.getD 300 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_300]
  decide +kernel
theorem coefficient_611 : validRep representative_611 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_611)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_612 : validRep representative_612 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_612)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_613 : validRep representative_613 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_613)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_614 : validRep representative_614 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_614)=dictionary32.getD 277 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_277]
  decide +kernel
theorem coefficient_615 : validRep representative_615 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_615)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_616 : validRep representative_616 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_616)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_617 : validRep representative_617 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_617)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_618 : validRep representative_618 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_618)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_619 : validRep representative_619 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_619)=dictionary32.getD 281 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_281]
  decide +kernel
theorem coefficient_620 : validRep representative_620 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_620)=dictionary32.getD 280 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_280]
  decide +kernel
theorem coefficient_621 : validRep representative_621 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_621)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_622 : validRep representative_622 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_622)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_623 : validRep representative_623 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_623)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_624 : validRep representative_624 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_624)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_625 : validRep representative_625 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_625)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_626 : validRep representative_626 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_626)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_627 : validRep representative_627 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_627)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_628 : validRep representative_628 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_628)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_629 : validRep representative_629 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_629)=dictionary32.getD 429 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_429]
  decide +kernel
theorem coefficient_630 : validRep representative_630 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_630)=dictionary32.getD 146 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_146]
  decide +kernel
theorem coefficient_631 : validRep representative_631 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_631)=dictionary32.getD 414 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_414]
  decide +kernel
theorem coefficient_632 : validRep representative_632 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_632)=dictionary32.getD 400 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_400]
  decide +kernel
theorem coefficient_633 : validRep representative_633 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_633)=dictionary32.getD 171 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_171]
  decide +kernel
theorem coefficient_634 : validRep representative_634 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_634)=dictionary32.getD 321 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_321]
  decide +kernel
theorem coefficient_635 : validRep representative_635 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_635)=dictionary32.getD 186 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_186]
  decide +kernel
theorem coefficient_636 : validRep representative_636 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_636)=dictionary32.getD 218 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_218]
  decide +kernel
theorem coefficient_637 : validRep representative_637 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_637)=dictionary32.getD 308 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_308]
  decide +kernel
theorem coefficient_638 : validRep representative_638 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_638)=dictionary32.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_639 : validRep representative_639 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_639)=dictionary32.getD 308 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_308]
  decide +kernel
def tree_009 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 608 (QuarticIntegerRepresentativeTree.Tree.branch 592 (QuarticIntegerRepresentativeTree.Tree.branch 584 (QuarticIntegerRepresentativeTree.Tree.branch 580 (QuarticIntegerRepresentativeTree.Tree.branch 578 (QuarticIntegerRepresentativeTree.Tree.branch 577 (QuarticIntegerRepresentativeTree.Tree.leaf 576 representative_576) (QuarticIntegerRepresentativeTree.Tree.leaf 577 representative_577)) (QuarticIntegerRepresentativeTree.Tree.branch 579 (QuarticIntegerRepresentativeTree.Tree.leaf 578 representative_578) (QuarticIntegerRepresentativeTree.Tree.leaf 579 representative_579))) (QuarticIntegerRepresentativeTree.Tree.branch 582 (QuarticIntegerRepresentativeTree.Tree.branch 581 (QuarticIntegerRepresentativeTree.Tree.leaf 580 representative_580) (QuarticIntegerRepresentativeTree.Tree.leaf 581 representative_581)) (QuarticIntegerRepresentativeTree.Tree.branch 583 (QuarticIntegerRepresentativeTree.Tree.leaf 582 representative_582) (QuarticIntegerRepresentativeTree.Tree.leaf 583 representative_583)))) (QuarticIntegerRepresentativeTree.Tree.branch 588 (QuarticIntegerRepresentativeTree.Tree.branch 586 (QuarticIntegerRepresentativeTree.Tree.branch 585 (QuarticIntegerRepresentativeTree.Tree.leaf 584 representative_584) (QuarticIntegerRepresentativeTree.Tree.leaf 585 representative_585)) (QuarticIntegerRepresentativeTree.Tree.branch 587 (QuarticIntegerRepresentativeTree.Tree.leaf 586 representative_586) (QuarticIntegerRepresentativeTree.Tree.leaf 587 representative_587))) (QuarticIntegerRepresentativeTree.Tree.branch 590 (QuarticIntegerRepresentativeTree.Tree.branch 589 (QuarticIntegerRepresentativeTree.Tree.leaf 588 representative_588) (QuarticIntegerRepresentativeTree.Tree.leaf 589 representative_589)) (QuarticIntegerRepresentativeTree.Tree.branch 591 (QuarticIntegerRepresentativeTree.Tree.leaf 590 representative_590) (QuarticIntegerRepresentativeTree.Tree.leaf 591 representative_591))))) (QuarticIntegerRepresentativeTree.Tree.branch 600 (QuarticIntegerRepresentativeTree.Tree.branch 596 (QuarticIntegerRepresentativeTree.Tree.branch 594 (QuarticIntegerRepresentativeTree.Tree.branch 593 (QuarticIntegerRepresentativeTree.Tree.leaf 592 representative_592) (QuarticIntegerRepresentativeTree.Tree.leaf 593 representative_593)) (QuarticIntegerRepresentativeTree.Tree.branch 595 (QuarticIntegerRepresentativeTree.Tree.leaf 594 representative_594) (QuarticIntegerRepresentativeTree.Tree.leaf 595 representative_595))) (QuarticIntegerRepresentativeTree.Tree.branch 598 (QuarticIntegerRepresentativeTree.Tree.branch 597 (QuarticIntegerRepresentativeTree.Tree.leaf 596 representative_596) (QuarticIntegerRepresentativeTree.Tree.leaf 597 representative_597)) (QuarticIntegerRepresentativeTree.Tree.branch 599 (QuarticIntegerRepresentativeTree.Tree.leaf 598 representative_598) (QuarticIntegerRepresentativeTree.Tree.leaf 599 representative_599)))) (QuarticIntegerRepresentativeTree.Tree.branch 604 (QuarticIntegerRepresentativeTree.Tree.branch 602 (QuarticIntegerRepresentativeTree.Tree.branch 601 (QuarticIntegerRepresentativeTree.Tree.leaf 600 representative_600) (QuarticIntegerRepresentativeTree.Tree.leaf 601 representative_601)) (QuarticIntegerRepresentativeTree.Tree.branch 603 (QuarticIntegerRepresentativeTree.Tree.leaf 602 representative_602) (QuarticIntegerRepresentativeTree.Tree.leaf 603 representative_603))) (QuarticIntegerRepresentativeTree.Tree.branch 606 (QuarticIntegerRepresentativeTree.Tree.branch 605 (QuarticIntegerRepresentativeTree.Tree.leaf 604 representative_604) (QuarticIntegerRepresentativeTree.Tree.leaf 605 representative_605)) (QuarticIntegerRepresentativeTree.Tree.branch 607 (QuarticIntegerRepresentativeTree.Tree.leaf 606 representative_606) (QuarticIntegerRepresentativeTree.Tree.leaf 607 representative_607)))))) (QuarticIntegerRepresentativeTree.Tree.branch 624 (QuarticIntegerRepresentativeTree.Tree.branch 616 (QuarticIntegerRepresentativeTree.Tree.branch 612 (QuarticIntegerRepresentativeTree.Tree.branch 610 (QuarticIntegerRepresentativeTree.Tree.branch 609 (QuarticIntegerRepresentativeTree.Tree.leaf 608 representative_608) (QuarticIntegerRepresentativeTree.Tree.leaf 609 representative_609)) (QuarticIntegerRepresentativeTree.Tree.branch 611 (QuarticIntegerRepresentativeTree.Tree.leaf 610 representative_610) (QuarticIntegerRepresentativeTree.Tree.leaf 611 representative_611))) (QuarticIntegerRepresentativeTree.Tree.branch 614 (QuarticIntegerRepresentativeTree.Tree.branch 613 (QuarticIntegerRepresentativeTree.Tree.leaf 612 representative_612) (QuarticIntegerRepresentativeTree.Tree.leaf 613 representative_613)) (QuarticIntegerRepresentativeTree.Tree.branch 615 (QuarticIntegerRepresentativeTree.Tree.leaf 614 representative_614) (QuarticIntegerRepresentativeTree.Tree.leaf 615 representative_615)))) (QuarticIntegerRepresentativeTree.Tree.branch 620 (QuarticIntegerRepresentativeTree.Tree.branch 618 (QuarticIntegerRepresentativeTree.Tree.branch 617 (QuarticIntegerRepresentativeTree.Tree.leaf 616 representative_616) (QuarticIntegerRepresentativeTree.Tree.leaf 617 representative_617)) (QuarticIntegerRepresentativeTree.Tree.branch 619 (QuarticIntegerRepresentativeTree.Tree.leaf 618 representative_618) (QuarticIntegerRepresentativeTree.Tree.leaf 619 representative_619))) (QuarticIntegerRepresentativeTree.Tree.branch 622 (QuarticIntegerRepresentativeTree.Tree.branch 621 (QuarticIntegerRepresentativeTree.Tree.leaf 620 representative_620) (QuarticIntegerRepresentativeTree.Tree.leaf 621 representative_621)) (QuarticIntegerRepresentativeTree.Tree.branch 623 (QuarticIntegerRepresentativeTree.Tree.leaf 622 representative_622) (QuarticIntegerRepresentativeTree.Tree.leaf 623 representative_623))))) (QuarticIntegerRepresentativeTree.Tree.branch 632 (QuarticIntegerRepresentativeTree.Tree.branch 628 (QuarticIntegerRepresentativeTree.Tree.branch 626 (QuarticIntegerRepresentativeTree.Tree.branch 625 (QuarticIntegerRepresentativeTree.Tree.leaf 624 representative_624) (QuarticIntegerRepresentativeTree.Tree.leaf 625 representative_625)) (QuarticIntegerRepresentativeTree.Tree.branch 627 (QuarticIntegerRepresentativeTree.Tree.leaf 626 representative_626) (QuarticIntegerRepresentativeTree.Tree.leaf 627 representative_627))) (QuarticIntegerRepresentativeTree.Tree.branch 630 (QuarticIntegerRepresentativeTree.Tree.branch 629 (QuarticIntegerRepresentativeTree.Tree.leaf 628 representative_628) (QuarticIntegerRepresentativeTree.Tree.leaf 629 representative_629)) (QuarticIntegerRepresentativeTree.Tree.branch 631 (QuarticIntegerRepresentativeTree.Tree.leaf 630 representative_630) (QuarticIntegerRepresentativeTree.Tree.leaf 631 representative_631)))) (QuarticIntegerRepresentativeTree.Tree.branch 636 (QuarticIntegerRepresentativeTree.Tree.branch 634 (QuarticIntegerRepresentativeTree.Tree.branch 633 (QuarticIntegerRepresentativeTree.Tree.leaf 632 representative_632) (QuarticIntegerRepresentativeTree.Tree.leaf 633 representative_633)) (QuarticIntegerRepresentativeTree.Tree.branch 635 (QuarticIntegerRepresentativeTree.Tree.leaf 634 representative_634) (QuarticIntegerRepresentativeTree.Tree.leaf 635 representative_635))) (QuarticIntegerRepresentativeTree.Tree.branch 638 (QuarticIntegerRepresentativeTree.Tree.branch 637 (QuarticIntegerRepresentativeTree.Tree.leaf 636 representative_636) (QuarticIntegerRepresentativeTree.Tree.leaf 637 representative_637)) (QuarticIntegerRepresentativeTree.Tree.branch 639 (QuarticIntegerRepresentativeTree.Tree.leaf 638 representative_638) (QuarticIntegerRepresentativeTree.Tree.leaf 639 representative_639)))))))
theorem accepted_009 : All validRep tree_009 := ⟨⟨⟨⟨⟨⟨coefficient_576,coefficient_577⟩,⟨coefficient_578,coefficient_579⟩⟩,⟨⟨coefficient_580,coefficient_581⟩,⟨coefficient_582,coefficient_583⟩⟩⟩,⟨⟨⟨coefficient_584,coefficient_585⟩,⟨coefficient_586,coefficient_587⟩⟩,⟨⟨coefficient_588,coefficient_589⟩,⟨coefficient_590,coefficient_591⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_592,coefficient_593⟩,⟨coefficient_594,coefficient_595⟩⟩,⟨⟨coefficient_596,coefficient_597⟩,⟨coefficient_598,coefficient_599⟩⟩⟩,⟨⟨⟨coefficient_600,coefficient_601⟩,⟨coefficient_602,coefficient_603⟩⟩,⟨⟨coefficient_604,coefficient_605⟩,⟨coefficient_606,coefficient_607⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_608,coefficient_609⟩,⟨coefficient_610,coefficient_611⟩⟩,⟨⟨coefficient_612,coefficient_613⟩,⟨coefficient_614,coefficient_615⟩⟩⟩,⟨⟨⟨coefficient_616,coefficient_617⟩,⟨coefficient_618,coefficient_619⟩⟩,⟨⟨coefficient_620,coefficient_621⟩,⟨coefficient_622,coefficient_623⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_624,coefficient_625⟩,⟨coefficient_626,coefficient_627⟩⟩,⟨⟨coefficient_628,coefficient_629⟩,⟨coefficient_630,coefficient_631⟩⟩⟩,⟨⟨⟨coefficient_632,coefficient_633⟩,⟨coefficient_634,coefficient_635⟩⟩,⟨⟨coefficient_636,coefficient_637⟩,⟨coefficient_638,coefficient_639⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

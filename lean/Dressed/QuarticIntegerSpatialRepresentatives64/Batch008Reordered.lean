import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_512 : Rep := ⟨![0,2,1,4],30⟩
def representative_513 : Rep := ⟨![0,2,1,5],434⟩
def representative_514 : Rep := ⟨![0,2,1,8],460⟩
def representative_515 : Rep := ⟨![0,2,1,11],26⟩
def representative_516 : Rep := ⟨![0,2,1,12],435⟩
def representative_517 : Rep := ⟨![0,2,1,13],163⟩
def representative_518 : Rep := ⟨![0,2,1,16],28⟩
def representative_519 : Rep := ⟨![0,2,1,17],455⟩
def representative_520 : Rep := ⟨![0,2,1,19],435⟩
def representative_521 : Rep := ⟨![0,2,1,20],180⟩
def representative_522 : Rep := ⟨![0,2,1,21],462⟩
def representative_523 : Rep := ⟨![0,2,1,24],428⟩
def representative_524 : Rep := ⟨![0,2,1,25],54⟩
def representative_525 : Rep := ⟨![0,2,1,27],193⟩
def representative_526 : Rep := ⟨![0,2,1,28],462⟩
def representative_527 : Rep := ⟨![0,2,1,29],462⟩
def representative_528 : Rep := ⟨![0,2,1,32],208⟩
def representative_529 : Rep := ⟨![0,2,1,33],462⟩
def representative_530 : Rep := ⟨![0,2,1,35],462⟩
def representative_531 : Rep := ⟨![0,2,1,36],462⟩
def representative_532 : Rep := ⟨![0,2,1,37],462⟩
def representative_533 : Rep := ⟨![0,2,3,5],326⟩
def representative_534 : Rep := ⟨![0,2,3,6],205⟩
def representative_535 : Rep := ⟨![0,2,3,7],364⟩
def representative_536 : Rep := ⟨![0,2,3,8],397⟩
def representative_537 : Rep := ⟨![0,2,3,9],53⟩
def representative_538 : Rep := ⟨![0,2,3,10],454⟩
def representative_539 : Rep := ⟨![0,2,3,12],372⟩
def representative_540 : Rep := ⟨![0,2,3,13],325⟩
def representative_541 : Rep := ⟨![0,2,3,14],265⟩
def representative_542 : Rep := ⟨![0,2,3,15],167⟩
def representative_543 : Rep := ⟨![0,2,3,16],164⟩
def representative_544 : Rep := ⟨![0,2,3,17],386⟩
def representative_545 : Rep := ⟨![0,2,3,18],69⟩
def representative_546 : Rep := ⟨![0,2,3,19],385⟩
def representative_547 : Rep := ⟨![0,2,3,20],211⟩
def representative_548 : Rep := ⟨![0,2,3,21],462⟩
def representative_549 : Rep := ⟨![0,2,3,22],237⟩
def representative_550 : Rep := ⟨![0,2,3,23],265⟩
def representative_551 : Rep := ⟨![0,2,3,24],255⟩
def representative_552 : Rep := ⟨![0,2,3,25],192⟩
def representative_553 : Rep := ⟨![0,2,3,26],338⟩
def representative_554 : Rep := ⟨![0,2,3,27],202⟩
def representative_555 : Rep := ⟨![0,2,3,28],462⟩
def representative_556 : Rep := ⟨![0,2,3,29],462⟩
def representative_557 : Rep := ⟨![0,2,3,30],462⟩
def representative_558 : Rep := ⟨![0,2,3,31],238⟩
def representative_559 : Rep := ⟨![0,2,3,32],239⟩
def representative_560 : Rep := ⟨![0,2,3,33],462⟩
def representative_561 : Rep := ⟨![0,2,3,34],208⟩
def representative_562 : Rep := ⟨![0,2,3,35],462⟩
def representative_563 : Rep := ⟨![0,2,3,36],462⟩
def representative_564 : Rep := ⟨![0,2,3,37],462⟩
def representative_565 : Rep := ⟨![0,2,3,38],462⟩
def representative_566 : Rep := ⟨![0,2,3,39],462⟩
def representative_567 : Rep := ⟨![0,2,4,6],273⟩
def representative_568 : Rep := ⟨![0,2,4,8],174⟩
def representative_569 : Rep := ⟨![0,2,4,9],346⟩
def representative_570 : Rep := ⟨![0,2,4,10],67⟩
def representative_571 : Rep := ⟨![0,2,4,11],349⟩
def representative_572 : Rep := ⟨![0,2,4,13],273⟩
def representative_573 : Rep := ⟨![0,2,4,14],235⟩
def representative_574 : Rep := ⟨![0,2,4,15],273⟩
def representative_575 : Rep := ⟨![0,2,4,16],273⟩
theorem coefficient_512 : validRep representative_512 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_512)=dictionary64.getD 30 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_30]
  decide +kernel
theorem coefficient_513 : validRep representative_513 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_513)=dictionary64.getD 434 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_434]
  decide +kernel
theorem coefficient_514 : validRep representative_514 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_514)=dictionary64.getD 460 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_460]
  decide +kernel
theorem coefficient_515 : validRep representative_515 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_515)=dictionary64.getD 26 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_26]
  decide +kernel
theorem coefficient_516 : validRep representative_516 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_516)=dictionary64.getD 435 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_435]
  decide +kernel
theorem coefficient_517 : validRep representative_517 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_517)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_518 : validRep representative_518 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_518)=dictionary64.getD 28 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_28]
  decide +kernel
theorem coefficient_519 : validRep representative_519 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_519)=dictionary64.getD 455 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_455]
  decide +kernel
theorem coefficient_520 : validRep representative_520 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_520)=dictionary64.getD 435 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_435]
  decide +kernel
theorem coefficient_521 : validRep representative_521 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_521)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_522 : validRep representative_522 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_522)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_523 : validRep representative_523 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_523)=dictionary64.getD 428 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_428]
  decide +kernel
theorem coefficient_524 : validRep representative_524 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_524)=dictionary64.getD 54 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_54]
  decide +kernel
theorem coefficient_525 : validRep representative_525 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_525)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_526 : validRep representative_526 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_526)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_527 : validRep representative_527 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_527)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_528 : validRep representative_528 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_528)=dictionary64.getD 208 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_208]
  decide +kernel
theorem coefficient_529 : validRep representative_529 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_529)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_530 : validRep representative_530 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_530)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_531 : validRep representative_531 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_531)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_532 : validRep representative_532 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_532)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_533 : validRep representative_533 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_533)=dictionary64.getD 326 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_326]
  decide +kernel
theorem coefficient_534 : validRep representative_534 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_534)=dictionary64.getD 205 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_205]
  decide +kernel
theorem coefficient_535 : validRep representative_535 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_535)=dictionary64.getD 364 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_364]
  decide +kernel
theorem coefficient_536 : validRep representative_536 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_536)=dictionary64.getD 397 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_397]
  decide +kernel
theorem coefficient_537 : validRep representative_537 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_537)=dictionary64.getD 53 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_53]
  decide +kernel
theorem coefficient_538 : validRep representative_538 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_538)=dictionary64.getD 454 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_454]
  decide +kernel
theorem coefficient_539 : validRep representative_539 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_539)=dictionary64.getD 372 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_372]
  decide +kernel
theorem coefficient_540 : validRep representative_540 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_540)=dictionary64.getD 325 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_325]
  decide +kernel
theorem coefficient_541 : validRep representative_541 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_541)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_542 : validRep representative_542 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_542)=dictionary64.getD 167 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_167]
  decide +kernel
theorem coefficient_543 : validRep representative_543 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_543)=dictionary64.getD 164 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_164]
  decide +kernel
theorem coefficient_544 : validRep representative_544 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_544)=dictionary64.getD 386 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_386]
  decide +kernel
theorem coefficient_545 : validRep representative_545 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_545)=dictionary64.getD 69 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_69]
  decide +kernel
theorem coefficient_546 : validRep representative_546 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_546)=dictionary64.getD 385 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_385]
  decide +kernel
theorem coefficient_547 : validRep representative_547 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_547)=dictionary64.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_548 : validRep representative_548 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_548)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_549 : validRep representative_549 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_549)=dictionary64.getD 237 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_237]
  decide +kernel
theorem coefficient_550 : validRep representative_550 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_550)=dictionary64.getD 265 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_265]
  decide +kernel
theorem coefficient_551 : validRep representative_551 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_551)=dictionary64.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_552 : validRep representative_552 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_552)=dictionary64.getD 192 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_192]
  decide +kernel
theorem coefficient_553 : validRep representative_553 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_553)=dictionary64.getD 338 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_338]
  decide +kernel
theorem coefficient_554 : validRep representative_554 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_554)=dictionary64.getD 202 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_202]
  decide +kernel
theorem coefficient_555 : validRep representative_555 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_555)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_556 : validRep representative_556 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_556)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_557 : validRep representative_557 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_557)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_558 : validRep representative_558 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_558)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_559 : validRep representative_559 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_559)=dictionary64.getD 239 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_239]
  decide +kernel
theorem coefficient_560 : validRep representative_560 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_560)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_561 : validRep representative_561 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_561)=dictionary64.getD 208 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_208]
  decide +kernel
theorem coefficient_562 : validRep representative_562 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_562)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_563 : validRep representative_563 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_563)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_564 : validRep representative_564 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_564)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_565 : validRep representative_565 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_565)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_566 : validRep representative_566 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_566)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_567 : validRep representative_567 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_567)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_568 : validRep representative_568 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_568)=dictionary64.getD 174 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_174]
  decide +kernel
theorem coefficient_569 : validRep representative_569 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_569)=dictionary64.getD 346 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_346]
  decide +kernel
theorem coefficient_570 : validRep representative_570 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_570)=dictionary64.getD 67 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_67]
  decide +kernel
theorem coefficient_571 : validRep representative_571 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_571)=dictionary64.getD 349 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_349]
  decide +kernel
theorem coefficient_572 : validRep representative_572 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_572)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_573 : validRep representative_573 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_573)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_574 : validRep representative_574 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_574)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_575 : validRep representative_575 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_575)=dictionary64.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_273]
  decide +kernel
def tree_008 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 544 (QuarticIntegerRepresentativeTree.Tree.branch 528 (QuarticIntegerRepresentativeTree.Tree.branch 520 (QuarticIntegerRepresentativeTree.Tree.branch 516 (QuarticIntegerRepresentativeTree.Tree.branch 514 (QuarticIntegerRepresentativeTree.Tree.branch 513 (QuarticIntegerRepresentativeTree.Tree.leaf 512 representative_512) (QuarticIntegerRepresentativeTree.Tree.leaf 513 representative_513)) (QuarticIntegerRepresentativeTree.Tree.branch 515 (QuarticIntegerRepresentativeTree.Tree.leaf 514 representative_514) (QuarticIntegerRepresentativeTree.Tree.leaf 515 representative_515))) (QuarticIntegerRepresentativeTree.Tree.branch 518 (QuarticIntegerRepresentativeTree.Tree.branch 517 (QuarticIntegerRepresentativeTree.Tree.leaf 516 representative_516) (QuarticIntegerRepresentativeTree.Tree.leaf 517 representative_517)) (QuarticIntegerRepresentativeTree.Tree.branch 519 (QuarticIntegerRepresentativeTree.Tree.leaf 518 representative_518) (QuarticIntegerRepresentativeTree.Tree.leaf 519 representative_519)))) (QuarticIntegerRepresentativeTree.Tree.branch 524 (QuarticIntegerRepresentativeTree.Tree.branch 522 (QuarticIntegerRepresentativeTree.Tree.branch 521 (QuarticIntegerRepresentativeTree.Tree.leaf 520 representative_520) (QuarticIntegerRepresentativeTree.Tree.leaf 521 representative_521)) (QuarticIntegerRepresentativeTree.Tree.branch 523 (QuarticIntegerRepresentativeTree.Tree.leaf 522 representative_522) (QuarticIntegerRepresentativeTree.Tree.leaf 523 representative_523))) (QuarticIntegerRepresentativeTree.Tree.branch 526 (QuarticIntegerRepresentativeTree.Tree.branch 525 (QuarticIntegerRepresentativeTree.Tree.leaf 524 representative_524) (QuarticIntegerRepresentativeTree.Tree.leaf 525 representative_525)) (QuarticIntegerRepresentativeTree.Tree.branch 527 (QuarticIntegerRepresentativeTree.Tree.leaf 526 representative_526) (QuarticIntegerRepresentativeTree.Tree.leaf 527 representative_527))))) (QuarticIntegerRepresentativeTree.Tree.branch 536 (QuarticIntegerRepresentativeTree.Tree.branch 532 (QuarticIntegerRepresentativeTree.Tree.branch 530 (QuarticIntegerRepresentativeTree.Tree.branch 529 (QuarticIntegerRepresentativeTree.Tree.leaf 528 representative_528) (QuarticIntegerRepresentativeTree.Tree.leaf 529 representative_529)) (QuarticIntegerRepresentativeTree.Tree.branch 531 (QuarticIntegerRepresentativeTree.Tree.leaf 530 representative_530) (QuarticIntegerRepresentativeTree.Tree.leaf 531 representative_531))) (QuarticIntegerRepresentativeTree.Tree.branch 534 (QuarticIntegerRepresentativeTree.Tree.branch 533 (QuarticIntegerRepresentativeTree.Tree.leaf 532 representative_532) (QuarticIntegerRepresentativeTree.Tree.leaf 533 representative_533)) (QuarticIntegerRepresentativeTree.Tree.branch 535 (QuarticIntegerRepresentativeTree.Tree.leaf 534 representative_534) (QuarticIntegerRepresentativeTree.Tree.leaf 535 representative_535)))) (QuarticIntegerRepresentativeTree.Tree.branch 540 (QuarticIntegerRepresentativeTree.Tree.branch 538 (QuarticIntegerRepresentativeTree.Tree.branch 537 (QuarticIntegerRepresentativeTree.Tree.leaf 536 representative_536) (QuarticIntegerRepresentativeTree.Tree.leaf 537 representative_537)) (QuarticIntegerRepresentativeTree.Tree.branch 539 (QuarticIntegerRepresentativeTree.Tree.leaf 538 representative_538) (QuarticIntegerRepresentativeTree.Tree.leaf 539 representative_539))) (QuarticIntegerRepresentativeTree.Tree.branch 542 (QuarticIntegerRepresentativeTree.Tree.branch 541 (QuarticIntegerRepresentativeTree.Tree.leaf 540 representative_540) (QuarticIntegerRepresentativeTree.Tree.leaf 541 representative_541)) (QuarticIntegerRepresentativeTree.Tree.branch 543 (QuarticIntegerRepresentativeTree.Tree.leaf 542 representative_542) (QuarticIntegerRepresentativeTree.Tree.leaf 543 representative_543)))))) (QuarticIntegerRepresentativeTree.Tree.branch 560 (QuarticIntegerRepresentativeTree.Tree.branch 552 (QuarticIntegerRepresentativeTree.Tree.branch 548 (QuarticIntegerRepresentativeTree.Tree.branch 546 (QuarticIntegerRepresentativeTree.Tree.branch 545 (QuarticIntegerRepresentativeTree.Tree.leaf 544 representative_544) (QuarticIntegerRepresentativeTree.Tree.leaf 545 representative_545)) (QuarticIntegerRepresentativeTree.Tree.branch 547 (QuarticIntegerRepresentativeTree.Tree.leaf 546 representative_546) (QuarticIntegerRepresentativeTree.Tree.leaf 547 representative_547))) (QuarticIntegerRepresentativeTree.Tree.branch 550 (QuarticIntegerRepresentativeTree.Tree.branch 549 (QuarticIntegerRepresentativeTree.Tree.leaf 548 representative_548) (QuarticIntegerRepresentativeTree.Tree.leaf 549 representative_549)) (QuarticIntegerRepresentativeTree.Tree.branch 551 (QuarticIntegerRepresentativeTree.Tree.leaf 550 representative_550) (QuarticIntegerRepresentativeTree.Tree.leaf 551 representative_551)))) (QuarticIntegerRepresentativeTree.Tree.branch 556 (QuarticIntegerRepresentativeTree.Tree.branch 554 (QuarticIntegerRepresentativeTree.Tree.branch 553 (QuarticIntegerRepresentativeTree.Tree.leaf 552 representative_552) (QuarticIntegerRepresentativeTree.Tree.leaf 553 representative_553)) (QuarticIntegerRepresentativeTree.Tree.branch 555 (QuarticIntegerRepresentativeTree.Tree.leaf 554 representative_554) (QuarticIntegerRepresentativeTree.Tree.leaf 555 representative_555))) (QuarticIntegerRepresentativeTree.Tree.branch 558 (QuarticIntegerRepresentativeTree.Tree.branch 557 (QuarticIntegerRepresentativeTree.Tree.leaf 556 representative_556) (QuarticIntegerRepresentativeTree.Tree.leaf 557 representative_557)) (QuarticIntegerRepresentativeTree.Tree.branch 559 (QuarticIntegerRepresentativeTree.Tree.leaf 558 representative_558) (QuarticIntegerRepresentativeTree.Tree.leaf 559 representative_559))))) (QuarticIntegerRepresentativeTree.Tree.branch 568 (QuarticIntegerRepresentativeTree.Tree.branch 564 (QuarticIntegerRepresentativeTree.Tree.branch 562 (QuarticIntegerRepresentativeTree.Tree.branch 561 (QuarticIntegerRepresentativeTree.Tree.leaf 560 representative_560) (QuarticIntegerRepresentativeTree.Tree.leaf 561 representative_561)) (QuarticIntegerRepresentativeTree.Tree.branch 563 (QuarticIntegerRepresentativeTree.Tree.leaf 562 representative_562) (QuarticIntegerRepresentativeTree.Tree.leaf 563 representative_563))) (QuarticIntegerRepresentativeTree.Tree.branch 566 (QuarticIntegerRepresentativeTree.Tree.branch 565 (QuarticIntegerRepresentativeTree.Tree.leaf 564 representative_564) (QuarticIntegerRepresentativeTree.Tree.leaf 565 representative_565)) (QuarticIntegerRepresentativeTree.Tree.branch 567 (QuarticIntegerRepresentativeTree.Tree.leaf 566 representative_566) (QuarticIntegerRepresentativeTree.Tree.leaf 567 representative_567)))) (QuarticIntegerRepresentativeTree.Tree.branch 572 (QuarticIntegerRepresentativeTree.Tree.branch 570 (QuarticIntegerRepresentativeTree.Tree.branch 569 (QuarticIntegerRepresentativeTree.Tree.leaf 568 representative_568) (QuarticIntegerRepresentativeTree.Tree.leaf 569 representative_569)) (QuarticIntegerRepresentativeTree.Tree.branch 571 (QuarticIntegerRepresentativeTree.Tree.leaf 570 representative_570) (QuarticIntegerRepresentativeTree.Tree.leaf 571 representative_571))) (QuarticIntegerRepresentativeTree.Tree.branch 574 (QuarticIntegerRepresentativeTree.Tree.branch 573 (QuarticIntegerRepresentativeTree.Tree.leaf 572 representative_572) (QuarticIntegerRepresentativeTree.Tree.leaf 573 representative_573)) (QuarticIntegerRepresentativeTree.Tree.branch 575 (QuarticIntegerRepresentativeTree.Tree.leaf 574 representative_574) (QuarticIntegerRepresentativeTree.Tree.leaf 575 representative_575)))))))
theorem accepted_008 : All validRep tree_008 := ⟨⟨⟨⟨⟨⟨coefficient_512,coefficient_513⟩,⟨coefficient_514,coefficient_515⟩⟩,⟨⟨coefficient_516,coefficient_517⟩,⟨coefficient_518,coefficient_519⟩⟩⟩,⟨⟨⟨coefficient_520,coefficient_521⟩,⟨coefficient_522,coefficient_523⟩⟩,⟨⟨coefficient_524,coefficient_525⟩,⟨coefficient_526,coefficient_527⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_528,coefficient_529⟩,⟨coefficient_530,coefficient_531⟩⟩,⟨⟨coefficient_532,coefficient_533⟩,⟨coefficient_534,coefficient_535⟩⟩⟩,⟨⟨⟨coefficient_536,coefficient_537⟩,⟨coefficient_538,coefficient_539⟩⟩,⟨⟨coefficient_540,coefficient_541⟩,⟨coefficient_542,coefficient_543⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_544,coefficient_545⟩,⟨coefficient_546,coefficient_547⟩⟩,⟨⟨coefficient_548,coefficient_549⟩,⟨coefficient_550,coefficient_551⟩⟩⟩,⟨⟨⟨coefficient_552,coefficient_553⟩,⟨coefficient_554,coefficient_555⟩⟩,⟨⟨coefficient_556,coefficient_557⟩,⟨coefficient_558,coefficient_559⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_560,coefficient_561⟩,⟨coefficient_562,coefficient_563⟩⟩,⟨⟨coefficient_564,coefficient_565⟩,⟨coefficient_566,coefficient_567⟩⟩⟩,⟨⟨⟨coefficient_568,coefficient_569⟩,⟨coefficient_570,coefficient_571⟩⟩,⟨⟨coefficient_572,coefficient_573⟩,⟨coefficient_574,coefficient_575⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

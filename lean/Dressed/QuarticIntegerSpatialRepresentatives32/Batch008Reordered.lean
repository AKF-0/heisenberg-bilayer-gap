import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_512 : Rep := ⟨![0,5,15,17],268⟩
def representative_513 : Rep := ⟨![0,5,15,18],508⟩
def representative_514 : Rep := ⟨![0,5,15,20],272⟩
def representative_515 : Rep := ⟨![0,5,15,21],508⟩
def representative_516 : Rep := ⟨![0,5,15,22],508⟩
def representative_517 : Rep := ⟨![0,5,15,23],508⟩
def representative_518 : Rep := ⟨![0,5,15,26],508⟩
def representative_519 : Rep := ⟨![0,5,16,21],508⟩
def representative_520 : Rep := ⟨![0,5,16,22],508⟩
def representative_521 : Rep := ⟨![0,5,16,23],508⟩
def representative_522 : Rep := ⟨![0,5,17,20],508⟩
def representative_523 : Rep := ⟨![0,5,17,22],508⟩
def representative_524 : Rep := ⟨![0,5,17,23],508⟩
def representative_525 : Rep := ⟨![0,5,18,23],508⟩
def representative_526 : Rep := ⟨![0,5,19,22],508⟩
def representative_527 : Rep := ⟨![0,6,1,7],470⟩
def representative_528 : Rep := ⟨![0,6,1,8],458⟩
def representative_529 : Rep := ⟨![0,6,1,9],75⟩
def representative_530 : Rep := ⟨![0,6,1,10],444⟩
def representative_531 : Rep := ⟨![0,6,1,11],109⟩
def representative_532 : Rep := ⟨![0,6,1,12],118⟩
def representative_533 : Rep := ⟨![0,6,1,13],384⟩
def representative_534 : Rep := ⟨![0,6,1,14],161⟩
def representative_535 : Rep := ⟨![0,6,1,15],339⟩
def representative_536 : Rep := ⟨![0,6,1,16],304⟩
def representative_537 : Rep := ⟨![0,6,1,17],262⟩
def representative_538 : Rep := ⟨![0,6,1,18],311⟩
def representative_539 : Rep := ⟨![0,6,1,19],262⟩
def representative_540 : Rep := ⟨![0,6,1,20],119⟩
def representative_541 : Rep := ⟨![0,6,1,21],381⟩
def representative_542 : Rep := ⟨![0,6,1,22],268⟩
def representative_543 : Rep := ⟨![0,6,1,23],317⟩
def representative_544 : Rep := ⟨![0,6,1,24],456⟩
def representative_545 : Rep := ⟨![0,6,1,25],77⟩
def representative_546 : Rep := ⟨![0,6,1,26],422⟩
def representative_547 : Rep := ⟨![0,6,1,27],110⟩
def representative_548 : Rep := ⟨![0,6,1,31],466⟩
def representative_549 : Rep := ⟨![0,6,2,4],471⟩
def representative_550 : Rep := ⟨![0,6,2,8],107⟩
def representative_551 : Rep := ⟨![0,6,2,9],465⟩
def representative_552 : Rep := ⟨![0,6,2,10],37⟩
def representative_553 : Rep := ⟨![0,6,2,12],340⟩
def representative_554 : Rep := ⟨![0,6,2,13],111⟩
def representative_555 : Rep := ⟨![0,6,2,14],455⟩
def representative_556 : Rep := ⟨![0,6,2,16],268⟩
def representative_557 : Rep := ⟨![0,6,2,17],316⟩
def representative_558 : Rep := ⟨![0,6,2,18],120⟩
def representative_559 : Rep := ⟨![0,6,2,20],312⟩
def representative_560 : Rep := ⟨![0,6,2,21],262⟩
def representative_561 : Rep := ⟨![0,6,2,22],380⟩
def representative_562 : Rep := ⟨![0,6,2,24],159⟩
def representative_563 : Rep := ⟨![0,6,2,25],421⟩
def representative_564 : Rep := ⟨![0,6,2,26],81⟩
def representative_565 : Rep := ⟨![0,6,2,28],446⟩
def representative_566 : Rep := ⟨![0,6,8,14],343⟩
def representative_567 : Rep := ⟨![0,6,8,16],195⟩
def representative_568 : Rep := ⟨![0,6,8,17],325⟩
def representative_569 : Rep := ⟨![0,6,8,18],258⟩
def representative_570 : Rep := ⟨![0,6,8,20],312⟩
def representative_571 : Rep := ⟨![0,6,8,21],268⟩
def representative_572 : Rep := ⟨![0,6,8,22],278⟩
def representative_573 : Rep := ⟨![0,6,8,24],187⟩
def representative_574 : Rep := ⟨![0,6,8,25],325⟩
def representative_575 : Rep := ⟨![0,6,8,26],253⟩
theorem coefficient_512 : validRep representative_512 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_512)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_513 : validRep representative_513 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_513)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_514 : validRep representative_514 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_514)=dictionary32.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_515 : validRep representative_515 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_515)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_516 : validRep representative_516 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_516)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_517 : validRep representative_517 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_517)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_518 : validRep representative_518 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_518)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_519 : validRep representative_519 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_519)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_520 : validRep representative_520 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_520)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_521 : validRep representative_521 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_521)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_522 : validRep representative_522 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_522)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_523 : validRep representative_523 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_523)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_524 : validRep representative_524 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_524)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_525 : validRep representative_525 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_525)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_526 : validRep representative_526 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_526)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_527 : validRep representative_527 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_527)=dictionary32.getD 470 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_470]
  decide +kernel
theorem coefficient_528 : validRep representative_528 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_528)=dictionary32.getD 458 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_458]
  decide +kernel
theorem coefficient_529 : validRep representative_529 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_529)=dictionary32.getD 75 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_75]
  decide +kernel
theorem coefficient_530 : validRep representative_530 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_530)=dictionary32.getD 444 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_444]
  decide +kernel
theorem coefficient_531 : validRep representative_531 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_531)=dictionary32.getD 109 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_109]
  decide +kernel
theorem coefficient_532 : validRep representative_532 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_532)=dictionary32.getD 118 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_118]
  decide +kernel
theorem coefficient_533 : validRep representative_533 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_533)=dictionary32.getD 384 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_384]
  decide +kernel
theorem coefficient_534 : validRep representative_534 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_534)=dictionary32.getD 161 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_161]
  decide +kernel
theorem coefficient_535 : validRep representative_535 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_535)=dictionary32.getD 339 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_339]
  decide +kernel
theorem coefficient_536 : validRep representative_536 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_536)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_537 : validRep representative_537 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_537)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_538 : validRep representative_538 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_538)=dictionary32.getD 311 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_311]
  decide +kernel
theorem coefficient_539 : validRep representative_539 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_539)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_540 : validRep representative_540 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_540)=dictionary32.getD 119 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_119]
  decide +kernel
theorem coefficient_541 : validRep representative_541 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_541)=dictionary32.getD 381 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_381]
  decide +kernel
theorem coefficient_542 : validRep representative_542 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_542)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_543 : validRep representative_543 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_543)=dictionary32.getD 317 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_317]
  decide +kernel
theorem coefficient_544 : validRep representative_544 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_544)=dictionary32.getD 456 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_456]
  decide +kernel
theorem coefficient_545 : validRep representative_545 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_545)=dictionary32.getD 77 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_77]
  decide +kernel
theorem coefficient_546 : validRep representative_546 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_546)=dictionary32.getD 422 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_422]
  decide +kernel
theorem coefficient_547 : validRep representative_547 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_547)=dictionary32.getD 110 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_110]
  decide +kernel
theorem coefficient_548 : validRep representative_548 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_548)=dictionary32.getD 466 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_466]
  decide +kernel
theorem coefficient_549 : validRep representative_549 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_549)=dictionary32.getD 471 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_471]
  decide +kernel
theorem coefficient_550 : validRep representative_550 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_550)=dictionary32.getD 107 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_107]
  decide +kernel
theorem coefficient_551 : validRep representative_551 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_551)=dictionary32.getD 465 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_465]
  decide +kernel
theorem coefficient_552 : validRep representative_552 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_552)=dictionary32.getD 37 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_37]
  decide +kernel
theorem coefficient_553 : validRep representative_553 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_553)=dictionary32.getD 340 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_340]
  decide +kernel
theorem coefficient_554 : validRep representative_554 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_554)=dictionary32.getD 111 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_111]
  decide +kernel
theorem coefficient_555 : validRep representative_555 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_555)=dictionary32.getD 455 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_455]
  decide +kernel
theorem coefficient_556 : validRep representative_556 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_556)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_557 : validRep representative_557 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_557)=dictionary32.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_558 : validRep representative_558 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_558)=dictionary32.getD 120 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_120]
  decide +kernel
theorem coefficient_559 : validRep representative_559 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_559)=dictionary32.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_560 : validRep representative_560 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_560)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_561 : validRep representative_561 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_561)=dictionary32.getD 380 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_380]
  decide +kernel
theorem coefficient_562 : validRep representative_562 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_562)=dictionary32.getD 159 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_159]
  decide +kernel
theorem coefficient_563 : validRep representative_563 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_563)=dictionary32.getD 421 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_421]
  decide +kernel
theorem coefficient_564 : validRep representative_564 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_564)=dictionary32.getD 81 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_81]
  decide +kernel
theorem coefficient_565 : validRep representative_565 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_565)=dictionary32.getD 446 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_446]
  decide +kernel
theorem coefficient_566 : validRep representative_566 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_566)=dictionary32.getD 343 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_343]
  decide +kernel
theorem coefficient_567 : validRep representative_567 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_567)=dictionary32.getD 195 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_195]
  decide +kernel
theorem coefficient_568 : validRep representative_568 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_568)=dictionary32.getD 325 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_325]
  decide +kernel
theorem coefficient_569 : validRep representative_569 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_569)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_570 : validRep representative_570 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_570)=dictionary32.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_571 : validRep representative_571 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_571)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_572 : validRep representative_572 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_572)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_573 : validRep representative_573 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_573)=dictionary32.getD 187 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_187]
  decide +kernel
theorem coefficient_574 : validRep representative_574 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_574)=dictionary32.getD 325 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_325]
  decide +kernel
theorem coefficient_575 : validRep representative_575 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_575)=dictionary32.getD 253 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_253]
  decide +kernel
def tree_008 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 544 (QuarticIntegerRepresentativeTree.Tree.branch 528 (QuarticIntegerRepresentativeTree.Tree.branch 520 (QuarticIntegerRepresentativeTree.Tree.branch 516 (QuarticIntegerRepresentativeTree.Tree.branch 514 (QuarticIntegerRepresentativeTree.Tree.branch 513 (QuarticIntegerRepresentativeTree.Tree.leaf 512 representative_512) (QuarticIntegerRepresentativeTree.Tree.leaf 513 representative_513)) (QuarticIntegerRepresentativeTree.Tree.branch 515 (QuarticIntegerRepresentativeTree.Tree.leaf 514 representative_514) (QuarticIntegerRepresentativeTree.Tree.leaf 515 representative_515))) (QuarticIntegerRepresentativeTree.Tree.branch 518 (QuarticIntegerRepresentativeTree.Tree.branch 517 (QuarticIntegerRepresentativeTree.Tree.leaf 516 representative_516) (QuarticIntegerRepresentativeTree.Tree.leaf 517 representative_517)) (QuarticIntegerRepresentativeTree.Tree.branch 519 (QuarticIntegerRepresentativeTree.Tree.leaf 518 representative_518) (QuarticIntegerRepresentativeTree.Tree.leaf 519 representative_519)))) (QuarticIntegerRepresentativeTree.Tree.branch 524 (QuarticIntegerRepresentativeTree.Tree.branch 522 (QuarticIntegerRepresentativeTree.Tree.branch 521 (QuarticIntegerRepresentativeTree.Tree.leaf 520 representative_520) (QuarticIntegerRepresentativeTree.Tree.leaf 521 representative_521)) (QuarticIntegerRepresentativeTree.Tree.branch 523 (QuarticIntegerRepresentativeTree.Tree.leaf 522 representative_522) (QuarticIntegerRepresentativeTree.Tree.leaf 523 representative_523))) (QuarticIntegerRepresentativeTree.Tree.branch 526 (QuarticIntegerRepresentativeTree.Tree.branch 525 (QuarticIntegerRepresentativeTree.Tree.leaf 524 representative_524) (QuarticIntegerRepresentativeTree.Tree.leaf 525 representative_525)) (QuarticIntegerRepresentativeTree.Tree.branch 527 (QuarticIntegerRepresentativeTree.Tree.leaf 526 representative_526) (QuarticIntegerRepresentativeTree.Tree.leaf 527 representative_527))))) (QuarticIntegerRepresentativeTree.Tree.branch 536 (QuarticIntegerRepresentativeTree.Tree.branch 532 (QuarticIntegerRepresentativeTree.Tree.branch 530 (QuarticIntegerRepresentativeTree.Tree.branch 529 (QuarticIntegerRepresentativeTree.Tree.leaf 528 representative_528) (QuarticIntegerRepresentativeTree.Tree.leaf 529 representative_529)) (QuarticIntegerRepresentativeTree.Tree.branch 531 (QuarticIntegerRepresentativeTree.Tree.leaf 530 representative_530) (QuarticIntegerRepresentativeTree.Tree.leaf 531 representative_531))) (QuarticIntegerRepresentativeTree.Tree.branch 534 (QuarticIntegerRepresentativeTree.Tree.branch 533 (QuarticIntegerRepresentativeTree.Tree.leaf 532 representative_532) (QuarticIntegerRepresentativeTree.Tree.leaf 533 representative_533)) (QuarticIntegerRepresentativeTree.Tree.branch 535 (QuarticIntegerRepresentativeTree.Tree.leaf 534 representative_534) (QuarticIntegerRepresentativeTree.Tree.leaf 535 representative_535)))) (QuarticIntegerRepresentativeTree.Tree.branch 540 (QuarticIntegerRepresentativeTree.Tree.branch 538 (QuarticIntegerRepresentativeTree.Tree.branch 537 (QuarticIntegerRepresentativeTree.Tree.leaf 536 representative_536) (QuarticIntegerRepresentativeTree.Tree.leaf 537 representative_537)) (QuarticIntegerRepresentativeTree.Tree.branch 539 (QuarticIntegerRepresentativeTree.Tree.leaf 538 representative_538) (QuarticIntegerRepresentativeTree.Tree.leaf 539 representative_539))) (QuarticIntegerRepresentativeTree.Tree.branch 542 (QuarticIntegerRepresentativeTree.Tree.branch 541 (QuarticIntegerRepresentativeTree.Tree.leaf 540 representative_540) (QuarticIntegerRepresentativeTree.Tree.leaf 541 representative_541)) (QuarticIntegerRepresentativeTree.Tree.branch 543 (QuarticIntegerRepresentativeTree.Tree.leaf 542 representative_542) (QuarticIntegerRepresentativeTree.Tree.leaf 543 representative_543)))))) (QuarticIntegerRepresentativeTree.Tree.branch 560 (QuarticIntegerRepresentativeTree.Tree.branch 552 (QuarticIntegerRepresentativeTree.Tree.branch 548 (QuarticIntegerRepresentativeTree.Tree.branch 546 (QuarticIntegerRepresentativeTree.Tree.branch 545 (QuarticIntegerRepresentativeTree.Tree.leaf 544 representative_544) (QuarticIntegerRepresentativeTree.Tree.leaf 545 representative_545)) (QuarticIntegerRepresentativeTree.Tree.branch 547 (QuarticIntegerRepresentativeTree.Tree.leaf 546 representative_546) (QuarticIntegerRepresentativeTree.Tree.leaf 547 representative_547))) (QuarticIntegerRepresentativeTree.Tree.branch 550 (QuarticIntegerRepresentativeTree.Tree.branch 549 (QuarticIntegerRepresentativeTree.Tree.leaf 548 representative_548) (QuarticIntegerRepresentativeTree.Tree.leaf 549 representative_549)) (QuarticIntegerRepresentativeTree.Tree.branch 551 (QuarticIntegerRepresentativeTree.Tree.leaf 550 representative_550) (QuarticIntegerRepresentativeTree.Tree.leaf 551 representative_551)))) (QuarticIntegerRepresentativeTree.Tree.branch 556 (QuarticIntegerRepresentativeTree.Tree.branch 554 (QuarticIntegerRepresentativeTree.Tree.branch 553 (QuarticIntegerRepresentativeTree.Tree.leaf 552 representative_552) (QuarticIntegerRepresentativeTree.Tree.leaf 553 representative_553)) (QuarticIntegerRepresentativeTree.Tree.branch 555 (QuarticIntegerRepresentativeTree.Tree.leaf 554 representative_554) (QuarticIntegerRepresentativeTree.Tree.leaf 555 representative_555))) (QuarticIntegerRepresentativeTree.Tree.branch 558 (QuarticIntegerRepresentativeTree.Tree.branch 557 (QuarticIntegerRepresentativeTree.Tree.leaf 556 representative_556) (QuarticIntegerRepresentativeTree.Tree.leaf 557 representative_557)) (QuarticIntegerRepresentativeTree.Tree.branch 559 (QuarticIntegerRepresentativeTree.Tree.leaf 558 representative_558) (QuarticIntegerRepresentativeTree.Tree.leaf 559 representative_559))))) (QuarticIntegerRepresentativeTree.Tree.branch 568 (QuarticIntegerRepresentativeTree.Tree.branch 564 (QuarticIntegerRepresentativeTree.Tree.branch 562 (QuarticIntegerRepresentativeTree.Tree.branch 561 (QuarticIntegerRepresentativeTree.Tree.leaf 560 representative_560) (QuarticIntegerRepresentativeTree.Tree.leaf 561 representative_561)) (QuarticIntegerRepresentativeTree.Tree.branch 563 (QuarticIntegerRepresentativeTree.Tree.leaf 562 representative_562) (QuarticIntegerRepresentativeTree.Tree.leaf 563 representative_563))) (QuarticIntegerRepresentativeTree.Tree.branch 566 (QuarticIntegerRepresentativeTree.Tree.branch 565 (QuarticIntegerRepresentativeTree.Tree.leaf 564 representative_564) (QuarticIntegerRepresentativeTree.Tree.leaf 565 representative_565)) (QuarticIntegerRepresentativeTree.Tree.branch 567 (QuarticIntegerRepresentativeTree.Tree.leaf 566 representative_566) (QuarticIntegerRepresentativeTree.Tree.leaf 567 representative_567)))) (QuarticIntegerRepresentativeTree.Tree.branch 572 (QuarticIntegerRepresentativeTree.Tree.branch 570 (QuarticIntegerRepresentativeTree.Tree.branch 569 (QuarticIntegerRepresentativeTree.Tree.leaf 568 representative_568) (QuarticIntegerRepresentativeTree.Tree.leaf 569 representative_569)) (QuarticIntegerRepresentativeTree.Tree.branch 571 (QuarticIntegerRepresentativeTree.Tree.leaf 570 representative_570) (QuarticIntegerRepresentativeTree.Tree.leaf 571 representative_571))) (QuarticIntegerRepresentativeTree.Tree.branch 574 (QuarticIntegerRepresentativeTree.Tree.branch 573 (QuarticIntegerRepresentativeTree.Tree.leaf 572 representative_572) (QuarticIntegerRepresentativeTree.Tree.leaf 573 representative_573)) (QuarticIntegerRepresentativeTree.Tree.branch 575 (QuarticIntegerRepresentativeTree.Tree.leaf 574 representative_574) (QuarticIntegerRepresentativeTree.Tree.leaf 575 representative_575)))))))
theorem accepted_008 : All validRep tree_008 := ⟨⟨⟨⟨⟨⟨coefficient_512,coefficient_513⟩,⟨coefficient_514,coefficient_515⟩⟩,⟨⟨coefficient_516,coefficient_517⟩,⟨coefficient_518,coefficient_519⟩⟩⟩,⟨⟨⟨coefficient_520,coefficient_521⟩,⟨coefficient_522,coefficient_523⟩⟩,⟨⟨coefficient_524,coefficient_525⟩,⟨coefficient_526,coefficient_527⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_528,coefficient_529⟩,⟨coefficient_530,coefficient_531⟩⟩,⟨⟨coefficient_532,coefficient_533⟩,⟨coefficient_534,coefficient_535⟩⟩⟩,⟨⟨⟨coefficient_536,coefficient_537⟩,⟨coefficient_538,coefficient_539⟩⟩,⟨⟨coefficient_540,coefficient_541⟩,⟨coefficient_542,coefficient_543⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_544,coefficient_545⟩,⟨coefficient_546,coefficient_547⟩⟩,⟨⟨coefficient_548,coefficient_549⟩,⟨coefficient_550,coefficient_551⟩⟩⟩,⟨⟨⟨coefficient_552,coefficient_553⟩,⟨coefficient_554,coefficient_555⟩⟩,⟨⟨coefficient_556,coefficient_557⟩,⟨coefficient_558,coefficient_559⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_560,coefficient_561⟩,⟨coefficient_562,coefficient_563⟩⟩,⟨⟨coefficient_564,coefficient_565⟩,⟨coefficient_566,coefficient_567⟩⟩⟩,⟨⟨⟨coefficient_568,coefficient_569⟩,⟨coefficient_570,coefficient_571⟩⟩,⟨⟨coefficient_572,coefficient_573⟩,⟨coefficient_574,coefficient_575⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

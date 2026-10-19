import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_448 : Rep := ⟨![0,5,9,30],413⟩
def representative_449 : Rep := ⟨![0,5,9,31],140⟩
def representative_450 : Rep := ⟨![0,5,10,12],169⟩
def representative_451 : Rep := ⟨![0,5,10,15],338⟩
def representative_452 : Rep := ⟨![0,5,10,16],307⟩
def representative_453 : Rep := ⟨![0,5,10,17],219⟩
def representative_454 : Rep := ⟨![0,5,10,18],322⟩
def representative_455 : Rep := ⟨![0,5,10,19],258⟩
def representative_456 : Rep := ⟨![0,5,10,20],268⟩
def representative_457 : Rep := ⟨![0,5,10,21],290⟩
def representative_458 : Rep := ⟨![0,5,10,22],268⟩
def representative_459 : Rep := ⟨![0,5,10,23],508⟩
def representative_460 : Rep := ⟨![0,5,10,24],322⟩
def representative_461 : Rep := ⟨![0,5,10,25],219⟩
def representative_462 : Rep := ⟨![0,5,10,26],307⟩
def representative_463 : Rep := ⟨![0,5,10,27],258⟩
def representative_464 : Rep := ⟨![0,5,10,30],169⟩
def representative_465 : Rep := ⟨![0,5,10,31],338⟩
def representative_466 : Rep := ⟨![0,5,11,12],344⟩
def representative_467 : Rep := ⟨![0,5,11,13],167⟩
def representative_468 : Rep := ⟨![0,5,11,14],341⟩
def representative_469 : Rep := ⟨![0,5,11,16],251⟩
def representative_470 : Rep := ⟨![0,5,11,17],310⟩
def representative_471 : Rep := ⟨![0,5,11,18],252⟩
def representative_472 : Rep := ⟨![0,5,11,19],321⟩
def representative_473 : Rep := ⟨![0,5,11,20],297⟩
def representative_474 : Rep := ⟨![0,5,11,21],262⟩
def representative_475 : Rep := ⟨![0,5,11,22],508⟩
def representative_476 : Rep := ⟨![0,5,11,23],260⟩
def representative_477 : Rep := ⟨![0,5,11,24],193⟩
def representative_478 : Rep := ⟨![0,5,11,25],331⟩
def representative_479 : Rep := ⟨![0,5,11,26],255⟩
def representative_480 : Rep := ⟨![0,5,11,27],321⟩
def representative_481 : Rep := ⟨![0,5,11,30],341⟩
def representative_482 : Rep := ⟨![0,5,12,17],310⟩
def representative_483 : Rep := ⟨![0,5,12,18],260⟩
def representative_484 : Rep := ⟨![0,5,12,19],297⟩
def representative_485 : Rep := ⟨![0,5,12,20],292⟩
def representative_486 : Rep := ⟨![0,5,12,21],264⟩
def representative_487 : Rep := ⟨![0,5,12,22],508⟩
def representative_488 : Rep := ⟨![0,5,12,23],267⟩
def representative_489 : Rep := ⟨![0,5,12,24],236⟩
def representative_490 : Rep := ⟨![0,5,12,25],310⟩
def representative_491 : Rep := ⟨![0,5,12,26],262⟩
def representative_492 : Rep := ⟨![0,5,12,27],297⟩
def representative_493 : Rep := ⟨![0,5,13,16],307⟩
def representative_494 : Rep := ⟨![0,5,13,18],307⟩
def representative_495 : Rep := ⟨![0,5,13,19],268⟩
def representative_496 : Rep := ⟨![0,5,13,20],269⟩
def representative_497 : Rep := ⟨![0,5,13,21],290⟩
def representative_498 : Rep := ⟨![0,5,13,22],271⟩
def representative_499 : Rep := ⟨![0,5,13,23],508⟩
def representative_500 : Rep := ⟨![0,5,13,24],307⟩
def representative_501 : Rep := ⟨![0,5,13,26],290⟩
def representative_502 : Rep := ⟨![0,5,13,27],268⟩
def representative_503 : Rep := ⟨![0,5,14,16],268⟩
def representative_504 : Rep := ⟨![0,5,14,19],508⟩
def representative_505 : Rep := ⟨![0,5,14,20],508⟩
def representative_506 : Rep := ⟨![0,5,14,21],271⟩
def representative_507 : Rep := ⟨![0,5,14,22],508⟩
def representative_508 : Rep := ⟨![0,5,14,23],508⟩
def representative_509 : Rep := ⟨![0,5,14,26],268⟩
def representative_510 : Rep := ⟨![0,5,14,27],508⟩
def representative_511 : Rep := ⟨![0,5,15,16],508⟩
theorem coefficient_448 : validRep representative_448 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_448)=dictionary32.getD 413 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_413]
  decide +kernel
theorem coefficient_449 : validRep representative_449 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_449)=dictionary32.getD 140 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_140]
  decide +kernel
theorem coefficient_450 : validRep representative_450 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_450)=dictionary32.getD 169 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_169]
  decide +kernel
theorem coefficient_451 : validRep representative_451 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_451)=dictionary32.getD 338 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_338]
  decide +kernel
theorem coefficient_452 : validRep representative_452 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_452)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_453 : validRep representative_453 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_453)=dictionary32.getD 219 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_219]
  decide +kernel
theorem coefficient_454 : validRep representative_454 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_454)=dictionary32.getD 322 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_322]
  decide +kernel
theorem coefficient_455 : validRep representative_455 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_455)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_456 : validRep representative_456 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_456)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_457 : validRep representative_457 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_457)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_458 : validRep representative_458 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_458)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_459 : validRep representative_459 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_459)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_460 : validRep representative_460 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_460)=dictionary32.getD 322 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_322]
  decide +kernel
theorem coefficient_461 : validRep representative_461 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_461)=dictionary32.getD 219 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_219]
  decide +kernel
theorem coefficient_462 : validRep representative_462 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_462)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_463 : validRep representative_463 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_463)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_464 : validRep representative_464 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_464)=dictionary32.getD 169 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_169]
  decide +kernel
theorem coefficient_465 : validRep representative_465 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_465)=dictionary32.getD 338 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_338]
  decide +kernel
theorem coefficient_466 : validRep representative_466 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_466)=dictionary32.getD 344 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_344]
  decide +kernel
theorem coefficient_467 : validRep representative_467 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_467)=dictionary32.getD 167 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_167]
  decide +kernel
theorem coefficient_468 : validRep representative_468 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_468)=dictionary32.getD 341 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_341]
  decide +kernel
theorem coefficient_469 : validRep representative_469 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_469)=dictionary32.getD 251 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_251]
  decide +kernel
theorem coefficient_470 : validRep representative_470 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_470)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_471 : validRep representative_471 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_471)=dictionary32.getD 252 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_252]
  decide +kernel
theorem coefficient_472 : validRep representative_472 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_472)=dictionary32.getD 321 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_321]
  decide +kernel
theorem coefficient_473 : validRep representative_473 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_473)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_474 : validRep representative_474 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_474)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_475 : validRep representative_475 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_475)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_476 : validRep representative_476 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_476)=dictionary32.getD 260 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_260]
  decide +kernel
theorem coefficient_477 : validRep representative_477 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_477)=dictionary32.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_478 : validRep representative_478 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_478)=dictionary32.getD 331 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_331]
  decide +kernel
theorem coefficient_479 : validRep representative_479 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_479)=dictionary32.getD 255 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_255]
  decide +kernel
theorem coefficient_480 : validRep representative_480 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_480)=dictionary32.getD 321 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_321]
  decide +kernel
theorem coefficient_481 : validRep representative_481 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_481)=dictionary32.getD 341 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_341]
  decide +kernel
theorem coefficient_482 : validRep representative_482 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_482)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_483 : validRep representative_483 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_483)=dictionary32.getD 260 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_260]
  decide +kernel
theorem coefficient_484 : validRep representative_484 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_484)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_485 : validRep representative_485 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_485)=dictionary32.getD 292 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_292]
  decide +kernel
theorem coefficient_486 : validRep representative_486 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_486)=dictionary32.getD 264 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_264]
  decide +kernel
theorem coefficient_487 : validRep representative_487 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_487)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_488 : validRep representative_488 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_488)=dictionary32.getD 267 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_267]
  decide +kernel
theorem coefficient_489 : validRep representative_489 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_489)=dictionary32.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_490 : validRep representative_490 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_490)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_491 : validRep representative_491 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_491)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_492 : validRep representative_492 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_492)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_493 : validRep representative_493 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_493)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_494 : validRep representative_494 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_494)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_495 : validRep representative_495 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_495)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_496 : validRep representative_496 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_496)=dictionary32.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_497 : validRep representative_497 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_497)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_498 : validRep representative_498 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_498)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_499 : validRep representative_499 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_499)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_500 : validRep representative_500 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_500)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_501 : validRep representative_501 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_501)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_502 : validRep representative_502 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_502)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_503 : validRep representative_503 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_503)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_504 : validRep representative_504 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_504)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_505 : validRep representative_505 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_505)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_506 : validRep representative_506 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_506)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_507 : validRep representative_507 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_507)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_508 : validRep representative_508 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_508)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_509 : validRep representative_509 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_509)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_510 : validRep representative_510 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_510)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_511 : validRep representative_511 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_511)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_007 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 480 (QuarticIntegerRepresentativeTree.Tree.branch 464 (QuarticIntegerRepresentativeTree.Tree.branch 456 (QuarticIntegerRepresentativeTree.Tree.branch 452 (QuarticIntegerRepresentativeTree.Tree.branch 450 (QuarticIntegerRepresentativeTree.Tree.branch 449 (QuarticIntegerRepresentativeTree.Tree.leaf 448 representative_448) (QuarticIntegerRepresentativeTree.Tree.leaf 449 representative_449)) (QuarticIntegerRepresentativeTree.Tree.branch 451 (QuarticIntegerRepresentativeTree.Tree.leaf 450 representative_450) (QuarticIntegerRepresentativeTree.Tree.leaf 451 representative_451))) (QuarticIntegerRepresentativeTree.Tree.branch 454 (QuarticIntegerRepresentativeTree.Tree.branch 453 (QuarticIntegerRepresentativeTree.Tree.leaf 452 representative_452) (QuarticIntegerRepresentativeTree.Tree.leaf 453 representative_453)) (QuarticIntegerRepresentativeTree.Tree.branch 455 (QuarticIntegerRepresentativeTree.Tree.leaf 454 representative_454) (QuarticIntegerRepresentativeTree.Tree.leaf 455 representative_455)))) (QuarticIntegerRepresentativeTree.Tree.branch 460 (QuarticIntegerRepresentativeTree.Tree.branch 458 (QuarticIntegerRepresentativeTree.Tree.branch 457 (QuarticIntegerRepresentativeTree.Tree.leaf 456 representative_456) (QuarticIntegerRepresentativeTree.Tree.leaf 457 representative_457)) (QuarticIntegerRepresentativeTree.Tree.branch 459 (QuarticIntegerRepresentativeTree.Tree.leaf 458 representative_458) (QuarticIntegerRepresentativeTree.Tree.leaf 459 representative_459))) (QuarticIntegerRepresentativeTree.Tree.branch 462 (QuarticIntegerRepresentativeTree.Tree.branch 461 (QuarticIntegerRepresentativeTree.Tree.leaf 460 representative_460) (QuarticIntegerRepresentativeTree.Tree.leaf 461 representative_461)) (QuarticIntegerRepresentativeTree.Tree.branch 463 (QuarticIntegerRepresentativeTree.Tree.leaf 462 representative_462) (QuarticIntegerRepresentativeTree.Tree.leaf 463 representative_463))))) (QuarticIntegerRepresentativeTree.Tree.branch 472 (QuarticIntegerRepresentativeTree.Tree.branch 468 (QuarticIntegerRepresentativeTree.Tree.branch 466 (QuarticIntegerRepresentativeTree.Tree.branch 465 (QuarticIntegerRepresentativeTree.Tree.leaf 464 representative_464) (QuarticIntegerRepresentativeTree.Tree.leaf 465 representative_465)) (QuarticIntegerRepresentativeTree.Tree.branch 467 (QuarticIntegerRepresentativeTree.Tree.leaf 466 representative_466) (QuarticIntegerRepresentativeTree.Tree.leaf 467 representative_467))) (QuarticIntegerRepresentativeTree.Tree.branch 470 (QuarticIntegerRepresentativeTree.Tree.branch 469 (QuarticIntegerRepresentativeTree.Tree.leaf 468 representative_468) (QuarticIntegerRepresentativeTree.Tree.leaf 469 representative_469)) (QuarticIntegerRepresentativeTree.Tree.branch 471 (QuarticIntegerRepresentativeTree.Tree.leaf 470 representative_470) (QuarticIntegerRepresentativeTree.Tree.leaf 471 representative_471)))) (QuarticIntegerRepresentativeTree.Tree.branch 476 (QuarticIntegerRepresentativeTree.Tree.branch 474 (QuarticIntegerRepresentativeTree.Tree.branch 473 (QuarticIntegerRepresentativeTree.Tree.leaf 472 representative_472) (QuarticIntegerRepresentativeTree.Tree.leaf 473 representative_473)) (QuarticIntegerRepresentativeTree.Tree.branch 475 (QuarticIntegerRepresentativeTree.Tree.leaf 474 representative_474) (QuarticIntegerRepresentativeTree.Tree.leaf 475 representative_475))) (QuarticIntegerRepresentativeTree.Tree.branch 478 (QuarticIntegerRepresentativeTree.Tree.branch 477 (QuarticIntegerRepresentativeTree.Tree.leaf 476 representative_476) (QuarticIntegerRepresentativeTree.Tree.leaf 477 representative_477)) (QuarticIntegerRepresentativeTree.Tree.branch 479 (QuarticIntegerRepresentativeTree.Tree.leaf 478 representative_478) (QuarticIntegerRepresentativeTree.Tree.leaf 479 representative_479)))))) (QuarticIntegerRepresentativeTree.Tree.branch 496 (QuarticIntegerRepresentativeTree.Tree.branch 488 (QuarticIntegerRepresentativeTree.Tree.branch 484 (QuarticIntegerRepresentativeTree.Tree.branch 482 (QuarticIntegerRepresentativeTree.Tree.branch 481 (QuarticIntegerRepresentativeTree.Tree.leaf 480 representative_480) (QuarticIntegerRepresentativeTree.Tree.leaf 481 representative_481)) (QuarticIntegerRepresentativeTree.Tree.branch 483 (QuarticIntegerRepresentativeTree.Tree.leaf 482 representative_482) (QuarticIntegerRepresentativeTree.Tree.leaf 483 representative_483))) (QuarticIntegerRepresentativeTree.Tree.branch 486 (QuarticIntegerRepresentativeTree.Tree.branch 485 (QuarticIntegerRepresentativeTree.Tree.leaf 484 representative_484) (QuarticIntegerRepresentativeTree.Tree.leaf 485 representative_485)) (QuarticIntegerRepresentativeTree.Tree.branch 487 (QuarticIntegerRepresentativeTree.Tree.leaf 486 representative_486) (QuarticIntegerRepresentativeTree.Tree.leaf 487 representative_487)))) (QuarticIntegerRepresentativeTree.Tree.branch 492 (QuarticIntegerRepresentativeTree.Tree.branch 490 (QuarticIntegerRepresentativeTree.Tree.branch 489 (QuarticIntegerRepresentativeTree.Tree.leaf 488 representative_488) (QuarticIntegerRepresentativeTree.Tree.leaf 489 representative_489)) (QuarticIntegerRepresentativeTree.Tree.branch 491 (QuarticIntegerRepresentativeTree.Tree.leaf 490 representative_490) (QuarticIntegerRepresentativeTree.Tree.leaf 491 representative_491))) (QuarticIntegerRepresentativeTree.Tree.branch 494 (QuarticIntegerRepresentativeTree.Tree.branch 493 (QuarticIntegerRepresentativeTree.Tree.leaf 492 representative_492) (QuarticIntegerRepresentativeTree.Tree.leaf 493 representative_493)) (QuarticIntegerRepresentativeTree.Tree.branch 495 (QuarticIntegerRepresentativeTree.Tree.leaf 494 representative_494) (QuarticIntegerRepresentativeTree.Tree.leaf 495 representative_495))))) (QuarticIntegerRepresentativeTree.Tree.branch 504 (QuarticIntegerRepresentativeTree.Tree.branch 500 (QuarticIntegerRepresentativeTree.Tree.branch 498 (QuarticIntegerRepresentativeTree.Tree.branch 497 (QuarticIntegerRepresentativeTree.Tree.leaf 496 representative_496) (QuarticIntegerRepresentativeTree.Tree.leaf 497 representative_497)) (QuarticIntegerRepresentativeTree.Tree.branch 499 (QuarticIntegerRepresentativeTree.Tree.leaf 498 representative_498) (QuarticIntegerRepresentativeTree.Tree.leaf 499 representative_499))) (QuarticIntegerRepresentativeTree.Tree.branch 502 (QuarticIntegerRepresentativeTree.Tree.branch 501 (QuarticIntegerRepresentativeTree.Tree.leaf 500 representative_500) (QuarticIntegerRepresentativeTree.Tree.leaf 501 representative_501)) (QuarticIntegerRepresentativeTree.Tree.branch 503 (QuarticIntegerRepresentativeTree.Tree.leaf 502 representative_502) (QuarticIntegerRepresentativeTree.Tree.leaf 503 representative_503)))) (QuarticIntegerRepresentativeTree.Tree.branch 508 (QuarticIntegerRepresentativeTree.Tree.branch 506 (QuarticIntegerRepresentativeTree.Tree.branch 505 (QuarticIntegerRepresentativeTree.Tree.leaf 504 representative_504) (QuarticIntegerRepresentativeTree.Tree.leaf 505 representative_505)) (QuarticIntegerRepresentativeTree.Tree.branch 507 (QuarticIntegerRepresentativeTree.Tree.leaf 506 representative_506) (QuarticIntegerRepresentativeTree.Tree.leaf 507 representative_507))) (QuarticIntegerRepresentativeTree.Tree.branch 510 (QuarticIntegerRepresentativeTree.Tree.branch 509 (QuarticIntegerRepresentativeTree.Tree.leaf 508 representative_508) (QuarticIntegerRepresentativeTree.Tree.leaf 509 representative_509)) (QuarticIntegerRepresentativeTree.Tree.branch 511 (QuarticIntegerRepresentativeTree.Tree.leaf 510 representative_510) (QuarticIntegerRepresentativeTree.Tree.leaf 511 representative_511)))))))
theorem accepted_007 : All validRep tree_007 := ⟨⟨⟨⟨⟨⟨coefficient_448,coefficient_449⟩,⟨coefficient_450,coefficient_451⟩⟩,⟨⟨coefficient_452,coefficient_453⟩,⟨coefficient_454,coefficient_455⟩⟩⟩,⟨⟨⟨coefficient_456,coefficient_457⟩,⟨coefficient_458,coefficient_459⟩⟩,⟨⟨coefficient_460,coefficient_461⟩,⟨coefficient_462,coefficient_463⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_464,coefficient_465⟩,⟨coefficient_466,coefficient_467⟩⟩,⟨⟨coefficient_468,coefficient_469⟩,⟨coefficient_470,coefficient_471⟩⟩⟩,⟨⟨⟨coefficient_472,coefficient_473⟩,⟨coefficient_474,coefficient_475⟩⟩,⟨⟨coefficient_476,coefficient_477⟩,⟨coefficient_478,coefficient_479⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_480,coefficient_481⟩,⟨coefficient_482,coefficient_483⟩⟩,⟨⟨coefficient_484,coefficient_485⟩,⟨coefficient_486,coefficient_487⟩⟩⟩,⟨⟨⟨coefficient_488,coefficient_489⟩,⟨coefficient_490,coefficient_491⟩⟩,⟨⟨coefficient_492,coefficient_493⟩,⟨coefficient_494,coefficient_495⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_496,coefficient_497⟩,⟨coefficient_498,coefficient_499⟩⟩,⟨⟨coefficient_500,coefficient_501⟩,⟨coefficient_502,coefficient_503⟩⟩⟩,⟨⟨⟨coefficient_504,coefficient_505⟩,⟨coefficient_506,coefficient_507⟩⟩,⟨⟨coefficient_508,coefficient_509⟩,⟨coefficient_510,coefficient_511⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

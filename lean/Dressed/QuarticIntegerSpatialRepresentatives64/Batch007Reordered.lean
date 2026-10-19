import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_448 : Rep := ⟨![0,1,24,44],462⟩
def representative_449 : Rep := ⟨![0,1,24,45],462⟩
def representative_450 : Rep := ⟨![0,1,24,46],462⟩
def representative_451 : Rep := ⟨![0,1,24,47],264⟩
def representative_452 : Rep := ⟨![0,1,26,27],462⟩
def representative_453 : Rep := ⟨![0,1,26,28],462⟩
def representative_454 : Rep := ⟨![0,1,26,29],462⟩
def representative_455 : Rep := ⟨![0,1,26,30],462⟩
def representative_456 : Rep := ⟨![0,1,26,31],462⟩
def representative_457 : Rep := ⟨![0,1,26,32],462⟩
def representative_458 : Rep := ⟨![0,1,26,33],462⟩
def representative_459 : Rep := ⟨![0,1,26,35],462⟩
def representative_460 : Rep := ⟨![0,1,26,36],462⟩
def representative_461 : Rep := ⟨![0,1,26,37],462⟩
def representative_462 : Rep := ⟨![0,1,26,38],462⟩
def representative_463 : Rep := ⟨![0,1,26,39],462⟩
def representative_464 : Rep := ⟨![0,1,26,42],462⟩
def representative_465 : Rep := ⟨![0,1,26,43],462⟩
def representative_466 : Rep := ⟨![0,1,26,44],462⟩
def representative_467 : Rep := ⟨![0,1,26,45],462⟩
def representative_468 : Rep := ⟨![0,1,26,46],462⟩
def representative_469 : Rep := ⟨![0,1,26,47],462⟩
def representative_470 : Rep := ⟨![0,1,27,28],462⟩
def representative_471 : Rep := ⟨![0,1,27,29],462⟩
def representative_472 : Rep := ⟨![0,1,27,30],462⟩
def representative_473 : Rep := ⟨![0,1,27,32],462⟩
def representative_474 : Rep := ⟨![0,1,27,33],462⟩
def representative_475 : Rep := ⟨![0,1,27,34],462⟩
def representative_476 : Rep := ⟨![0,1,27,36],462⟩
def representative_477 : Rep := ⟨![0,1,27,37],462⟩
def representative_478 : Rep := ⟨![0,1,27,38],462⟩
def representative_479 : Rep := ⟨![0,1,27,39],462⟩
def representative_480 : Rep := ⟨![0,1,27,43],462⟩
def representative_481 : Rep := ⟨![0,1,27,44],462⟩
def representative_482 : Rep := ⟨![0,1,27,45],462⟩
def representative_483 : Rep := ⟨![0,1,27,46],462⟩
def representative_484 : Rep := ⟨![0,1,28,29],462⟩
def representative_485 : Rep := ⟨![0,1,28,32],462⟩
def representative_486 : Rep := ⟨![0,1,28,33],462⟩
def representative_487 : Rep := ⟨![0,1,28,34],462⟩
def representative_488 : Rep := ⟨![0,1,28,35],462⟩
def representative_489 : Rep := ⟨![0,1,28,36],462⟩
def representative_490 : Rep := ⟨![0,1,28,37],462⟩
def representative_491 : Rep := ⟨![0,1,28,38],462⟩
def representative_492 : Rep := ⟨![0,1,28,39],462⟩
def representative_493 : Rep := ⟨![0,1,28,44],462⟩
def representative_494 : Rep := ⟨![0,1,28,45],462⟩
def representative_495 : Rep := ⟨![0,1,32,33],462⟩
def representative_496 : Rep := ⟨![0,1,32,34],462⟩
def representative_497 : Rep := ⟨![0,1,32,35],462⟩
def representative_498 : Rep := ⟨![0,1,32,36],462⟩
def representative_499 : Rep := ⟨![0,1,32,37],462⟩
def representative_500 : Rep := ⟨![0,1,32,38],462⟩
def representative_501 : Rep := ⟨![0,1,32,39],462⟩
def representative_502 : Rep := ⟨![0,1,34,35],462⟩
def representative_503 : Rep := ⟨![0,1,34,36],462⟩
def representative_504 : Rep := ⟨![0,1,34,37],462⟩
def representative_505 : Rep := ⟨![0,1,34,38],462⟩
def representative_506 : Rep := ⟨![0,1,34,39],462⟩
def representative_507 : Rep := ⟨![0,1,35,36],462⟩
def representative_508 : Rep := ⟨![0,1,35,37],462⟩
def representative_509 : Rep := ⟨![0,1,35,38],462⟩
def representative_510 : Rep := ⟨![0,1,36,37],462⟩
def representative_511 : Rep := ⟨![0,2,1,3],459⟩
theorem coefficient_448 : validRep representative_448 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_448)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_449 : validRep representative_449 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_449)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_450 : validRep representative_450 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_450)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_451 : validRep representative_451 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_451)=dictionary64.getD 264 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_264]
  decide +kernel
theorem coefficient_452 : validRep representative_452 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_452)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_453 : validRep representative_453 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_453)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_454 : validRep representative_454 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_454)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_455 : validRep representative_455 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_455)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_456 : validRep representative_456 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_456)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_457 : validRep representative_457 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_457)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_458 : validRep representative_458 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_458)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_459 : validRep representative_459 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_459)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_460 : validRep representative_460 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_460)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_461 : validRep representative_461 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_461)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_462 : validRep representative_462 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_462)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_463 : validRep representative_463 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_463)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_464 : validRep representative_464 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_464)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_465 : validRep representative_465 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_465)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_466 : validRep representative_466 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_466)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_467 : validRep representative_467 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_467)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_468 : validRep representative_468 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_468)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_469 : validRep representative_469 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_469)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_470 : validRep representative_470 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_470)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_471 : validRep representative_471 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_471)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_472 : validRep representative_472 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_472)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_473 : validRep representative_473 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_473)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_474 : validRep representative_474 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_474)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_475 : validRep representative_475 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_475)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_476 : validRep representative_476 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_476)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_477 : validRep representative_477 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_477)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_478 : validRep representative_478 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_478)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_479 : validRep representative_479 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_479)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_480 : validRep representative_480 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_480)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_481 : validRep representative_481 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_481)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_482 : validRep representative_482 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_482)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_483 : validRep representative_483 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_483)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_484 : validRep representative_484 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_484)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_485 : validRep representative_485 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_485)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_486 : validRep representative_486 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_486)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_487 : validRep representative_487 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_487)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_488 : validRep representative_488 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_488)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_489 : validRep representative_489 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_489)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_490 : validRep representative_490 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_490)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_491 : validRep representative_491 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_491)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_492 : validRep representative_492 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_492)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_493 : validRep representative_493 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_493)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_494 : validRep representative_494 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_494)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_495 : validRep representative_495 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_495)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_496 : validRep representative_496 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_496)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_497 : validRep representative_497 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_497)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_498 : validRep representative_498 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_498)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_499 : validRep representative_499 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_499)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_500 : validRep representative_500 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_500)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_501 : validRep representative_501 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_501)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_502 : validRep representative_502 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_502)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_503 : validRep representative_503 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_503)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_504 : validRep representative_504 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_504)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_505 : validRep representative_505 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_505)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_506 : validRep representative_506 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_506)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_507 : validRep representative_507 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_507)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_508 : validRep representative_508 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_508)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_509 : validRep representative_509 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_509)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_510 : validRep representative_510 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_510)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_511 : validRep representative_511 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_511)=dictionary64.getD 459 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_459]
  decide +kernel
def tree_007 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 480 (QuarticIntegerRepresentativeTree.Tree.branch 464 (QuarticIntegerRepresentativeTree.Tree.branch 456 (QuarticIntegerRepresentativeTree.Tree.branch 452 (QuarticIntegerRepresentativeTree.Tree.branch 450 (QuarticIntegerRepresentativeTree.Tree.branch 449 (QuarticIntegerRepresentativeTree.Tree.leaf 448 representative_448) (QuarticIntegerRepresentativeTree.Tree.leaf 449 representative_449)) (QuarticIntegerRepresentativeTree.Tree.branch 451 (QuarticIntegerRepresentativeTree.Tree.leaf 450 representative_450) (QuarticIntegerRepresentativeTree.Tree.leaf 451 representative_451))) (QuarticIntegerRepresentativeTree.Tree.branch 454 (QuarticIntegerRepresentativeTree.Tree.branch 453 (QuarticIntegerRepresentativeTree.Tree.leaf 452 representative_452) (QuarticIntegerRepresentativeTree.Tree.leaf 453 representative_453)) (QuarticIntegerRepresentativeTree.Tree.branch 455 (QuarticIntegerRepresentativeTree.Tree.leaf 454 representative_454) (QuarticIntegerRepresentativeTree.Tree.leaf 455 representative_455)))) (QuarticIntegerRepresentativeTree.Tree.branch 460 (QuarticIntegerRepresentativeTree.Tree.branch 458 (QuarticIntegerRepresentativeTree.Tree.branch 457 (QuarticIntegerRepresentativeTree.Tree.leaf 456 representative_456) (QuarticIntegerRepresentativeTree.Tree.leaf 457 representative_457)) (QuarticIntegerRepresentativeTree.Tree.branch 459 (QuarticIntegerRepresentativeTree.Tree.leaf 458 representative_458) (QuarticIntegerRepresentativeTree.Tree.leaf 459 representative_459))) (QuarticIntegerRepresentativeTree.Tree.branch 462 (QuarticIntegerRepresentativeTree.Tree.branch 461 (QuarticIntegerRepresentativeTree.Tree.leaf 460 representative_460) (QuarticIntegerRepresentativeTree.Tree.leaf 461 representative_461)) (QuarticIntegerRepresentativeTree.Tree.branch 463 (QuarticIntegerRepresentativeTree.Tree.leaf 462 representative_462) (QuarticIntegerRepresentativeTree.Tree.leaf 463 representative_463))))) (QuarticIntegerRepresentativeTree.Tree.branch 472 (QuarticIntegerRepresentativeTree.Tree.branch 468 (QuarticIntegerRepresentativeTree.Tree.branch 466 (QuarticIntegerRepresentativeTree.Tree.branch 465 (QuarticIntegerRepresentativeTree.Tree.leaf 464 representative_464) (QuarticIntegerRepresentativeTree.Tree.leaf 465 representative_465)) (QuarticIntegerRepresentativeTree.Tree.branch 467 (QuarticIntegerRepresentativeTree.Tree.leaf 466 representative_466) (QuarticIntegerRepresentativeTree.Tree.leaf 467 representative_467))) (QuarticIntegerRepresentativeTree.Tree.branch 470 (QuarticIntegerRepresentativeTree.Tree.branch 469 (QuarticIntegerRepresentativeTree.Tree.leaf 468 representative_468) (QuarticIntegerRepresentativeTree.Tree.leaf 469 representative_469)) (QuarticIntegerRepresentativeTree.Tree.branch 471 (QuarticIntegerRepresentativeTree.Tree.leaf 470 representative_470) (QuarticIntegerRepresentativeTree.Tree.leaf 471 representative_471)))) (QuarticIntegerRepresentativeTree.Tree.branch 476 (QuarticIntegerRepresentativeTree.Tree.branch 474 (QuarticIntegerRepresentativeTree.Tree.branch 473 (QuarticIntegerRepresentativeTree.Tree.leaf 472 representative_472) (QuarticIntegerRepresentativeTree.Tree.leaf 473 representative_473)) (QuarticIntegerRepresentativeTree.Tree.branch 475 (QuarticIntegerRepresentativeTree.Tree.leaf 474 representative_474) (QuarticIntegerRepresentativeTree.Tree.leaf 475 representative_475))) (QuarticIntegerRepresentativeTree.Tree.branch 478 (QuarticIntegerRepresentativeTree.Tree.branch 477 (QuarticIntegerRepresentativeTree.Tree.leaf 476 representative_476) (QuarticIntegerRepresentativeTree.Tree.leaf 477 representative_477)) (QuarticIntegerRepresentativeTree.Tree.branch 479 (QuarticIntegerRepresentativeTree.Tree.leaf 478 representative_478) (QuarticIntegerRepresentativeTree.Tree.leaf 479 representative_479)))))) (QuarticIntegerRepresentativeTree.Tree.branch 496 (QuarticIntegerRepresentativeTree.Tree.branch 488 (QuarticIntegerRepresentativeTree.Tree.branch 484 (QuarticIntegerRepresentativeTree.Tree.branch 482 (QuarticIntegerRepresentativeTree.Tree.branch 481 (QuarticIntegerRepresentativeTree.Tree.leaf 480 representative_480) (QuarticIntegerRepresentativeTree.Tree.leaf 481 representative_481)) (QuarticIntegerRepresentativeTree.Tree.branch 483 (QuarticIntegerRepresentativeTree.Tree.leaf 482 representative_482) (QuarticIntegerRepresentativeTree.Tree.leaf 483 representative_483))) (QuarticIntegerRepresentativeTree.Tree.branch 486 (QuarticIntegerRepresentativeTree.Tree.branch 485 (QuarticIntegerRepresentativeTree.Tree.leaf 484 representative_484) (QuarticIntegerRepresentativeTree.Tree.leaf 485 representative_485)) (QuarticIntegerRepresentativeTree.Tree.branch 487 (QuarticIntegerRepresentativeTree.Tree.leaf 486 representative_486) (QuarticIntegerRepresentativeTree.Tree.leaf 487 representative_487)))) (QuarticIntegerRepresentativeTree.Tree.branch 492 (QuarticIntegerRepresentativeTree.Tree.branch 490 (QuarticIntegerRepresentativeTree.Tree.branch 489 (QuarticIntegerRepresentativeTree.Tree.leaf 488 representative_488) (QuarticIntegerRepresentativeTree.Tree.leaf 489 representative_489)) (QuarticIntegerRepresentativeTree.Tree.branch 491 (QuarticIntegerRepresentativeTree.Tree.leaf 490 representative_490) (QuarticIntegerRepresentativeTree.Tree.leaf 491 representative_491))) (QuarticIntegerRepresentativeTree.Tree.branch 494 (QuarticIntegerRepresentativeTree.Tree.branch 493 (QuarticIntegerRepresentativeTree.Tree.leaf 492 representative_492) (QuarticIntegerRepresentativeTree.Tree.leaf 493 representative_493)) (QuarticIntegerRepresentativeTree.Tree.branch 495 (QuarticIntegerRepresentativeTree.Tree.leaf 494 representative_494) (QuarticIntegerRepresentativeTree.Tree.leaf 495 representative_495))))) (QuarticIntegerRepresentativeTree.Tree.branch 504 (QuarticIntegerRepresentativeTree.Tree.branch 500 (QuarticIntegerRepresentativeTree.Tree.branch 498 (QuarticIntegerRepresentativeTree.Tree.branch 497 (QuarticIntegerRepresentativeTree.Tree.leaf 496 representative_496) (QuarticIntegerRepresentativeTree.Tree.leaf 497 representative_497)) (QuarticIntegerRepresentativeTree.Tree.branch 499 (QuarticIntegerRepresentativeTree.Tree.leaf 498 representative_498) (QuarticIntegerRepresentativeTree.Tree.leaf 499 representative_499))) (QuarticIntegerRepresentativeTree.Tree.branch 502 (QuarticIntegerRepresentativeTree.Tree.branch 501 (QuarticIntegerRepresentativeTree.Tree.leaf 500 representative_500) (QuarticIntegerRepresentativeTree.Tree.leaf 501 representative_501)) (QuarticIntegerRepresentativeTree.Tree.branch 503 (QuarticIntegerRepresentativeTree.Tree.leaf 502 representative_502) (QuarticIntegerRepresentativeTree.Tree.leaf 503 representative_503)))) (QuarticIntegerRepresentativeTree.Tree.branch 508 (QuarticIntegerRepresentativeTree.Tree.branch 506 (QuarticIntegerRepresentativeTree.Tree.branch 505 (QuarticIntegerRepresentativeTree.Tree.leaf 504 representative_504) (QuarticIntegerRepresentativeTree.Tree.leaf 505 representative_505)) (QuarticIntegerRepresentativeTree.Tree.branch 507 (QuarticIntegerRepresentativeTree.Tree.leaf 506 representative_506) (QuarticIntegerRepresentativeTree.Tree.leaf 507 representative_507))) (QuarticIntegerRepresentativeTree.Tree.branch 510 (QuarticIntegerRepresentativeTree.Tree.branch 509 (QuarticIntegerRepresentativeTree.Tree.leaf 508 representative_508) (QuarticIntegerRepresentativeTree.Tree.leaf 509 representative_509)) (QuarticIntegerRepresentativeTree.Tree.branch 511 (QuarticIntegerRepresentativeTree.Tree.leaf 510 representative_510) (QuarticIntegerRepresentativeTree.Tree.leaf 511 representative_511)))))))
theorem accepted_007 : All validRep tree_007 := ⟨⟨⟨⟨⟨⟨coefficient_448,coefficient_449⟩,⟨coefficient_450,coefficient_451⟩⟩,⟨⟨coefficient_452,coefficient_453⟩,⟨coefficient_454,coefficient_455⟩⟩⟩,⟨⟨⟨coefficient_456,coefficient_457⟩,⟨coefficient_458,coefficient_459⟩⟩,⟨⟨coefficient_460,coefficient_461⟩,⟨coefficient_462,coefficient_463⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_464,coefficient_465⟩,⟨coefficient_466,coefficient_467⟩⟩,⟨⟨coefficient_468,coefficient_469⟩,⟨coefficient_470,coefficient_471⟩⟩⟩,⟨⟨⟨coefficient_472,coefficient_473⟩,⟨coefficient_474,coefficient_475⟩⟩,⟨⟨coefficient_476,coefficient_477⟩,⟨coefficient_478,coefficient_479⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_480,coefficient_481⟩,⟨coefficient_482,coefficient_483⟩⟩,⟨⟨coefficient_484,coefficient_485⟩,⟨coefficient_486,coefficient_487⟩⟩⟩,⟨⟨⟨coefficient_488,coefficient_489⟩,⟨coefficient_490,coefficient_491⟩⟩,⟨⟨coefficient_492,coefficient_493⟩,⟨coefficient_494,coefficient_495⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_496,coefficient_497⟩,⟨coefficient_498,coefficient_499⟩⟩,⟨⟨coefficient_500,coefficient_501⟩,⟨coefficient_502,coefficient_503⟩⟩⟩,⟨⟨⟨coefficient_504,coefficient_505⟩,⟨coefficient_506,coefficient_507⟩⟩,⟨⟨coefficient_508,coefficient_509⟩,⟨coefficient_510,coefficient_511⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

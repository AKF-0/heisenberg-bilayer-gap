import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_384 : Rep := ⟨![0,1,19,33],462⟩
def representative_385 : Rep := ⟨![0,1,19,34],462⟩
def representative_386 : Rep := ⟨![0,1,19,35],462⟩
def representative_387 : Rep := ⟨![0,1,19,36],462⟩
def representative_388 : Rep := ⟨![0,1,19,37],462⟩
def representative_389 : Rep := ⟨![0,1,19,38],462⟩
def representative_390 : Rep := ⟨![0,1,19,39],462⟩
def representative_391 : Rep := ⟨![0,1,19,40],462⟩
def representative_392 : Rep := ⟨![0,1,19,41],269⟩
def representative_393 : Rep := ⟨![0,1,19,42],462⟩
def representative_394 : Rep := ⟨![0,1,19,43],462⟩
def representative_395 : Rep := ⟨![0,1,19,44],462⟩
def representative_396 : Rep := ⟨![0,1,19,45],462⟩
def representative_397 : Rep := ⟨![0,1,19,46],462⟩
def representative_398 : Rep := ⟨![0,1,19,47],462⟩
def representative_399 : Rep := ⟨![0,1,19,51],462⟩
def representative_400 : Rep := ⟨![0,1,19,52],462⟩
def representative_401 : Rep := ⟨![0,1,19,53],462⟩
def representative_402 : Rep := ⟨![0,1,19,54],462⟩
def representative_403 : Rep := ⟨![0,1,20,21],462⟩
def representative_404 : Rep := ⟨![0,1,20,24],462⟩
def representative_405 : Rep := ⟨![0,1,20,25],462⟩
def representative_406 : Rep := ⟨![0,1,20,26],462⟩
def representative_407 : Rep := ⟨![0,1,20,27],462⟩
def representative_408 : Rep := ⟨![0,1,20,28],462⟩
def representative_409 : Rep := ⟨![0,1,20,29],462⟩
def representative_410 : Rep := ⟨![0,1,20,30],462⟩
def representative_411 : Rep := ⟨![0,1,20,31],462⟩
def representative_412 : Rep := ⟨![0,1,20,32],462⟩
def representative_413 : Rep := ⟨![0,1,20,33],462⟩
def representative_414 : Rep := ⟨![0,1,20,34],462⟩
def representative_415 : Rep := ⟨![0,1,20,35],462⟩
def representative_416 : Rep := ⟨![0,1,20,36],462⟩
def representative_417 : Rep := ⟨![0,1,20,37],462⟩
def representative_418 : Rep := ⟨![0,1,20,38],462⟩
def representative_419 : Rep := ⟨![0,1,20,39],462⟩
def representative_420 : Rep := ⟨![0,1,20,40],462⟩
def representative_421 : Rep := ⟨![0,1,20,41],462⟩
def representative_422 : Rep := ⟨![0,1,20,42],462⟩
def representative_423 : Rep := ⟨![0,1,20,43],462⟩
def representative_424 : Rep := ⟨![0,1,20,44],462⟩
def representative_425 : Rep := ⟨![0,1,20,45],462⟩
def representative_426 : Rep := ⟨![0,1,20,46],462⟩
def representative_427 : Rep := ⟨![0,1,20,47],462⟩
def representative_428 : Rep := ⟨![0,1,20,52],462⟩
def representative_429 : Rep := ⟨![0,1,20,53],462⟩
def representative_430 : Rep := ⟨![0,1,24,25],186⟩
def representative_431 : Rep := ⟨![0,1,24,26],238⟩
def representative_432 : Rep := ⟨![0,1,24,27],241⟩
def representative_433 : Rep := ⟨![0,1,24,28],462⟩
def representative_434 : Rep := ⟨![0,1,24,29],241⟩
def representative_435 : Rep := ⟨![0,1,24,30],238⟩
def representative_436 : Rep := ⟨![0,1,24,31],274⟩
def representative_437 : Rep := ⟨![0,1,24,33],236⟩
def representative_438 : Rep := ⟨![0,1,24,34],243⟩
def representative_439 : Rep := ⟨![0,1,24,35],462⟩
def representative_440 : Rep := ⟨![0,1,24,36],462⟩
def representative_441 : Rep := ⟨![0,1,24,37],462⟩
def representative_442 : Rep := ⟨![0,1,24,38],243⟩
def representative_443 : Rep := ⟨![0,1,24,39],236⟩
def representative_444 : Rep := ⟨![0,1,24,40],207⟩
def representative_445 : Rep := ⟨![0,1,24,41],204⟩
def representative_446 : Rep := ⟨![0,1,24,42],462⟩
def representative_447 : Rep := ⟨![0,1,24,43],462⟩
theorem coefficient_384 : validRep representative_384 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_384)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_385 : validRep representative_385 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_385)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_386 : validRep representative_386 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_386)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_387 : validRep representative_387 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_387)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_388 : validRep representative_388 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_388)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_389 : validRep representative_389 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_389)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_390 : validRep representative_390 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_390)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_391 : validRep representative_391 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_391)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_392 : validRep representative_392 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_392)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_393 : validRep representative_393 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_393)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_394 : validRep representative_394 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_394)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_395 : validRep representative_395 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_395)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_396 : validRep representative_396 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_396)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_397 : validRep representative_397 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_397)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_398 : validRep representative_398 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_398)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_399 : validRep representative_399 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_399)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_400 : validRep representative_400 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_400)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_401 : validRep representative_401 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_401)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_402 : validRep representative_402 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_402)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_403 : validRep representative_403 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_403)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_404 : validRep representative_404 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_404)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_405 : validRep representative_405 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_405)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_406 : validRep representative_406 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_406)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_407 : validRep representative_407 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_407)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_408 : validRep representative_408 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_408)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_409 : validRep representative_409 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_409)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_410 : validRep representative_410 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_410)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_411 : validRep representative_411 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_411)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_412 : validRep representative_412 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_412)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_413 : validRep representative_413 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_413)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_414 : validRep representative_414 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_414)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_415 : validRep representative_415 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_415)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_416 : validRep representative_416 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_416)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_417 : validRep representative_417 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_417)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_418 : validRep representative_418 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_418)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_419 : validRep representative_419 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_419)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_420 : validRep representative_420 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_420)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_421 : validRep representative_421 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_421)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_422 : validRep representative_422 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_422)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_423 : validRep representative_423 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_423)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_424 : validRep representative_424 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_424)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_425 : validRep representative_425 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_425)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_426 : validRep representative_426 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_426)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_427 : validRep representative_427 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_427)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_428 : validRep representative_428 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_428)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_429 : validRep representative_429 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_429)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_430 : validRep representative_430 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_430)=dictionary64.getD 186 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_186]
  decide +kernel
theorem coefficient_431 : validRep representative_431 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_431)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_432 : validRep representative_432 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_432)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_433 : validRep representative_433 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_433)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_434 : validRep representative_434 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_434)=dictionary64.getD 241 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_241]
  decide +kernel
theorem coefficient_435 : validRep representative_435 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_435)=dictionary64.getD 238 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_238]
  decide +kernel
theorem coefficient_436 : validRep representative_436 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_436)=dictionary64.getD 274 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_274]
  decide +kernel
theorem coefficient_437 : validRep representative_437 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_437)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_438 : validRep representative_438 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_438)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_439 : validRep representative_439 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_439)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_440 : validRep representative_440 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_440)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_441 : validRep representative_441 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_441)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_442 : validRep representative_442 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_442)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_443 : validRep representative_443 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_443)=dictionary64.getD 236 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_236]
  decide +kernel
theorem coefficient_444 : validRep representative_444 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_444)=dictionary64.getD 207 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_207]
  decide +kernel
theorem coefficient_445 : validRep representative_445 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_445)=dictionary64.getD 204 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_204]
  decide +kernel
theorem coefficient_446 : validRep representative_446 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_446)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_447 : validRep representative_447 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_447)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_006 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 416 (QuarticIntegerRepresentativeTree.Tree.branch 400 (QuarticIntegerRepresentativeTree.Tree.branch 392 (QuarticIntegerRepresentativeTree.Tree.branch 388 (QuarticIntegerRepresentativeTree.Tree.branch 386 (QuarticIntegerRepresentativeTree.Tree.branch 385 (QuarticIntegerRepresentativeTree.Tree.leaf 384 representative_384) (QuarticIntegerRepresentativeTree.Tree.leaf 385 representative_385)) (QuarticIntegerRepresentativeTree.Tree.branch 387 (QuarticIntegerRepresentativeTree.Tree.leaf 386 representative_386) (QuarticIntegerRepresentativeTree.Tree.leaf 387 representative_387))) (QuarticIntegerRepresentativeTree.Tree.branch 390 (QuarticIntegerRepresentativeTree.Tree.branch 389 (QuarticIntegerRepresentativeTree.Tree.leaf 388 representative_388) (QuarticIntegerRepresentativeTree.Tree.leaf 389 representative_389)) (QuarticIntegerRepresentativeTree.Tree.branch 391 (QuarticIntegerRepresentativeTree.Tree.leaf 390 representative_390) (QuarticIntegerRepresentativeTree.Tree.leaf 391 representative_391)))) (QuarticIntegerRepresentativeTree.Tree.branch 396 (QuarticIntegerRepresentativeTree.Tree.branch 394 (QuarticIntegerRepresentativeTree.Tree.branch 393 (QuarticIntegerRepresentativeTree.Tree.leaf 392 representative_392) (QuarticIntegerRepresentativeTree.Tree.leaf 393 representative_393)) (QuarticIntegerRepresentativeTree.Tree.branch 395 (QuarticIntegerRepresentativeTree.Tree.leaf 394 representative_394) (QuarticIntegerRepresentativeTree.Tree.leaf 395 representative_395))) (QuarticIntegerRepresentativeTree.Tree.branch 398 (QuarticIntegerRepresentativeTree.Tree.branch 397 (QuarticIntegerRepresentativeTree.Tree.leaf 396 representative_396) (QuarticIntegerRepresentativeTree.Tree.leaf 397 representative_397)) (QuarticIntegerRepresentativeTree.Tree.branch 399 (QuarticIntegerRepresentativeTree.Tree.leaf 398 representative_398) (QuarticIntegerRepresentativeTree.Tree.leaf 399 representative_399))))) (QuarticIntegerRepresentativeTree.Tree.branch 408 (QuarticIntegerRepresentativeTree.Tree.branch 404 (QuarticIntegerRepresentativeTree.Tree.branch 402 (QuarticIntegerRepresentativeTree.Tree.branch 401 (QuarticIntegerRepresentativeTree.Tree.leaf 400 representative_400) (QuarticIntegerRepresentativeTree.Tree.leaf 401 representative_401)) (QuarticIntegerRepresentativeTree.Tree.branch 403 (QuarticIntegerRepresentativeTree.Tree.leaf 402 representative_402) (QuarticIntegerRepresentativeTree.Tree.leaf 403 representative_403))) (QuarticIntegerRepresentativeTree.Tree.branch 406 (QuarticIntegerRepresentativeTree.Tree.branch 405 (QuarticIntegerRepresentativeTree.Tree.leaf 404 representative_404) (QuarticIntegerRepresentativeTree.Tree.leaf 405 representative_405)) (QuarticIntegerRepresentativeTree.Tree.branch 407 (QuarticIntegerRepresentativeTree.Tree.leaf 406 representative_406) (QuarticIntegerRepresentativeTree.Tree.leaf 407 representative_407)))) (QuarticIntegerRepresentativeTree.Tree.branch 412 (QuarticIntegerRepresentativeTree.Tree.branch 410 (QuarticIntegerRepresentativeTree.Tree.branch 409 (QuarticIntegerRepresentativeTree.Tree.leaf 408 representative_408) (QuarticIntegerRepresentativeTree.Tree.leaf 409 representative_409)) (QuarticIntegerRepresentativeTree.Tree.branch 411 (QuarticIntegerRepresentativeTree.Tree.leaf 410 representative_410) (QuarticIntegerRepresentativeTree.Tree.leaf 411 representative_411))) (QuarticIntegerRepresentativeTree.Tree.branch 414 (QuarticIntegerRepresentativeTree.Tree.branch 413 (QuarticIntegerRepresentativeTree.Tree.leaf 412 representative_412) (QuarticIntegerRepresentativeTree.Tree.leaf 413 representative_413)) (QuarticIntegerRepresentativeTree.Tree.branch 415 (QuarticIntegerRepresentativeTree.Tree.leaf 414 representative_414) (QuarticIntegerRepresentativeTree.Tree.leaf 415 representative_415)))))) (QuarticIntegerRepresentativeTree.Tree.branch 432 (QuarticIntegerRepresentativeTree.Tree.branch 424 (QuarticIntegerRepresentativeTree.Tree.branch 420 (QuarticIntegerRepresentativeTree.Tree.branch 418 (QuarticIntegerRepresentativeTree.Tree.branch 417 (QuarticIntegerRepresentativeTree.Tree.leaf 416 representative_416) (QuarticIntegerRepresentativeTree.Tree.leaf 417 representative_417)) (QuarticIntegerRepresentativeTree.Tree.branch 419 (QuarticIntegerRepresentativeTree.Tree.leaf 418 representative_418) (QuarticIntegerRepresentativeTree.Tree.leaf 419 representative_419))) (QuarticIntegerRepresentativeTree.Tree.branch 422 (QuarticIntegerRepresentativeTree.Tree.branch 421 (QuarticIntegerRepresentativeTree.Tree.leaf 420 representative_420) (QuarticIntegerRepresentativeTree.Tree.leaf 421 representative_421)) (QuarticIntegerRepresentativeTree.Tree.branch 423 (QuarticIntegerRepresentativeTree.Tree.leaf 422 representative_422) (QuarticIntegerRepresentativeTree.Tree.leaf 423 representative_423)))) (QuarticIntegerRepresentativeTree.Tree.branch 428 (QuarticIntegerRepresentativeTree.Tree.branch 426 (QuarticIntegerRepresentativeTree.Tree.branch 425 (QuarticIntegerRepresentativeTree.Tree.leaf 424 representative_424) (QuarticIntegerRepresentativeTree.Tree.leaf 425 representative_425)) (QuarticIntegerRepresentativeTree.Tree.branch 427 (QuarticIntegerRepresentativeTree.Tree.leaf 426 representative_426) (QuarticIntegerRepresentativeTree.Tree.leaf 427 representative_427))) (QuarticIntegerRepresentativeTree.Tree.branch 430 (QuarticIntegerRepresentativeTree.Tree.branch 429 (QuarticIntegerRepresentativeTree.Tree.leaf 428 representative_428) (QuarticIntegerRepresentativeTree.Tree.leaf 429 representative_429)) (QuarticIntegerRepresentativeTree.Tree.branch 431 (QuarticIntegerRepresentativeTree.Tree.leaf 430 representative_430) (QuarticIntegerRepresentativeTree.Tree.leaf 431 representative_431))))) (QuarticIntegerRepresentativeTree.Tree.branch 440 (QuarticIntegerRepresentativeTree.Tree.branch 436 (QuarticIntegerRepresentativeTree.Tree.branch 434 (QuarticIntegerRepresentativeTree.Tree.branch 433 (QuarticIntegerRepresentativeTree.Tree.leaf 432 representative_432) (QuarticIntegerRepresentativeTree.Tree.leaf 433 representative_433)) (QuarticIntegerRepresentativeTree.Tree.branch 435 (QuarticIntegerRepresentativeTree.Tree.leaf 434 representative_434) (QuarticIntegerRepresentativeTree.Tree.leaf 435 representative_435))) (QuarticIntegerRepresentativeTree.Tree.branch 438 (QuarticIntegerRepresentativeTree.Tree.branch 437 (QuarticIntegerRepresentativeTree.Tree.leaf 436 representative_436) (QuarticIntegerRepresentativeTree.Tree.leaf 437 representative_437)) (QuarticIntegerRepresentativeTree.Tree.branch 439 (QuarticIntegerRepresentativeTree.Tree.leaf 438 representative_438) (QuarticIntegerRepresentativeTree.Tree.leaf 439 representative_439)))) (QuarticIntegerRepresentativeTree.Tree.branch 444 (QuarticIntegerRepresentativeTree.Tree.branch 442 (QuarticIntegerRepresentativeTree.Tree.branch 441 (QuarticIntegerRepresentativeTree.Tree.leaf 440 representative_440) (QuarticIntegerRepresentativeTree.Tree.leaf 441 representative_441)) (QuarticIntegerRepresentativeTree.Tree.branch 443 (QuarticIntegerRepresentativeTree.Tree.leaf 442 representative_442) (QuarticIntegerRepresentativeTree.Tree.leaf 443 representative_443))) (QuarticIntegerRepresentativeTree.Tree.branch 446 (QuarticIntegerRepresentativeTree.Tree.branch 445 (QuarticIntegerRepresentativeTree.Tree.leaf 444 representative_444) (QuarticIntegerRepresentativeTree.Tree.leaf 445 representative_445)) (QuarticIntegerRepresentativeTree.Tree.branch 447 (QuarticIntegerRepresentativeTree.Tree.leaf 446 representative_446) (QuarticIntegerRepresentativeTree.Tree.leaf 447 representative_447)))))))
theorem accepted_006 : All validRep tree_006 := ⟨⟨⟨⟨⟨⟨coefficient_384,coefficient_385⟩,⟨coefficient_386,coefficient_387⟩⟩,⟨⟨coefficient_388,coefficient_389⟩,⟨coefficient_390,coefficient_391⟩⟩⟩,⟨⟨⟨coefficient_392,coefficient_393⟩,⟨coefficient_394,coefficient_395⟩⟩,⟨⟨coefficient_396,coefficient_397⟩,⟨coefficient_398,coefficient_399⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_400,coefficient_401⟩,⟨coefficient_402,coefficient_403⟩⟩,⟨⟨coefficient_404,coefficient_405⟩,⟨coefficient_406,coefficient_407⟩⟩⟩,⟨⟨⟨coefficient_408,coefficient_409⟩,⟨coefficient_410,coefficient_411⟩⟩,⟨⟨coefficient_412,coefficient_413⟩,⟨coefficient_414,coefficient_415⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_416,coefficient_417⟩,⟨coefficient_418,coefficient_419⟩⟩,⟨⟨coefficient_420,coefficient_421⟩,⟨coefficient_422,coefficient_423⟩⟩⟩,⟨⟨⟨coefficient_424,coefficient_425⟩,⟨coefficient_426,coefficient_427⟩⟩,⟨⟨coefficient_428,coefficient_429⟩,⟨coefficient_430,coefficient_431⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_432,coefficient_433⟩,⟨coefficient_434,coefficient_435⟩⟩,⟨⟨coefficient_436,coefficient_437⟩,⟨coefficient_438,coefficient_439⟩⟩⟩,⟨⟨⟨coefficient_440,coefficient_441⟩,⟨coefficient_442,coefficient_443⟩⟩,⟨⟨coefficient_444,coefficient_445⟩,⟨coefficient_446,coefficient_447⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

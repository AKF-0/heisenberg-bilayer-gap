import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_384 : Rep := ⟨![0,5,2,25],134⟩
def representative_385 : Rep := ⟨![0,5,2,26],390⟩
def representative_386 : Rep := ⟨![0,5,2,27],136⟩
def representative_387 : Rep := ⟨![0,5,2,28],54⟩
def representative_388 : Rep := ⟨![0,5,2,29],438⟩
def representative_389 : Rep := ⟨![0,5,2,31],432⟩
def representative_390 : Rep := ⟨![0,5,3,6],448⟩
def representative_391 : Rep := ⟨![0,5,3,8],74⟩
def representative_392 : Rep := ⟨![0,5,3,9],440⟩
def representative_393 : Rep := ⟨![0,5,3,10],127⟩
def representative_394 : Rep := ⟨![0,5,3,11],430⟩
def representative_395 : Rep := ⟨![0,5,3,12],375⟩
def representative_396 : Rep := ⟨![0,5,3,13],153⟩
def representative_397 : Rep := ⟨![0,5,3,14],335⟩
def representative_398 : Rep := ⟨![0,5,3,15],173⟩
def representative_399 : Rep := ⟨![0,5,3,16],229⟩
def representative_400 : Rep := ⟨![0,5,3,17],310⟩
def representative_401 : Rep := ⟨![0,5,3,18],262⟩
def representative_402 : Rep := ⟨![0,5,3,19],508⟩
def representative_403 : Rep := ⟨![0,5,3,20],374⟩
def representative_404 : Rep := ⟨![0,5,3,21],209⟩
def representative_405 : Rep := ⟨![0,5,3,22],508⟩
def representative_406 : Rep := ⟨![0,5,3,23],174⟩
def representative_407 : Rep := ⟨![0,5,3,24],76⟩
def representative_408 : Rep := ⟨![0,5,3,25],415⟩
def representative_409 : Rep := ⟨![0,5,3,26],133⟩
def representative_410 : Rep := ⟨![0,5,3,27],429⟩
def representative_411 : Rep := ⟨![0,5,3,29],52⟩
def representative_412 : Rep := ⟨![0,5,3,30],441⟩
def representative_413 : Rep := ⟨![0,5,8,13],409⟩
def representative_414 : Rep := ⟨![0,5,8,14],137⟩
def representative_415 : Rep := ⟨![0,5,8,15],389⟩
def representative_416 : Rep := ⟨![0,5,8,16],358⟩
def representative_417 : Rep := ⟨![0,5,8,17],172⟩
def representative_418 : Rep := ⟨![0,5,8,18],307⟩
def representative_419 : Rep := ⟨![0,5,8,19],188⟩
def representative_420 : Rep := ⟨![0,5,8,20],212⟩
def representative_421 : Rep := ⟨![0,5,8,21],307⟩
def representative_422 : Rep := ⟨![0,5,8,22],508⟩
def representative_423 : Rep := ⟨![0,5,8,23],290⟩
def representative_424 : Rep := ⟨![0,5,8,24],358⟩
def representative_425 : Rep := ⟨![0,5,8,25],178⟩
def representative_426 : Rep := ⟨![0,5,8,26],322⟩
def representative_427 : Rep := ⟨![0,5,8,27],196⟩
def representative_428 : Rep := ⟨![0,5,8,28],79⟩
def representative_429 : Rep := ⟨![0,5,8,29],408⟩
def representative_430 : Rep := ⟨![0,5,8,30],143⟩
def representative_431 : Rep := ⟨![0,5,8,31],388⟩
def representative_432 : Rep := ⟨![0,5,9,12],418⟩
def representative_433 : Rep := ⟨![0,5,9,14],417⟩
def representative_434 : Rep := ⟨![0,5,9,15],157⟩
def representative_435 : Rep := ⟨![0,5,9,16],204⟩
def representative_436 : Rep := ⟨![0,5,9,17],379⟩
def representative_437 : Rep := ⟨![0,5,9,18],205⟩
def representative_438 : Rep := ⟨![0,5,9,19],508⟩
def representative_439 : Rep := ⟨![0,5,9,20],297⟩
def representative_440 : Rep := ⟨![0,5,9,21],228⟩
def representative_441 : Rep := ⟨![0,5,9,22],508⟩
def representative_442 : Rep := ⟨![0,5,9,23],268⟩
def representative_443 : Rep := ⟨![0,5,9,24],176⟩
def representative_444 : Rep := ⟨![0,5,9,25],372⟩
def representative_445 : Rep := ⟨![0,5,9,26],206⟩
def representative_446 : Rep := ⟨![0,5,9,27],321⟩
def representative_447 : Rep := ⟨![0,5,9,28],434⟩
theorem coefficient_384 : validRep representative_384 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_384)=dictionary32.getD 134 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_134]
  decide +kernel
theorem coefficient_385 : validRep representative_385 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_385)=dictionary32.getD 390 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_390]
  decide +kernel
theorem coefficient_386 : validRep representative_386 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_386)=dictionary32.getD 136 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_136]
  decide +kernel
theorem coefficient_387 : validRep representative_387 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_387)=dictionary32.getD 54 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_54]
  decide +kernel
theorem coefficient_388 : validRep representative_388 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_388)=dictionary32.getD 438 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_438]
  decide +kernel
theorem coefficient_389 : validRep representative_389 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_389)=dictionary32.getD 432 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_432]
  decide +kernel
theorem coefficient_390 : validRep representative_390 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_390)=dictionary32.getD 448 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_448]
  decide +kernel
theorem coefficient_391 : validRep representative_391 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_391)=dictionary32.getD 74 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_74]
  decide +kernel
theorem coefficient_392 : validRep representative_392 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_392)=dictionary32.getD 440 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_440]
  decide +kernel
theorem coefficient_393 : validRep representative_393 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_393)=dictionary32.getD 127 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_127]
  decide +kernel
theorem coefficient_394 : validRep representative_394 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_394)=dictionary32.getD 430 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_430]
  decide +kernel
theorem coefficient_395 : validRep representative_395 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_395)=dictionary32.getD 375 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_375]
  decide +kernel
theorem coefficient_396 : validRep representative_396 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_396)=dictionary32.getD 153 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_153]
  decide +kernel
theorem coefficient_397 : validRep representative_397 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_397)=dictionary32.getD 335 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_335]
  decide +kernel
theorem coefficient_398 : validRep representative_398 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_398)=dictionary32.getD 173 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_173]
  decide +kernel
theorem coefficient_399 : validRep representative_399 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_399)=dictionary32.getD 229 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_229]
  decide +kernel
theorem coefficient_400 : validRep representative_400 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_400)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_401 : validRep representative_401 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_401)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_402 : validRep representative_402 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_402)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_403 : validRep representative_403 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_403)=dictionary32.getD 374 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_374]
  decide +kernel
theorem coefficient_404 : validRep representative_404 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_404)=dictionary32.getD 209 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_209]
  decide +kernel
theorem coefficient_405 : validRep representative_405 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_405)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_406 : validRep representative_406 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_406)=dictionary32.getD 174 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_174]
  decide +kernel
theorem coefficient_407 : validRep representative_407 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_407)=dictionary32.getD 76 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_76]
  decide +kernel
theorem coefficient_408 : validRep representative_408 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_408)=dictionary32.getD 415 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_415]
  decide +kernel
theorem coefficient_409 : validRep representative_409 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_409)=dictionary32.getD 133 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_133]
  decide +kernel
theorem coefficient_410 : validRep representative_410 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_410)=dictionary32.getD 429 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_429]
  decide +kernel
theorem coefficient_411 : validRep representative_411 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_411)=dictionary32.getD 52 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_52]
  decide +kernel
theorem coefficient_412 : validRep representative_412 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_412)=dictionary32.getD 441 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_441]
  decide +kernel
theorem coefficient_413 : validRep representative_413 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_413)=dictionary32.getD 409 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_409]
  decide +kernel
theorem coefficient_414 : validRep representative_414 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_414)=dictionary32.getD 137 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_137]
  decide +kernel
theorem coefficient_415 : validRep representative_415 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_415)=dictionary32.getD 389 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_389]
  decide +kernel
theorem coefficient_416 : validRep representative_416 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_416)=dictionary32.getD 358 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_358]
  decide +kernel
theorem coefficient_417 : validRep representative_417 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_417)=dictionary32.getD 172 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_172]
  decide +kernel
theorem coefficient_418 : validRep representative_418 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_418)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_419 : validRep representative_419 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_419)=dictionary32.getD 188 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_188]
  decide +kernel
theorem coefficient_420 : validRep representative_420 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_420)=dictionary32.getD 212 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_212]
  decide +kernel
theorem coefficient_421 : validRep representative_421 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_421)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_422 : validRep representative_422 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_422)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_423 : validRep representative_423 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_423)=dictionary32.getD 290 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_290]
  decide +kernel
theorem coefficient_424 : validRep representative_424 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_424)=dictionary32.getD 358 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_358]
  decide +kernel
theorem coefficient_425 : validRep representative_425 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_425)=dictionary32.getD 178 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_178]
  decide +kernel
theorem coefficient_426 : validRep representative_426 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_426)=dictionary32.getD 322 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_322]
  decide +kernel
theorem coefficient_427 : validRep representative_427 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_427)=dictionary32.getD 196 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_196]
  decide +kernel
theorem coefficient_428 : validRep representative_428 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_428)=dictionary32.getD 79 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_79]
  decide +kernel
theorem coefficient_429 : validRep representative_429 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_429)=dictionary32.getD 408 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_408]
  decide +kernel
theorem coefficient_430 : validRep representative_430 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_430)=dictionary32.getD 143 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_143]
  decide +kernel
theorem coefficient_431 : validRep representative_431 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_431)=dictionary32.getD 388 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_388]
  decide +kernel
theorem coefficient_432 : validRep representative_432 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_432)=dictionary32.getD 418 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_418]
  decide +kernel
theorem coefficient_433 : validRep representative_433 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_433)=dictionary32.getD 417 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_417]
  decide +kernel
theorem coefficient_434 : validRep representative_434 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_434)=dictionary32.getD 157 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_157]
  decide +kernel
theorem coefficient_435 : validRep representative_435 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_435)=dictionary32.getD 204 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_204]
  decide +kernel
theorem coefficient_436 : validRep representative_436 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_436)=dictionary32.getD 379 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_379]
  decide +kernel
theorem coefficient_437 : validRep representative_437 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_437)=dictionary32.getD 205 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_205]
  decide +kernel
theorem coefficient_438 : validRep representative_438 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_438)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_439 : validRep representative_439 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_439)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_440 : validRep representative_440 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_440)=dictionary32.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_441 : validRep representative_441 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_441)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_442 : validRep representative_442 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_442)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_443 : validRep representative_443 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_443)=dictionary32.getD 176 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_176]
  decide +kernel
theorem coefficient_444 : validRep representative_444 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_444)=dictionary32.getD 372 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_372]
  decide +kernel
theorem coefficient_445 : validRep representative_445 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_445)=dictionary32.getD 206 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_206]
  decide +kernel
theorem coefficient_446 : validRep representative_446 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_446)=dictionary32.getD 321 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_321]
  decide +kernel
theorem coefficient_447 : validRep representative_447 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_447)=dictionary32.getD 434 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_434]
  decide +kernel
def tree_006 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 416 (QuarticIntegerRepresentativeTree.Tree.branch 400 (QuarticIntegerRepresentativeTree.Tree.branch 392 (QuarticIntegerRepresentativeTree.Tree.branch 388 (QuarticIntegerRepresentativeTree.Tree.branch 386 (QuarticIntegerRepresentativeTree.Tree.branch 385 (QuarticIntegerRepresentativeTree.Tree.leaf 384 representative_384) (QuarticIntegerRepresentativeTree.Tree.leaf 385 representative_385)) (QuarticIntegerRepresentativeTree.Tree.branch 387 (QuarticIntegerRepresentativeTree.Tree.leaf 386 representative_386) (QuarticIntegerRepresentativeTree.Tree.leaf 387 representative_387))) (QuarticIntegerRepresentativeTree.Tree.branch 390 (QuarticIntegerRepresentativeTree.Tree.branch 389 (QuarticIntegerRepresentativeTree.Tree.leaf 388 representative_388) (QuarticIntegerRepresentativeTree.Tree.leaf 389 representative_389)) (QuarticIntegerRepresentativeTree.Tree.branch 391 (QuarticIntegerRepresentativeTree.Tree.leaf 390 representative_390) (QuarticIntegerRepresentativeTree.Tree.leaf 391 representative_391)))) (QuarticIntegerRepresentativeTree.Tree.branch 396 (QuarticIntegerRepresentativeTree.Tree.branch 394 (QuarticIntegerRepresentativeTree.Tree.branch 393 (QuarticIntegerRepresentativeTree.Tree.leaf 392 representative_392) (QuarticIntegerRepresentativeTree.Tree.leaf 393 representative_393)) (QuarticIntegerRepresentativeTree.Tree.branch 395 (QuarticIntegerRepresentativeTree.Tree.leaf 394 representative_394) (QuarticIntegerRepresentativeTree.Tree.leaf 395 representative_395))) (QuarticIntegerRepresentativeTree.Tree.branch 398 (QuarticIntegerRepresentativeTree.Tree.branch 397 (QuarticIntegerRepresentativeTree.Tree.leaf 396 representative_396) (QuarticIntegerRepresentativeTree.Tree.leaf 397 representative_397)) (QuarticIntegerRepresentativeTree.Tree.branch 399 (QuarticIntegerRepresentativeTree.Tree.leaf 398 representative_398) (QuarticIntegerRepresentativeTree.Tree.leaf 399 representative_399))))) (QuarticIntegerRepresentativeTree.Tree.branch 408 (QuarticIntegerRepresentativeTree.Tree.branch 404 (QuarticIntegerRepresentativeTree.Tree.branch 402 (QuarticIntegerRepresentativeTree.Tree.branch 401 (QuarticIntegerRepresentativeTree.Tree.leaf 400 representative_400) (QuarticIntegerRepresentativeTree.Tree.leaf 401 representative_401)) (QuarticIntegerRepresentativeTree.Tree.branch 403 (QuarticIntegerRepresentativeTree.Tree.leaf 402 representative_402) (QuarticIntegerRepresentativeTree.Tree.leaf 403 representative_403))) (QuarticIntegerRepresentativeTree.Tree.branch 406 (QuarticIntegerRepresentativeTree.Tree.branch 405 (QuarticIntegerRepresentativeTree.Tree.leaf 404 representative_404) (QuarticIntegerRepresentativeTree.Tree.leaf 405 representative_405)) (QuarticIntegerRepresentativeTree.Tree.branch 407 (QuarticIntegerRepresentativeTree.Tree.leaf 406 representative_406) (QuarticIntegerRepresentativeTree.Tree.leaf 407 representative_407)))) (QuarticIntegerRepresentativeTree.Tree.branch 412 (QuarticIntegerRepresentativeTree.Tree.branch 410 (QuarticIntegerRepresentativeTree.Tree.branch 409 (QuarticIntegerRepresentativeTree.Tree.leaf 408 representative_408) (QuarticIntegerRepresentativeTree.Tree.leaf 409 representative_409)) (QuarticIntegerRepresentativeTree.Tree.branch 411 (QuarticIntegerRepresentativeTree.Tree.leaf 410 representative_410) (QuarticIntegerRepresentativeTree.Tree.leaf 411 representative_411))) (QuarticIntegerRepresentativeTree.Tree.branch 414 (QuarticIntegerRepresentativeTree.Tree.branch 413 (QuarticIntegerRepresentativeTree.Tree.leaf 412 representative_412) (QuarticIntegerRepresentativeTree.Tree.leaf 413 representative_413)) (QuarticIntegerRepresentativeTree.Tree.branch 415 (QuarticIntegerRepresentativeTree.Tree.leaf 414 representative_414) (QuarticIntegerRepresentativeTree.Tree.leaf 415 representative_415)))))) (QuarticIntegerRepresentativeTree.Tree.branch 432 (QuarticIntegerRepresentativeTree.Tree.branch 424 (QuarticIntegerRepresentativeTree.Tree.branch 420 (QuarticIntegerRepresentativeTree.Tree.branch 418 (QuarticIntegerRepresentativeTree.Tree.branch 417 (QuarticIntegerRepresentativeTree.Tree.leaf 416 representative_416) (QuarticIntegerRepresentativeTree.Tree.leaf 417 representative_417)) (QuarticIntegerRepresentativeTree.Tree.branch 419 (QuarticIntegerRepresentativeTree.Tree.leaf 418 representative_418) (QuarticIntegerRepresentativeTree.Tree.leaf 419 representative_419))) (QuarticIntegerRepresentativeTree.Tree.branch 422 (QuarticIntegerRepresentativeTree.Tree.branch 421 (QuarticIntegerRepresentativeTree.Tree.leaf 420 representative_420) (QuarticIntegerRepresentativeTree.Tree.leaf 421 representative_421)) (QuarticIntegerRepresentativeTree.Tree.branch 423 (QuarticIntegerRepresentativeTree.Tree.leaf 422 representative_422) (QuarticIntegerRepresentativeTree.Tree.leaf 423 representative_423)))) (QuarticIntegerRepresentativeTree.Tree.branch 428 (QuarticIntegerRepresentativeTree.Tree.branch 426 (QuarticIntegerRepresentativeTree.Tree.branch 425 (QuarticIntegerRepresentativeTree.Tree.leaf 424 representative_424) (QuarticIntegerRepresentativeTree.Tree.leaf 425 representative_425)) (QuarticIntegerRepresentativeTree.Tree.branch 427 (QuarticIntegerRepresentativeTree.Tree.leaf 426 representative_426) (QuarticIntegerRepresentativeTree.Tree.leaf 427 representative_427))) (QuarticIntegerRepresentativeTree.Tree.branch 430 (QuarticIntegerRepresentativeTree.Tree.branch 429 (QuarticIntegerRepresentativeTree.Tree.leaf 428 representative_428) (QuarticIntegerRepresentativeTree.Tree.leaf 429 representative_429)) (QuarticIntegerRepresentativeTree.Tree.branch 431 (QuarticIntegerRepresentativeTree.Tree.leaf 430 representative_430) (QuarticIntegerRepresentativeTree.Tree.leaf 431 representative_431))))) (QuarticIntegerRepresentativeTree.Tree.branch 440 (QuarticIntegerRepresentativeTree.Tree.branch 436 (QuarticIntegerRepresentativeTree.Tree.branch 434 (QuarticIntegerRepresentativeTree.Tree.branch 433 (QuarticIntegerRepresentativeTree.Tree.leaf 432 representative_432) (QuarticIntegerRepresentativeTree.Tree.leaf 433 representative_433)) (QuarticIntegerRepresentativeTree.Tree.branch 435 (QuarticIntegerRepresentativeTree.Tree.leaf 434 representative_434) (QuarticIntegerRepresentativeTree.Tree.leaf 435 representative_435))) (QuarticIntegerRepresentativeTree.Tree.branch 438 (QuarticIntegerRepresentativeTree.Tree.branch 437 (QuarticIntegerRepresentativeTree.Tree.leaf 436 representative_436) (QuarticIntegerRepresentativeTree.Tree.leaf 437 representative_437)) (QuarticIntegerRepresentativeTree.Tree.branch 439 (QuarticIntegerRepresentativeTree.Tree.leaf 438 representative_438) (QuarticIntegerRepresentativeTree.Tree.leaf 439 representative_439)))) (QuarticIntegerRepresentativeTree.Tree.branch 444 (QuarticIntegerRepresentativeTree.Tree.branch 442 (QuarticIntegerRepresentativeTree.Tree.branch 441 (QuarticIntegerRepresentativeTree.Tree.leaf 440 representative_440) (QuarticIntegerRepresentativeTree.Tree.leaf 441 representative_441)) (QuarticIntegerRepresentativeTree.Tree.branch 443 (QuarticIntegerRepresentativeTree.Tree.leaf 442 representative_442) (QuarticIntegerRepresentativeTree.Tree.leaf 443 representative_443))) (QuarticIntegerRepresentativeTree.Tree.branch 446 (QuarticIntegerRepresentativeTree.Tree.branch 445 (QuarticIntegerRepresentativeTree.Tree.leaf 444 representative_444) (QuarticIntegerRepresentativeTree.Tree.leaf 445 representative_445)) (QuarticIntegerRepresentativeTree.Tree.branch 447 (QuarticIntegerRepresentativeTree.Tree.leaf 446 representative_446) (QuarticIntegerRepresentativeTree.Tree.leaf 447 representative_447)))))))
theorem accepted_006 : All validRep tree_006 := ⟨⟨⟨⟨⟨⟨coefficient_384,coefficient_385⟩,⟨coefficient_386,coefficient_387⟩⟩,⟨⟨coefficient_388,coefficient_389⟩,⟨coefficient_390,coefficient_391⟩⟩⟩,⟨⟨⟨coefficient_392,coefficient_393⟩,⟨coefficient_394,coefficient_395⟩⟩,⟨⟨coefficient_396,coefficient_397⟩,⟨coefficient_398,coefficient_399⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_400,coefficient_401⟩,⟨coefficient_402,coefficient_403⟩⟩,⟨⟨coefficient_404,coefficient_405⟩,⟨coefficient_406,coefficient_407⟩⟩⟩,⟨⟨⟨coefficient_408,coefficient_409⟩,⟨coefficient_410,coefficient_411⟩⟩,⟨⟨coefficient_412,coefficient_413⟩,⟨coefficient_414,coefficient_415⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_416,coefficient_417⟩,⟨coefficient_418,coefficient_419⟩⟩,⟨⟨coefficient_420,coefficient_421⟩,⟨coefficient_422,coefficient_423⟩⟩⟩,⟨⟨⟨coefficient_424,coefficient_425⟩,⟨coefficient_426,coefficient_427⟩⟩,⟨⟨coefficient_428,coefficient_429⟩,⟨coefficient_430,coefficient_431⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_432,coefficient_433⟩,⟨coefficient_434,coefficient_435⟩⟩,⟨⟨coefficient_436,coefficient_437⟩,⟨coefficient_438,coefficient_439⟩⟩⟩,⟨⟨⟨coefficient_440,coefficient_441⟩,⟨coefficient_442,coefficient_443⟩⟩,⟨⟨coefficient_444,coefficient_445⟩,⟨coefficient_446,coefficient_447⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

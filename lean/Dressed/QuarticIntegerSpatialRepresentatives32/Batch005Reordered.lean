import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_320 : Rep := ⟨![0,4,13,21],271⟩
def representative_321 : Rep := ⟨![0,4,13,22],276⟩
def representative_322 : Rep := ⟨![0,4,13,23],508⟩
def representative_323 : Rep := ⟨![0,4,13,25],165⟩
def representative_324 : Rep := ⟨![0,4,13,26],508⟩
def representative_325 : Rep := ⟨![0,4,13,27],164⟩
def representative_326 : Rep := ⟨![0,4,14,16],304⟩
def representative_327 : Rep := ⟨![0,4,14,17],508⟩
def representative_328 : Rep := ⟨![0,4,14,18],508⟩
def representative_329 : Rep := ⟨![0,4,14,20],508⟩
def representative_330 : Rep := ⟨![0,4,14,21],508⟩
def representative_331 : Rep := ⟨![0,4,14,22],508⟩
def representative_332 : Rep := ⟨![0,4,14,26],508⟩
def representative_333 : Rep := ⟨![0,4,16,20],226⟩
def representative_334 : Rep := ⟨![0,4,16,21],273⟩
def representative_335 : Rep := ⟨![0,4,16,22],274⟩
def representative_336 : Rep := ⟨![0,4,17,21],508⟩
def representative_337 : Rep := ⟨![0,4,17,22],508⟩
def representative_338 : Rep := ⟨![0,4,17,23],508⟩
def representative_339 : Rep := ⟨![0,4,18,22],508⟩
def representative_340 : Rep := ⟨![0,5,1,4],506⟩
def representative_341 : Rep := ⟨![0,5,1,6],505⟩
def representative_342 : Rep := ⟨![0,5,1,7],34⟩
def representative_343 : Rep := ⟨![0,5,1,8],35⟩
def representative_344 : Rep := ⟨![0,5,1,9],502⟩
def representative_345 : Rep := ⟨![0,5,1,10],38⟩
def representative_346 : Rep := ⟨![0,5,1,11],472⟩
def representative_347 : Rep := ⟨![0,5,1,12],467⟩
def representative_348 : Rep := ⟨![0,5,1,13],42⟩
def representative_349 : Rep := ⟨![0,5,1,14],462⟩
def representative_350 : Rep := ⟨![0,5,1,15],148⟩
def representative_351 : Rep := ⟨![0,5,1,16],189⟩
def representative_352 : Rep := ⟨![0,5,1,17],452⟩
def representative_353 : Rep := ⟨![0,5,1,18],211⟩
def representative_354 : Rep := ⟨![0,5,1,19],508⟩
def representative_355 : Rep := ⟨![0,5,1,20],451⟩
def representative_356 : Rep := ⟨![0,5,1,21],83⟩
def representative_357 : Rep := ⟨![0,5,1,22],508⟩
def representative_358 : Rep := ⟨![0,5,1,23],210⟩
def representative_359 : Rep := ⟨![0,5,1,24],41⟩
def representative_360 : Rep := ⟨![0,5,1,25],491⟩
def representative_361 : Rep := ⟨![0,5,1,26],48⟩
def representative_362 : Rep := ⟨![0,5,1,27],461⟩
def representative_363 : Rep := ⟨![0,5,1,28],503⟩
def representative_364 : Rep := ⟨![0,5,1,30],499⟩
def representative_365 : Rep := ⟨![0,5,1,31],36⟩
def representative_366 : Rep := ⟨![0,5,2,7],443⟩
def representative_367 : Rep := ⟨![0,5,2,8],424⟩
def representative_368 : Rep := ⟨![0,5,2,9],55⟩
def representative_369 : Rep := ⟨![0,5,2,10],425⟩
def representative_370 : Rep := ⟨![0,5,2,11],130⟩
def representative_371 : Rep := ⟨![0,5,2,12],155⟩
def representative_372 : Rep := ⟨![0,5,2,13],386⟩
def representative_373 : Rep := ⟨![0,5,2,14],152⟩
def representative_374 : Rep := ⟨![0,5,2,15],332⟩
def representative_375 : Rep := ⟨![0,5,2,16],310⟩
def representative_376 : Rep := ⟨![0,5,2,17],221⟩
def representative_377 : Rep := ⟨![0,5,2,18],307⟩
def representative_378 : Rep := ⟨![0,5,2,19],508⟩
def representative_379 : Rep := ⟨![0,5,2,20],220⟩
def representative_380 : Rep := ⟨![0,5,2,21],310⟩
def representative_381 : Rep := ⟨![0,5,2,22],207⟩
def representative_382 : Rep := ⟨![0,5,2,23],307⟩
def representative_383 : Rep := ⟨![0,5,2,24],387⟩
theorem coefficient_320 : validRep representative_320 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_320)=dictionary32.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_321 : validRep representative_321 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_321)=dictionary32.getD 276 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_276]
  decide +kernel
theorem coefficient_322 : validRep representative_322 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_322)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_323 : validRep representative_323 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_323)=dictionary32.getD 165 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_165]
  decide +kernel
theorem coefficient_324 : validRep representative_324 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_324)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_325 : validRep representative_325 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_325)=dictionary32.getD 164 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_164]
  decide +kernel
theorem coefficient_326 : validRep representative_326 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_326)=dictionary32.getD 304 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_304]
  decide +kernel
theorem coefficient_327 : validRep representative_327 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_327)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_328 : validRep representative_328 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_328)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_329 : validRep representative_329 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_329)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_330 : validRep representative_330 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_330)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_331 : validRep representative_331 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_331)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_332 : validRep representative_332 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_332)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_333 : validRep representative_333 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_333)=dictionary32.getD 226 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_226]
  decide +kernel
theorem coefficient_334 : validRep representative_334 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_334)=dictionary32.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_335 : validRep representative_335 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_335)=dictionary32.getD 274 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_274]
  decide +kernel
theorem coefficient_336 : validRep representative_336 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_336)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_337 : validRep representative_337 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_337)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_338 : validRep representative_338 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_338)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_339 : validRep representative_339 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_339)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_340 : validRep representative_340 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_340)=dictionary32.getD 506 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_506]
  decide +kernel
theorem coefficient_341 : validRep representative_341 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_341)=dictionary32.getD 505 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_505]
  decide +kernel
theorem coefficient_342 : validRep representative_342 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_342)=dictionary32.getD 34 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_34]
  decide +kernel
theorem coefficient_343 : validRep representative_343 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_343)=dictionary32.getD 35 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_35]
  decide +kernel
theorem coefficient_344 : validRep representative_344 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_344)=dictionary32.getD 502 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_502]
  decide +kernel
theorem coefficient_345 : validRep representative_345 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_345)=dictionary32.getD 38 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_38]
  decide +kernel
theorem coefficient_346 : validRep representative_346 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_346)=dictionary32.getD 472 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_472]
  decide +kernel
theorem coefficient_347 : validRep representative_347 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_347)=dictionary32.getD 467 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_467]
  decide +kernel
theorem coefficient_348 : validRep representative_348 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_348)=dictionary32.getD 42 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_42]
  decide +kernel
theorem coefficient_349 : validRep representative_349 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_349)=dictionary32.getD 462 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_462]
  decide +kernel
theorem coefficient_350 : validRep representative_350 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_350)=dictionary32.getD 148 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_148]
  decide +kernel
theorem coefficient_351 : validRep representative_351 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_351)=dictionary32.getD 189 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_189]
  decide +kernel
theorem coefficient_352 : validRep representative_352 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_352)=dictionary32.getD 452 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_452]
  decide +kernel
theorem coefficient_353 : validRep representative_353 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_353)=dictionary32.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_354 : validRep representative_354 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_354)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_355 : validRep representative_355 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_355)=dictionary32.getD 451 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_451]
  decide +kernel
theorem coefficient_356 : validRep representative_356 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_356)=dictionary32.getD 83 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_83]
  decide +kernel
theorem coefficient_357 : validRep representative_357 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_357)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_358 : validRep representative_358 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_358)=dictionary32.getD 210 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_210]
  decide +kernel
theorem coefficient_359 : validRep representative_359 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_359)=dictionary32.getD 41 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_360 : validRep representative_360 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_360)=dictionary32.getD 491 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_491]
  decide +kernel
theorem coefficient_361 : validRep representative_361 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_361)=dictionary32.getD 48 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_48]
  decide +kernel
theorem coefficient_362 : validRep representative_362 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_362)=dictionary32.getD 461 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_461]
  decide +kernel
theorem coefficient_363 : validRep representative_363 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_363)=dictionary32.getD 503 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_503]
  decide +kernel
theorem coefficient_364 : validRep representative_364 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_364)=dictionary32.getD 499 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_499]
  decide +kernel
theorem coefficient_365 : validRep representative_365 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_365)=dictionary32.getD 36 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_36]
  decide +kernel
theorem coefficient_366 : validRep representative_366 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_366)=dictionary32.getD 443 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_443]
  decide +kernel
theorem coefficient_367 : validRep representative_367 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_367)=dictionary32.getD 424 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_424]
  decide +kernel
theorem coefficient_368 : validRep representative_368 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_368)=dictionary32.getD 55 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_55]
  decide +kernel
theorem coefficient_369 : validRep representative_369 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_369)=dictionary32.getD 425 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_425]
  decide +kernel
theorem coefficient_370 : validRep representative_370 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_370)=dictionary32.getD 130 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_130]
  decide +kernel
theorem coefficient_371 : validRep representative_371 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_371)=dictionary32.getD 155 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_155]
  decide +kernel
theorem coefficient_372 : validRep representative_372 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_372)=dictionary32.getD 386 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_386]
  decide +kernel
theorem coefficient_373 : validRep representative_373 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_373)=dictionary32.getD 152 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_152]
  decide +kernel
theorem coefficient_374 : validRep representative_374 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_374)=dictionary32.getD 332 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_332]
  decide +kernel
theorem coefficient_375 : validRep representative_375 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_375)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_376 : validRep representative_376 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_376)=dictionary32.getD 221 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_221]
  decide +kernel
theorem coefficient_377 : validRep representative_377 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_377)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_378 : validRep representative_378 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_378)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_379 : validRep representative_379 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_379)=dictionary32.getD 220 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_220]
  decide +kernel
theorem coefficient_380 : validRep representative_380 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_380)=dictionary32.getD 310 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_310]
  decide +kernel
theorem coefficient_381 : validRep representative_381 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_381)=dictionary32.getD 207 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_207]
  decide +kernel
theorem coefficient_382 : validRep representative_382 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_382)=dictionary32.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_383 : validRep representative_383 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_383)=dictionary32.getD 387 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_387]
  decide +kernel
def tree_005 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 352 (QuarticIntegerRepresentativeTree.Tree.branch 336 (QuarticIntegerRepresentativeTree.Tree.branch 328 (QuarticIntegerRepresentativeTree.Tree.branch 324 (QuarticIntegerRepresentativeTree.Tree.branch 322 (QuarticIntegerRepresentativeTree.Tree.branch 321 (QuarticIntegerRepresentativeTree.Tree.leaf 320 representative_320) (QuarticIntegerRepresentativeTree.Tree.leaf 321 representative_321)) (QuarticIntegerRepresentativeTree.Tree.branch 323 (QuarticIntegerRepresentativeTree.Tree.leaf 322 representative_322) (QuarticIntegerRepresentativeTree.Tree.leaf 323 representative_323))) (QuarticIntegerRepresentativeTree.Tree.branch 326 (QuarticIntegerRepresentativeTree.Tree.branch 325 (QuarticIntegerRepresentativeTree.Tree.leaf 324 representative_324) (QuarticIntegerRepresentativeTree.Tree.leaf 325 representative_325)) (QuarticIntegerRepresentativeTree.Tree.branch 327 (QuarticIntegerRepresentativeTree.Tree.leaf 326 representative_326) (QuarticIntegerRepresentativeTree.Tree.leaf 327 representative_327)))) (QuarticIntegerRepresentativeTree.Tree.branch 332 (QuarticIntegerRepresentativeTree.Tree.branch 330 (QuarticIntegerRepresentativeTree.Tree.branch 329 (QuarticIntegerRepresentativeTree.Tree.leaf 328 representative_328) (QuarticIntegerRepresentativeTree.Tree.leaf 329 representative_329)) (QuarticIntegerRepresentativeTree.Tree.branch 331 (QuarticIntegerRepresentativeTree.Tree.leaf 330 representative_330) (QuarticIntegerRepresentativeTree.Tree.leaf 331 representative_331))) (QuarticIntegerRepresentativeTree.Tree.branch 334 (QuarticIntegerRepresentativeTree.Tree.branch 333 (QuarticIntegerRepresentativeTree.Tree.leaf 332 representative_332) (QuarticIntegerRepresentativeTree.Tree.leaf 333 representative_333)) (QuarticIntegerRepresentativeTree.Tree.branch 335 (QuarticIntegerRepresentativeTree.Tree.leaf 334 representative_334) (QuarticIntegerRepresentativeTree.Tree.leaf 335 representative_335))))) (QuarticIntegerRepresentativeTree.Tree.branch 344 (QuarticIntegerRepresentativeTree.Tree.branch 340 (QuarticIntegerRepresentativeTree.Tree.branch 338 (QuarticIntegerRepresentativeTree.Tree.branch 337 (QuarticIntegerRepresentativeTree.Tree.leaf 336 representative_336) (QuarticIntegerRepresentativeTree.Tree.leaf 337 representative_337)) (QuarticIntegerRepresentativeTree.Tree.branch 339 (QuarticIntegerRepresentativeTree.Tree.leaf 338 representative_338) (QuarticIntegerRepresentativeTree.Tree.leaf 339 representative_339))) (QuarticIntegerRepresentativeTree.Tree.branch 342 (QuarticIntegerRepresentativeTree.Tree.branch 341 (QuarticIntegerRepresentativeTree.Tree.leaf 340 representative_340) (QuarticIntegerRepresentativeTree.Tree.leaf 341 representative_341)) (QuarticIntegerRepresentativeTree.Tree.branch 343 (QuarticIntegerRepresentativeTree.Tree.leaf 342 representative_342) (QuarticIntegerRepresentativeTree.Tree.leaf 343 representative_343)))) (QuarticIntegerRepresentativeTree.Tree.branch 348 (QuarticIntegerRepresentativeTree.Tree.branch 346 (QuarticIntegerRepresentativeTree.Tree.branch 345 (QuarticIntegerRepresentativeTree.Tree.leaf 344 representative_344) (QuarticIntegerRepresentativeTree.Tree.leaf 345 representative_345)) (QuarticIntegerRepresentativeTree.Tree.branch 347 (QuarticIntegerRepresentativeTree.Tree.leaf 346 representative_346) (QuarticIntegerRepresentativeTree.Tree.leaf 347 representative_347))) (QuarticIntegerRepresentativeTree.Tree.branch 350 (QuarticIntegerRepresentativeTree.Tree.branch 349 (QuarticIntegerRepresentativeTree.Tree.leaf 348 representative_348) (QuarticIntegerRepresentativeTree.Tree.leaf 349 representative_349)) (QuarticIntegerRepresentativeTree.Tree.branch 351 (QuarticIntegerRepresentativeTree.Tree.leaf 350 representative_350) (QuarticIntegerRepresentativeTree.Tree.leaf 351 representative_351)))))) (QuarticIntegerRepresentativeTree.Tree.branch 368 (QuarticIntegerRepresentativeTree.Tree.branch 360 (QuarticIntegerRepresentativeTree.Tree.branch 356 (QuarticIntegerRepresentativeTree.Tree.branch 354 (QuarticIntegerRepresentativeTree.Tree.branch 353 (QuarticIntegerRepresentativeTree.Tree.leaf 352 representative_352) (QuarticIntegerRepresentativeTree.Tree.leaf 353 representative_353)) (QuarticIntegerRepresentativeTree.Tree.branch 355 (QuarticIntegerRepresentativeTree.Tree.leaf 354 representative_354) (QuarticIntegerRepresentativeTree.Tree.leaf 355 representative_355))) (QuarticIntegerRepresentativeTree.Tree.branch 358 (QuarticIntegerRepresentativeTree.Tree.branch 357 (QuarticIntegerRepresentativeTree.Tree.leaf 356 representative_356) (QuarticIntegerRepresentativeTree.Tree.leaf 357 representative_357)) (QuarticIntegerRepresentativeTree.Tree.branch 359 (QuarticIntegerRepresentativeTree.Tree.leaf 358 representative_358) (QuarticIntegerRepresentativeTree.Tree.leaf 359 representative_359)))) (QuarticIntegerRepresentativeTree.Tree.branch 364 (QuarticIntegerRepresentativeTree.Tree.branch 362 (QuarticIntegerRepresentativeTree.Tree.branch 361 (QuarticIntegerRepresentativeTree.Tree.leaf 360 representative_360) (QuarticIntegerRepresentativeTree.Tree.leaf 361 representative_361)) (QuarticIntegerRepresentativeTree.Tree.branch 363 (QuarticIntegerRepresentativeTree.Tree.leaf 362 representative_362) (QuarticIntegerRepresentativeTree.Tree.leaf 363 representative_363))) (QuarticIntegerRepresentativeTree.Tree.branch 366 (QuarticIntegerRepresentativeTree.Tree.branch 365 (QuarticIntegerRepresentativeTree.Tree.leaf 364 representative_364) (QuarticIntegerRepresentativeTree.Tree.leaf 365 representative_365)) (QuarticIntegerRepresentativeTree.Tree.branch 367 (QuarticIntegerRepresentativeTree.Tree.leaf 366 representative_366) (QuarticIntegerRepresentativeTree.Tree.leaf 367 representative_367))))) (QuarticIntegerRepresentativeTree.Tree.branch 376 (QuarticIntegerRepresentativeTree.Tree.branch 372 (QuarticIntegerRepresentativeTree.Tree.branch 370 (QuarticIntegerRepresentativeTree.Tree.branch 369 (QuarticIntegerRepresentativeTree.Tree.leaf 368 representative_368) (QuarticIntegerRepresentativeTree.Tree.leaf 369 representative_369)) (QuarticIntegerRepresentativeTree.Tree.branch 371 (QuarticIntegerRepresentativeTree.Tree.leaf 370 representative_370) (QuarticIntegerRepresentativeTree.Tree.leaf 371 representative_371))) (QuarticIntegerRepresentativeTree.Tree.branch 374 (QuarticIntegerRepresentativeTree.Tree.branch 373 (QuarticIntegerRepresentativeTree.Tree.leaf 372 representative_372) (QuarticIntegerRepresentativeTree.Tree.leaf 373 representative_373)) (QuarticIntegerRepresentativeTree.Tree.branch 375 (QuarticIntegerRepresentativeTree.Tree.leaf 374 representative_374) (QuarticIntegerRepresentativeTree.Tree.leaf 375 representative_375)))) (QuarticIntegerRepresentativeTree.Tree.branch 380 (QuarticIntegerRepresentativeTree.Tree.branch 378 (QuarticIntegerRepresentativeTree.Tree.branch 377 (QuarticIntegerRepresentativeTree.Tree.leaf 376 representative_376) (QuarticIntegerRepresentativeTree.Tree.leaf 377 representative_377)) (QuarticIntegerRepresentativeTree.Tree.branch 379 (QuarticIntegerRepresentativeTree.Tree.leaf 378 representative_378) (QuarticIntegerRepresentativeTree.Tree.leaf 379 representative_379))) (QuarticIntegerRepresentativeTree.Tree.branch 382 (QuarticIntegerRepresentativeTree.Tree.branch 381 (QuarticIntegerRepresentativeTree.Tree.leaf 380 representative_380) (QuarticIntegerRepresentativeTree.Tree.leaf 381 representative_381)) (QuarticIntegerRepresentativeTree.Tree.branch 383 (QuarticIntegerRepresentativeTree.Tree.leaf 382 representative_382) (QuarticIntegerRepresentativeTree.Tree.leaf 383 representative_383)))))))
theorem accepted_005 : All validRep tree_005 := ⟨⟨⟨⟨⟨⟨coefficient_320,coefficient_321⟩,⟨coefficient_322,coefficient_323⟩⟩,⟨⟨coefficient_324,coefficient_325⟩,⟨coefficient_326,coefficient_327⟩⟩⟩,⟨⟨⟨coefficient_328,coefficient_329⟩,⟨coefficient_330,coefficient_331⟩⟩,⟨⟨coefficient_332,coefficient_333⟩,⟨coefficient_334,coefficient_335⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_336,coefficient_337⟩,⟨coefficient_338,coefficient_339⟩⟩,⟨⟨coefficient_340,coefficient_341⟩,⟨coefficient_342,coefficient_343⟩⟩⟩,⟨⟨⟨coefficient_344,coefficient_345⟩,⟨coefficient_346,coefficient_347⟩⟩,⟨⟨coefficient_348,coefficient_349⟩,⟨coefficient_350,coefficient_351⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_352,coefficient_353⟩,⟨coefficient_354,coefficient_355⟩⟩,⟨⟨coefficient_356,coefficient_357⟩,⟨coefficient_358,coefficient_359⟩⟩⟩,⟨⟨⟨coefficient_360,coefficient_361⟩,⟨coefficient_362,coefficient_363⟩⟩,⟨⟨coefficient_364,coefficient_365⟩,⟨coefficient_366,coefficient_367⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_368,coefficient_369⟩,⟨coefficient_370,coefficient_371⟩⟩,⟨⟨coefficient_372,coefficient_373⟩,⟨coefficient_374,coefficient_375⟩⟩⟩,⟨⟨⟨coefficient_376,coefficient_377⟩,⟨coefficient_378,coefficient_379⟩⟩,⟨⟨coefficient_380,coefficient_381⟩,⟨coefficient_382,coefficient_383⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

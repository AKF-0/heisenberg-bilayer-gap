import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_320 : Rep := ⟨![0,1,16,38],462⟩
def representative_321 : Rep := ⟨![0,1,16,39],291⟩
def representative_322 : Rep := ⟨![0,1,16,40],329⟩
def representative_323 : Rep := ⟨![0,1,16,41],332⟩
def representative_324 : Rep := ⟨![0,1,16,42],284⟩
def representative_325 : Rep := ⟨![0,1,16,43],462⟩
def representative_326 : Rep := ⟨![0,1,16,44],462⟩
def representative_327 : Rep := ⟨![0,1,16,45],462⟩
def representative_328 : Rep := ⟨![0,1,16,46],462⟩
def representative_329 : Rep := ⟨![0,1,16,47],193⟩
def representative_330 : Rep := ⟨![0,1,16,48],79⟩
def representative_331 : Rep := ⟨![0,1,16,49],78⟩
def representative_332 : Rep := ⟨![0,1,16,50],368⟩
def representative_333 : Rep := ⟨![0,1,16,51],293⟩
def representative_334 : Rep := ⟨![0,1,16,52],462⟩
def representative_335 : Rep := ⟨![0,1,16,53],462⟩
def representative_336 : Rep := ⟨![0,1,16,54],180⟩
def representative_337 : Rep := ⟨![0,1,16,55],361⟩
def representative_338 : Rep := ⟨![0,1,18,19],316⟩
def representative_339 : Rep := ⟨![0,1,18,20],234⟩
def representative_340 : Rep := ⟨![0,1,18,21],244⟩
def representative_341 : Rep := ⟨![0,1,18,22],462⟩
def representative_342 : Rep := ⟨![0,1,18,23],119⟩
def representative_343 : Rep := ⟨![0,1,18,24],173⟩
def representative_344 : Rep := ⟨![0,1,18,25],177⟩
def representative_345 : Rep := ⟨![0,1,18,27],228⟩
def representative_346 : Rep := ⟨![0,1,18,28],248⟩
def representative_347 : Rep := ⟨![0,1,18,29],462⟩
def representative_348 : Rep := ⟨![0,1,18,30],462⟩
def representative_349 : Rep := ⟨![0,1,18,31],462⟩
def representative_350 : Rep := ⟨![0,1,18,32],462⟩
def representative_351 : Rep := ⟨![0,1,18,33],272⟩
def representative_352 : Rep := ⟨![0,1,18,34],234⟩
def representative_353 : Rep := ⟨![0,1,18,35],248⟩
def representative_354 : Rep := ⟨![0,1,18,36],462⟩
def representative_355 : Rep := ⟨![0,1,18,37],462⟩
def representative_356 : Rep := ⟨![0,1,18,38],462⟩
def representative_357 : Rep := ⟨![0,1,18,39],462⟩
def representative_358 : Rep := ⟨![0,1,18,40],172⟩
def representative_359 : Rep := ⟨![0,1,18,41],180⟩
def representative_360 : Rep := ⟨![0,1,18,42],285⟩
def representative_361 : Rep := ⟨![0,1,18,43],462⟩
def representative_362 : Rep := ⟨![0,1,18,44],462⟩
def representative_363 : Rep := ⟨![0,1,18,45],462⟩
def representative_364 : Rep := ⟨![0,1,18,46],462⟩
def representative_365 : Rep := ⟨![0,1,18,47],462⟩
def representative_366 : Rep := ⟨![0,1,18,50],131⟩
def representative_367 : Rep := ⟨![0,1,18,51],293⟩
def representative_368 : Rep := ⟨![0,1,18,52],462⟩
def representative_369 : Rep := ⟨![0,1,18,53],462⟩
def representative_370 : Rep := ⟨![0,1,18,54],462⟩
def representative_371 : Rep := ⟨![0,1,18,55],118⟩
def representative_372 : Rep := ⟨![0,1,19,20],462⟩
def representative_373 : Rep := ⟨![0,1,19,21],462⟩
def representative_374 : Rep := ⟨![0,1,19,22],462⟩
def representative_375 : Rep := ⟨![0,1,19,24],462⟩
def representative_376 : Rep := ⟨![0,1,19,25],271⟩
def representative_377 : Rep := ⟨![0,1,19,26],462⟩
def representative_378 : Rep := ⟨![0,1,19,27],462⟩
def representative_379 : Rep := ⟨![0,1,19,28],462⟩
def representative_380 : Rep := ⟨![0,1,19,29],462⟩
def representative_381 : Rep := ⟨![0,1,19,30],462⟩
def representative_382 : Rep := ⟨![0,1,19,31],462⟩
def representative_383 : Rep := ⟨![0,1,19,32],462⟩
theorem coefficient_320 : validRep representative_320 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_320)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_321 : validRep representative_321 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_321)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_322 : validRep representative_322 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_322)=dictionary64.getD 329 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_329]
  decide +kernel
theorem coefficient_323 : validRep representative_323 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_323)=dictionary64.getD 332 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_332]
  decide +kernel
theorem coefficient_324 : validRep representative_324 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_324)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_325 : validRep representative_325 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_325)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_326 : validRep representative_326 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_326)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_327 : validRep representative_327 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_327)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_328 : validRep representative_328 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_328)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_329 : validRep representative_329 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_329)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_330 : validRep representative_330 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_330)=dictionary64.getD 79 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_79]
  decide +kernel
theorem coefficient_331 : validRep representative_331 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_331)=dictionary64.getD 78 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_78]
  decide +kernel
theorem coefficient_332 : validRep representative_332 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_332)=dictionary64.getD 368 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_368]
  decide +kernel
theorem coefficient_333 : validRep representative_333 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_333)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_334 : validRep representative_334 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_334)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_335 : validRep representative_335 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_335)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_336 : validRep representative_336 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_336)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_337 : validRep representative_337 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_337)=dictionary64.getD 361 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_361]
  decide +kernel
theorem coefficient_338 : validRep representative_338 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_338)=dictionary64.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_339 : validRep representative_339 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_339)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_340 : validRep representative_340 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_340)=dictionary64.getD 244 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_244]
  decide +kernel
theorem coefficient_341 : validRep representative_341 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_341)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_342 : validRep representative_342 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_342)=dictionary64.getD 119 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_119]
  decide +kernel
theorem coefficient_343 : validRep representative_343 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_343)=dictionary64.getD 173 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_173]
  decide +kernel
theorem coefficient_344 : validRep representative_344 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_344)=dictionary64.getD 177 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_177]
  decide +kernel
theorem coefficient_345 : validRep representative_345 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_345)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_346 : validRep representative_346 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_346)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_347 : validRep representative_347 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_347)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_348 : validRep representative_348 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_348)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_349 : validRep representative_349 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_349)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_350 : validRep representative_350 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_350)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_351 : validRep representative_351 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_351)=dictionary64.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_352 : validRep representative_352 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_352)=dictionary64.getD 234 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_234]
  decide +kernel
theorem coefficient_353 : validRep representative_353 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_353)=dictionary64.getD 248 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_248]
  decide +kernel
theorem coefficient_354 : validRep representative_354 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_354)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_355 : validRep representative_355 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_355)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_356 : validRep representative_356 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_356)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_357 : validRep representative_357 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_357)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_358 : validRep representative_358 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_358)=dictionary64.getD 172 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_172]
  decide +kernel
theorem coefficient_359 : validRep representative_359 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_359)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_360 : validRep representative_360 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_360)=dictionary64.getD 285 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_285]
  decide +kernel
theorem coefficient_361 : validRep representative_361 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_361)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_362 : validRep representative_362 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_362)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_363 : validRep representative_363 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_363)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_364 : validRep representative_364 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_364)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_365 : validRep representative_365 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_365)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_366 : validRep representative_366 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_366)=dictionary64.getD 131 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_131]
  decide +kernel
theorem coefficient_367 : validRep representative_367 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_367)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_368 : validRep representative_368 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_368)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_369 : validRep representative_369 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_369)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_370 : validRep representative_370 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_370)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_371 : validRep representative_371 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_371)=dictionary64.getD 118 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_118]
  decide +kernel
theorem coefficient_372 : validRep representative_372 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_372)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_373 : validRep representative_373 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_373)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_374 : validRep representative_374 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_374)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_375 : validRep representative_375 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_375)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_376 : validRep representative_376 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_376)=dictionary64.getD 271 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_271]
  decide +kernel
theorem coefficient_377 : validRep representative_377 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_377)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_378 : validRep representative_378 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_378)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_379 : validRep representative_379 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_379)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_380 : validRep representative_380 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_380)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_381 : validRep representative_381 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_381)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_382 : validRep representative_382 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_382)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_383 : validRep representative_383 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_383)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_005 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 352 (QuarticIntegerRepresentativeTree.Tree.branch 336 (QuarticIntegerRepresentativeTree.Tree.branch 328 (QuarticIntegerRepresentativeTree.Tree.branch 324 (QuarticIntegerRepresentativeTree.Tree.branch 322 (QuarticIntegerRepresentativeTree.Tree.branch 321 (QuarticIntegerRepresentativeTree.Tree.leaf 320 representative_320) (QuarticIntegerRepresentativeTree.Tree.leaf 321 representative_321)) (QuarticIntegerRepresentativeTree.Tree.branch 323 (QuarticIntegerRepresentativeTree.Tree.leaf 322 representative_322) (QuarticIntegerRepresentativeTree.Tree.leaf 323 representative_323))) (QuarticIntegerRepresentativeTree.Tree.branch 326 (QuarticIntegerRepresentativeTree.Tree.branch 325 (QuarticIntegerRepresentativeTree.Tree.leaf 324 representative_324) (QuarticIntegerRepresentativeTree.Tree.leaf 325 representative_325)) (QuarticIntegerRepresentativeTree.Tree.branch 327 (QuarticIntegerRepresentativeTree.Tree.leaf 326 representative_326) (QuarticIntegerRepresentativeTree.Tree.leaf 327 representative_327)))) (QuarticIntegerRepresentativeTree.Tree.branch 332 (QuarticIntegerRepresentativeTree.Tree.branch 330 (QuarticIntegerRepresentativeTree.Tree.branch 329 (QuarticIntegerRepresentativeTree.Tree.leaf 328 representative_328) (QuarticIntegerRepresentativeTree.Tree.leaf 329 representative_329)) (QuarticIntegerRepresentativeTree.Tree.branch 331 (QuarticIntegerRepresentativeTree.Tree.leaf 330 representative_330) (QuarticIntegerRepresentativeTree.Tree.leaf 331 representative_331))) (QuarticIntegerRepresentativeTree.Tree.branch 334 (QuarticIntegerRepresentativeTree.Tree.branch 333 (QuarticIntegerRepresentativeTree.Tree.leaf 332 representative_332) (QuarticIntegerRepresentativeTree.Tree.leaf 333 representative_333)) (QuarticIntegerRepresentativeTree.Tree.branch 335 (QuarticIntegerRepresentativeTree.Tree.leaf 334 representative_334) (QuarticIntegerRepresentativeTree.Tree.leaf 335 representative_335))))) (QuarticIntegerRepresentativeTree.Tree.branch 344 (QuarticIntegerRepresentativeTree.Tree.branch 340 (QuarticIntegerRepresentativeTree.Tree.branch 338 (QuarticIntegerRepresentativeTree.Tree.branch 337 (QuarticIntegerRepresentativeTree.Tree.leaf 336 representative_336) (QuarticIntegerRepresentativeTree.Tree.leaf 337 representative_337)) (QuarticIntegerRepresentativeTree.Tree.branch 339 (QuarticIntegerRepresentativeTree.Tree.leaf 338 representative_338) (QuarticIntegerRepresentativeTree.Tree.leaf 339 representative_339))) (QuarticIntegerRepresentativeTree.Tree.branch 342 (QuarticIntegerRepresentativeTree.Tree.branch 341 (QuarticIntegerRepresentativeTree.Tree.leaf 340 representative_340) (QuarticIntegerRepresentativeTree.Tree.leaf 341 representative_341)) (QuarticIntegerRepresentativeTree.Tree.branch 343 (QuarticIntegerRepresentativeTree.Tree.leaf 342 representative_342) (QuarticIntegerRepresentativeTree.Tree.leaf 343 representative_343)))) (QuarticIntegerRepresentativeTree.Tree.branch 348 (QuarticIntegerRepresentativeTree.Tree.branch 346 (QuarticIntegerRepresentativeTree.Tree.branch 345 (QuarticIntegerRepresentativeTree.Tree.leaf 344 representative_344) (QuarticIntegerRepresentativeTree.Tree.leaf 345 representative_345)) (QuarticIntegerRepresentativeTree.Tree.branch 347 (QuarticIntegerRepresentativeTree.Tree.leaf 346 representative_346) (QuarticIntegerRepresentativeTree.Tree.leaf 347 representative_347))) (QuarticIntegerRepresentativeTree.Tree.branch 350 (QuarticIntegerRepresentativeTree.Tree.branch 349 (QuarticIntegerRepresentativeTree.Tree.leaf 348 representative_348) (QuarticIntegerRepresentativeTree.Tree.leaf 349 representative_349)) (QuarticIntegerRepresentativeTree.Tree.branch 351 (QuarticIntegerRepresentativeTree.Tree.leaf 350 representative_350) (QuarticIntegerRepresentativeTree.Tree.leaf 351 representative_351)))))) (QuarticIntegerRepresentativeTree.Tree.branch 368 (QuarticIntegerRepresentativeTree.Tree.branch 360 (QuarticIntegerRepresentativeTree.Tree.branch 356 (QuarticIntegerRepresentativeTree.Tree.branch 354 (QuarticIntegerRepresentativeTree.Tree.branch 353 (QuarticIntegerRepresentativeTree.Tree.leaf 352 representative_352) (QuarticIntegerRepresentativeTree.Tree.leaf 353 representative_353)) (QuarticIntegerRepresentativeTree.Tree.branch 355 (QuarticIntegerRepresentativeTree.Tree.leaf 354 representative_354) (QuarticIntegerRepresentativeTree.Tree.leaf 355 representative_355))) (QuarticIntegerRepresentativeTree.Tree.branch 358 (QuarticIntegerRepresentativeTree.Tree.branch 357 (QuarticIntegerRepresentativeTree.Tree.leaf 356 representative_356) (QuarticIntegerRepresentativeTree.Tree.leaf 357 representative_357)) (QuarticIntegerRepresentativeTree.Tree.branch 359 (QuarticIntegerRepresentativeTree.Tree.leaf 358 representative_358) (QuarticIntegerRepresentativeTree.Tree.leaf 359 representative_359)))) (QuarticIntegerRepresentativeTree.Tree.branch 364 (QuarticIntegerRepresentativeTree.Tree.branch 362 (QuarticIntegerRepresentativeTree.Tree.branch 361 (QuarticIntegerRepresentativeTree.Tree.leaf 360 representative_360) (QuarticIntegerRepresentativeTree.Tree.leaf 361 representative_361)) (QuarticIntegerRepresentativeTree.Tree.branch 363 (QuarticIntegerRepresentativeTree.Tree.leaf 362 representative_362) (QuarticIntegerRepresentativeTree.Tree.leaf 363 representative_363))) (QuarticIntegerRepresentativeTree.Tree.branch 366 (QuarticIntegerRepresentativeTree.Tree.branch 365 (QuarticIntegerRepresentativeTree.Tree.leaf 364 representative_364) (QuarticIntegerRepresentativeTree.Tree.leaf 365 representative_365)) (QuarticIntegerRepresentativeTree.Tree.branch 367 (QuarticIntegerRepresentativeTree.Tree.leaf 366 representative_366) (QuarticIntegerRepresentativeTree.Tree.leaf 367 representative_367))))) (QuarticIntegerRepresentativeTree.Tree.branch 376 (QuarticIntegerRepresentativeTree.Tree.branch 372 (QuarticIntegerRepresentativeTree.Tree.branch 370 (QuarticIntegerRepresentativeTree.Tree.branch 369 (QuarticIntegerRepresentativeTree.Tree.leaf 368 representative_368) (QuarticIntegerRepresentativeTree.Tree.leaf 369 representative_369)) (QuarticIntegerRepresentativeTree.Tree.branch 371 (QuarticIntegerRepresentativeTree.Tree.leaf 370 representative_370) (QuarticIntegerRepresentativeTree.Tree.leaf 371 representative_371))) (QuarticIntegerRepresentativeTree.Tree.branch 374 (QuarticIntegerRepresentativeTree.Tree.branch 373 (QuarticIntegerRepresentativeTree.Tree.leaf 372 representative_372) (QuarticIntegerRepresentativeTree.Tree.leaf 373 representative_373)) (QuarticIntegerRepresentativeTree.Tree.branch 375 (QuarticIntegerRepresentativeTree.Tree.leaf 374 representative_374) (QuarticIntegerRepresentativeTree.Tree.leaf 375 representative_375)))) (QuarticIntegerRepresentativeTree.Tree.branch 380 (QuarticIntegerRepresentativeTree.Tree.branch 378 (QuarticIntegerRepresentativeTree.Tree.branch 377 (QuarticIntegerRepresentativeTree.Tree.leaf 376 representative_376) (QuarticIntegerRepresentativeTree.Tree.leaf 377 representative_377)) (QuarticIntegerRepresentativeTree.Tree.branch 379 (QuarticIntegerRepresentativeTree.Tree.leaf 378 representative_378) (QuarticIntegerRepresentativeTree.Tree.leaf 379 representative_379))) (QuarticIntegerRepresentativeTree.Tree.branch 382 (QuarticIntegerRepresentativeTree.Tree.branch 381 (QuarticIntegerRepresentativeTree.Tree.leaf 380 representative_380) (QuarticIntegerRepresentativeTree.Tree.leaf 381 representative_381)) (QuarticIntegerRepresentativeTree.Tree.branch 383 (QuarticIntegerRepresentativeTree.Tree.leaf 382 representative_382) (QuarticIntegerRepresentativeTree.Tree.leaf 383 representative_383)))))))
theorem accepted_005 : All validRep tree_005 := ⟨⟨⟨⟨⟨⟨coefficient_320,coefficient_321⟩,⟨coefficient_322,coefficient_323⟩⟩,⟨⟨coefficient_324,coefficient_325⟩,⟨coefficient_326,coefficient_327⟩⟩⟩,⟨⟨⟨coefficient_328,coefficient_329⟩,⟨coefficient_330,coefficient_331⟩⟩,⟨⟨coefficient_332,coefficient_333⟩,⟨coefficient_334,coefficient_335⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_336,coefficient_337⟩,⟨coefficient_338,coefficient_339⟩⟩,⟨⟨coefficient_340,coefficient_341⟩,⟨coefficient_342,coefficient_343⟩⟩⟩,⟨⟨⟨coefficient_344,coefficient_345⟩,⟨coefficient_346,coefficient_347⟩⟩,⟨⟨coefficient_348,coefficient_349⟩,⟨coefficient_350,coefficient_351⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_352,coefficient_353⟩,⟨coefficient_354,coefficient_355⟩⟩,⟨⟨coefficient_356,coefficient_357⟩,⟨coefficient_358,coefficient_359⟩⟩⟩,⟨⟨⟨coefficient_360,coefficient_361⟩,⟨coefficient_362,coefficient_363⟩⟩,⟨⟨coefficient_364,coefficient_365⟩,⟨coefficient_366,coefficient_367⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_368,coefficient_369⟩,⟨coefficient_370,coefficient_371⟩⟩,⟨⟨coefficient_372,coefficient_373⟩,⟨coefficient_374,coefficient_375⟩⟩⟩,⟨⟨⟨coefficient_376,coefficient_377⟩,⟨coefficient_378,coefficient_379⟩⟩,⟨⟨coefficient_380,coefficient_381⟩,⟨coefficient_382,coefficient_383⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

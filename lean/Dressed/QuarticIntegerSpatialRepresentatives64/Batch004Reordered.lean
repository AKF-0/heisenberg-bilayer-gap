import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_256 : Rep := ⟨![0,1,11,62],115⟩
def representative_257 : Rep := ⟨![0,1,12,13],462⟩
def representative_258 : Rep := ⟨![0,1,12,16],284⟩
def representative_259 : Rep := ⟨![0,1,12,17],193⟩
def representative_260 : Rep := ⟨![0,1,12,18],287⟩
def representative_261 : Rep := ⟨![0,1,12,19],462⟩
def representative_262 : Rep := ⟨![0,1,12,20],462⟩
def representative_263 : Rep := ⟨![0,1,12,21],462⟩
def representative_264 : Rep := ⟨![0,1,12,22],462⟩
def representative_265 : Rep := ⟨![0,1,12,23],462⟩
def representative_266 : Rep := ⟨![0,1,12,24],462⟩
def representative_267 : Rep := ⟨![0,1,12,25],263⟩
def representative_268 : Rep := ⟨![0,1,12,26],462⟩
def representative_269 : Rep := ⟨![0,1,12,27],462⟩
def representative_270 : Rep := ⟨![0,1,12,28],462⟩
def representative_271 : Rep := ⟨![0,1,12,29],462⟩
def representative_272 : Rep := ⟨![0,1,12,30],462⟩
def representative_273 : Rep := ⟨![0,1,12,31],462⟩
def representative_274 : Rep := ⟨![0,1,12,32],462⟩
def representative_275 : Rep := ⟨![0,1,12,33],462⟩
def representative_276 : Rep := ⟨![0,1,12,34],462⟩
def representative_277 : Rep := ⟨![0,1,12,35],462⟩
def representative_278 : Rep := ⟨![0,1,12,36],462⟩
def representative_279 : Rep := ⟨![0,1,12,37],462⟩
def representative_280 : Rep := ⟨![0,1,12,38],462⟩
def representative_281 : Rep := ⟨![0,1,12,39],462⟩
def representative_282 : Rep := ⟨![0,1,12,40],462⟩
def representative_283 : Rep := ⟨![0,1,12,41],263⟩
def representative_284 : Rep := ⟨![0,1,12,42],462⟩
def representative_285 : Rep := ⟨![0,1,12,43],462⟩
def representative_286 : Rep := ⟨![0,1,12,44],462⟩
def representative_287 : Rep := ⟨![0,1,12,45],462⟩
def representative_288 : Rep := ⟨![0,1,12,46],462⟩
def representative_289 : Rep := ⟨![0,1,12,47],462⟩
def representative_290 : Rep := ⟨![0,1,12,48],284⟩
def representative_291 : Rep := ⟨![0,1,12,49],193⟩
def representative_292 : Rep := ⟨![0,1,12,50],284⟩
def representative_293 : Rep := ⟨![0,1,12,51],462⟩
def representative_294 : Rep := ⟨![0,1,12,52],462⟩
def representative_295 : Rep := ⟨![0,1,12,53],462⟩
def representative_296 : Rep := ⟨![0,1,12,54],462⟩
def representative_297 : Rep := ⟨![0,1,12,55],462⟩
def representative_298 : Rep := ⟨![0,1,12,60],462⟩
def representative_299 : Rep := ⟨![0,1,12,61],462⟩
def representative_300 : Rep := ⟨![0,1,16,17],63⟩
def representative_301 : Rep := ⟨![0,1,16,18],367⟩
def representative_302 : Rep := ⟨![0,1,16,19],302⟩
def representative_303 : Rep := ⟨![0,1,16,20],462⟩
def representative_304 : Rep := ⟨![0,1,16,21],266⟩
def representative_305 : Rep := ⟨![0,1,16,22],140⟩
def representative_306 : Rep := ⟨![0,1,16,23],394⟩
def representative_307 : Rep := ⟨![0,1,16,25],331⟩
def representative_308 : Rep := ⟨![0,1,16,26],305⟩
def representative_309 : Rep := ⟨![0,1,16,27],462⟩
def representative_310 : Rep := ⟨![0,1,16,28],462⟩
def representative_311 : Rep := ⟨![0,1,16,29],462⟩
def representative_312 : Rep := ⟨![0,1,16,30],291⟩
def representative_313 : Rep := ⟨![0,1,16,31],132⟩
def representative_314 : Rep := ⟨![0,1,16,32],174⟩
def representative_315 : Rep := ⟨![0,1,16,33],299⟩
def representative_316 : Rep := ⟨![0,1,16,34],462⟩
def representative_317 : Rep := ⟨![0,1,16,35],462⟩
def representative_318 : Rep := ⟨![0,1,16,36],462⟩
def representative_319 : Rep := ⟨![0,1,16,37],462⟩
theorem coefficient_256 : validRep representative_256 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_256)=dictionary64.getD 115 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_115]
  decide +kernel
theorem coefficient_257 : validRep representative_257 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_257)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_258 : validRep representative_258 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_258)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_259 : validRep representative_259 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_259)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_260 : validRep representative_260 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_260)=dictionary64.getD 287 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_287]
  decide +kernel
theorem coefficient_261 : validRep representative_261 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_261)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_262 : validRep representative_262 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_262)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_263 : validRep representative_263 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_263)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_264 : validRep representative_264 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_264)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_265 : validRep representative_265 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_265)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_266 : validRep representative_266 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_266)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_267 : validRep representative_267 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_267)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_268 : validRep representative_268 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_268)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_269 : validRep representative_269 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_269)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_270 : validRep representative_270 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_270)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_271 : validRep representative_271 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_271)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_272 : validRep representative_272 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_272)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_273 : validRep representative_273 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_273)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_274 : validRep representative_274 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_274)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_275 : validRep representative_275 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_275)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_276 : validRep representative_276 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_276)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_277 : validRep representative_277 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_277)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_278 : validRep representative_278 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_278)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_279 : validRep representative_279 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_279)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_280 : validRep representative_280 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_280)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_281 : validRep representative_281 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_281)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_282 : validRep representative_282 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_282)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_283 : validRep representative_283 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_283)=dictionary64.getD 263 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_263]
  decide +kernel
theorem coefficient_284 : validRep representative_284 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_284)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_285 : validRep representative_285 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_285)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_286 : validRep representative_286 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_286)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_287 : validRep representative_287 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_287)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_288 : validRep representative_288 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_288)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_289 : validRep representative_289 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_289)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_290 : validRep representative_290 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_290)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_291 : validRep representative_291 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_291)=dictionary64.getD 193 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_193]
  decide +kernel
theorem coefficient_292 : validRep representative_292 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_292)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_293 : validRep representative_293 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_293)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_294 : validRep representative_294 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_294)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_295 : validRep representative_295 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_295)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_296 : validRep representative_296 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_296)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_297 : validRep representative_297 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_297)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_298 : validRep representative_298 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_298)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_299 : validRep representative_299 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_299)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_300 : validRep representative_300 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_300)=dictionary64.getD 63 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_63]
  decide +kernel
theorem coefficient_301 : validRep representative_301 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_301)=dictionary64.getD 367 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_367]
  decide +kernel
theorem coefficient_302 : validRep representative_302 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_302)=dictionary64.getD 302 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_302]
  decide +kernel
theorem coefficient_303 : validRep representative_303 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_303)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_304 : validRep representative_304 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_304)=dictionary64.getD 266 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_266]
  decide +kernel
theorem coefficient_305 : validRep representative_305 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_305)=dictionary64.getD 140 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_140]
  decide +kernel
theorem coefficient_306 : validRep representative_306 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_306)=dictionary64.getD 394 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_394]
  decide +kernel
theorem coefficient_307 : validRep representative_307 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_307)=dictionary64.getD 331 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_331]
  decide +kernel
theorem coefficient_308 : validRep representative_308 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_308)=dictionary64.getD 305 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_305]
  decide +kernel
theorem coefficient_309 : validRep representative_309 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_309)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_310 : validRep representative_310 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_310)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_311 : validRep representative_311 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_311)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_312 : validRep representative_312 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_312)=dictionary64.getD 291 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_291]
  decide +kernel
theorem coefficient_313 : validRep representative_313 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_313)=dictionary64.getD 132 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_132]
  decide +kernel
theorem coefficient_314 : validRep representative_314 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_314)=dictionary64.getD 174 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_174]
  decide +kernel
theorem coefficient_315 : validRep representative_315 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_315)=dictionary64.getD 299 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_299]
  decide +kernel
theorem coefficient_316 : validRep representative_316 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_316)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_317 : validRep representative_317 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_317)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_318 : validRep representative_318 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_318)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_319 : validRep representative_319 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_319)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_004 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 288 (QuarticIntegerRepresentativeTree.Tree.branch 272 (QuarticIntegerRepresentativeTree.Tree.branch 264 (QuarticIntegerRepresentativeTree.Tree.branch 260 (QuarticIntegerRepresentativeTree.Tree.branch 258 (QuarticIntegerRepresentativeTree.Tree.branch 257 (QuarticIntegerRepresentativeTree.Tree.leaf 256 representative_256) (QuarticIntegerRepresentativeTree.Tree.leaf 257 representative_257)) (QuarticIntegerRepresentativeTree.Tree.branch 259 (QuarticIntegerRepresentativeTree.Tree.leaf 258 representative_258) (QuarticIntegerRepresentativeTree.Tree.leaf 259 representative_259))) (QuarticIntegerRepresentativeTree.Tree.branch 262 (QuarticIntegerRepresentativeTree.Tree.branch 261 (QuarticIntegerRepresentativeTree.Tree.leaf 260 representative_260) (QuarticIntegerRepresentativeTree.Tree.leaf 261 representative_261)) (QuarticIntegerRepresentativeTree.Tree.branch 263 (QuarticIntegerRepresentativeTree.Tree.leaf 262 representative_262) (QuarticIntegerRepresentativeTree.Tree.leaf 263 representative_263)))) (QuarticIntegerRepresentativeTree.Tree.branch 268 (QuarticIntegerRepresentativeTree.Tree.branch 266 (QuarticIntegerRepresentativeTree.Tree.branch 265 (QuarticIntegerRepresentativeTree.Tree.leaf 264 representative_264) (QuarticIntegerRepresentativeTree.Tree.leaf 265 representative_265)) (QuarticIntegerRepresentativeTree.Tree.branch 267 (QuarticIntegerRepresentativeTree.Tree.leaf 266 representative_266) (QuarticIntegerRepresentativeTree.Tree.leaf 267 representative_267))) (QuarticIntegerRepresentativeTree.Tree.branch 270 (QuarticIntegerRepresentativeTree.Tree.branch 269 (QuarticIntegerRepresentativeTree.Tree.leaf 268 representative_268) (QuarticIntegerRepresentativeTree.Tree.leaf 269 representative_269)) (QuarticIntegerRepresentativeTree.Tree.branch 271 (QuarticIntegerRepresentativeTree.Tree.leaf 270 representative_270) (QuarticIntegerRepresentativeTree.Tree.leaf 271 representative_271))))) (QuarticIntegerRepresentativeTree.Tree.branch 280 (QuarticIntegerRepresentativeTree.Tree.branch 276 (QuarticIntegerRepresentativeTree.Tree.branch 274 (QuarticIntegerRepresentativeTree.Tree.branch 273 (QuarticIntegerRepresentativeTree.Tree.leaf 272 representative_272) (QuarticIntegerRepresentativeTree.Tree.leaf 273 representative_273)) (QuarticIntegerRepresentativeTree.Tree.branch 275 (QuarticIntegerRepresentativeTree.Tree.leaf 274 representative_274) (QuarticIntegerRepresentativeTree.Tree.leaf 275 representative_275))) (QuarticIntegerRepresentativeTree.Tree.branch 278 (QuarticIntegerRepresentativeTree.Tree.branch 277 (QuarticIntegerRepresentativeTree.Tree.leaf 276 representative_276) (QuarticIntegerRepresentativeTree.Tree.leaf 277 representative_277)) (QuarticIntegerRepresentativeTree.Tree.branch 279 (QuarticIntegerRepresentativeTree.Tree.leaf 278 representative_278) (QuarticIntegerRepresentativeTree.Tree.leaf 279 representative_279)))) (QuarticIntegerRepresentativeTree.Tree.branch 284 (QuarticIntegerRepresentativeTree.Tree.branch 282 (QuarticIntegerRepresentativeTree.Tree.branch 281 (QuarticIntegerRepresentativeTree.Tree.leaf 280 representative_280) (QuarticIntegerRepresentativeTree.Tree.leaf 281 representative_281)) (QuarticIntegerRepresentativeTree.Tree.branch 283 (QuarticIntegerRepresentativeTree.Tree.leaf 282 representative_282) (QuarticIntegerRepresentativeTree.Tree.leaf 283 representative_283))) (QuarticIntegerRepresentativeTree.Tree.branch 286 (QuarticIntegerRepresentativeTree.Tree.branch 285 (QuarticIntegerRepresentativeTree.Tree.leaf 284 representative_284) (QuarticIntegerRepresentativeTree.Tree.leaf 285 representative_285)) (QuarticIntegerRepresentativeTree.Tree.branch 287 (QuarticIntegerRepresentativeTree.Tree.leaf 286 representative_286) (QuarticIntegerRepresentativeTree.Tree.leaf 287 representative_287)))))) (QuarticIntegerRepresentativeTree.Tree.branch 304 (QuarticIntegerRepresentativeTree.Tree.branch 296 (QuarticIntegerRepresentativeTree.Tree.branch 292 (QuarticIntegerRepresentativeTree.Tree.branch 290 (QuarticIntegerRepresentativeTree.Tree.branch 289 (QuarticIntegerRepresentativeTree.Tree.leaf 288 representative_288) (QuarticIntegerRepresentativeTree.Tree.leaf 289 representative_289)) (QuarticIntegerRepresentativeTree.Tree.branch 291 (QuarticIntegerRepresentativeTree.Tree.leaf 290 representative_290) (QuarticIntegerRepresentativeTree.Tree.leaf 291 representative_291))) (QuarticIntegerRepresentativeTree.Tree.branch 294 (QuarticIntegerRepresentativeTree.Tree.branch 293 (QuarticIntegerRepresentativeTree.Tree.leaf 292 representative_292) (QuarticIntegerRepresentativeTree.Tree.leaf 293 representative_293)) (QuarticIntegerRepresentativeTree.Tree.branch 295 (QuarticIntegerRepresentativeTree.Tree.leaf 294 representative_294) (QuarticIntegerRepresentativeTree.Tree.leaf 295 representative_295)))) (QuarticIntegerRepresentativeTree.Tree.branch 300 (QuarticIntegerRepresentativeTree.Tree.branch 298 (QuarticIntegerRepresentativeTree.Tree.branch 297 (QuarticIntegerRepresentativeTree.Tree.leaf 296 representative_296) (QuarticIntegerRepresentativeTree.Tree.leaf 297 representative_297)) (QuarticIntegerRepresentativeTree.Tree.branch 299 (QuarticIntegerRepresentativeTree.Tree.leaf 298 representative_298) (QuarticIntegerRepresentativeTree.Tree.leaf 299 representative_299))) (QuarticIntegerRepresentativeTree.Tree.branch 302 (QuarticIntegerRepresentativeTree.Tree.branch 301 (QuarticIntegerRepresentativeTree.Tree.leaf 300 representative_300) (QuarticIntegerRepresentativeTree.Tree.leaf 301 representative_301)) (QuarticIntegerRepresentativeTree.Tree.branch 303 (QuarticIntegerRepresentativeTree.Tree.leaf 302 representative_302) (QuarticIntegerRepresentativeTree.Tree.leaf 303 representative_303))))) (QuarticIntegerRepresentativeTree.Tree.branch 312 (QuarticIntegerRepresentativeTree.Tree.branch 308 (QuarticIntegerRepresentativeTree.Tree.branch 306 (QuarticIntegerRepresentativeTree.Tree.branch 305 (QuarticIntegerRepresentativeTree.Tree.leaf 304 representative_304) (QuarticIntegerRepresentativeTree.Tree.leaf 305 representative_305)) (QuarticIntegerRepresentativeTree.Tree.branch 307 (QuarticIntegerRepresentativeTree.Tree.leaf 306 representative_306) (QuarticIntegerRepresentativeTree.Tree.leaf 307 representative_307))) (QuarticIntegerRepresentativeTree.Tree.branch 310 (QuarticIntegerRepresentativeTree.Tree.branch 309 (QuarticIntegerRepresentativeTree.Tree.leaf 308 representative_308) (QuarticIntegerRepresentativeTree.Tree.leaf 309 representative_309)) (QuarticIntegerRepresentativeTree.Tree.branch 311 (QuarticIntegerRepresentativeTree.Tree.leaf 310 representative_310) (QuarticIntegerRepresentativeTree.Tree.leaf 311 representative_311)))) (QuarticIntegerRepresentativeTree.Tree.branch 316 (QuarticIntegerRepresentativeTree.Tree.branch 314 (QuarticIntegerRepresentativeTree.Tree.branch 313 (QuarticIntegerRepresentativeTree.Tree.leaf 312 representative_312) (QuarticIntegerRepresentativeTree.Tree.leaf 313 representative_313)) (QuarticIntegerRepresentativeTree.Tree.branch 315 (QuarticIntegerRepresentativeTree.Tree.leaf 314 representative_314) (QuarticIntegerRepresentativeTree.Tree.leaf 315 representative_315))) (QuarticIntegerRepresentativeTree.Tree.branch 318 (QuarticIntegerRepresentativeTree.Tree.branch 317 (QuarticIntegerRepresentativeTree.Tree.leaf 316 representative_316) (QuarticIntegerRepresentativeTree.Tree.leaf 317 representative_317)) (QuarticIntegerRepresentativeTree.Tree.branch 319 (QuarticIntegerRepresentativeTree.Tree.leaf 318 representative_318) (QuarticIntegerRepresentativeTree.Tree.leaf 319 representative_319)))))))
theorem accepted_004 : All validRep tree_004 := ⟨⟨⟨⟨⟨⟨coefficient_256,coefficient_257⟩,⟨coefficient_258,coefficient_259⟩⟩,⟨⟨coefficient_260,coefficient_261⟩,⟨coefficient_262,coefficient_263⟩⟩⟩,⟨⟨⟨coefficient_264,coefficient_265⟩,⟨coefficient_266,coefficient_267⟩⟩,⟨⟨coefficient_268,coefficient_269⟩,⟨coefficient_270,coefficient_271⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_272,coefficient_273⟩,⟨coefficient_274,coefficient_275⟩⟩,⟨⟨coefficient_276,coefficient_277⟩,⟨coefficient_278,coefficient_279⟩⟩⟩,⟨⟨⟨coefficient_280,coefficient_281⟩,⟨coefficient_282,coefficient_283⟩⟩,⟨⟨coefficient_284,coefficient_285⟩,⟨coefficient_286,coefficient_287⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_288,coefficient_289⟩,⟨coefficient_290,coefficient_291⟩⟩,⟨⟨coefficient_292,coefficient_293⟩,⟨coefficient_294,coefficient_295⟩⟩⟩,⟨⟨⟨coefficient_296,coefficient_297⟩,⟨coefficient_298,coefficient_299⟩⟩,⟨⟨coefficient_300,coefficient_301⟩,⟨coefficient_302,coefficient_303⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_304,coefficient_305⟩,⟨coefficient_306,coefficient_307⟩⟩,⟨⟨coefficient_308,coefficient_309⟩,⟨coefficient_310,coefficient_311⟩⟩⟩,⟨⟨⟨coefficient_312,coefficient_313⟩,⟨coefficient_314,coefficient_315⟩⟩,⟨⟨coefficient_316,coefficient_317⟩,⟨coefficient_318,coefficient_319⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

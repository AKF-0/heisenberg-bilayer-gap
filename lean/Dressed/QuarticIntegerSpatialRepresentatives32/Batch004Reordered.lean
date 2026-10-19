import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_256 : Rep := ⟨![0,4,2,28],493⟩
def representative_257 : Rep := ⟨![0,4,2,29],64⟩
def representative_258 : Rep := ⟨![0,4,2,30],439⟩
def representative_259 : Rep := ⟨![0,4,8,12],473⟩
def representative_260 : Rep := ⟨![0,4,8,13],73⟩
def representative_261 : Rep := ⟨![0,4,8,14],191⟩
def representative_262 : Rep := ⟨![0,4,8,16],106⟩
def representative_263 : Rep := ⟨![0,4,8,17],124⟩
def representative_264 : Rep := ⟨![0,4,8,18],508⟩
def representative_265 : Rep := ⟨![0,4,8,20],98⟩
def representative_266 : Rep := ⟨![0,4,8,21],235⟩
def representative_267 : Rep := ⟨![0,4,8,22],508⟩
def representative_268 : Rep := ⟨![0,4,8,24],478⟩
def representative_269 : Rep := ⟨![0,4,8,25],67⟩
def representative_270 : Rep := ⟨![0,4,8,26],190⟩
def representative_271 : Rep := ⟨![0,4,8,28],28⟩
def representative_272 : Rep := ⟨![0,4,8,29],490⟩
def representative_273 : Rep := ⟨![0,4,8,30],49⟩
def representative_274 : Rep := ⟨![0,4,9,12],85⟩
def representative_275 : Rep := ⟨![0,4,9,13],426⟩
def representative_276 : Rep := ⟨![0,4,9,14],140⟩
def representative_277 : Rep := ⟨![0,4,9,15],398⟩
def representative_278 : Rep := ⟨![0,4,9,16],362⟩
def representative_279 : Rep := ⟨![0,4,9,17],177⟩
def representative_280 : Rep := ⟨![0,4,9,18],323⟩
def representative_281 : Rep := ⟨![0,4,9,19],211⟩
def representative_282 : Rep := ⟨![0,4,9,20],366⟩
def representative_283 : Rep := ⟨![0,4,9,21],315⟩
def representative_284 : Rep := ⟨![0,4,9,22],508⟩
def representative_285 : Rep := ⟨![0,4,9,23],303⟩
def representative_286 : Rep := ⟨![0,4,9,24],86⟩
def representative_287 : Rep := ⟨![0,4,9,25],404⟩
def representative_288 : Rep := ⟨![0,4,9,26],326⟩
def representative_289 : Rep := ⟨![0,4,9,27],404⟩
def representative_290 : Rep := ⟨![0,4,9,29],62⟩
def representative_291 : Rep := ⟨![0,4,9,30],428⟩
def representative_292 : Rep := ⟨![0,4,9,31],61⟩
def representative_293 : Rep := ⟨![0,4,10,12],399⟩
def representative_294 : Rep := ⟨![0,4,10,13],147⟩
def representative_295 : Rep := ⟨![0,4,10,14],345⟩
def representative_296 : Rep := ⟨![0,4,10,16],190⟩
def representative_297 : Rep := ⟨![0,4,10,17],318⟩
def representative_298 : Rep := ⟨![0,4,10,18],258⟩
def representative_299 : Rep := ⟨![0,4,10,20],184⟩
def representative_300 : Rep := ⟨![0,4,10,21],508⟩
def representative_301 : Rep := ⟨![0,4,10,22],278⟩
def representative_302 : Rep := ⟨![0,4,10,24],405⟩
def representative_303 : Rep := ⟨![0,4,10,25],141⟩
def representative_304 : Rep := ⟨![0,4,10,26],508⟩
def representative_305 : Rep := ⟨![0,4,10,30],129⟩
def representative_306 : Rep := ⟨![0,4,12,16],363⟩
def representative_307 : Rep := ⟨![0,4,12,17],213⟩
def representative_308 : Rep := ⟨![0,4,12,18],299⟩
def representative_309 : Rep := ⟨![0,4,12,20],352⟩
def representative_310 : Rep := ⟨![0,4,12,21],296⟩
def representative_311 : Rep := ⟨![0,4,12,22],508⟩
def representative_312 : Rep := ⟨![0,4,12,24],103⟩
def representative_313 : Rep := ⟨![0,4,12,25],378⟩
def representative_314 : Rep := ⟨![0,4,12,26],303⟩
def representative_315 : Rep := ⟨![0,4,13,16],224⟩
def representative_316 : Rep := ⟨![0,4,13,17],316⟩
def representative_317 : Rep := ⟨![0,4,13,18],268⟩
def representative_318 : Rep := ⟨![0,4,13,19],306⟩
def representative_319 : Rep := ⟨![0,4,13,20],215⟩
theorem coefficient_256 : validRep representative_256 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_256)=dictionary32.getD 493 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_493]
  decide +kernel
theorem coefficient_257 : validRep representative_257 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_257)=dictionary32.getD 64 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_64]
  decide +kernel
theorem coefficient_258 : validRep representative_258 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_258)=dictionary32.getD 439 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_439]
  decide +kernel
theorem coefficient_259 : validRep representative_259 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_259)=dictionary32.getD 473 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_473]
  decide +kernel
theorem coefficient_260 : validRep representative_260 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_260)=dictionary32.getD 73 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_73]
  decide +kernel
theorem coefficient_261 : validRep representative_261 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_261)=dictionary32.getD 191 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_191]
  decide +kernel
theorem coefficient_262 : validRep representative_262 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_262)=dictionary32.getD 106 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_106]
  decide +kernel
theorem coefficient_263 : validRep representative_263 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_263)=dictionary32.getD 124 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_124]
  decide +kernel
theorem coefficient_264 : validRep representative_264 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_264)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_265 : validRep representative_265 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_265)=dictionary32.getD 98 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_98]
  decide +kernel
theorem coefficient_266 : validRep representative_266 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_266)=dictionary32.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_267 : validRep representative_267 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_267)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_268 : validRep representative_268 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_268)=dictionary32.getD 478 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_478]
  decide +kernel
theorem coefficient_269 : validRep representative_269 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_269)=dictionary32.getD 67 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_67]
  decide +kernel
theorem coefficient_270 : validRep representative_270 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_270)=dictionary32.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_271 : validRep representative_271 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_271)=dictionary32.getD 28 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_28]
  decide +kernel
theorem coefficient_272 : validRep representative_272 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_272)=dictionary32.getD 490 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_490]
  decide +kernel
theorem coefficient_273 : validRep representative_273 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_273)=dictionary32.getD 49 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_49]
  decide +kernel
theorem coefficient_274 : validRep representative_274 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_274)=dictionary32.getD 85 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_85]
  decide +kernel
theorem coefficient_275 : validRep representative_275 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_275)=dictionary32.getD 426 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_426]
  decide +kernel
theorem coefficient_276 : validRep representative_276 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_276)=dictionary32.getD 140 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_140]
  decide +kernel
theorem coefficient_277 : validRep representative_277 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_277)=dictionary32.getD 398 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_398]
  decide +kernel
theorem coefficient_278 : validRep representative_278 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_278)=dictionary32.getD 362 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_362]
  decide +kernel
theorem coefficient_279 : validRep representative_279 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_279)=dictionary32.getD 177 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_177]
  decide +kernel
theorem coefficient_280 : validRep representative_280 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_280)=dictionary32.getD 323 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_323]
  decide +kernel
theorem coefficient_281 : validRep representative_281 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_281)=dictionary32.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_282 : validRep representative_282 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_282)=dictionary32.getD 366 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_366]
  decide +kernel
theorem coefficient_283 : validRep representative_283 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_283)=dictionary32.getD 315 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_315]
  decide +kernel
theorem coefficient_284 : validRep representative_284 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_284)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_285 : validRep representative_285 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_285)=dictionary32.getD 303 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_303]
  decide +kernel
theorem coefficient_286 : validRep representative_286 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_286)=dictionary32.getD 86 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_86]
  decide +kernel
theorem coefficient_287 : validRep representative_287 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_287)=dictionary32.getD 404 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_404]
  decide +kernel
theorem coefficient_288 : validRep representative_288 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_288)=dictionary32.getD 326 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_326]
  decide +kernel
theorem coefficient_289 : validRep representative_289 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_289)=dictionary32.getD 404 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_404]
  decide +kernel
theorem coefficient_290 : validRep representative_290 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_290)=dictionary32.getD 62 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_62]
  decide +kernel
theorem coefficient_291 : validRep representative_291 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_291)=dictionary32.getD 428 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_428]
  decide +kernel
theorem coefficient_292 : validRep representative_292 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_292)=dictionary32.getD 61 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_61]
  decide +kernel
theorem coefficient_293 : validRep representative_293 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_293)=dictionary32.getD 399 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_399]
  decide +kernel
theorem coefficient_294 : validRep representative_294 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_294)=dictionary32.getD 147 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_147]
  decide +kernel
theorem coefficient_295 : validRep representative_295 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_295)=dictionary32.getD 345 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_345]
  decide +kernel
theorem coefficient_296 : validRep representative_296 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_296)=dictionary32.getD 190 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_190]
  decide +kernel
theorem coefficient_297 : validRep representative_297 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_297)=dictionary32.getD 318 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_318]
  decide +kernel
theorem coefficient_298 : validRep representative_298 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_298)=dictionary32.getD 258 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_258]
  decide +kernel
theorem coefficient_299 : validRep representative_299 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_299)=dictionary32.getD 184 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_184]
  decide +kernel
theorem coefficient_300 : validRep representative_300 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_300)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_301 : validRep representative_301 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_301)=dictionary32.getD 278 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_278]
  decide +kernel
theorem coefficient_302 : validRep representative_302 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_302)=dictionary32.getD 405 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_405]
  decide +kernel
theorem coefficient_303 : validRep representative_303 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_303)=dictionary32.getD 141 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_141]
  decide +kernel
theorem coefficient_304 : validRep representative_304 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_304)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_305 : validRep representative_305 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_305)=dictionary32.getD 129 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_129]
  decide +kernel
theorem coefficient_306 : validRep representative_306 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_306)=dictionary32.getD 363 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_363]
  decide +kernel
theorem coefficient_307 : validRep representative_307 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_307)=dictionary32.getD 213 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_213]
  decide +kernel
theorem coefficient_308 : validRep representative_308 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_308)=dictionary32.getD 299 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_299]
  decide +kernel
theorem coefficient_309 : validRep representative_309 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_309)=dictionary32.getD 352 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_352]
  decide +kernel
theorem coefficient_310 : validRep representative_310 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_310)=dictionary32.getD 296 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_296]
  decide +kernel
theorem coefficient_311 : validRep representative_311 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_311)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_312 : validRep representative_312 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_312)=dictionary32.getD 103 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_103]
  decide +kernel
theorem coefficient_313 : validRep representative_313 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_313)=dictionary32.getD 378 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_378]
  decide +kernel
theorem coefficient_314 : validRep representative_314 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_314)=dictionary32.getD 303 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_303]
  decide +kernel
theorem coefficient_315 : validRep representative_315 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_315)=dictionary32.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_316 : validRep representative_316 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_316)=dictionary32.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_317 : validRep representative_317 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_317)=dictionary32.getD 268 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_268]
  decide +kernel
theorem coefficient_318 : validRep representative_318 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_318)=dictionary32.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_319 : validRep representative_319 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_319)=dictionary32.getD 215 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_215]
  decide +kernel
def tree_004 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 288 (QuarticIntegerRepresentativeTree.Tree.branch 272 (QuarticIntegerRepresentativeTree.Tree.branch 264 (QuarticIntegerRepresentativeTree.Tree.branch 260 (QuarticIntegerRepresentativeTree.Tree.branch 258 (QuarticIntegerRepresentativeTree.Tree.branch 257 (QuarticIntegerRepresentativeTree.Tree.leaf 256 representative_256) (QuarticIntegerRepresentativeTree.Tree.leaf 257 representative_257)) (QuarticIntegerRepresentativeTree.Tree.branch 259 (QuarticIntegerRepresentativeTree.Tree.leaf 258 representative_258) (QuarticIntegerRepresentativeTree.Tree.leaf 259 representative_259))) (QuarticIntegerRepresentativeTree.Tree.branch 262 (QuarticIntegerRepresentativeTree.Tree.branch 261 (QuarticIntegerRepresentativeTree.Tree.leaf 260 representative_260) (QuarticIntegerRepresentativeTree.Tree.leaf 261 representative_261)) (QuarticIntegerRepresentativeTree.Tree.branch 263 (QuarticIntegerRepresentativeTree.Tree.leaf 262 representative_262) (QuarticIntegerRepresentativeTree.Tree.leaf 263 representative_263)))) (QuarticIntegerRepresentativeTree.Tree.branch 268 (QuarticIntegerRepresentativeTree.Tree.branch 266 (QuarticIntegerRepresentativeTree.Tree.branch 265 (QuarticIntegerRepresentativeTree.Tree.leaf 264 representative_264) (QuarticIntegerRepresentativeTree.Tree.leaf 265 representative_265)) (QuarticIntegerRepresentativeTree.Tree.branch 267 (QuarticIntegerRepresentativeTree.Tree.leaf 266 representative_266) (QuarticIntegerRepresentativeTree.Tree.leaf 267 representative_267))) (QuarticIntegerRepresentativeTree.Tree.branch 270 (QuarticIntegerRepresentativeTree.Tree.branch 269 (QuarticIntegerRepresentativeTree.Tree.leaf 268 representative_268) (QuarticIntegerRepresentativeTree.Tree.leaf 269 representative_269)) (QuarticIntegerRepresentativeTree.Tree.branch 271 (QuarticIntegerRepresentativeTree.Tree.leaf 270 representative_270) (QuarticIntegerRepresentativeTree.Tree.leaf 271 representative_271))))) (QuarticIntegerRepresentativeTree.Tree.branch 280 (QuarticIntegerRepresentativeTree.Tree.branch 276 (QuarticIntegerRepresentativeTree.Tree.branch 274 (QuarticIntegerRepresentativeTree.Tree.branch 273 (QuarticIntegerRepresentativeTree.Tree.leaf 272 representative_272) (QuarticIntegerRepresentativeTree.Tree.leaf 273 representative_273)) (QuarticIntegerRepresentativeTree.Tree.branch 275 (QuarticIntegerRepresentativeTree.Tree.leaf 274 representative_274) (QuarticIntegerRepresentativeTree.Tree.leaf 275 representative_275))) (QuarticIntegerRepresentativeTree.Tree.branch 278 (QuarticIntegerRepresentativeTree.Tree.branch 277 (QuarticIntegerRepresentativeTree.Tree.leaf 276 representative_276) (QuarticIntegerRepresentativeTree.Tree.leaf 277 representative_277)) (QuarticIntegerRepresentativeTree.Tree.branch 279 (QuarticIntegerRepresentativeTree.Tree.leaf 278 representative_278) (QuarticIntegerRepresentativeTree.Tree.leaf 279 representative_279)))) (QuarticIntegerRepresentativeTree.Tree.branch 284 (QuarticIntegerRepresentativeTree.Tree.branch 282 (QuarticIntegerRepresentativeTree.Tree.branch 281 (QuarticIntegerRepresentativeTree.Tree.leaf 280 representative_280) (QuarticIntegerRepresentativeTree.Tree.leaf 281 representative_281)) (QuarticIntegerRepresentativeTree.Tree.branch 283 (QuarticIntegerRepresentativeTree.Tree.leaf 282 representative_282) (QuarticIntegerRepresentativeTree.Tree.leaf 283 representative_283))) (QuarticIntegerRepresentativeTree.Tree.branch 286 (QuarticIntegerRepresentativeTree.Tree.branch 285 (QuarticIntegerRepresentativeTree.Tree.leaf 284 representative_284) (QuarticIntegerRepresentativeTree.Tree.leaf 285 representative_285)) (QuarticIntegerRepresentativeTree.Tree.branch 287 (QuarticIntegerRepresentativeTree.Tree.leaf 286 representative_286) (QuarticIntegerRepresentativeTree.Tree.leaf 287 representative_287)))))) (QuarticIntegerRepresentativeTree.Tree.branch 304 (QuarticIntegerRepresentativeTree.Tree.branch 296 (QuarticIntegerRepresentativeTree.Tree.branch 292 (QuarticIntegerRepresentativeTree.Tree.branch 290 (QuarticIntegerRepresentativeTree.Tree.branch 289 (QuarticIntegerRepresentativeTree.Tree.leaf 288 representative_288) (QuarticIntegerRepresentativeTree.Tree.leaf 289 representative_289)) (QuarticIntegerRepresentativeTree.Tree.branch 291 (QuarticIntegerRepresentativeTree.Tree.leaf 290 representative_290) (QuarticIntegerRepresentativeTree.Tree.leaf 291 representative_291))) (QuarticIntegerRepresentativeTree.Tree.branch 294 (QuarticIntegerRepresentativeTree.Tree.branch 293 (QuarticIntegerRepresentativeTree.Tree.leaf 292 representative_292) (QuarticIntegerRepresentativeTree.Tree.leaf 293 representative_293)) (QuarticIntegerRepresentativeTree.Tree.branch 295 (QuarticIntegerRepresentativeTree.Tree.leaf 294 representative_294) (QuarticIntegerRepresentativeTree.Tree.leaf 295 representative_295)))) (QuarticIntegerRepresentativeTree.Tree.branch 300 (QuarticIntegerRepresentativeTree.Tree.branch 298 (QuarticIntegerRepresentativeTree.Tree.branch 297 (QuarticIntegerRepresentativeTree.Tree.leaf 296 representative_296) (QuarticIntegerRepresentativeTree.Tree.leaf 297 representative_297)) (QuarticIntegerRepresentativeTree.Tree.branch 299 (QuarticIntegerRepresentativeTree.Tree.leaf 298 representative_298) (QuarticIntegerRepresentativeTree.Tree.leaf 299 representative_299))) (QuarticIntegerRepresentativeTree.Tree.branch 302 (QuarticIntegerRepresentativeTree.Tree.branch 301 (QuarticIntegerRepresentativeTree.Tree.leaf 300 representative_300) (QuarticIntegerRepresentativeTree.Tree.leaf 301 representative_301)) (QuarticIntegerRepresentativeTree.Tree.branch 303 (QuarticIntegerRepresentativeTree.Tree.leaf 302 representative_302) (QuarticIntegerRepresentativeTree.Tree.leaf 303 representative_303))))) (QuarticIntegerRepresentativeTree.Tree.branch 312 (QuarticIntegerRepresentativeTree.Tree.branch 308 (QuarticIntegerRepresentativeTree.Tree.branch 306 (QuarticIntegerRepresentativeTree.Tree.branch 305 (QuarticIntegerRepresentativeTree.Tree.leaf 304 representative_304) (QuarticIntegerRepresentativeTree.Tree.leaf 305 representative_305)) (QuarticIntegerRepresentativeTree.Tree.branch 307 (QuarticIntegerRepresentativeTree.Tree.leaf 306 representative_306) (QuarticIntegerRepresentativeTree.Tree.leaf 307 representative_307))) (QuarticIntegerRepresentativeTree.Tree.branch 310 (QuarticIntegerRepresentativeTree.Tree.branch 309 (QuarticIntegerRepresentativeTree.Tree.leaf 308 representative_308) (QuarticIntegerRepresentativeTree.Tree.leaf 309 representative_309)) (QuarticIntegerRepresentativeTree.Tree.branch 311 (QuarticIntegerRepresentativeTree.Tree.leaf 310 representative_310) (QuarticIntegerRepresentativeTree.Tree.leaf 311 representative_311)))) (QuarticIntegerRepresentativeTree.Tree.branch 316 (QuarticIntegerRepresentativeTree.Tree.branch 314 (QuarticIntegerRepresentativeTree.Tree.branch 313 (QuarticIntegerRepresentativeTree.Tree.leaf 312 representative_312) (QuarticIntegerRepresentativeTree.Tree.leaf 313 representative_313)) (QuarticIntegerRepresentativeTree.Tree.branch 315 (QuarticIntegerRepresentativeTree.Tree.leaf 314 representative_314) (QuarticIntegerRepresentativeTree.Tree.leaf 315 representative_315))) (QuarticIntegerRepresentativeTree.Tree.branch 318 (QuarticIntegerRepresentativeTree.Tree.branch 317 (QuarticIntegerRepresentativeTree.Tree.leaf 316 representative_316) (QuarticIntegerRepresentativeTree.Tree.leaf 317 representative_317)) (QuarticIntegerRepresentativeTree.Tree.branch 319 (QuarticIntegerRepresentativeTree.Tree.leaf 318 representative_318) (QuarticIntegerRepresentativeTree.Tree.leaf 319 representative_319)))))))
theorem accepted_004 : All validRep tree_004 := ⟨⟨⟨⟨⟨⟨coefficient_256,coefficient_257⟩,⟨coefficient_258,coefficient_259⟩⟩,⟨⟨coefficient_260,coefficient_261⟩,⟨coefficient_262,coefficient_263⟩⟩⟩,⟨⟨⟨coefficient_264,coefficient_265⟩,⟨coefficient_266,coefficient_267⟩⟩,⟨⟨coefficient_268,coefficient_269⟩,⟨coefficient_270,coefficient_271⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_272,coefficient_273⟩,⟨coefficient_274,coefficient_275⟩⟩,⟨⟨coefficient_276,coefficient_277⟩,⟨coefficient_278,coefficient_279⟩⟩⟩,⟨⟨⟨coefficient_280,coefficient_281⟩,⟨coefficient_282,coefficient_283⟩⟩,⟨⟨coefficient_284,coefficient_285⟩,⟨coefficient_286,coefficient_287⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_288,coefficient_289⟩,⟨coefficient_290,coefficient_291⟩⟩,⟨⟨coefficient_292,coefficient_293⟩,⟨coefficient_294,coefficient_295⟩⟩⟩,⟨⟨⟨coefficient_296,coefficient_297⟩,⟨coefficient_298,coefficient_299⟩⟩,⟨⟨coefficient_300,coefficient_301⟩,⟨coefficient_302,coefficient_303⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_304,coefficient_305⟩,⟨coefficient_306,coefficient_307⟩⟩,⟨⟨coefficient_308,coefficient_309⟩,⟨coefficient_310,coefficient_311⟩⟩⟩,⟨⟨⟨coefficient_312,coefficient_313⟩,⟨coefficient_314,coefficient_315⟩⟩,⟨⟨coefficient_316,coefficient_317⟩,⟨coefficient_318,coefficient_319⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

import Dressed.QuarticIntegerMembership16.Dictionary
import Dressed.QuarticIntegerBalancedKernel
import Dressed.QuarticIntegerZeroCases
namespace BilayerDressed.QuarticIntegerRepresentatives16
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership16
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem coefficient_256 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,1,11]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_257 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,1,14]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_258 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,1,15]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_259 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,4]) i))=dictionary16.getD 34 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_34]
  decide +kernel
theorem coefficient_260 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,5]) i))=dictionary16.getD 8 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_8]
  decide +kernel
theorem coefficient_261 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,8]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_262 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,9]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_263 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,10]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_264 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,11]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_265 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,12]) i))=dictionary16.getD 31 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_31]
  decide +kernel
theorem coefficient_266 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,2,15]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_267 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,8]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_268 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,9]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_269 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,10]) i))=dictionary16.getD 31 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_31]
  decide +kernel
theorem coefficient_270 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,11]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_271 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,12]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_272 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,3,13]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_273 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,4,11]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_274 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,4,12]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_275 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,4,13]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_276 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,4,14]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_277 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,4,15]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_278 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,5,8]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_279 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,5,12]) i))=dictionary16.getD 31 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_31]
  decide +kernel
theorem coefficient_280 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,5,13]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_281 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,5,14]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_282 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,5,15]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_283 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,7,10]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_284 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,7,12]) i))=dictionary16.getD 31 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_31]
  decide +kernel
theorem coefficient_285 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,7,13]) i))=dictionary16.getD 16 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_16]
  decide +kernel
theorem coefficient_286 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,7,14]) i))=dictionary16.getD 33 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_33]
  decide +kernel
theorem coefficient_287 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,7,15]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_288 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,8,14]) i))=dictionary16.getD 23 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_23]
  decide +kernel
theorem coefficient_289 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,8,15]) i))=dictionary16.getD 19 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_19]
  decide +kernel
theorem coefficient_290 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,9,12]) i))=dictionary16.getD 18 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_18]
  decide +kernel
theorem coefficient_291 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,9,15]) i))=dictionary16.getD 23 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_23]
  decide +kernel
theorem coefficient_292 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,10,12]) i))=dictionary16.getD 20 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_20]
  decide +kernel
theorem coefficient_293 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,10,13]) i))=dictionary16.getD 18 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_18]
  decide +kernel
theorem coefficient_294 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),6,11,14]) i))=dictionary16.getD 19 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_19]
  decide +kernel
theorem coefficient_295 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,4]) i))=dictionary16.getD 41 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_296 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,8]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_297 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,9]) i))=dictionary16.getD 28 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_28]
  decide +kernel
theorem coefficient_298 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,10]) i))=dictionary16.getD 18 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_18]
  decide +kernel
theorem coefficient_299 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,11]) i))=dictionary16.getD 30 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_30]
  decide +kernel
theorem coefficient_300 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,1,14]) i))=dictionary16.getD 28 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_28]
  decide +kernel
theorem coefficient_301 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,5]) i))=dictionary16.getD 29 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_29]
  decide +kernel
theorem coefficient_302 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,8]) i))=dictionary16.getD 25 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_25]
  decide +kernel
theorem coefficient_303 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,9]) i))=dictionary16.getD 19 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_19]
  decide +kernel
theorem coefficient_304 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,10]) i))=dictionary16.getD 26 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_26]
  decide +kernel
theorem coefficient_305 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,11]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_306 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,2,15]) i))=dictionary16.getD 29 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_29]
  decide +kernel
theorem coefficient_307 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,3,8]) i))=dictionary16.getD 8 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_8]
  decide +kernel
theorem coefficient_308 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,3,9]) i))=dictionary16.getD 35 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_35]
  decide +kernel
theorem coefficient_309 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,3,10]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_310 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,3,11]) i))=dictionary16.getD 41 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_311 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,3,12]) i))=dictionary16.getD 41 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_312 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,4,12]) i))=dictionary16.getD 41 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_41]
  decide +kernel
theorem coefficient_313 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,4,13]) i))=dictionary16.getD 9 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_9]
  decide +kernel
theorem coefficient_314 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,4,14]) i))=dictionary16.getD 35 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_35]
  decide +kernel
theorem coefficient_315 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,4,15]) i))=dictionary16.getD 8 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_8]
  decide +kernel
theorem coefficient_316 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,5,12]) i))=dictionary16.getD 13 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_13]
  decide +kernel
theorem coefficient_317 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,5,13]) i))=dictionary16.getD 26 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_26]
  decide +kernel
theorem coefficient_318 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,5,14]) i))=dictionary16.getD 19 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_19]
  decide +kernel
theorem coefficient_319 : forward (cachedKernel 2 2 kernelData16) (Torus.xNext 2 2) (Torus.yNext 2 2) (fun i => (QuarticRowMajor.index 2 2).symm ((![(0:Fin 16),7,5,15]) i))=dictionary16.getD 25 0 := by
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel16_eq_tree,dictionary_25]
  decide +kernel
end BilayerDressed.QuarticIntegerRepresentatives16

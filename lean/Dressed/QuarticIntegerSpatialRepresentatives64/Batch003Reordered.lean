import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_192 : Rep := ⟨![0,1,10,44],462⟩
def representative_193 : Rep := ⟨![0,1,10,45],462⟩
def representative_194 : Rep := ⟨![0,1,10,46],462⟩
def representative_195 : Rep := ⟨![0,1,10,47],284⟩
def representative_196 : Rep := ⟨![0,1,10,48],59⟩
def representative_197 : Rep := ⟨![0,1,10,49],62⟩
def representative_198 : Rep := ⟨![0,1,10,50],395⟩
def representative_199 : Rep := ⟨![0,1,10,51],139⟩
def representative_200 : Rep := ⟨![0,1,10,52],462⟩
def representative_201 : Rep := ⟨![0,1,10,53],462⟩
def representative_202 : Rep := ⟨![0,1,10,54],293⟩
def representative_203 : Rep := ⟨![0,1,10,55],398⟩
def representative_204 : Rep := ⟨![0,1,10,58],38⟩
def representative_205 : Rep := ⟨![0,1,10,59],396⟩
def representative_206 : Rep := ⟨![0,1,10,60],163⟩
def representative_207 : Rep := ⟨![0,1,10,61],284⟩
def representative_208 : Rep := ⟨![0,1,10,62],399⟩
def representative_209 : Rep := ⟨![0,1,10,63],39⟩
def representative_210 : Rep := ⟨![0,1,11,12],303⟩
def representative_211 : Rep := ⟨![0,1,11,13],235⟩
def representative_212 : Rep := ⟨![0,1,11,14],116⟩
def representative_213 : Rep := ⟨![0,1,11,16],369⟩
def representative_214 : Rep := ⟨![0,1,11,17],362⟩
def representative_215 : Rep := ⟨![0,1,11,18],129⟩
def representative_216 : Rep := ⟨![0,1,11,19],307⟩
def representative_217 : Rep := ⟨![0,1,11,20],232⟩
def representative_218 : Rep := ⟨![0,1,11,21],246⟩
def representative_219 : Rep := ⟨![0,1,11,22],462⟩
def representative_220 : Rep := ⟨![0,1,11,23],117⟩
def representative_221 : Rep := ⟨![0,1,11,24],171⟩
def representative_222 : Rep := ⟨![0,1,11,25],180⟩
def representative_223 : Rep := ⟨![0,1,11,26],286⟩
def representative_224 : Rep := ⟨![0,1,11,27],235⟩
def representative_225 : Rep := ⟨![0,1,11,28],246⟩
def representative_226 : Rep := ⟨![0,1,11,29],462⟩
def representative_227 : Rep := ⟨![0,1,11,30],462⟩
def representative_228 : Rep := ⟨![0,1,11,31],462⟩
def representative_229 : Rep := ⟨![0,1,11,32],462⟩
def representative_230 : Rep := ⟨![0,1,11,33],269⟩
def representative_231 : Rep := ⟨![0,1,11,34],462⟩
def representative_232 : Rep := ⟨![0,1,11,35],243⟩
def representative_233 : Rep := ⟨![0,1,11,36],462⟩
def representative_234 : Rep := ⟨![0,1,11,37],462⟩
def representative_235 : Rep := ⟨![0,1,11,38],462⟩
def representative_236 : Rep := ⟨![0,1,11,39],462⟩
def representative_237 : Rep := ⟨![0,1,11,40],171⟩
def representative_238 : Rep := ⟨![0,1,11,41],180⟩
def representative_239 : Rep := ⟨![0,1,11,42],284⟩
def representative_240 : Rep := ⟨![0,1,11,43],462⟩
def representative_241 : Rep := ⟨![0,1,11,44],462⟩
def representative_242 : Rep := ⟨![0,1,11,45],462⟩
def representative_243 : Rep := ⟨![0,1,11,46],462⟩
def representative_244 : Rep := ⟨![0,1,11,47],462⟩
def representative_245 : Rep := ⟨![0,1,11,48],369⟩
def representative_246 : Rep := ⟨![0,1,11,49],360⟩
def representative_247 : Rep := ⟨![0,1,11,50],131⟩
def representative_248 : Rep := ⟨![0,1,11,51],294⟩
def representative_249 : Rep := ⟨![0,1,11,52],462⟩
def representative_250 : Rep := ⟨![0,1,11,53],462⟩
def representative_251 : Rep := ⟨![0,1,11,54],462⟩
def representative_252 : Rep := ⟨![0,1,11,55],117⟩
def representative_253 : Rep := ⟨![0,1,11,59],130⟩
def representative_254 : Rep := ⟨![0,1,11,60],286⟩
def representative_255 : Rep := ⟨![0,1,11,61],462⟩
theorem coefficient_192 : validRep representative_192 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_192)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_193 : validRep representative_193 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_193)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_194 : validRep representative_194 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_194)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_195 : validRep representative_195 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_195)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_196 : validRep representative_196 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_196)=dictionary64.getD 59 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_59]
  decide +kernel
theorem coefficient_197 : validRep representative_197 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_197)=dictionary64.getD 62 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_62]
  decide +kernel
theorem coefficient_198 : validRep representative_198 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_198)=dictionary64.getD 395 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_395]
  decide +kernel
theorem coefficient_199 : validRep representative_199 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_199)=dictionary64.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_139]
  decide +kernel
theorem coefficient_200 : validRep representative_200 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_200)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_201 : validRep representative_201 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_201)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_202 : validRep representative_202 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_202)=dictionary64.getD 293 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_293]
  decide +kernel
theorem coefficient_203 : validRep representative_203 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_203)=dictionary64.getD 398 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_398]
  decide +kernel
theorem coefficient_204 : validRep representative_204 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_204)=dictionary64.getD 38 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_38]
  decide +kernel
theorem coefficient_205 : validRep representative_205 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_205)=dictionary64.getD 396 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_396]
  decide +kernel
theorem coefficient_206 : validRep representative_206 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_206)=dictionary64.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_207 : validRep representative_207 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_207)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_208 : validRep representative_208 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_208)=dictionary64.getD 399 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_399]
  decide +kernel
theorem coefficient_209 : validRep representative_209 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_209)=dictionary64.getD 39 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_39]
  decide +kernel
theorem coefficient_210 : validRep representative_210 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_210)=dictionary64.getD 303 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_303]
  decide +kernel
theorem coefficient_211 : validRep representative_211 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_211)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_212 : validRep representative_212 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_212)=dictionary64.getD 116 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_116]
  decide +kernel
theorem coefficient_213 : validRep representative_213 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_213)=dictionary64.getD 369 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_369]
  decide +kernel
theorem coefficient_214 : validRep representative_214 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_214)=dictionary64.getD 362 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_362]
  decide +kernel
theorem coefficient_215 : validRep representative_215 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_215)=dictionary64.getD 129 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_129]
  decide +kernel
theorem coefficient_216 : validRep representative_216 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_216)=dictionary64.getD 307 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_307]
  decide +kernel
theorem coefficient_217 : validRep representative_217 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_217)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_218 : validRep representative_218 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_218)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_219 : validRep representative_219 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_219)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_220 : validRep representative_220 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_220)=dictionary64.getD 117 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_117]
  decide +kernel
theorem coefficient_221 : validRep representative_221 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_221)=dictionary64.getD 171 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_171]
  decide +kernel
theorem coefficient_222 : validRep representative_222 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_222)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_223 : validRep representative_223 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_223)=dictionary64.getD 286 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_286]
  decide +kernel
theorem coefficient_224 : validRep representative_224 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_224)=dictionary64.getD 235 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_235]
  decide +kernel
theorem coefficient_225 : validRep representative_225 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_225)=dictionary64.getD 246 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_246]
  decide +kernel
theorem coefficient_226 : validRep representative_226 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_226)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_227 : validRep representative_227 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_227)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_228 : validRep representative_228 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_228)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_229 : validRep representative_229 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_229)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_230 : validRep representative_230 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_230)=dictionary64.getD 269 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_269]
  decide +kernel
theorem coefficient_231 : validRep representative_231 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_231)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_232 : validRep representative_232 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_232)=dictionary64.getD 243 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_243]
  decide +kernel
theorem coefficient_233 : validRep representative_233 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_233)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_234 : validRep representative_234 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_234)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_235 : validRep representative_235 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_235)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_236 : validRep representative_236 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_236)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_237 : validRep representative_237 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_237)=dictionary64.getD 171 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_171]
  decide +kernel
theorem coefficient_238 : validRep representative_238 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_238)=dictionary64.getD 180 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_180]
  decide +kernel
theorem coefficient_239 : validRep representative_239 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_239)=dictionary64.getD 284 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_284]
  decide +kernel
theorem coefficient_240 : validRep representative_240 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_240)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_241 : validRep representative_241 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_241)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_242 : validRep representative_242 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_242)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_243 : validRep representative_243 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_243)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_244 : validRep representative_244 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_244)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_245 : validRep representative_245 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_245)=dictionary64.getD 369 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_369]
  decide +kernel
theorem coefficient_246 : validRep representative_246 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_246)=dictionary64.getD 360 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_360]
  decide +kernel
theorem coefficient_247 : validRep representative_247 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_247)=dictionary64.getD 131 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_131]
  decide +kernel
theorem coefficient_248 : validRep representative_248 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_248)=dictionary64.getD 294 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_294]
  decide +kernel
theorem coefficient_249 : validRep representative_249 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_249)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_250 : validRep representative_250 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_250)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_251 : validRep representative_251 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_251)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_252 : validRep representative_252 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_252)=dictionary64.getD 117 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_117]
  decide +kernel
theorem coefficient_253 : validRep representative_253 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_253)=dictionary64.getD 130 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_130]
  decide +kernel
theorem coefficient_254 : validRep representative_254 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_254)=dictionary64.getD 286 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_286]
  decide +kernel
theorem coefficient_255 : validRep representative_255 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_255)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_003 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 224 (QuarticIntegerRepresentativeTree.Tree.branch 208 (QuarticIntegerRepresentativeTree.Tree.branch 200 (QuarticIntegerRepresentativeTree.Tree.branch 196 (QuarticIntegerRepresentativeTree.Tree.branch 194 (QuarticIntegerRepresentativeTree.Tree.branch 193 (QuarticIntegerRepresentativeTree.Tree.leaf 192 representative_192) (QuarticIntegerRepresentativeTree.Tree.leaf 193 representative_193)) (QuarticIntegerRepresentativeTree.Tree.branch 195 (QuarticIntegerRepresentativeTree.Tree.leaf 194 representative_194) (QuarticIntegerRepresentativeTree.Tree.leaf 195 representative_195))) (QuarticIntegerRepresentativeTree.Tree.branch 198 (QuarticIntegerRepresentativeTree.Tree.branch 197 (QuarticIntegerRepresentativeTree.Tree.leaf 196 representative_196) (QuarticIntegerRepresentativeTree.Tree.leaf 197 representative_197)) (QuarticIntegerRepresentativeTree.Tree.branch 199 (QuarticIntegerRepresentativeTree.Tree.leaf 198 representative_198) (QuarticIntegerRepresentativeTree.Tree.leaf 199 representative_199)))) (QuarticIntegerRepresentativeTree.Tree.branch 204 (QuarticIntegerRepresentativeTree.Tree.branch 202 (QuarticIntegerRepresentativeTree.Tree.branch 201 (QuarticIntegerRepresentativeTree.Tree.leaf 200 representative_200) (QuarticIntegerRepresentativeTree.Tree.leaf 201 representative_201)) (QuarticIntegerRepresentativeTree.Tree.branch 203 (QuarticIntegerRepresentativeTree.Tree.leaf 202 representative_202) (QuarticIntegerRepresentativeTree.Tree.leaf 203 representative_203))) (QuarticIntegerRepresentativeTree.Tree.branch 206 (QuarticIntegerRepresentativeTree.Tree.branch 205 (QuarticIntegerRepresentativeTree.Tree.leaf 204 representative_204) (QuarticIntegerRepresentativeTree.Tree.leaf 205 representative_205)) (QuarticIntegerRepresentativeTree.Tree.branch 207 (QuarticIntegerRepresentativeTree.Tree.leaf 206 representative_206) (QuarticIntegerRepresentativeTree.Tree.leaf 207 representative_207))))) (QuarticIntegerRepresentativeTree.Tree.branch 216 (QuarticIntegerRepresentativeTree.Tree.branch 212 (QuarticIntegerRepresentativeTree.Tree.branch 210 (QuarticIntegerRepresentativeTree.Tree.branch 209 (QuarticIntegerRepresentativeTree.Tree.leaf 208 representative_208) (QuarticIntegerRepresentativeTree.Tree.leaf 209 representative_209)) (QuarticIntegerRepresentativeTree.Tree.branch 211 (QuarticIntegerRepresentativeTree.Tree.leaf 210 representative_210) (QuarticIntegerRepresentativeTree.Tree.leaf 211 representative_211))) (QuarticIntegerRepresentativeTree.Tree.branch 214 (QuarticIntegerRepresentativeTree.Tree.branch 213 (QuarticIntegerRepresentativeTree.Tree.leaf 212 representative_212) (QuarticIntegerRepresentativeTree.Tree.leaf 213 representative_213)) (QuarticIntegerRepresentativeTree.Tree.branch 215 (QuarticIntegerRepresentativeTree.Tree.leaf 214 representative_214) (QuarticIntegerRepresentativeTree.Tree.leaf 215 representative_215)))) (QuarticIntegerRepresentativeTree.Tree.branch 220 (QuarticIntegerRepresentativeTree.Tree.branch 218 (QuarticIntegerRepresentativeTree.Tree.branch 217 (QuarticIntegerRepresentativeTree.Tree.leaf 216 representative_216) (QuarticIntegerRepresentativeTree.Tree.leaf 217 representative_217)) (QuarticIntegerRepresentativeTree.Tree.branch 219 (QuarticIntegerRepresentativeTree.Tree.leaf 218 representative_218) (QuarticIntegerRepresentativeTree.Tree.leaf 219 representative_219))) (QuarticIntegerRepresentativeTree.Tree.branch 222 (QuarticIntegerRepresentativeTree.Tree.branch 221 (QuarticIntegerRepresentativeTree.Tree.leaf 220 representative_220) (QuarticIntegerRepresentativeTree.Tree.leaf 221 representative_221)) (QuarticIntegerRepresentativeTree.Tree.branch 223 (QuarticIntegerRepresentativeTree.Tree.leaf 222 representative_222) (QuarticIntegerRepresentativeTree.Tree.leaf 223 representative_223)))))) (QuarticIntegerRepresentativeTree.Tree.branch 240 (QuarticIntegerRepresentativeTree.Tree.branch 232 (QuarticIntegerRepresentativeTree.Tree.branch 228 (QuarticIntegerRepresentativeTree.Tree.branch 226 (QuarticIntegerRepresentativeTree.Tree.branch 225 (QuarticIntegerRepresentativeTree.Tree.leaf 224 representative_224) (QuarticIntegerRepresentativeTree.Tree.leaf 225 representative_225)) (QuarticIntegerRepresentativeTree.Tree.branch 227 (QuarticIntegerRepresentativeTree.Tree.leaf 226 representative_226) (QuarticIntegerRepresentativeTree.Tree.leaf 227 representative_227))) (QuarticIntegerRepresentativeTree.Tree.branch 230 (QuarticIntegerRepresentativeTree.Tree.branch 229 (QuarticIntegerRepresentativeTree.Tree.leaf 228 representative_228) (QuarticIntegerRepresentativeTree.Tree.leaf 229 representative_229)) (QuarticIntegerRepresentativeTree.Tree.branch 231 (QuarticIntegerRepresentativeTree.Tree.leaf 230 representative_230) (QuarticIntegerRepresentativeTree.Tree.leaf 231 representative_231)))) (QuarticIntegerRepresentativeTree.Tree.branch 236 (QuarticIntegerRepresentativeTree.Tree.branch 234 (QuarticIntegerRepresentativeTree.Tree.branch 233 (QuarticIntegerRepresentativeTree.Tree.leaf 232 representative_232) (QuarticIntegerRepresentativeTree.Tree.leaf 233 representative_233)) (QuarticIntegerRepresentativeTree.Tree.branch 235 (QuarticIntegerRepresentativeTree.Tree.leaf 234 representative_234) (QuarticIntegerRepresentativeTree.Tree.leaf 235 representative_235))) (QuarticIntegerRepresentativeTree.Tree.branch 238 (QuarticIntegerRepresentativeTree.Tree.branch 237 (QuarticIntegerRepresentativeTree.Tree.leaf 236 representative_236) (QuarticIntegerRepresentativeTree.Tree.leaf 237 representative_237)) (QuarticIntegerRepresentativeTree.Tree.branch 239 (QuarticIntegerRepresentativeTree.Tree.leaf 238 representative_238) (QuarticIntegerRepresentativeTree.Tree.leaf 239 representative_239))))) (QuarticIntegerRepresentativeTree.Tree.branch 248 (QuarticIntegerRepresentativeTree.Tree.branch 244 (QuarticIntegerRepresentativeTree.Tree.branch 242 (QuarticIntegerRepresentativeTree.Tree.branch 241 (QuarticIntegerRepresentativeTree.Tree.leaf 240 representative_240) (QuarticIntegerRepresentativeTree.Tree.leaf 241 representative_241)) (QuarticIntegerRepresentativeTree.Tree.branch 243 (QuarticIntegerRepresentativeTree.Tree.leaf 242 representative_242) (QuarticIntegerRepresentativeTree.Tree.leaf 243 representative_243))) (QuarticIntegerRepresentativeTree.Tree.branch 246 (QuarticIntegerRepresentativeTree.Tree.branch 245 (QuarticIntegerRepresentativeTree.Tree.leaf 244 representative_244) (QuarticIntegerRepresentativeTree.Tree.leaf 245 representative_245)) (QuarticIntegerRepresentativeTree.Tree.branch 247 (QuarticIntegerRepresentativeTree.Tree.leaf 246 representative_246) (QuarticIntegerRepresentativeTree.Tree.leaf 247 representative_247)))) (QuarticIntegerRepresentativeTree.Tree.branch 252 (QuarticIntegerRepresentativeTree.Tree.branch 250 (QuarticIntegerRepresentativeTree.Tree.branch 249 (QuarticIntegerRepresentativeTree.Tree.leaf 248 representative_248) (QuarticIntegerRepresentativeTree.Tree.leaf 249 representative_249)) (QuarticIntegerRepresentativeTree.Tree.branch 251 (QuarticIntegerRepresentativeTree.Tree.leaf 250 representative_250) (QuarticIntegerRepresentativeTree.Tree.leaf 251 representative_251))) (QuarticIntegerRepresentativeTree.Tree.branch 254 (QuarticIntegerRepresentativeTree.Tree.branch 253 (QuarticIntegerRepresentativeTree.Tree.leaf 252 representative_252) (QuarticIntegerRepresentativeTree.Tree.leaf 253 representative_253)) (QuarticIntegerRepresentativeTree.Tree.branch 255 (QuarticIntegerRepresentativeTree.Tree.leaf 254 representative_254) (QuarticIntegerRepresentativeTree.Tree.leaf 255 representative_255)))))))
theorem accepted_003 : All validRep tree_003 := ⟨⟨⟨⟨⟨⟨coefficient_192,coefficient_193⟩,⟨coefficient_194,coefficient_195⟩⟩,⟨⟨coefficient_196,coefficient_197⟩,⟨coefficient_198,coefficient_199⟩⟩⟩,⟨⟨⟨coefficient_200,coefficient_201⟩,⟨coefficient_202,coefficient_203⟩⟩,⟨⟨coefficient_204,coefficient_205⟩,⟨coefficient_206,coefficient_207⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_208,coefficient_209⟩,⟨coefficient_210,coefficient_211⟩⟩,⟨⟨coefficient_212,coefficient_213⟩,⟨coefficient_214,coefficient_215⟩⟩⟩,⟨⟨⟨coefficient_216,coefficient_217⟩,⟨coefficient_218,coefficient_219⟩⟩,⟨⟨coefficient_220,coefficient_221⟩,⟨coefficient_222,coefficient_223⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_224,coefficient_225⟩,⟨coefficient_226,coefficient_227⟩⟩,⟨⟨coefficient_228,coefficient_229⟩,⟨coefficient_230,coefficient_231⟩⟩⟩,⟨⟨⟨coefficient_232,coefficient_233⟩,⟨coefficient_234,coefficient_235⟩⟩,⟨⟨coefficient_236,coefficient_237⟩,⟨coefficient_238,coefficient_239⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_240,coefficient_241⟩,⟨coefficient_242,coefficient_243⟩⟩,⟨⟨coefficient_244,coefficient_245⟩,⟨coefficient_246,coefficient_247⟩⟩⟩,⟨⟨⟨coefficient_248,coefficient_249⟩,⟨coefficient_250,coefficient_251⟩⟩,⟨⟨coefficient_252,coefficient_253⟩,⟨coefficient_254,coefficient_255⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64

import Dressed.QuarticIntegerSpatialRepresentatives32.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_192 : Rep := ⟨![0,2,9,19],508⟩
def representative_193 : Rep := ⟨![0,2,9,20],297⟩
def representative_194 : Rep := ⟨![0,2,9,21],259⟩
def representative_195 : Rep := ⟨![0,2,9,23],262⟩
def representative_196 : Rep := ⟨![0,2,9,25],335⟩
def representative_197 : Rep := ⟨![0,2,9,27],335⟩
def representative_198 : Rep := ⟨![0,2,12,14],508⟩
def representative_199 : Rep := ⟨![0,2,12,16],273⟩
def representative_200 : Rep := ⟨![0,2,12,17],508⟩
def representative_201 : Rep := ⟨![0,2,12,18],508⟩
def representative_202 : Rep := ⟨![0,2,12,20],283⟩
def representative_203 : Rep := ⟨![0,2,12,21],272⟩
def representative_204 : Rep := ⟨![0,2,12,22],508⟩
def representative_205 : Rep := ⟨![0,2,13,15],508⟩
def representative_206 : Rep := ⟨![0,2,13,16],508⟩
def representative_207 : Rep := ⟨![0,2,13,17],508⟩
def representative_208 : Rep := ⟨![0,2,13,19],508⟩
def representative_209 : Rep := ⟨![0,2,13,21],508⟩
def representative_210 : Rep := ⟨![0,2,13,23],508⟩
def representative_211 : Rep := ⟨![0,2,16,18],508⟩
def representative_212 : Rep := ⟨![0,2,17,19],508⟩
def representative_213 : Rep := ⟨![0,4,1,5],25⟩
def representative_214 : Rep := ⟨![0,4,1,6],484⟩
def representative_215 : Rep := ⟨![0,4,1,7],30⟩
def representative_216 : Rep := ⟨![0,4,1,8],29⟩
def representative_217 : Rep := ⟨![0,4,1,9],488⟩
def representative_218 : Rep := ⟨![0,4,1,10],50⟩
def representative_219 : Rep := ⟨![0,4,1,11],489⟩
def representative_220 : Rep := ⟨![0,4,1,12],477⟩
def representative_221 : Rep := ⟨![0,4,1,13],69⟩
def representative_222 : Rep := ⟨![0,4,1,14],163⟩
def representative_223 : Rep := ⟨![0,4,1,15],68⟩
def representative_224 : Rep := ⟨![0,4,1,16],99⟩
def representative_225 : Rep := ⟨![0,4,1,17],211⟩
def representative_226 : Rep := ⟨![0,4,1,18],508⟩
def representative_227 : Rep := ⟨![0,4,1,19],211⟩
def representative_228 : Rep := ⟨![0,4,1,20],96⟩
def representative_229 : Rep := ⟨![0,4,1,21],368⟩
def representative_230 : Rep := ⟨![0,4,1,22],508⟩
def representative_231 : Rep := ⟨![0,4,1,23],367⟩
def representative_232 : Rep := ⟨![0,4,1,24],481⟩
def representative_233 : Rep := ⟨![0,4,1,25],57⟩
def representative_234 : Rep := ⟨![0,4,1,26],411⟩
def representative_235 : Rep := ⟨![0,4,1,27],59⟩
def representative_236 : Rep := ⟨![0,4,1,28],24⟩
def representative_237 : Rep := ⟨![0,4,1,29],498⟩
def representative_238 : Rep := ⟨![0,4,1,30],44⟩
def representative_239 : Rep := ⟨![0,4,1,31],495⟩
def representative_240 : Rep := ⟨![0,4,2,6],47⟩
def representative_241 : Rep := ⟨![0,4,2,8],486⟩
def representative_242 : Rep := ⟨![0,4,2,9],63⟩
def representative_243 : Rep := ⟨![0,4,2,10],427⟩
def representative_244 : Rep := ⟨![0,4,2,12],88⟩
def representative_245 : Rep := ⟨![0,4,2,13],403⟩
def representative_246 : Rep := ⟨![0,4,2,14],340⟩
def representative_247 : Rep := ⟨![0,4,2,16],365⟩
def representative_248 : Rep := ⟨![0,4,2,17],316⟩
def representative_249 : Rep := ⟨![0,4,2,18],508⟩
def representative_250 : Rep := ⟨![0,4,2,20],359⟩
def representative_251 : Rep := ⟨![0,4,2,21],211⟩
def representative_252 : Rep := ⟨![0,4,2,22],312⟩
def representative_253 : Rep := ⟨![0,4,2,24],87⟩
def representative_254 : Rep := ⟨![0,4,2,25],396⟩
def representative_255 : Rep := ⟨![0,4,2,26],139⟩
theorem coefficient_192 : validRep representative_192 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_192)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_193 : validRep representative_193 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_193)=dictionary32.getD 297 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_297]
  decide +kernel
theorem coefficient_194 : validRep representative_194 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_194)=dictionary32.getD 259 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_259]
  decide +kernel
theorem coefficient_195 : validRep representative_195 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_195)=dictionary32.getD 262 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_262]
  decide +kernel
theorem coefficient_196 : validRep representative_196 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_196)=dictionary32.getD 335 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_335]
  decide +kernel
theorem coefficient_197 : validRep representative_197 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_197)=dictionary32.getD 335 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_335]
  decide +kernel
theorem coefficient_198 : validRep representative_198 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_198)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_199 : validRep representative_199 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_199)=dictionary32.getD 273 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_273]
  decide +kernel
theorem coefficient_200 : validRep representative_200 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_200)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_201 : validRep representative_201 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_201)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_202 : validRep representative_202 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_202)=dictionary32.getD 283 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_283]
  decide +kernel
theorem coefficient_203 : validRep representative_203 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_203)=dictionary32.getD 272 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_272]
  decide +kernel
theorem coefficient_204 : validRep representative_204 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_204)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_205 : validRep representative_205 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_205)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_206 : validRep representative_206 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_206)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_207 : validRep representative_207 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_207)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_208 : validRep representative_208 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_208)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_209 : validRep representative_209 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_209)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_210 : validRep representative_210 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_210)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_211 : validRep representative_211 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_211)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_212 : validRep representative_212 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_212)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_213 : validRep representative_213 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_213)=dictionary32.getD 25 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_25]
  decide +kernel
theorem coefficient_214 : validRep representative_214 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_214)=dictionary32.getD 484 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_484]
  decide +kernel
theorem coefficient_215 : validRep representative_215 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_215)=dictionary32.getD 30 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_30]
  decide +kernel
theorem coefficient_216 : validRep representative_216 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_216)=dictionary32.getD 29 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_29]
  decide +kernel
theorem coefficient_217 : validRep representative_217 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_217)=dictionary32.getD 488 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_488]
  decide +kernel
theorem coefficient_218 : validRep representative_218 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_218)=dictionary32.getD 50 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_50]
  decide +kernel
theorem coefficient_219 : validRep representative_219 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_219)=dictionary32.getD 489 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_489]
  decide +kernel
theorem coefficient_220 : validRep representative_220 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_220)=dictionary32.getD 477 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_477]
  decide +kernel
theorem coefficient_221 : validRep representative_221 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_221)=dictionary32.getD 69 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_69]
  decide +kernel
theorem coefficient_222 : validRep representative_222 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_222)=dictionary32.getD 163 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_163]
  decide +kernel
theorem coefficient_223 : validRep representative_223 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_223)=dictionary32.getD 68 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_68]
  decide +kernel
theorem coefficient_224 : validRep representative_224 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_224)=dictionary32.getD 99 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_99]
  decide +kernel
theorem coefficient_225 : validRep representative_225 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_225)=dictionary32.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_226 : validRep representative_226 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_226)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_227 : validRep representative_227 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_227)=dictionary32.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_228 : validRep representative_228 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_228)=dictionary32.getD 96 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_96]
  decide +kernel
theorem coefficient_229 : validRep representative_229 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_229)=dictionary32.getD 368 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_368]
  decide +kernel
theorem coefficient_230 : validRep representative_230 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_230)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_231 : validRep representative_231 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_231)=dictionary32.getD 367 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_367]
  decide +kernel
theorem coefficient_232 : validRep representative_232 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_232)=dictionary32.getD 481 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_481]
  decide +kernel
theorem coefficient_233 : validRep representative_233 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_233)=dictionary32.getD 57 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_57]
  decide +kernel
theorem coefficient_234 : validRep representative_234 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_234)=dictionary32.getD 411 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_411]
  decide +kernel
theorem coefficient_235 : validRep representative_235 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_235)=dictionary32.getD 59 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_59]
  decide +kernel
theorem coefficient_236 : validRep representative_236 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_236)=dictionary32.getD 24 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_24]
  decide +kernel
theorem coefficient_237 : validRep representative_237 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_237)=dictionary32.getD 498 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_498]
  decide +kernel
theorem coefficient_238 : validRep representative_238 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_238)=dictionary32.getD 44 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_44]
  decide +kernel
theorem coefficient_239 : validRep representative_239 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_239)=dictionary32.getD 495 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_495]
  decide +kernel
theorem coefficient_240 : validRep representative_240 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_240)=dictionary32.getD 47 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_47]
  decide +kernel
theorem coefficient_241 : validRep representative_241 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_241)=dictionary32.getD 486 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_486]
  decide +kernel
theorem coefficient_242 : validRep representative_242 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_242)=dictionary32.getD 63 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_63]
  decide +kernel
theorem coefficient_243 : validRep representative_243 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_243)=dictionary32.getD 427 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_427]
  decide +kernel
theorem coefficient_244 : validRep representative_244 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_244)=dictionary32.getD 88 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_88]
  decide +kernel
theorem coefficient_245 : validRep representative_245 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_245)=dictionary32.getD 403 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_403]
  decide +kernel
theorem coefficient_246 : validRep representative_246 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_246)=dictionary32.getD 340 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_340]
  decide +kernel
theorem coefficient_247 : validRep representative_247 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_247)=dictionary32.getD 365 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_365]
  decide +kernel
theorem coefficient_248 : validRep representative_248 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_248)=dictionary32.getD 316 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_316]
  decide +kernel
theorem coefficient_249 : validRep representative_249 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_249)=dictionary32.getD 508 0
  rw [cachedKernel32_eq_tree,dictionary_508]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_250 : validRep representative_250 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_250)=dictionary32.getD 359 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_359]
  decide +kernel
theorem coefficient_251 : validRep representative_251 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_251)=dictionary32.getD 211 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_211]
  decide +kernel
theorem coefficient_252 : validRep representative_252 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_252)=dictionary32.getD 312 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_312]
  decide +kernel
theorem coefficient_253 : validRep representative_253 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_253)=dictionary32.getD 87 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_87]
  decide +kernel
theorem coefficient_254 : validRep representative_254 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_254)=dictionary32.getD 396 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_396]
  decide +kernel
theorem coefficient_255 : validRep representative_255 := by
  change forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2) (repTuple 4 2 representative_255)=dictionary32.getD 139 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel32_eq_tree,dictionary_139]
  decide +kernel
def tree_003 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 224 (QuarticIntegerRepresentativeTree.Tree.branch 208 (QuarticIntegerRepresentativeTree.Tree.branch 200 (QuarticIntegerRepresentativeTree.Tree.branch 196 (QuarticIntegerRepresentativeTree.Tree.branch 194 (QuarticIntegerRepresentativeTree.Tree.branch 193 (QuarticIntegerRepresentativeTree.Tree.leaf 192 representative_192) (QuarticIntegerRepresentativeTree.Tree.leaf 193 representative_193)) (QuarticIntegerRepresentativeTree.Tree.branch 195 (QuarticIntegerRepresentativeTree.Tree.leaf 194 representative_194) (QuarticIntegerRepresentativeTree.Tree.leaf 195 representative_195))) (QuarticIntegerRepresentativeTree.Tree.branch 198 (QuarticIntegerRepresentativeTree.Tree.branch 197 (QuarticIntegerRepresentativeTree.Tree.leaf 196 representative_196) (QuarticIntegerRepresentativeTree.Tree.leaf 197 representative_197)) (QuarticIntegerRepresentativeTree.Tree.branch 199 (QuarticIntegerRepresentativeTree.Tree.leaf 198 representative_198) (QuarticIntegerRepresentativeTree.Tree.leaf 199 representative_199)))) (QuarticIntegerRepresentativeTree.Tree.branch 204 (QuarticIntegerRepresentativeTree.Tree.branch 202 (QuarticIntegerRepresentativeTree.Tree.branch 201 (QuarticIntegerRepresentativeTree.Tree.leaf 200 representative_200) (QuarticIntegerRepresentativeTree.Tree.leaf 201 representative_201)) (QuarticIntegerRepresentativeTree.Tree.branch 203 (QuarticIntegerRepresentativeTree.Tree.leaf 202 representative_202) (QuarticIntegerRepresentativeTree.Tree.leaf 203 representative_203))) (QuarticIntegerRepresentativeTree.Tree.branch 206 (QuarticIntegerRepresentativeTree.Tree.branch 205 (QuarticIntegerRepresentativeTree.Tree.leaf 204 representative_204) (QuarticIntegerRepresentativeTree.Tree.leaf 205 representative_205)) (QuarticIntegerRepresentativeTree.Tree.branch 207 (QuarticIntegerRepresentativeTree.Tree.leaf 206 representative_206) (QuarticIntegerRepresentativeTree.Tree.leaf 207 representative_207))))) (QuarticIntegerRepresentativeTree.Tree.branch 216 (QuarticIntegerRepresentativeTree.Tree.branch 212 (QuarticIntegerRepresentativeTree.Tree.branch 210 (QuarticIntegerRepresentativeTree.Tree.branch 209 (QuarticIntegerRepresentativeTree.Tree.leaf 208 representative_208) (QuarticIntegerRepresentativeTree.Tree.leaf 209 representative_209)) (QuarticIntegerRepresentativeTree.Tree.branch 211 (QuarticIntegerRepresentativeTree.Tree.leaf 210 representative_210) (QuarticIntegerRepresentativeTree.Tree.leaf 211 representative_211))) (QuarticIntegerRepresentativeTree.Tree.branch 214 (QuarticIntegerRepresentativeTree.Tree.branch 213 (QuarticIntegerRepresentativeTree.Tree.leaf 212 representative_212) (QuarticIntegerRepresentativeTree.Tree.leaf 213 representative_213)) (QuarticIntegerRepresentativeTree.Tree.branch 215 (QuarticIntegerRepresentativeTree.Tree.leaf 214 representative_214) (QuarticIntegerRepresentativeTree.Tree.leaf 215 representative_215)))) (QuarticIntegerRepresentativeTree.Tree.branch 220 (QuarticIntegerRepresentativeTree.Tree.branch 218 (QuarticIntegerRepresentativeTree.Tree.branch 217 (QuarticIntegerRepresentativeTree.Tree.leaf 216 representative_216) (QuarticIntegerRepresentativeTree.Tree.leaf 217 representative_217)) (QuarticIntegerRepresentativeTree.Tree.branch 219 (QuarticIntegerRepresentativeTree.Tree.leaf 218 representative_218) (QuarticIntegerRepresentativeTree.Tree.leaf 219 representative_219))) (QuarticIntegerRepresentativeTree.Tree.branch 222 (QuarticIntegerRepresentativeTree.Tree.branch 221 (QuarticIntegerRepresentativeTree.Tree.leaf 220 representative_220) (QuarticIntegerRepresentativeTree.Tree.leaf 221 representative_221)) (QuarticIntegerRepresentativeTree.Tree.branch 223 (QuarticIntegerRepresentativeTree.Tree.leaf 222 representative_222) (QuarticIntegerRepresentativeTree.Tree.leaf 223 representative_223)))))) (QuarticIntegerRepresentativeTree.Tree.branch 240 (QuarticIntegerRepresentativeTree.Tree.branch 232 (QuarticIntegerRepresentativeTree.Tree.branch 228 (QuarticIntegerRepresentativeTree.Tree.branch 226 (QuarticIntegerRepresentativeTree.Tree.branch 225 (QuarticIntegerRepresentativeTree.Tree.leaf 224 representative_224) (QuarticIntegerRepresentativeTree.Tree.leaf 225 representative_225)) (QuarticIntegerRepresentativeTree.Tree.branch 227 (QuarticIntegerRepresentativeTree.Tree.leaf 226 representative_226) (QuarticIntegerRepresentativeTree.Tree.leaf 227 representative_227))) (QuarticIntegerRepresentativeTree.Tree.branch 230 (QuarticIntegerRepresentativeTree.Tree.branch 229 (QuarticIntegerRepresentativeTree.Tree.leaf 228 representative_228) (QuarticIntegerRepresentativeTree.Tree.leaf 229 representative_229)) (QuarticIntegerRepresentativeTree.Tree.branch 231 (QuarticIntegerRepresentativeTree.Tree.leaf 230 representative_230) (QuarticIntegerRepresentativeTree.Tree.leaf 231 representative_231)))) (QuarticIntegerRepresentativeTree.Tree.branch 236 (QuarticIntegerRepresentativeTree.Tree.branch 234 (QuarticIntegerRepresentativeTree.Tree.branch 233 (QuarticIntegerRepresentativeTree.Tree.leaf 232 representative_232) (QuarticIntegerRepresentativeTree.Tree.leaf 233 representative_233)) (QuarticIntegerRepresentativeTree.Tree.branch 235 (QuarticIntegerRepresentativeTree.Tree.leaf 234 representative_234) (QuarticIntegerRepresentativeTree.Tree.leaf 235 representative_235))) (QuarticIntegerRepresentativeTree.Tree.branch 238 (QuarticIntegerRepresentativeTree.Tree.branch 237 (QuarticIntegerRepresentativeTree.Tree.leaf 236 representative_236) (QuarticIntegerRepresentativeTree.Tree.leaf 237 representative_237)) (QuarticIntegerRepresentativeTree.Tree.branch 239 (QuarticIntegerRepresentativeTree.Tree.leaf 238 representative_238) (QuarticIntegerRepresentativeTree.Tree.leaf 239 representative_239))))) (QuarticIntegerRepresentativeTree.Tree.branch 248 (QuarticIntegerRepresentativeTree.Tree.branch 244 (QuarticIntegerRepresentativeTree.Tree.branch 242 (QuarticIntegerRepresentativeTree.Tree.branch 241 (QuarticIntegerRepresentativeTree.Tree.leaf 240 representative_240) (QuarticIntegerRepresentativeTree.Tree.leaf 241 representative_241)) (QuarticIntegerRepresentativeTree.Tree.branch 243 (QuarticIntegerRepresentativeTree.Tree.leaf 242 representative_242) (QuarticIntegerRepresentativeTree.Tree.leaf 243 representative_243))) (QuarticIntegerRepresentativeTree.Tree.branch 246 (QuarticIntegerRepresentativeTree.Tree.branch 245 (QuarticIntegerRepresentativeTree.Tree.leaf 244 representative_244) (QuarticIntegerRepresentativeTree.Tree.leaf 245 representative_245)) (QuarticIntegerRepresentativeTree.Tree.branch 247 (QuarticIntegerRepresentativeTree.Tree.leaf 246 representative_246) (QuarticIntegerRepresentativeTree.Tree.leaf 247 representative_247)))) (QuarticIntegerRepresentativeTree.Tree.branch 252 (QuarticIntegerRepresentativeTree.Tree.branch 250 (QuarticIntegerRepresentativeTree.Tree.branch 249 (QuarticIntegerRepresentativeTree.Tree.leaf 248 representative_248) (QuarticIntegerRepresentativeTree.Tree.leaf 249 representative_249)) (QuarticIntegerRepresentativeTree.Tree.branch 251 (QuarticIntegerRepresentativeTree.Tree.leaf 250 representative_250) (QuarticIntegerRepresentativeTree.Tree.leaf 251 representative_251))) (QuarticIntegerRepresentativeTree.Tree.branch 254 (QuarticIntegerRepresentativeTree.Tree.branch 253 (QuarticIntegerRepresentativeTree.Tree.leaf 252 representative_252) (QuarticIntegerRepresentativeTree.Tree.leaf 253 representative_253)) (QuarticIntegerRepresentativeTree.Tree.branch 255 (QuarticIntegerRepresentativeTree.Tree.leaf 254 representative_254) (QuarticIntegerRepresentativeTree.Tree.leaf 255 representative_255)))))))
theorem accepted_003 : All validRep tree_003 := ⟨⟨⟨⟨⟨⟨coefficient_192,coefficient_193⟩,⟨coefficient_194,coefficient_195⟩⟩,⟨⟨coefficient_196,coefficient_197⟩,⟨coefficient_198,coefficient_199⟩⟩⟩,⟨⟨⟨coefficient_200,coefficient_201⟩,⟨coefficient_202,coefficient_203⟩⟩,⟨⟨coefficient_204,coefficient_205⟩,⟨coefficient_206,coefficient_207⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_208,coefficient_209⟩,⟨coefficient_210,coefficient_211⟩⟩,⟨⟨coefficient_212,coefficient_213⟩,⟨coefficient_214,coefficient_215⟩⟩⟩,⟨⟨⟨coefficient_216,coefficient_217⟩,⟨coefficient_218,coefficient_219⟩⟩,⟨⟨coefficient_220,coefficient_221⟩,⟨coefficient_222,coefficient_223⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_224,coefficient_225⟩,⟨coefficient_226,coefficient_227⟩⟩,⟨⟨coefficient_228,coefficient_229⟩,⟨coefficient_230,coefficient_231⟩⟩⟩,⟨⟨⟨coefficient_232,coefficient_233⟩,⟨coefficient_234,coefficient_235⟩⟩,⟨⟨coefficient_236,coefficient_237⟩,⟨coefficient_238,coefficient_239⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_240,coefficient_241⟩,⟨coefficient_242,coefficient_243⟩⟩,⟨⟨coefficient_244,coefficient_245⟩,⟨coefficient_246,coefficient_247⟩⟩⟩,⟨⟨⟨coefficient_248,coefficient_249⟩,⟨coefficient_250,coefficient_251⟩⟩,⟨⟨coefficient_252,coefficient_253⟩,⟨coefficient_254,coefficient_255⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives32

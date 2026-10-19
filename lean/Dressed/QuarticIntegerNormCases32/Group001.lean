import Dressed.QuarticIntegerGramCases
import Dressed.QuarticIntegerGramPermutation
import Dressed.QuarticIntegerMembership32.Dictionary
import Dressed.QuarticIntegerNormSorted32.Group000
import Dressed.QuarticIntegerNormSorted32.Group001
import Dressed.QuarticIntegerNormSorted32.Group002
import Dressed.QuarticIntegerNormSorted32.Group003
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerNormCases32
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_256 : gram (fun a=>dictionary32.getD ((row3 240 114 405) a) 0)=norm_075 := by
  rw [gram_eq_of_entries dictionary32 (row3 240 114 405) _ _ _ dictionary_240 dictionary_114 dictionary_405]
  exact (gram102 (![0,0,0,0,0,0,-15360,-21120,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-1920,7680,-1680,-1800]) (![0,0,0,0,0,0,15360,-3840,-11520,-6480,-1800])).trans sorted_075
theorem gram_257 : gram (fun a=>dictionary32.getD ((row3 241 9 282) a) 0)=norm_000 := by
  rw [gram_eq_of_entries dictionary32 (row3 241 9 282) _ _ _ dictionary_241 dictionary_9 dictionary_282]
  exact (gram102 (![0,0,0,0,0,0,0,1600,0,0,0]) (![0,0,0,0,0,0,0,-1600,2800,1400,4750]) (![0,0,0,0,0,0,0,0,1200,600,3750])).trans sorted_000
theorem gram_258 : gram (fun a=>dictionary32.getD ((row3 241 282 9) a) 0)=norm_000 := by
  rw [gram_eq_of_entries dictionary32 (row3 241 282 9) _ _ _ dictionary_241 dictionary_282 dictionary_9]
  exact (gram120 (![0,0,0,0,0,0,0,1600,0,0,0]) (![0,0,0,0,0,0,0,-1600,2800,1400,4750]) (![0,0,0,0,0,0,0,0,1200,600,3750])).trans sorted_000
theorem gram_259 : gram (fun a=>dictionary32.getD ((row3 242 125 352) a) 0)=norm_085 := by
  rw [gram_eq_of_entries dictionary32 (row3 242 125 352) _ _ _ dictionary_242 dictionary_125 dictionary_352]
  exact (gram102 (![0,0,0,0,0,0,-2560,-4800,-1920,-4880,-2200]) (![0,0,0,0,0,0,0,-1472,-128,-2824,-1364]) (![0,0,0,0,0,0,2560,-1792,-3328,-3624,-1364])).trans sorted_085
theorem gram_260 : gram (fun a=>dictionary32.getD ((row3 243 239 239) a) 0)=norm_132 := by
  rw [gram_eq_of_entries dictionary32 (row3 243 239 239) _ _ _ dictionary_243 dictionary_239 dictionary_239]
  exact (gram201 (![0,0,0,0,0,0,0,-2240,-640,-2560,-1200]) (![0,0,0,0,0,0,0,-2240,-640,-2560,-1200]) (![0,0,0,0,0,0,0,-1280,-1280,-2720,-1200])).trans sorted_132
theorem gram_261 : gram (fun a=>dictionary32.getD ((row3 244 15 129) a) 0)=norm_012 := by
  rw [gram_eq_of_entries dictionary32 (row3 244 15 129) _ _ _ dictionary_244 dictionary_15 dictionary_129]
  exact (gram201 (![0,0,0,0,0,0,0,57600,0,0,0]) (![0,0,0,0,0,0,0,-57600,43200,21600,31500]) (![0,0,0,0,0,0,0,0,-14400,-7200,13500])).trans sorted_012
theorem gram_262 : gram (fun a=>dictionary32.getD ((row3 245 14 141) a) 0)=norm_010 := by
  rw [gram_eq_of_entries dictionary32 (row3 245 14 141) _ _ _ dictionary_245 dictionary_14 dictionary_141]
  exact (gram201 (![0,0,0,0,0,0,0,28800,0,0,0]) (![0,0,0,0,0,0,0,-28800,16800,8400,5250]) (![0,0,0,0,0,0,0,0,-12000,-6000,-3750])).trans sorted_010
theorem gram_263 : gram (fun a=>dictionary32.getD ((row3 246 13 164) a) 0)=norm_007 := by
  rw [gram_eq_of_entries dictionary32 (row3 246 13 164) _ _ _ dictionary_246 dictionary_13 dictionary_164]
  exact (gram201 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,6000,3000,1875]) (![0,0,0,0,0,0,0,0,-8400,-4200,-2625])).trans sorted_007
theorem gram_264 : gram (fun a=>dictionary32.getD ((row3 247 13 165) a) 0)=norm_008 := by
  rw [gram_eq_of_entries dictionary32 (row3 247 13 165) _ _ _ dictionary_247 dictionary_13 dictionary_165]
  exact (gram201 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,6000,3000,4875]) (![0,0,0,0,0,0,0,0,-8400,-4200,375])).trans sorted_008
theorem gram_265 : gram (fun a=>dictionary32.getD ((row3 248 12 184) a) 0)=norm_006 := by
  rw [gram_eq_of_entries dictionary32 (row3 248 12 184) _ _ _ dictionary_248 dictionary_12 dictionary_184]
  exact (gram201 (![0,0,0,0,0,0,0,9600,0,0,0]) (![0,0,0,0,0,0,0,-9600,7200,3600,2250]) (![0,0,0,0,0,0,0,0,-2400,-1200,-750])).trans sorted_006
theorem gram_266 : gram (fun a=>dictionary32.getD ((row3 249 11 215) a) 0)=norm_003 := by
  rw [gram_eq_of_entries dictionary32 (row3 249 11 215) _ _ _ dictionary_249 dictionary_11 dictionary_215]
  exact (gram201 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,2800,1400,6125]) (![0,0,0,0,0,0,0,0,-2000,-1000,4625])).trans sorted_003
theorem gram_267 : gram (fun a=>dictionary32.getD ((row3 250 10 226) a) 0)=norm_001 := by
  rw [gram_eq_of_entries dictionary32 (row3 250 10 226) _ _ _ dictionary_250 dictionary_10 dictionary_226]
  exact (gram201 (![0,0,0,0,0,0,0,3200,0,0,0]) (![0,0,0,0,0,0,0,-3200,2400,1200,750]) (![0,0,0,0,0,0,0,0,-800,-400,-250])).trans sorted_001
theorem gram_268 : gram (fun a=>dictionary32.getD ((row3 251 255 252) a) 0)=norm_133 := by
  rw [gram_eq_of_entries dictionary32 (row3 251 255 252) _ _ _ dictionary_251 dictionary_255 dictionary_252]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-33600,-16800]) (![0,0,0,0,0,0,0,0,0,-31200,-15600]) (![0,0,0,0,0,0,0,0,0,-24000,-12000])).trans sorted_133
theorem gram_269 : gram (fun a=>dictionary32.getD ((row3 252 254 254) a) 0)=norm_135 := by
  rw [gram_eq_of_entries dictionary32 (row3 252 254 254) _ _ _ dictionary_252 dictionary_254 dictionary_254]
  exact sorted_135
theorem gram_270 : gram (fun a=>dictionary32.getD ((row3 252 255 251) a) 0)=norm_133 := by
  rw [gram_eq_of_entries dictionary32 (row3 252 255 251) _ _ _ dictionary_252 dictionary_255 dictionary_251]
  exact (gram120 (![0,0,0,0,0,0,0,0,0,-33600,-16800]) (![0,0,0,0,0,0,0,0,0,-31200,-15600]) (![0,0,0,0,0,0,0,0,0,-24000,-12000])).trans sorted_133
theorem gram_271 : gram (fun a=>dictionary32.getD ((row3 252 256 252) a) 0)=norm_134 := by
  rw [gram_eq_of_entries dictionary32 (row3 252 256 252) _ _ _ dictionary_252 dictionary_256 dictionary_252]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-31200,-15600]) (![0,0,0,0,0,0,0,0,0,-31200,-15600]) (![0,0,0,0,0,0,0,0,0,-21600,-10800])).trans sorted_134
theorem gram_272 : gram (fun a=>dictionary32.getD ((row3 253 253 258) a) 0)=norm_136 := by
  rw [gram_eq_of_entries dictionary32 (row3 253 253 258) _ _ _ dictionary_253 dictionary_253 dictionary_258]
  exact sorted_136
theorem gram_273 : gram (fun a=>dictionary32.getD ((row3 254 254 252) a) 0)=norm_135 := by
  rw [gram_eq_of_entries dictionary32 (row3 254 254 252) _ _ _ dictionary_254 dictionary_254 dictionary_252]
  exact (gram120 (![0,0,0,0,0,0,0,0,0,-31200,-15600]) (![0,0,0,0,0,0,0,0,0,-26400,-13200]) (![0,0,0,0,0,0,0,0,0,-26400,-13200])).trans sorted_135
theorem gram_274 : gram (fun a=>dictionary32.getD ((row3 255 258 262) a) 0)=norm_137 := by
  rw [gram_eq_of_entries dictionary32 (row3 255 258 262) _ _ _ dictionary_255 dictionary_258 dictionary_262]
  exact sorted_137
theorem gram_275 : gram (fun a=>dictionary32.getD ((row3 257 257 508) a) 0)=norm_138 := by
  rw [gram_eq_of_entries dictionary32 (row3 257 257 508) _ _ _ dictionary_257 dictionary_257 dictionary_508]
  exact sorted_138
theorem gram_276 : gram (fun a=>dictionary32.getD ((row3 257 508 257) a) 0)=norm_138 := by
  rw [gram_eq_of_entries dictionary32 (row3 257 508 257) _ _ _ dictionary_257 dictionary_508 dictionary_257]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-19200,-9600]) (![0,0,0,0,0,0,0,0,0,-19200,-9600]) (0)).trans sorted_138
theorem gram_277 : gram (fun a=>dictionary32.getD ((row3 258 253 253) a) 0)=norm_136 := by
  rw [gram_eq_of_entries dictionary32 (row3 258 253 253) _ _ _ dictionary_258 dictionary_253 dictionary_253]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-28800,-14400]) (![0,0,0,0,0,0,0,0,0,-28800,-14400]) (![0,0,0,0,0,0,0,0,0,-14400,-7200])).trans sorted_136
theorem gram_278 : gram (fun a=>dictionary32.getD ((row3 258 258 508) a) 0)=norm_139 := by
  rw [gram_eq_of_entries dictionary32 (row3 258 258 508) _ _ _ dictionary_258 dictionary_258 dictionary_508]
  exact sorted_139
theorem gram_279 : gram (fun a=>dictionary32.getD ((row3 258 508 258) a) 0)=norm_139 := by
  rw [gram_eq_of_entries dictionary32 (row3 258 508 258) _ _ _ dictionary_258 dictionary_508 dictionary_258]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-14400,-7200]) (![0,0,0,0,0,0,0,0,0,-14400,-7200]) (0)).trans sorted_139
theorem gram_280 : gram (fun a=>dictionary32.getD ((row3 259 259 261) a) 0)=norm_140 := by
  rw [gram_eq_of_entries dictionary32 (row3 259 259 261) _ _ _ dictionary_259 dictionary_259 dictionary_261]
  exact sorted_140
theorem gram_281 : gram (fun a=>dictionary32.getD ((row3 259 261 259) a) 0)=norm_140 := by
  rw [gram_eq_of_entries dictionary32 (row3 259 261 259) _ _ _ dictionary_259 dictionary_261 dictionary_259]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-13200,-6600]) (![0,0,0,0,0,0,0,0,0,-13200,-6600]) (![0,0,0,0,0,0,0,0,0,-10800,-5400])).trans sorted_140
theorem gram_282 : gram (fun a=>dictionary32.getD ((row3 259 263 263) a) 0)=norm_141 := by
  rw [gram_eq_of_entries dictionary32 (row3 259 263 263) _ _ _ dictionary_259 dictionary_263 dictionary_263]
  exact sorted_141
theorem gram_283 : gram (fun a=>dictionary32.getD ((row3 260 260 265) a) 0)=norm_142 := by
  rw [gram_eq_of_entries dictionary32 (row3 260 260 265) _ _ _ dictionary_260 dictionary_260 dictionary_265]
  exact sorted_142
theorem gram_284 : gram (fun a=>dictionary32.getD ((row3 260 265 260) a) 0)=norm_142 := by
  rw [gram_eq_of_entries dictionary32 (row3 260 265 260) _ _ _ dictionary_260 dictionary_265 dictionary_260]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-12000,-6000]) (![0,0,0,0,0,0,0,0,0,-12000,-6000]) (![0,0,0,0,0,0,0,0,0,-7200,-3600])).trans sorted_142
theorem gram_285 : gram (fun a=>dictionary32.getD ((row3 261 259 259) a) 0)=norm_140 := by
  rw [gram_eq_of_entries dictionary32 (row3 261 259 259) _ _ _ dictionary_261 dictionary_259 dictionary_259]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-13200,-6600]) (![0,0,0,0,0,0,0,0,0,-13200,-6600]) (![0,0,0,0,0,0,0,0,0,-10800,-5400])).trans sorted_140
theorem gram_286 : gram (fun a=>dictionary32.getD ((row3 262 211 207) a) 0)=norm_116 := by
  rw [gram_eq_of_entries dictionary32 (row3 262 211 207) _ _ _ dictionary_262 dictionary_211 dictionary_207]
  exact (gram210 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_116
theorem gram_287 : gram (fun a=>dictionary32.getD ((row3 262 229 234) a) 0)=norm_127 := by
  rw [gram_eq_of_entries dictionary32 (row3 262 229 234) _ _ _ dictionary_262 dictionary_229 dictionary_234]
  exact (gram201 (![0,0,0,0,0,0,0,-2560,-2560,-11840,-5600]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_127
theorem gram_288 : gram (fun a=>dictionary32.getD ((row3 262 258 255) a) 0)=norm_137 := by
  rw [gram_eq_of_entries dictionary32 (row3 262 258 255) _ _ _ dictionary_262 dictionary_258 dictionary_255]
  exact (gram210 (![0,0,0,0,0,0,0,0,0,-24000,-12000]) (![0,0,0,0,0,0,0,0,0,-14400,-7200]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_137
theorem gram_289 : gram (fun a=>dictionary32.getD ((row3 262 262 508) a) 0)=norm_143 := by
  rw [gram_eq_of_entries dictionary32 (row3 262 262 508) _ _ _ dictionary_262 dictionary_262 dictionary_508]
  exact sorted_143
theorem gram_290 : gram (fun a=>dictionary32.getD ((row3 262 268 268) a) 0)=norm_144 := by
  rw [gram_eq_of_entries dictionary32 (row3 262 268 268) _ _ _ dictionary_262 dictionary_268 dictionary_268]
  exact sorted_144
theorem gram_291 : gram (fun a=>dictionary32.getD ((row3 263 263 259) a) 0)=norm_141 := by
  rw [gram_eq_of_entries dictionary32 (row3 263 263 259) _ _ _ dictionary_263 dictionary_263 dictionary_259]
  exact (gram120 (![0,0,0,0,0,0,0,0,0,-13200,-6600]) (![0,0,0,0,0,0,0,0,0,-8400,-4200]) (![0,0,0,0,0,0,0,0,0,-8400,-4200])).trans sorted_141
theorem gram_292 : gram (fun a=>dictionary32.getD ((row3 264 267 266) a) 0)=norm_145 := by
  rw [gram_eq_of_entries dictionary32 (row3 264 267 266) _ _ _ dictionary_264 dictionary_267 dictionary_266]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-7600,-3800]) (![0,0,0,0,0,0,0,0,0,-6000,-3000]) (![0,0,0,0,0,0,0,0,0,-5200,-2600])).trans sorted_145
theorem gram_293 : gram (fun a=>dictionary32.getD ((row3 265 260 260) a) 0)=norm_142 := by
  rw [gram_eq_of_entries dictionary32 (row3 265 260 260) _ _ _ dictionary_265 dictionary_260 dictionary_260]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-12000,-6000]) (![0,0,0,0,0,0,0,0,0,-12000,-6000]) (![0,0,0,0,0,0,0,0,0,-7200,-3600])).trans sorted_142
theorem gram_294 : gram (fun a=>dictionary32.getD ((row3 265 265 265) a) 0)=norm_146 := by
  rw [gram_eq_of_entries dictionary32 (row3 265 265 265) _ _ _ dictionary_265 dictionary_265 dictionary_265]
  exact sorted_146
theorem gram_295 : gram (fun a=>dictionary32.getD ((row3 265 265 508) a) 0)=norm_147 := by
  rw [gram_eq_of_entries dictionary32 (row3 265 265 508) _ _ _ dictionary_265 dictionary_265 dictionary_508]
  exact sorted_147
theorem gram_296 : gram (fun a=>dictionary32.getD ((row3 265 508 265) a) 0)=norm_147 := by
  rw [gram_eq_of_entries dictionary32 (row3 265 508 265) _ _ _ dictionary_265 dictionary_508 dictionary_265]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-7200,-3600]) (![0,0,0,0,0,0,0,0,0,-7200,-3600]) (0)).trans sorted_147
theorem gram_297 : gram (fun a=>dictionary32.getD ((row3 266 267 264) a) 0)=norm_145 := by
  rw [gram_eq_of_entries dictionary32 (row3 266 267 264) _ _ _ dictionary_266 dictionary_267 dictionary_264]
  exact (gram120 (![0,0,0,0,0,0,0,0,0,-7600,-3800]) (![0,0,0,0,0,0,0,0,0,-6000,-3000]) (![0,0,0,0,0,0,0,0,0,-5200,-2600])).trans sorted_145
theorem gram_298 : gram (fun a=>dictionary32.getD ((row3 267 267 270) a) 0)=norm_148 := by
  rw [gram_eq_of_entries dictionary32 (row3 267 267 270) _ _ _ dictionary_267 dictionary_267 dictionary_270]
  exact sorted_148
theorem gram_299 : gram (fun a=>dictionary32.getD ((row3 268 209 210) a) 0)=norm_120 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 209 210) _ _ _ dictionary_268 dictionary_209 dictionary_210]
  exact (gram201 (![0,0,0,0,0,0,0,-5120,-5120,-9280,-4000]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_120
theorem gram_300 : gram (fun a=>dictionary32.getD ((row3 268 262 268) a) 0)=norm_144 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 262 268) _ _ _ dictionary_268 dictionary_262 dictionary_268]
  exact (gram102 (![0,0,0,0,0,0,0,0,0,-9600,-4800]) (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_144
theorem gram_301 : gram (fun a=>dictionary32.getD ((row3 268 268 262) a) 0)=norm_144 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 268 262) _ _ _ dictionary_268 dictionary_268 dictionary_262]
  exact (gram120 (![0,0,0,0,0,0,0,0,0,-9600,-4800]) (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_144
theorem gram_302 : gram (fun a=>dictionary32.getD ((row3 268 268 271) a) 0)=norm_149 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 268 271) _ _ _ dictionary_268 dictionary_268 dictionary_271]
  exact sorted_149
theorem gram_303 : gram (fun a=>dictionary32.getD ((row3 268 268 508) a) 0)=norm_150 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 268 508) _ _ _ dictionary_268 dictionary_268 dictionary_508]
  exact sorted_150
theorem gram_304 : gram (fun a=>dictionary32.getD ((row3 268 508 268) a) 0)=norm_150 := by
  rw [gram_eq_of_entries dictionary32 (row3 268 508 268) _ _ _ dictionary_268 dictionary_508 dictionary_268]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (0)).trans sorted_150
theorem gram_305 : gram (fun a=>dictionary32.getD ((row3 269 508 269) a) 0)=norm_151 := by
  rw [gram_eq_of_entries dictionary32 (row3 269 508 269) _ _ _ dictionary_269 dictionary_508 dictionary_269]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-4000,-2000]) (![0,0,0,0,0,0,0,0,0,-4000,-2000]) (0)).trans sorted_151
theorem gram_306 : gram (fun a=>dictionary32.getD ((row3 270 267 267) a) 0)=norm_148 := by
  rw [gram_eq_of_entries dictionary32 (row3 270 267 267) _ _ _ dictionary_270 dictionary_267 dictionary_267]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-5200,-2600]) (![0,0,0,0,0,0,0,0,0,-5200,-2600]) (![0,0,0,0,0,0,0,0,0,-3600,-1800])).trans sorted_148
theorem gram_307 : gram (fun a=>dictionary32.getD ((row3 271 233 234) a) 0)=norm_130 := by
  rw [gram_eq_of_entries dictionary32 (row3 271 233 234) _ _ _ dictionary_271 dictionary_233 dictionary_234]
  exact (gram201 (![0,0,0,0,0,0,0,-2560,-2560,-4640,-2000]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-2400,-1200])).trans sorted_130
theorem gram_308 : gram (fun a=>dictionary32.getD ((row3 271 268 268) a) 0)=norm_149 := by
  rw [gram_eq_of_entries dictionary32 (row3 271 268 268) _ _ _ dictionary_271 dictionary_268 dictionary_268]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-2400,-1200])).trans sorted_149
theorem gram_309 : gram (fun a=>dictionary32.getD ((row3 271 271 508) a) 0)=norm_152 := by
  rw [gram_eq_of_entries dictionary32 (row3 271 271 508) _ _ _ dictionary_271 dictionary_271 dictionary_508]
  exact sorted_152
theorem gram_310 : gram (fun a=>dictionary32.getD ((row3 271 508 271) a) 0)=norm_152 := by
  rw [gram_eq_of_entries dictionary32 (row3 271 508 271) _ _ _ dictionary_271 dictionary_508 dictionary_271]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-2400,-1200]) (![0,0,0,0,0,0,0,0,0,-2400,-1200]) (0)).trans sorted_152
theorem gram_311 : gram (fun a=>dictionary32.getD ((row3 272 272 508) a) 0)=norm_153 := by
  rw [gram_eq_of_entries dictionary32 (row3 272 272 508) _ _ _ dictionary_272 dictionary_272 dictionary_508]
  exact sorted_153
theorem gram_312 : gram (fun a=>dictionary32.getD ((row3 272 508 272) a) 0)=norm_153 := by
  rw [gram_eq_of_entries dictionary32 (row3 272 508 272) _ _ _ dictionary_272 dictionary_508 dictionary_272]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-1600,-800]) (![0,0,0,0,0,0,0,0,0,-1600,-800]) (0)).trans sorted_153
theorem gram_313 : gram (fun a=>dictionary32.getD ((row3 273 273 508) a) 0)=norm_154 := by
  rw [gram_eq_of_entries dictionary32 (row3 273 273 508) _ _ _ dictionary_273 dictionary_273 dictionary_508]
  exact sorted_154
theorem gram_314 : gram (fun a=>dictionary32.getD ((row3 273 508 273) a) 0)=norm_154 := by
  rw [gram_eq_of_entries dictionary32 (row3 273 508 273) _ _ _ dictionary_273 dictionary_508 dictionary_273]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,-800,-400]) (![0,0,0,0,0,0,0,0,0,-800,-400]) (0)).trans sorted_154
theorem gram_315 : gram (fun a=>dictionary32.getD ((row3 274 508 274) a) 0)=norm_155 := by
  rw [gram_eq_of_entries dictionary32 (row3 274 508 274) _ _ _ dictionary_274 dictionary_508 dictionary_274]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,1500]) (![0,0,0,0,0,0,0,0,0,0,1500]) (0)).trans sorted_155
theorem gram_316 : gram (fun a=>dictionary32.getD ((row3 275 275 508) a) 0)=norm_156 := by
  rw [gram_eq_of_entries dictionary32 (row3 275 275 508) _ _ _ dictionary_275 dictionary_275 dictionary_508]
  exact sorted_156
theorem gram_317 : gram (fun a=>dictionary32.getD ((row3 275 508 275) a) 0)=norm_156 := by
  rw [gram_eq_of_entries dictionary32 (row3 275 508 275) _ _ _ dictionary_275 dictionary_508 dictionary_275]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,3000]) (![0,0,0,0,0,0,0,0,0,0,3000]) (0)).trans sorted_156
theorem gram_318 : gram (fun a=>dictionary32.getD ((row3 276 276 508) a) 0)=norm_157 := by
  rw [gram_eq_of_entries dictionary32 (row3 276 276 508) _ _ _ dictionary_276 dictionary_276 dictionary_508]
  exact sorted_157
theorem gram_319 : gram (fun a=>dictionary32.getD ((row3 276 508 276) a) 0)=norm_157 := by
  rw [gram_eq_of_entries dictionary32 (row3 276 508 276) _ _ _ dictionary_276 dictionary_508 dictionary_276]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,4500]) (![0,0,0,0,0,0,0,0,0,0,4500]) (0)).trans sorted_157
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_320 : gram (fun a=>dictionary32.getD ((row3 277 277 508) a) 0)=norm_158 := by
  rw [gram_eq_of_entries dictionary32 (row3 277 277 508) _ _ _ dictionary_277 dictionary_277 dictionary_508]
  exact sorted_158
theorem gram_321 : gram (fun a=>dictionary32.getD ((row3 277 508 277) a) 0)=norm_158 := by
  rw [gram_eq_of_entries dictionary32 (row3 277 508 277) _ _ _ dictionary_277 dictionary_508 dictionary_277]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,7500]) (![0,0,0,0,0,0,0,0,0,0,7500]) (0)).trans sorted_158
theorem gram_322 : gram (fun a=>dictionary32.getD ((row3 278 278 508) a) 0)=norm_159 := by
  rw [gram_eq_of_entries dictionary32 (row3 278 278 508) _ _ _ dictionary_278 dictionary_278 dictionary_508]
  exact sorted_159
theorem gram_323 : gram (fun a=>dictionary32.getD ((row3 278 508 278) a) 0)=norm_159 := by
  rw [gram_eq_of_entries dictionary32 (row3 278 508 278) _ _ _ dictionary_278 dictionary_508 dictionary_278]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,9000]) (![0,0,0,0,0,0,0,0,0,0,9000]) (0)).trans sorted_159
theorem gram_324 : gram (fun a=>dictionary32.getD ((row3 279 279 508) a) 0)=norm_160 := by
  rw [gram_eq_of_entries dictionary32 (row3 279 279 508) _ _ _ dictionary_279 dictionary_279 dictionary_508]
  exact sorted_160
theorem gram_325 : gram (fun a=>dictionary32.getD ((row3 279 508 279) a) 0)=norm_160 := by
  rw [gram_eq_of_entries dictionary32 (row3 279 508 279) _ _ _ dictionary_279 dictionary_508 dictionary_279]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,13500]) (![0,0,0,0,0,0,0,0,0,0,13500]) (0)).trans sorted_160
theorem gram_326 : gram (fun a=>dictionary32.getD ((row3 280 280 508) a) 0)=norm_161 := by
  rw [gram_eq_of_entries dictionary32 (row3 280 280 508) _ _ _ dictionary_280 dictionary_280 dictionary_508]
  exact sorted_161
theorem gram_327 : gram (fun a=>dictionary32.getD ((row3 280 508 280) a) 0)=norm_161 := by
  rw [gram_eq_of_entries dictionary32 (row3 280 508 280) _ _ _ dictionary_280 dictionary_508 dictionary_280]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,18000]) (![0,0,0,0,0,0,0,0,0,0,18000]) (0)).trans sorted_161
theorem gram_328 : gram (fun a=>dictionary32.getD ((row3 281 508 281) a) 0)=norm_162 := by
  rw [gram_eq_of_entries dictionary32 (row3 281 508 281) _ _ _ dictionary_281 dictionary_508 dictionary_281]
  exact (gram021 (![0,0,0,0,0,0,0,0,0,0,21000]) (![0,0,0,0,0,0,0,0,0,0,21000]) (0)).trans sorted_162
theorem gram_329 : gram (fun a=>dictionary32.getD ((row3 282 9 241) a) 0)=norm_000 := by
  rw [gram_eq_of_entries dictionary32 (row3 282 9 241) _ _ _ dictionary_282 dictionary_9 dictionary_241]
  exact (gram201 (![0,0,0,0,0,0,0,1600,0,0,0]) (![0,0,0,0,0,0,0,-1600,2800,1400,4750]) (![0,0,0,0,0,0,0,0,1200,600,3750])).trans sorted_000
theorem gram_330 : gram (fun a=>dictionary32.getD ((row3 283 284 284) a) 0)=norm_163 := by
  rw [gram_eq_of_entries dictionary32 (row3 283 284 284) _ _ _ dictionary_283 dictionary_284 dictionary_284]
  exact sorted_163
theorem gram_331 : gram (fun a=>dictionary32.getD ((row3 284 284 283) a) 0)=norm_163 := by
  rw [gram_eq_of_entries dictionary32 (row3 284 284 283) _ _ _ dictionary_284 dictionary_284 dictionary_283]
  exact (gram120 (![0,0,0,0,0,0,0,0,1280,1280,320]) (![0,0,0,0,0,0,0,0,1440,1040,2160]) (![0,0,0,0,0,0,0,0,1440,1040,2160])).trans sorted_163
theorem gram_332 : gram (fun a=>dictionary32.getD ((row3 285 285 508) a) 0)=norm_164 := by
  rw [gram_eq_of_entries dictionary32 (row3 285 285 508) _ _ _ dictionary_285 dictionary_285 dictionary_508]
  exact sorted_164
theorem gram_333 : gram (fun a=>dictionary32.getD ((row3 285 508 285) a) 0)=norm_164 := by
  rw [gram_eq_of_entries dictionary32 (row3 285 508 285) _ _ _ dictionary_285 dictionary_508 dictionary_285]
  exact (gram021 (![0,0,0,0,0,0,0,0,1600,800,2500]) (![0,0,0,0,0,0,0,0,1600,800,2500]) (0)).trans sorted_164
theorem gram_334 : gram (fun a=>dictionary32.getD ((row3 286 296 296) a) 0)=norm_165 := by
  rw [gram_eq_of_entries dictionary32 (row3 286 296 296) _ _ _ dictionary_286 dictionary_296 dictionary_296]
  exact sorted_165
theorem gram_335 : gram (fun a=>dictionary32.getD ((row3 287 287 508) a) 0)=norm_166 := by
  rw [gram_eq_of_entries dictionary32 (row3 287 287 508) _ _ _ dictionary_287 dictionary_287 dictionary_508]
  exact sorted_166
theorem gram_336 : gram (fun a=>dictionary32.getD ((row3 287 508 287) a) 0)=norm_166 := by
  rw [gram_eq_of_entries dictionary32 (row3 287 508 287) _ _ _ dictionary_287 dictionary_508 dictionary_287]
  exact (gram021 (![0,0,0,0,0,0,0,0,2400,1200,1000]) (![0,0,0,0,0,0,0,0,2400,1200,1000]) (0)).trans sorted_166
theorem gram_337 : gram (fun a=>dictionary32.getD ((row3 289 289 508) a) 0)=norm_167 := by
  rw [gram_eq_of_entries dictionary32 (row3 289 289 508) _ _ _ dictionary_289 dictionary_289 dictionary_508]
  exact sorted_167
theorem gram_338 : gram (fun a=>dictionary32.getD ((row3 289 508 289) a) 0)=norm_167 := by
  rw [gram_eq_of_entries dictionary32 (row3 289 508 289) _ _ _ dictionary_289 dictionary_508 dictionary_289]
  exact (gram021 (![0,0,0,0,0,0,0,0,2400,1200,15000]) (![0,0,0,0,0,0,0,0,2400,1200,15000]) (0)).trans sorted_167
theorem gram_339 : gram (fun a=>dictionary32.getD ((row3 290 290 508) a) 0)=norm_169 := by
  rw [gram_eq_of_entries dictionary32 (row3 290 290 508) _ _ _ dictionary_290 dictionary_290 dictionary_508]
  exact sorted_169
theorem gram_340 : gram (fun a=>dictionary32.getD ((row3 290 307 290) a) 0)=norm_168 := by
  rw [gram_eq_of_entries dictionary32 (row3 290 307 290) _ _ _ dictionary_290 dictionary_307 dictionary_290]
  exact (gram021 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,5120,5120,1280])).trans sorted_168
theorem gram_341 : gram (fun a=>dictionary32.getD ((row3 290 307 310) a) 0)=norm_170 := by
  rw [gram_eq_of_entries dictionary32 (row3 290 307 310) _ _ _ dictionary_290 dictionary_307 dictionary_310]
  exact sorted_170
theorem gram_342 : gram (fun a=>dictionary32.getD ((row3 290 310 307) a) 0)=norm_170 := by
  rw [gram_eq_of_entries dictionary32 (row3 290 310 307) _ _ _ dictionary_290 dictionary_310 dictionary_307]
  exact (gram021 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,7680,7680,1920])).trans sorted_170
theorem gram_343 : gram (fun a=>dictionary32.getD ((row3 290 508 290) a) 0)=norm_169 := by
  rw [gram_eq_of_entries dictionary32 (row3 290 508 290) _ _ _ dictionary_290 dictionary_508 dictionary_290]
  exact (gram021 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,2560,2560,640]) (0)).trans sorted_169
theorem gram_344 : gram (fun a=>dictionary32.getD ((row3 291 291 508) a) 0)=norm_171 := by
  rw [gram_eq_of_entries dictionary32 (row3 291 291 508) _ _ _ dictionary_291 dictionary_291 dictionary_508]
  exact sorted_171
theorem gram_345 : gram (fun a=>dictionary32.getD ((row3 291 508 291) a) 0)=norm_171 := by
  rw [gram_eq_of_entries dictionary32 (row3 291 508 291) _ _ _ dictionary_291 dictionary_508 dictionary_291]
  exact (gram021 (![0,0,0,0,0,0,0,0,3200,1600,2000]) (![0,0,0,0,0,0,0,0,3200,1600,2000]) (0)).trans sorted_171
theorem gram_346 : gram (fun a=>dictionary32.getD ((row3 292 295 295) a) 0)=norm_172 := by
  rw [gram_eq_of_entries dictionary32 (row3 292 295 295) _ _ _ dictionary_292 dictionary_295 dictionary_295]
  exact sorted_172
theorem gram_347 : gram (fun a=>dictionary32.getD ((row3 293 11 216) a) 0)=norm_004 := by
  rw [gram_eq_of_entries dictionary32 (row3 293 11 216) _ _ _ dictionary_293 dictionary_11 dictionary_216]
  exact (gram201 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,5250]) (![0,0,0,0,0,0,0,0,3600,1800,2250])).trans sorted_004
theorem gram_348 : gram (fun a=>dictionary32.getD ((row3 294 11 217) a) 0)=norm_005 := by
  rw [gram_eq_of_entries dictionary32 (row3 294 11 217) _ _ _ dictionary_294 dictionary_11 dictionary_217]
  exact (gram201 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,35250]) (![0,0,0,0,0,0,0,0,3600,1800,32250])).trans sorted_005
theorem gram_349 : gram (fun a=>dictionary32.getD ((row3 295 295 292) a) 0)=norm_172 := by
  rw [gram_eq_of_entries dictionary32 (row3 295 295 292) _ _ _ dictionary_295 dictionary_295 dictionary_292]
  exact (gram120 (![0,0,0,0,0,0,0,0,3200,3200,800]) (![0,0,0,0,0,0,0,0,3600,2600,4900]) (![0,0,0,0,0,0,0,0,3600,2600,4900])).trans sorted_172
theorem gram_350 : gram (fun a=>dictionary32.getD ((row3 296 296 286) a) 0)=norm_165 := by
  rw [gram_eq_of_entries dictionary32 (row3 296 296 286) _ _ _ dictionary_296 dictionary_296 dictionary_286]
  exact (gram120 (![0,0,0,0,0,0,0,0,1920,1920,480]) (![0,0,0,0,0,0,0,0,3760,2360,3740]) (![0,0,0,0,0,0,0,0,3760,2360,3740])).trans sorted_165
theorem gram_351 : gram (fun a=>dictionary32.getD ((row3 297 298 298) a) 0)=norm_173 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 298 298) _ _ _ dictionary_297 dictionary_298 dictionary_298]
  exact sorted_173
theorem gram_352 : gram (fun a=>dictionary32.getD ((row3 297 299 299) a) 0)=norm_174 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 299 299) _ _ _ dictionary_297 dictionary_299 dictionary_299]
  exact sorted_174
theorem gram_353 : gram (fun a=>dictionary32.getD ((row3 297 300 300) a) 0)=norm_175 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 300 300) _ _ _ dictionary_297 dictionary_300 dictionary_300]
  exact sorted_175
theorem gram_354 : gram (fun a=>dictionary32.getD ((row3 297 301 301) a) 0)=norm_176 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 301 301) _ _ _ dictionary_297 dictionary_301 dictionary_301]
  exact sorted_176
theorem gram_355 : gram (fun a=>dictionary32.getD ((row3 297 302 302) a) 0)=norm_177 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 302 302) _ _ _ dictionary_297 dictionary_302 dictionary_302]
  exact sorted_177
theorem gram_356 : gram (fun a=>dictionary32.getD ((row3 297 315 315) a) 0)=norm_178 := by
  rw [gram_eq_of_entries dictionary32 (row3 297 315 315) _ _ _ dictionary_297 dictionary_315 dictionary_315]
  exact sorted_178
theorem gram_357 : gram (fun a=>dictionary32.getD ((row3 298 298 297) a) 0)=norm_173 := by
  rw [gram_eq_of_entries dictionary32 (row3 298 298 297) _ _ _ dictionary_298 dictionary_298 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,4320,3120,4980]) (![0,0,0,0,0,0,0,0,4320,3120,4980])).trans sorted_173
theorem gram_358 : gram (fun a=>dictionary32.getD ((row3 299 299 297) a) 0)=norm_174 := by
  rw [gram_eq_of_entries dictionary32 (row3 299 299 297) _ _ _ dictionary_299 dictionary_299 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,4320,3120,6480]) (![0,0,0,0,0,0,0,0,4320,3120,6480])).trans sorted_174
theorem gram_359 : gram (fun a=>dictionary32.getD ((row3 300 300 297) a) 0)=norm_175 := by
  rw [gram_eq_of_entries dictionary32 (row3 300 300 297) _ _ _ dictionary_300 dictionary_300 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,4320,3120,7980]) (![0,0,0,0,0,0,0,0,4320,3120,7980])).trans sorted_175
theorem gram_360 : gram (fun a=>dictionary32.getD ((row3 301 301 297) a) 0)=norm_176 := by
  rw [gram_eq_of_entries dictionary32 (row3 301 301 297) _ _ _ dictionary_301 dictionary_301 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,4320,3120,10980]) (![0,0,0,0,0,0,0,0,4320,3120,10980])).trans sorted_176
theorem gram_361 : gram (fun a=>dictionary32.getD ((row3 302 302 297) a) 0)=norm_177 := by
  rw [gram_eq_of_entries dictionary32 (row3 302 302 297) _ _ _ dictionary_302 dictionary_302 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,4320,3120,13980]) (![0,0,0,0,0,0,0,0,4320,3120,13980])).trans sorted_177
theorem gram_362 : gram (fun a=>dictionary32.getD ((row3 303 303 508) a) 0)=norm_179 := by
  rw [gram_eq_of_entries dictionary32 (row3 303 303 508) _ _ _ dictionary_303 dictionary_303 dictionary_508]
  exact sorted_179
theorem gram_363 : gram (fun a=>dictionary32.getD ((row3 304 304 508) a) 0)=norm_180 := by
  rw [gram_eq_of_entries dictionary32 (row3 304 304 508) _ _ _ dictionary_304 dictionary_304 dictionary_508]
  exact sorted_180
theorem gram_364 : gram (fun a=>dictionary32.getD ((row3 304 508 304) a) 0)=norm_180 := by
  rw [gram_eq_of_entries dictionary32 (row3 304 508 304) _ _ _ dictionary_304 dictionary_508 dictionary_304]
  exact (gram021 (![0,0,0,0,0,0,0,0,4800,2400,3000]) (![0,0,0,0,0,0,0,0,4800,2400,3000]) (0)).trans sorted_180
theorem gram_365 : gram (fun a=>dictionary32.getD ((row3 305 305 508) a) 0)=norm_181 := by
  rw [gram_eq_of_entries dictionary32 (row3 305 305 508) _ _ _ dictionary_305 dictionary_305 dictionary_508]
  exact sorted_181
theorem gram_366 : gram (fun a=>dictionary32.getD ((row3 305 508 305) a) 0)=norm_181 := by
  rw [gram_eq_of_entries dictionary32 (row3 305 508 305) _ _ _ dictionary_305 dictionary_508 dictionary_305]
  exact (gram021 (![0,0,0,0,0,0,0,0,4800,2400,7500]) (![0,0,0,0,0,0,0,0,4800,2400,7500]) (0)).trans sorted_181
theorem gram_367 : gram (fun a=>dictionary32.getD ((row3 306 508 306) a) 0)=norm_182 := by
  rw [gram_eq_of_entries dictionary32 (row3 306 508 306) _ _ _ dictionary_306 dictionary_508 dictionary_306]
  exact (gram021 (![0,0,0,0,0,0,0,0,4800,2400,10500]) (![0,0,0,0,0,0,0,0,4800,2400,10500]) (0)).trans sorted_182
theorem gram_368 : gram (fun a=>dictionary32.getD ((row3 307 307 307) a) 0)=norm_183 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 307 307) _ _ _ dictionary_307 dictionary_307 dictionary_307]
  exact sorted_183
theorem gram_369 : gram (fun a=>dictionary32.getD ((row3 307 307 319) a) 0)=norm_184 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 307 319) _ _ _ dictionary_307 dictionary_307 dictionary_319]
  exact sorted_184
theorem gram_370 : gram (fun a=>dictionary32.getD ((row3 307 307 508) a) 0)=norm_185 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 307 508) _ _ _ dictionary_307 dictionary_307 dictionary_508]
  exact sorted_185
theorem gram_371 : gram (fun a=>dictionary32.getD ((row3 307 310 290) a) 0)=norm_170 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 310 290) _ _ _ dictionary_307 dictionary_310 dictionary_290]
  exact (gram120 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,7680,7680,1920])).trans sorted_170
theorem gram_372 : gram (fun a=>dictionary32.getD ((row3 307 310 322) a) 0)=norm_186 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 310 322) _ _ _ dictionary_307 dictionary_310 dictionary_322]
  exact sorted_186
theorem gram_373 : gram (fun a=>dictionary32.getD ((row3 307 508 307) a) 0)=norm_185 := by
  rw [gram_eq_of_entries dictionary32 (row3 307 508 307) _ _ _ dictionary_307 dictionary_508 dictionary_307]
  exact (gram021 (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (0)).trans sorted_185
theorem gram_374 : gram (fun a=>dictionary32.getD ((row3 308 309 309) a) 0)=norm_187 := by
  rw [gram_eq_of_entries dictionary32 (row3 308 309 309) _ _ _ dictionary_308 dictionary_309 dictionary_309]
  exact sorted_187
theorem gram_375 : gram (fun a=>dictionary32.getD ((row3 308 314 314) a) 0)=norm_188 := by
  rw [gram_eq_of_entries dictionary32 (row3 308 314 314) _ _ _ dictionary_308 dictionary_314 dictionary_314]
  exact sorted_188
theorem gram_376 : gram (fun a=>dictionary32.getD ((row3 309 308 309) a) 0)=norm_187 := by
  rw [gram_eq_of_entries dictionary32 (row3 309 308 309) _ _ _ dictionary_309 dictionary_308 dictionary_309]
  exact (gram102 (![0,0,0,0,0,0,0,0,5760,5760,1440]) (![0,0,0,0,0,0,0,0,6480,4680,9720]) (![0,0,0,0,0,0,0,0,6480,4680,9720])).trans sorted_187
theorem gram_377 : gram (fun a=>dictionary32.getD ((row3 309 309 308) a) 0)=norm_187 := by
  rw [gram_eq_of_entries dictionary32 (row3 309 309 308) _ _ _ dictionary_309 dictionary_309 dictionary_308]
  exact (gram120 (![0,0,0,0,0,0,0,0,5760,5760,1440]) (![0,0,0,0,0,0,0,0,6480,4680,9720]) (![0,0,0,0,0,0,0,0,6480,4680,9720])).trans sorted_187
theorem gram_378 : gram (fun a=>dictionary32.getD ((row3 310 307 290) a) 0)=norm_170 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 307 290) _ _ _ dictionary_310 dictionary_307 dictionary_290]
  exact (gram210 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,7680,7680,1920])).trans sorted_170
theorem gram_379 : gram (fun a=>dictionary32.getD ((row3 310 310 319) a) 0)=norm_189 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 310 319) _ _ _ dictionary_310 dictionary_310 dictionary_319]
  exact sorted_189
theorem gram_380 : gram (fun a=>dictionary32.getD ((row3 310 311 311) a) 0)=norm_190 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 311 311) _ _ _ dictionary_310 dictionary_311 dictionary_311]
  exact sorted_190
theorem gram_381 : gram (fun a=>dictionary32.getD ((row3 310 312 312) a) 0)=norm_191 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 312 312) _ _ _ dictionary_310 dictionary_312 dictionary_312]
  exact sorted_191
theorem gram_382 : gram (fun a=>dictionary32.getD ((row3 310 313 313) a) 0)=norm_192 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 313 313) _ _ _ dictionary_310 dictionary_313 dictionary_313]
  exact sorted_192
theorem gram_383 : gram (fun a=>dictionary32.getD ((row3 310 340 340) a) 0)=norm_193 := by
  rw [gram_eq_of_entries dictionary32 (row3 310 340 340) _ _ _ dictionary_310 dictionary_340 dictionary_340]
  exact sorted_193
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_384 : gram (fun a=>dictionary32.getD ((row3 311 310 311) a) 0)=norm_190 := by
  rw [gram_eq_of_entries dictionary32 (row3 311 310 311) _ _ _ dictionary_311 dictionary_310 dictionary_311]
  exact (gram102 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,8640,6240,9960]) (![0,0,0,0,0,0,0,0,8640,6240,9960])).trans sorted_190
theorem gram_385 : gram (fun a=>dictionary32.getD ((row3 311 311 310) a) 0)=norm_190 := by
  rw [gram_eq_of_entries dictionary32 (row3 311 311 310) _ _ _ dictionary_311 dictionary_311 dictionary_310]
  exact (gram120 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,8640,6240,9960]) (![0,0,0,0,0,0,0,0,8640,6240,9960])).trans sorted_190
theorem gram_386 : gram (fun a=>dictionary32.getD ((row3 312 310 312) a) 0)=norm_191 := by
  rw [gram_eq_of_entries dictionary32 (row3 312 310 312) _ _ _ dictionary_312 dictionary_310 dictionary_312]
  exact (gram102 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,8640,6240,12960]) (![0,0,0,0,0,0,0,0,8640,6240,12960])).trans sorted_191
theorem gram_387 : gram (fun a=>dictionary32.getD ((row3 312 312 310) a) 0)=norm_191 := by
  rw [gram_eq_of_entries dictionary32 (row3 312 312 310) _ _ _ dictionary_312 dictionary_312 dictionary_310]
  exact (gram120 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,8640,6240,12960]) (![0,0,0,0,0,0,0,0,8640,6240,12960])).trans sorted_191
theorem gram_388 : gram (fun a=>dictionary32.getD ((row3 313 313 310) a) 0)=norm_192 := by
  rw [gram_eq_of_entries dictionary32 (row3 313 313 310) _ _ _ dictionary_313 dictionary_313 dictionary_310]
  exact (gram120 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,8640,6240,36960]) (![0,0,0,0,0,0,0,0,8640,6240,36960])).trans sorted_192
theorem gram_389 : gram (fun a=>dictionary32.getD ((row3 314 308 314) a) 0)=norm_188 := by
  rw [gram_eq_of_entries dictionary32 (row3 314 308 314) _ _ _ dictionary_314 dictionary_308 dictionary_314]
  exact (gram102 (![0,0,0,0,0,0,0,0,5760,5760,1440]) (![0,0,0,0,0,0,0,0,8880,5880,11220]) (![0,0,0,0,0,0,0,0,8880,5880,11220])).trans sorted_188
theorem gram_390 : gram (fun a=>dictionary32.getD ((row3 314 314 308) a) 0)=norm_188 := by
  rw [gram_eq_of_entries dictionary32 (row3 314 314 308) _ _ _ dictionary_314 dictionary_314 dictionary_308]
  exact (gram120 (![0,0,0,0,0,0,0,0,5760,5760,1440]) (![0,0,0,0,0,0,0,0,8880,5880,11220]) (![0,0,0,0,0,0,0,0,8880,5880,11220])).trans sorted_188
theorem gram_391 : gram (fun a=>dictionary32.getD ((row3 315 315 297) a) 0)=norm_178 := by
  rw [gram_eq_of_entries dictionary32 (row3 315 315 297) _ _ _ dictionary_315 dictionary_315 dictionary_297]
  exact (gram120 (![0,0,0,0,0,0,0,0,3840,3840,960]) (![0,0,0,0,0,0,0,0,9120,5520,6480]) (![0,0,0,0,0,0,0,0,9120,5520,6480])).trans sorted_178
theorem gram_392 : gram (fun a=>dictionary32.getD ((row3 316 316 508) a) 0)=norm_194 := by
  rw [gram_eq_of_entries dictionary32 (row3 316 316 508) _ _ _ dictionary_316 dictionary_316 dictionary_508]
  exact sorted_194
theorem gram_393 : gram (fun a=>dictionary32.getD ((row3 316 508 316) a) 0)=norm_194 := by
  rw [gram_eq_of_entries dictionary32 (row3 316 508 316) _ _ _ dictionary_316 dictionary_508 dictionary_316]
  exact (gram021 (![0,0,0,0,0,0,0,0,9600,4800,3000]) (![0,0,0,0,0,0,0,0,9600,4800,3000]) (0)).trans sorted_194
theorem gram_394 : gram (fun a=>dictionary32.getD ((row3 317 317 508) a) 0)=norm_195 := by
  rw [gram_eq_of_entries dictionary32 (row3 317 317 508) _ _ _ dictionary_317 dictionary_317 dictionary_508]
  exact sorted_195
theorem gram_395 : gram (fun a=>dictionary32.getD ((row3 317 508 317) a) 0)=norm_195 := by
  rw [gram_eq_of_entries dictionary32 (row3 317 508 317) _ _ _ dictionary_317 dictionary_508 dictionary_317]
  exact (gram021 (![0,0,0,0,0,0,0,0,9600,4800,6000]) (![0,0,0,0,0,0,0,0,9600,4800,6000]) (0)).trans sorted_195
theorem gram_396 : gram (fun a=>dictionary32.getD ((row3 318 508 318) a) 0)=norm_196 := by
  rw [gram_eq_of_entries dictionary32 (row3 318 508 318) _ _ _ dictionary_318 dictionary_508 dictionary_318]
  exact (gram021 (![0,0,0,0,0,0,0,0,9600,4800,30000]) (![0,0,0,0,0,0,0,0,9600,4800,30000]) (0)).trans sorted_196
theorem gram_397 : gram (fun a=>dictionary32.getD ((row3 319 307 307) a) 0)=norm_184 := by
  rw [gram_eq_of_entries dictionary32 (row3 319 307 307) _ _ _ dictionary_319 dictionary_307 dictionary_307]
  exact (gram201 (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,10240,10240,2560])).trans sorted_184
theorem gram_398 : gram (fun a=>dictionary32.getD ((row3 319 310 310) a) 0)=norm_189 := by
  rw [gram_eq_of_entries dictionary32 (row3 319 310 310) _ _ _ dictionary_319 dictionary_310 dictionary_310]
  exact (gram201 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,10240,10240,2560])).trans sorted_189
theorem gram_399 : gram (fun a=>dictionary32.getD ((row3 319 319 508) a) 0)=norm_197 := by
  rw [gram_eq_of_entries dictionary32 (row3 319 319 508) _ _ _ dictionary_319 dictionary_319 dictionary_508]
  exact sorted_197
theorem gram_400 : gram (fun a=>dictionary32.getD ((row3 319 332 332) a) 0)=norm_198 := by
  rw [gram_eq_of_entries dictionary32 (row3 319 332 332) _ _ _ dictionary_319 dictionary_332 dictionary_332]
  exact sorted_198
theorem gram_401 : gram (fun a=>dictionary32.getD ((row3 319 508 319) a) 0)=norm_197 := by
  rw [gram_eq_of_entries dictionary32 (row3 319 508 319) _ _ _ dictionary_319 dictionary_508 dictionary_319]
  exact (gram021 (![0,0,0,0,0,0,0,0,10240,10240,2560]) (![0,0,0,0,0,0,0,0,10240,10240,2560]) (0)).trans sorted_197
theorem gram_402 : gram (fun a=>dictionary32.getD ((row3 320 13 166) a) 0)=norm_009 := by
  rw [gram_eq_of_entries dictionary32 (row3 320 13 166) _ _ _ dictionary_320 dictionary_13 dictionary_166]
  exact (gram201 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,25200,12600,15750]) (![0,0,0,0,0,0,0,0,10800,5400,6750])).trans sorted_009
theorem gram_403 : gram (fun a=>dictionary32.getD ((row3 321 323 323) a) 0)=norm_199 := by
  rw [gram_eq_of_entries dictionary32 (row3 321 323 323) _ _ _ dictionary_321 dictionary_323 dictionary_323]
  exact sorted_199
theorem gram_404 : gram (fun a=>dictionary32.getD ((row3 321 324 324) a) 0)=norm_200 := by
  rw [gram_eq_of_entries dictionary32 (row3 321 324 324) _ _ _ dictionary_321 dictionary_324 dictionary_324]
  exact sorted_200
theorem gram_405 : gram (fun a=>dictionary32.getD ((row3 321 329 329) a) 0)=norm_202 := by
  rw [gram_eq_of_entries dictionary32 (row3 321 329 329) _ _ _ dictionary_321 dictionary_329 dictionary_329]
  exact sorted_202
theorem gram_406 : gram (fun a=>dictionary32.getD ((row3 322 310 307) a) 0)=norm_186 := by
  rw [gram_eq_of_entries dictionary32 (row3 322 310 307) _ _ _ dictionary_322 dictionary_310 dictionary_307]
  exact (gram210 (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,12800,12800,3200])).trans sorted_186
theorem gram_407 : gram (fun a=>dictionary32.getD ((row3 322 508 322) a) 0)=norm_203 := by
  rw [gram_eq_of_entries dictionary32 (row3 322 508 322) _ _ _ dictionary_322 dictionary_508 dictionary_322]
  exact (gram021 (![0,0,0,0,0,0,0,0,12800,12800,3200]) (![0,0,0,0,0,0,0,0,12800,12800,3200]) (0)).trans sorted_203
theorem gram_408 : gram (fun a=>dictionary32.getD ((row3 323 323 321) a) 0)=norm_199 := by
  rw [gram_eq_of_entries dictionary32 (row3 323 323 321) _ _ _ dictionary_323 dictionary_323 dictionary_321]
  exact (gram120 (![0,0,0,0,0,0,0,0,11520,11520,2880]) (![0,0,0,0,0,0,0,0,12960,9360,14940]) (![0,0,0,0,0,0,0,0,12960,9360,14940])).trans sorted_199
theorem gram_409 : gram (fun a=>dictionary32.getD ((row3 324 324 321) a) 0)=norm_200 := by
  rw [gram_eq_of_entries dictionary32 (row3 324 324 321) _ _ _ dictionary_324 dictionary_324 dictionary_321]
  exact (gram120 (![0,0,0,0,0,0,0,0,11520,11520,2880]) (![0,0,0,0,0,0,0,0,12960,9360,19440]) (![0,0,0,0,0,0,0,0,12960,9360,19440])).trans sorted_200
theorem gram_410 : gram (fun a=>dictionary32.getD ((row3 325 321 325) a) 0)=norm_201 := by
  rw [gram_eq_of_entries dictionary32 (row3 325 321 325) _ _ _ dictionary_325 dictionary_321 dictionary_325]
  exact (gram102 (![0,0,0,0,0,0,0,0,11520,11520,2880]) (![0,0,0,0,0,0,0,0,12960,9360,37440]) (![0,0,0,0,0,0,0,0,12960,9360,37440])).trans sorted_201
theorem gram_411 : gram (fun a=>dictionary32.getD ((row3 326 326 508) a) 0)=norm_204 := by
  rw [gram_eq_of_entries dictionary32 (row3 326 326 508) _ _ _ dictionary_326 dictionary_326 dictionary_508]
  exact sorted_204
theorem gram_412 : gram (fun a=>dictionary32.getD ((row3 327 327 508) a) 0)=norm_205 := by
  rw [gram_eq_of_entries dictionary32 (row3 327 327 508) _ _ _ dictionary_327 dictionary_327 dictionary_508]
  exact sorted_205
theorem gram_413 : gram (fun a=>dictionary32.getD ((row3 327 328 328) a) 0)=norm_206 := by
  rw [gram_eq_of_entries dictionary32 (row3 327 328 328) _ _ _ dictionary_327 dictionary_328 dictionary_328]
  exact sorted_206
theorem gram_414 : gram (fun a=>dictionary32.getD ((row3 327 508 327) a) 0)=norm_205 := by
  rw [gram_eq_of_entries dictionary32 (row3 327 508 327) _ _ _ dictionary_327 dictionary_508 dictionary_327]
  exact (gram021 (![0,0,0,0,0,0,0,0,15360,15360,3840]) (![0,0,0,0,0,0,0,0,15360,15360,3840]) (0)).trans sorted_205
theorem gram_415 : gram (fun a=>dictionary32.getD ((row3 328 328 327) a) 0)=norm_206 := by
  rw [gram_eq_of_entries dictionary32 (row3 328 328 327) _ _ _ dictionary_328 dictionary_328 dictionary_327]
  exact (gram120 (![0,0,0,0,0,0,0,0,15360,15360,3840]) (![0,0,0,0,0,0,0,0,17280,12480,21420]) (![0,0,0,0,0,0,0,0,17280,12480,21420])).trans sorted_206
theorem gram_416 : gram (fun a=>dictionary32.getD ((row3 329 321 329) a) 0)=norm_202 := by
  rw [gram_eq_of_entries dictionary32 (row3 329 321 329) _ _ _ dictionary_329 dictionary_321 dictionary_329]
  exact (gram102 (![0,0,0,0,0,0,0,0,11520,11520,2880]) (![0,0,0,0,0,0,0,0,17760,11760,22440]) (![0,0,0,0,0,0,0,0,17760,11760,22440])).trans sorted_202
theorem gram_417 : gram (fun a=>dictionary32.getD ((row3 329 329 321) a) 0)=norm_202 := by
  rw [gram_eq_of_entries dictionary32 (row3 329 329 321) _ _ _ dictionary_329 dictionary_329 dictionary_321]
  exact (gram120 (![0,0,0,0,0,0,0,0,11520,11520,2880]) (![0,0,0,0,0,0,0,0,17760,11760,22440]) (![0,0,0,0,0,0,0,0,17760,11760,22440])).trans sorted_202
theorem gram_418 : gram (fun a=>dictionary32.getD ((row3 330 330 508) a) 0)=norm_207 := by
  rw [gram_eq_of_entries dictionary32 (row3 330 330 508) _ _ _ dictionary_330 dictionary_330 dictionary_508]
  exact sorted_207
theorem gram_419 : gram (fun a=>dictionary32.getD ((row3 330 508 330) a) 0)=norm_207 := by
  rw [gram_eq_of_entries dictionary32 (row3 330 508 330) _ _ _ dictionary_330 dictionary_508 dictionary_330]
  exact (gram021 (![0,0,0,0,0,0,0,0,19200,9600,7500]) (![0,0,0,0,0,0,0,0,19200,9600,7500]) (0)).trans sorted_207
theorem gram_420 : gram (fun a=>dictionary32.getD ((row3 331 334 334) a) 0)=norm_208 := by
  rw [gram_eq_of_entries dictionary32 (row3 331 334 334) _ _ _ dictionary_331 dictionary_334 dictionary_334]
  exact sorted_208
theorem gram_421 : gram (fun a=>dictionary32.getD ((row3 332 332 319) a) 0)=norm_198 := by
  rw [gram_eq_of_entries dictionary32 (row3 332 332 319) _ _ _ dictionary_332 dictionary_332 dictionary_319]
  exact (gram120 (![0,0,0,0,0,0,0,0,10240,10240,2560]) (![0,0,0,0,0,0,0,0,20480,20480,5120]) (![0,0,0,0,0,0,0,0,20480,20480,5120])).trans sorted_198
theorem gram_422 : gram (fun a=>dictionary32.getD ((row3 334 334 331) a) 0)=norm_208 := by
  rw [gram_eq_of_entries dictionary32 (row3 334 334 331) _ _ _ dictionary_334 dictionary_334 dictionary_331]
  exact (gram120 (![0,0,0,0,0,0,0,0,19200,19200,4800]) (![0,0,0,0,0,0,0,0,21600,15600,24900]) (![0,0,0,0,0,0,0,0,21600,15600,24900])).trans sorted_208
theorem gram_423 : gram (fun a=>dictionary32.getD ((row3 335 336 336) a) 0)=norm_209 := by
  rw [gram_eq_of_entries dictionary32 (row3 335 336 336) _ _ _ dictionary_335 dictionary_336 dictionary_336]
  exact sorted_209
theorem gram_424 : gram (fun a=>dictionary32.getD ((row3 335 337 337) a) 0)=norm_210 := by
  rw [gram_eq_of_entries dictionary32 (row3 335 337 337) _ _ _ dictionary_335 dictionary_337 dictionary_337]
  exact sorted_210
theorem gram_425 : gram (fun a=>dictionary32.getD ((row3 335 339 339) a) 0)=norm_211 := by
  rw [gram_eq_of_entries dictionary32 (row3 335 339 339) _ _ _ dictionary_335 dictionary_339 dictionary_339]
  exact sorted_211
theorem gram_426 : gram (fun a=>dictionary32.getD ((row3 336 336 335) a) 0)=norm_209 := by
  rw [gram_eq_of_entries dictionary32 (row3 336 336 335) _ _ _ dictionary_336 dictionary_336 dictionary_335]
  exact (gram120 (![0,0,0,0,0,0,0,0,23040,23040,5760]) (![0,0,0,0,0,0,0,0,25920,18720,38880]) (![0,0,0,0,0,0,0,0,25920,18720,38880])).trans sorted_209
theorem gram_427 : gram (fun a=>dictionary32.getD ((row3 337 337 335) a) 0)=norm_210 := by
  rw [gram_eq_of_entries dictionary32 (row3 337 337 335) _ _ _ dictionary_337 dictionary_337 dictionary_335]
  exact (gram120 (![0,0,0,0,0,0,0,0,23040,23040,5760]) (![0,0,0,0,0,0,0,0,25920,18720,43380]) (![0,0,0,0,0,0,0,0,25920,18720,43380])).trans sorted_210
theorem gram_428 : gram (fun a=>dictionary32.getD ((row3 338 338 508) a) 0)=norm_212 := by
  rw [gram_eq_of_entries dictionary32 (row3 338 338 508) _ _ _ dictionary_338 dictionary_338 dictionary_508]
  exact sorted_212
theorem gram_429 : gram (fun a=>dictionary32.getD ((row3 338 508 338) a) 0)=norm_212 := by
  rw [gram_eq_of_entries dictionary32 (row3 338 508 338) _ _ _ dictionary_338 dictionary_508 dictionary_338]
  exact (gram021 (![0,0,0,0,0,0,0,0,30720,30720,7680]) (![0,0,0,0,0,0,0,0,30720,30720,7680]) (0)).trans sorted_212
theorem gram_430 : gram (fun a=>dictionary32.getD ((row3 339 335 339) a) 0)=norm_211 := by
  rw [gram_eq_of_entries dictionary32 (row3 339 335 339) _ _ _ dictionary_339 dictionary_335 dictionary_339]
  exact (gram102 (![0,0,0,0,0,0,0,0,23040,23040,5760]) (![0,0,0,0,0,0,0,0,35520,23520,35880]) (![0,0,0,0,0,0,0,0,35520,23520,35880])).trans sorted_211
theorem gram_431 : gram (fun a=>dictionary32.getD ((row3 339 339 335) a) 0)=norm_211 := by
  rw [gram_eq_of_entries dictionary32 (row3 339 339 335) _ _ _ dictionary_339 dictionary_339 dictionary_335]
  exact (gram120 (![0,0,0,0,0,0,0,0,23040,23040,5760]) (![0,0,0,0,0,0,0,0,35520,23520,35880]) (![0,0,0,0,0,0,0,0,35520,23520,35880])).trans sorted_211
theorem gram_432 : gram (fun a=>dictionary32.getD ((row3 340 340 310) a) 0)=norm_193 := by
  rw [gram_eq_of_entries dictionary32 (row3 340 340 310) _ _ _ dictionary_340 dictionary_340 dictionary_310]
  exact (gram120 (![0,0,0,0,0,0,0,0,7680,7680,1920]) (![0,0,0,0,0,0,0,0,37440,20640,21960]) (![0,0,0,0,0,0,0,0,37440,20640,21960])).trans sorted_193
theorem gram_433 : gram (fun a=>dictionary32.getD ((row3 341 342 342) a) 0)=norm_213 := by
  rw [gram_eq_of_entries dictionary32 (row3 341 342 342) _ _ _ dictionary_341 dictionary_342 dictionary_342]
  exact sorted_213
theorem gram_434 : gram (fun a=>dictionary32.getD ((row3 341 343 343) a) 0)=norm_214 := by
  rw [gram_eq_of_entries dictionary32 (row3 341 343 343) _ _ _ dictionary_341 dictionary_343 dictionary_343]
  exact sorted_214
theorem gram_435 : gram (fun a=>dictionary32.getD ((row3 342 342 341) a) 0)=norm_213 := by
  rw [gram_eq_of_entries dictionary32 (row3 342 342 341) _ _ _ dictionary_342 dictionary_342 dictionary_341]
  exact (gram120 (![0,0,0,0,0,0,0,0,46080,46080,11520]) (![0,0,0,0,0,0,0,0,51840,37440,59760]) (![0,0,0,0,0,0,0,0,51840,37440,59760])).trans sorted_213
theorem gram_436 : gram (fun a=>dictionary32.getD ((row3 343 341 343) a) 0)=norm_214 := by
  rw [gram_eq_of_entries dictionary32 (row3 343 341 343) _ _ _ dictionary_343 dictionary_341 dictionary_343]
  exact (gram102 (![0,0,0,0,0,0,0,0,46080,46080,11520]) (![0,0,0,0,0,0,0,0,51840,37440,77760]) (![0,0,0,0,0,0,0,0,51840,37440,77760])).trans sorted_214
theorem gram_437 : gram (fun a=>dictionary32.getD ((row3 343 343 341) a) 0)=norm_214 := by
  rw [gram_eq_of_entries dictionary32 (row3 343 343 341) _ _ _ dictionary_343 dictionary_343 dictionary_341]
  exact (gram120 (![0,0,0,0,0,0,0,0,46080,46080,11520]) (![0,0,0,0,0,0,0,0,51840,37440,77760]) (![0,0,0,0,0,0,0,0,51840,37440,77760])).trans sorted_214
theorem gram_438 : gram (fun a=>dictionary32.getD ((row3 344 346 346) a) 0)=norm_215 := by
  rw [gram_eq_of_entries dictionary32 (row3 344 346 346) _ _ _ dictionary_344 dictionary_346 dictionary_346]
  exact sorted_215
theorem gram_439 : gram (fun a=>dictionary32.getD ((row3 345 508 345) a) 0)=norm_216 := by
  rw [gram_eq_of_entries dictionary32 (row3 345 508 345) _ _ _ dictionary_345 dictionary_508 dictionary_345]
  exact (gram021 (![0,0,0,0,0,0,0,0,57600,28800,18000]) (![0,0,0,0,0,0,0,0,57600,28800,18000]) (0)).trans sorted_216
theorem gram_440 : gram (fun a=>dictionary32.getD ((row3 346 346 344) a) 0)=norm_215 := by
  rw [gram_eq_of_entries dictionary32 (row3 346 346 344) _ _ _ dictionary_346 dictionary_346 dictionary_344]
  exact (gram120 (![0,0,0,0,0,0,0,0,53760,53760,13440]) (![0,0,0,0,0,0,0,0,60480,43680,69720]) (![0,0,0,0,0,0,0,0,60480,43680,69720])).trans sorted_215
theorem gram_441 : gram (fun a=>dictionary32.getD ((row3 347 117 378) a) 0)=norm_078 := by
  rw [gram_eq_of_entries dictionary32 (row3 347 117 378) _ _ _ dictionary_347 dictionary_117 dictionary_378]
  exact (gram102 (![0,0,0,0,0,0,-7680,-10560,-1920,-4880,-2200]) (![0,0,0,0,0,0,0,320,5120,-920,-1100]) (![0,0,0,0,0,0,7680,-640,-4480,-2520,-700])).trans sorted_078
theorem gram_442 : gram (fun a=>dictionary32.getD ((row3 348 449 103) a) 0)=norm_066 := by
  rw [gram_eq_of_entries dictionary32 (row3 348 449 103) _ _ _ dictionary_348 dictionary_449 dictionary_103]
  exact (gram120 (![0,0,0,0,0,-4096,-512,1472,9968,4888,4115]) (![0,0,0,0,0,0,2048,-448,1216,3136,880]) (![0,0,0,0,0,4096,11776,6144,10480,6840,4335])).trans sorted_066
theorem gram_443 : gram (fun a=>dictionary32.getD ((row3 349 354 356) a) 0)=norm_217 := by
  rw [gram_eq_of_entries dictionary32 (row3 349 354 356) _ _ _ dictionary_349 dictionary_354 dictionary_356]
  exact sorted_217
theorem gram_444 : gram (fun a=>dictionary32.getD ((row3 349 356 354) a) 0)=norm_217 := by
  rw [gram_eq_of_entries dictionary32 (row3 349 356 354) _ _ _ dictionary_349 dictionary_356 dictionary_354]
  exact (gram021 (![0,0,0,0,0,0,2304,-1984,11488,6128,8150]) (![0,0,0,0,0,0,3584,7616,5248,4608,1120]) (![0,0,0,0,0,0,3840,2560,7200,4880,5470])).trans sorted_217
theorem gram_445 : gram (fun a=>dictionary32.getD ((row3 350 122 171) a) 0)=norm_083 := by
  rw [gram_eq_of_entries dictionary32 (row3 350 122 171) _ _ _ dictionary_350 dictionary_122 dictionary_171]
  exact (gram201 (![0,0,0,0,0,0,-2560,-15680,-9600,-24000,-10800]) (![0,0,0,0,0,0,0,-12992,-9728,-16784,-6984]) (![0,0,0,0,0,0,2560,-11392,-14208,-19504,-7784])).trans sorted_083
theorem gram_446 : gram (fun a=>dictionary32.getD ((row3 350 171 122) a) 0)=norm_083 := by
  rw [gram_eq_of_entries dictionary32 (row3 350 171 122) _ _ _ dictionary_350 dictionary_171 dictionary_122]
  exact (gram210 (![0,0,0,0,0,0,-2560,-15680,-9600,-24000,-10800]) (![0,0,0,0,0,0,0,-12992,-9728,-16784,-6984]) (![0,0,0,0,0,0,2560,-11392,-14208,-19504,-7784])).trans sorted_083
theorem gram_447 : gram (fun a=>dictionary32.getD ((row3 351 123 203) a) 0)=norm_084 := by
  rw [gram_eq_of_entries dictionary32 (row3 351 123 203) _ _ _ dictionary_351 dictionary_123 dictionary_203]
  exact (gram201 (![0,0,0,0,0,0,-2560,-8000,-1920,-7680,-3600]) (![0,0,0,0,0,0,0,-6080,-1280,-7120,-3400]) (![0,0,0,0,0,0,2560,-4480,-5760,-5040,-1800])).trans sorted_084
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_448 : gram (fun a=>dictionary32.getD ((row3 351 203 123) a) 0)=norm_084 := by
  rw [gram_eq_of_entries dictionary32 (row3 351 203 123) _ _ _ dictionary_351 dictionary_203 dictionary_123]
  exact (gram210 (![0,0,0,0,0,0,-2560,-8000,-1920,-7680,-3600]) (![0,0,0,0,0,0,0,-6080,-1280,-7120,-3400]) (![0,0,0,0,0,0,2560,-4480,-5760,-5040,-1800])).trans sorted_084
theorem gram_449 : gram (fun a=>dictionary32.getD ((row3 352 125 242) a) 0)=norm_085 := by
  rw [gram_eq_of_entries dictionary32 (row3 352 125 242) _ _ _ dictionary_352 dictionary_125 dictionary_242]
  exact (gram201 (![0,0,0,0,0,0,-2560,-4800,-1920,-4880,-2200]) (![0,0,0,0,0,0,0,-1472,-128,-2824,-1364]) (![0,0,0,0,0,0,2560,-1792,-3328,-3624,-1364])).trans sorted_085
theorem gram_450 : gram (fun a=>dictionary32.getD ((row3 353 353 508) a) 0)=norm_218 := by
  rw [gram_eq_of_entries dictionary32 (row3 353 353 508) _ _ _ dictionary_353 dictionary_353 dictionary_508]
  exact sorted_218
theorem gram_451 : gram (fun a=>dictionary32.getD ((row3 353 508 353) a) 0)=norm_218 := by
  rw [gram_eq_of_entries dictionary32 (row3 353 508 353) _ _ _ dictionary_353 dictionary_508 dictionary_353]
  exact (gram021 (![0,0,0,0,0,0,2560,2560,3840,1600,1000]) (![0,0,0,0,0,0,2560,2560,3840,1600,1000]) (0)).trans sorted_218
theorem gram_452 : gram (fun a=>dictionary32.getD ((row3 354 356 349) a) 0)=norm_217 := by
  rw [gram_eq_of_entries dictionary32 (row3 354 356 349) _ _ _ dictionary_354 dictionary_356 dictionary_349]
  exact (gram120 (![0,0,0,0,0,0,2304,-1984,11488,6128,8150]) (![0,0,0,0,0,0,3584,7616,5248,4608,1120]) (![0,0,0,0,0,0,3840,2560,7200,4880,5470])).trans sorted_217
theorem gram_453 : gram (fun a=>dictionary32.getD ((row3 355 99 452) a) 0)=norm_063 := by
  rw [gram_eq_of_entries dictionary32 (row3 355 99 452) _ _ _ dictionary_355 dictionary_99 dictionary_452]
  exact (gram102 (![0,0,0,0,0,-5120,3328,3712,9936,4296,1910]) (![0,0,0,0,0,0,3840,1280,4880,4200,1550]) (![0,0,0,0,0,5120,9728,8832,5376,4096,960])).trans sorted_063
theorem gram_454 : gram (fun a=>dictionary32.getD ((row3 355 452 99) a) 0)=norm_063 := by
  rw [gram_eq_of_entries dictionary32 (row3 355 452 99) _ _ _ dictionary_355 dictionary_452 dictionary_99]
  exact (gram120 (![0,0,0,0,0,-5120,3328,3712,9936,4296,1910]) (![0,0,0,0,0,0,3840,1280,4880,4200,1550]) (![0,0,0,0,0,5120,9728,8832,5376,4096,960])).trans sorted_063
theorem gram_455 : gram (fun a=>dictionary32.getD ((row3 356 354 349) a) 0)=norm_217 := by
  rw [gram_eq_of_entries dictionary32 (row3 356 354 349) _ _ _ dictionary_356 dictionary_354 dictionary_349]
  exact (gram210 (![0,0,0,0,0,0,2304,-1984,11488,6128,8150]) (![0,0,0,0,0,0,3584,7616,5248,4608,1120]) (![0,0,0,0,0,0,3840,2560,7200,4880,5470])).trans sorted_217
theorem gram_456 : gram (fun a=>dictionary32.getD ((row3 357 357 357) a) 0)=norm_219 := by
  rw [gram_eq_of_entries dictionary32 (row3 357 357 357) _ _ _ dictionary_357 dictionary_357 dictionary_357]
  exact sorted_219
theorem gram_457 : gram (fun a=>dictionary32.getD ((row3 358 357 358) a) 0)=norm_220 := by
  rw [gram_eq_of_entries dictionary32 (row3 358 357 358) _ _ _ dictionary_358 dictionary_357 dictionary_358]
  exact (gram102 (![0,0,0,0,0,0,4096,6144,13312,10752,2560]) (![0,0,0,0,0,0,4096,6144,18432,15872,3840]) (![0,0,0,0,0,0,4096,6144,18432,15872,3840])).trans sorted_220
theorem gram_458 : gram (fun a=>dictionary32.getD ((row3 359 380 373) a) 0)=norm_221 := by
  rw [gram_eq_of_entries dictionary32 (row3 359 380 373) _ _ _ dictionary_359 dictionary_380 dictionary_373]
  exact (gram021 (![0,0,0,0,0,0,4608,-3968,12416,5696,2910]) (![0,0,0,0,0,0,7168,15232,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,3840,3200,550])).trans sorted_221
theorem gram_459 : gram (fun a=>dictionary32.getD ((row3 360 374 381) a) 0)=norm_222 := by
  rw [gram_eq_of_entries dictionary32 (row3 360 374 381) _ _ _ dictionary_360 dictionary_374 dictionary_381]
  exact sorted_222
theorem gram_460 : gram (fun a=>dictionary32.getD ((row3 360 381 374) a) 0)=norm_222 := by
  rw [gram_eq_of_entries dictionary32 (row3 360 381 374) _ _ _ dictionary_360 dictionary_381 dictionary_374]
  exact (gram021 (![0,0,0,0,0,0,4608,-3968,17056,8336,7820]) (![0,0,0,0,0,0,7168,15232,6656,5376,1280]) (![0,0,0,0,0,0,7680,5120,8480,5840,2460])).trans sorted_222
theorem gram_461 : gram (fun a=>dictionary32.getD ((row3 361 375 384) a) 0)=norm_223 := by
  rw [gram_eq_of_entries dictionary32 (row3 361 375 384) _ _ _ dictionary_361 dictionary_375 dictionary_384]
  exact sorted_223
theorem gram_462 : gram (fun a=>dictionary32.getD ((row3 361 384 375) a) 0)=norm_223 := by
  rw [gram_eq_of_entries dictionary32 (row3 361 384 375) _ _ _ dictionary_361 dictionary_384 dictionary_375]
  exact (gram021 (![0,0,0,0,0,0,4608,-3968,42976,27056,39200]) (![0,0,0,0,0,0,7168,15232,29696,28416,7040]) (![0,0,0,0,0,0,7680,5120,34400,24560,33840])).trans sorted_223
theorem gram_463 : gram (fun a=>dictionary32.getD ((row3 362 383 372) a) 0)=norm_224 := by
  rw [gram_eq_of_entries dictionary32 (row3 362 383 372) _ _ _ dictionary_362 dictionary_383 dictionary_372]
  exact (gram021 (![0,0,0,0,0,0,4608,832,22576,13656,17725]) (![0,0,0,0,0,0,7168,10432,16896,15616,3840]) (![0,0,0,0,0,0,7680,5120,18800,13560,16865])).trans sorted_224
theorem gram_464 : gram (fun a=>dictionary32.getD ((row3 363 382 371) a) 0)=norm_225 := by
  rw [gram_eq_of_entries dictionary32 (row3 363 382 371) _ _ _ dictionary_363 dictionary_382 dictionary_371]
  exact (gram021 (![0,0,0,0,0,0,4608,2432,10816,4896,2410]) (![0,0,0,0,0,0,7168,8832,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,8640,5600,2050])).trans sorted_225
theorem gram_465 : gram (fun a=>dictionary32.getD ((row3 364 118 173) a) 0)=norm_079 := by
  rw [gram_eq_of_entries dictionary32 (row3 364 118 173) _ _ _ dictionary_364 dictionary_118 dictionary_173]
  exact (gram201 (![0,0,0,0,0,0,-5120,-16000,-3840,-39360,-19200]) (![0,0,0,0,0,0,0,-12160,-2560,-38240,-18800]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_079
theorem gram_466 : gram (fun a=>dictionary32.getD ((row3 364 119 174) a) 0)=norm_080 := by
  rw [gram_eq_of_entries dictionary32 (row3 364 119 174) _ _ _ dictionary_364 dictionary_119 dictionary_174]
  exact (gram201 (![0,0,0,0,0,0,-5120,-16000,-3840,-10560,-4800]) (![0,0,0,0,0,0,0,-12160,-2560,-9440,-4400]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_080
theorem gram_467 : gram (fun a=>dictionary32.getD ((row3 364 173 118) a) 0)=norm_079 := by
  rw [gram_eq_of_entries dictionary32 (row3 364 173 118) _ _ _ dictionary_364 dictionary_173 dictionary_118]
  exact (gram210 (![0,0,0,0,0,0,-5120,-16000,-3840,-39360,-19200]) (![0,0,0,0,0,0,0,-12160,-2560,-38240,-18800]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_079
theorem gram_468 : gram (fun a=>dictionary32.getD ((row3 364 174 119) a) 0)=norm_080 := by
  rw [gram_eq_of_entries dictionary32 (row3 364 174 119) _ _ _ dictionary_364 dictionary_174 dictionary_119]
  exact (gram210 (![0,0,0,0,0,0,-5120,-16000,-3840,-10560,-4800]) (![0,0,0,0,0,0,0,-12160,-2560,-9440,-4400]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_080
theorem gram_469 : gram (fun a=>dictionary32.getD ((row3 365 120 183) a) 0)=norm_081 := by
  rw [gram_eq_of_entries dictionary32 (row3 365 120 183) _ _ _ dictionary_365 dictionary_120 dictionary_183]
  exact (gram201 (![0,0,0,0,0,0,-5120,-16000,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-9600,0,-6000,-3000]) (![0,0,0,0,0,0,5120,-6400,-8960,-5040,-1400])).trans sorted_081
theorem gram_470 : gram (fun a=>dictionary32.getD ((row3 366 121 228) a) 0)=norm_082 := by
  rw [gram_eq_of_entries dictionary32 (row3 366 121 228) _ _ _ dictionary_366 dictionary_121 dictionary_228]
  exact (gram201 (![0,0,0,0,0,0,-5120,-9280,-1920,-8880,-4200]) (![0,0,0,0,0,0,0,-2880,1920,-6720,-3600]) (![0,0,0,0,0,0,5120,-2560,-5120,-2880,-800])).trans sorted_082
theorem gram_471 : gram (fun a=>dictionary32.getD ((row3 367 367 508) a) 0)=norm_226 := by
  rw [gram_eq_of_entries dictionary32 (row3 367 367 508) _ _ _ dictionary_367 dictionary_367 dictionary_508]
  exact sorted_226
theorem gram_472 : gram (fun a=>dictionary32.getD ((row3 367 508 367) a) 0)=norm_226 := by
  rw [gram_eq_of_entries dictionary32 (row3 367 508 367) _ _ _ dictionary_367 dictionary_508 dictionary_367]
  exact (gram021 (![0,0,0,0,0,0,5120,5120,6080,2400,1000]) (![0,0,0,0,0,0,5120,5120,6080,2400,1000]) (0)).trans sorted_226
theorem gram_473 : gram (fun a=>dictionary32.getD ((row3 368 451 101) a) 0)=norm_065 := by
  rw [gram_eq_of_entries dictionary32 (row3 368 451 101) _ _ _ dictionary_368 dictionary_451 dictionary_101]
  exact (gram120 (![0,0,0,0,0,-5120,5888,7872,14416,6536,4070]) (![0,0,0,0,0,0,6400,3840,9360,6440,3710]) (![0,0,0,0,0,5120,9728,7232,6656,5376,1280])).trans sorted_065
theorem gram_474 : gram (fun a=>dictionary32.getD ((row3 369 100 453) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 369 100 453) _ _ _ dictionary_369 dictionary_100 dictionary_453]
  exact (gram102 (![0,0,0,0,0,-5120,5888,6272,17216,7936,5820]) (![0,0,0,0,0,0,6400,3840,10560,7040,4460]) (![0,0,0,0,0,5120,9728,8832,6656,5376,1280])).trans sorted_064
theorem gram_475 : gram (fun a=>dictionary32.getD ((row3 369 453 100) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 369 453 100) _ _ _ dictionary_369 dictionary_453 dictionary_100]
  exact (gram120 (![0,0,0,0,0,-5120,5888,6272,17216,7936,5820]) (![0,0,0,0,0,0,6400,3840,10560,7040,4460]) (![0,0,0,0,0,5120,9728,8832,6656,5376,1280])).trans sorted_064
theorem gram_476 : gram (fun a=>dictionary32.getD ((row3 370 393 394) a) 0)=norm_227 := by
  rw [gram_eq_of_entries dictionary32 (row3 370 393 394) _ _ _ dictionary_370 dictionary_393 dictionary_394]
  exact sorted_227
theorem gram_477 : gram (fun a=>dictionary32.getD ((row3 370 394 393) a) 0)=norm_227 := by
  rw [gram_eq_of_entries dictionary32 (row3 370 394 393) _ _ _ dictionary_370 dictionary_394 dictionary_393]
  exact (gram021 (![0,0,0,0,0,0,6912,-5952,27984,13704,13230]) (![0,0,0,0,0,0,10752,22848,9984,8064,1920]) (![0,0,0,0,0,0,11520,7680,15120,9960,5190])).trans sorted_227
theorem gram_478 : gram (fun a=>dictionary32.getD ((row3 371 382 363) a) 0)=norm_225 := by
  rw [gram_eq_of_entries dictionary32 (row3 371 382 363) _ _ _ dictionary_371 dictionary_382 dictionary_363]
  exact (gram120 (![0,0,0,0,0,0,4608,2432,10816,4896,2410]) (![0,0,0,0,0,0,7168,8832,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,8640,5600,2050])).trans sorted_225
theorem gram_479 : gram (fun a=>dictionary32.getD ((row3 372 383 362) a) 0)=norm_224 := by
  rw [gram_eq_of_entries dictionary32 (row3 372 383 362) _ _ _ dictionary_372 dictionary_383 dictionary_362]
  exact (gram120 (![0,0,0,0,0,0,4608,832,22576,13656,17725]) (![0,0,0,0,0,0,7168,10432,16896,15616,3840]) (![0,0,0,0,0,0,7680,5120,18800,13560,16865])).trans sorted_224
theorem gram_480 : gram (fun a=>dictionary32.getD ((row3 373 359 380) a) 0)=norm_221 := by
  rw [gram_eq_of_entries dictionary32 (row3 373 359 380) _ _ _ dictionary_373 dictionary_359 dictionary_380]
  exact (gram102 (![0,0,0,0,0,0,4608,-3968,12416,5696,2910]) (![0,0,0,0,0,0,7168,15232,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,3840,3200,550])).trans sorted_221
theorem gram_481 : gram (fun a=>dictionary32.getD ((row3 373 380 359) a) 0)=norm_221 := by
  rw [gram_eq_of_entries dictionary32 (row3 373 380 359) _ _ _ dictionary_373 dictionary_380 dictionary_359]
  exact (gram120 (![0,0,0,0,0,0,4608,-3968,12416,5696,2910]) (![0,0,0,0,0,0,7168,15232,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,3840,3200,550])).trans sorted_221
theorem gram_482 : gram (fun a=>dictionary32.getD ((row3 374 381 360) a) 0)=norm_222 := by
  rw [gram_eq_of_entries dictionary32 (row3 374 381 360) _ _ _ dictionary_374 dictionary_381 dictionary_360]
  exact (gram120 (![0,0,0,0,0,0,4608,-3968,17056,8336,7820]) (![0,0,0,0,0,0,7168,15232,6656,5376,1280]) (![0,0,0,0,0,0,7680,5120,8480,5840,2460])).trans sorted_222
theorem gram_483 : gram (fun a=>dictionary32.getD ((row3 375 384 361) a) 0)=norm_223 := by
  rw [gram_eq_of_entries dictionary32 (row3 375 384 361) _ _ _ dictionary_375 dictionary_384 dictionary_361]
  exact (gram120 (![0,0,0,0,0,0,4608,-3968,42976,27056,39200]) (![0,0,0,0,0,0,7168,15232,29696,28416,7040]) (![0,0,0,0,0,0,7680,5120,34400,24560,33840])).trans sorted_223
theorem gram_484 : gram (fun a=>dictionary32.getD ((row3 376 115 146) a) 0)=norm_076 := by
  rw [gram_eq_of_entries dictionary32 (row3 376 115 146) _ _ _ dictionary_376 dictionary_115 dictionary_146]
  exact (gram201 (![0,0,0,0,0,0,-7680,-31680,-13440,-36960,-16800]) (![0,0,0,0,0,0,0,-25152,-12288,-41424,-18984]) (![0,0,0,0,0,0,7680,-20352,-25728,-42384,-17784])).trans sorted_076
theorem gram_485 : gram (fun a=>dictionary32.getD ((row3 376 146 115) a) 0)=norm_076 := by
  rw [gram_eq_of_entries dictionary32 (row3 376 146 115) _ _ _ dictionary_376 dictionary_146 dictionary_115]
  exact (gram210 (![0,0,0,0,0,0,-7680,-31680,-13440,-36960,-16800]) (![0,0,0,0,0,0,0,-25152,-12288,-41424,-18984]) (![0,0,0,0,0,0,7680,-20352,-25728,-42384,-17784])).trans sorted_076
theorem gram_486 : gram (fun a=>dictionary32.getD ((row3 377 116 156) a) 0)=norm_077 := by
  rw [gram_eq_of_entries dictionary32 (row3 377 116 156) _ _ _ dictionary_377 dictionary_116 dictionary_156]
  exact (gram201 (![0,0,0,0,0,0,-7680,-24000,-5760,-15840,-7200]) (![0,0,0,0,0,0,0,-18240,-3840,-14160,-6600]) (![0,0,0,0,0,0,7680,-13440,-17280,-15120,-5400])).trans sorted_077
theorem gram_487 : gram (fun a=>dictionary32.getD ((row3 377 156 116) a) 0)=norm_077 := by
  rw [gram_eq_of_entries dictionary32 (row3 377 156 116) _ _ _ dictionary_377 dictionary_156 dictionary_116]
  exact (gram210 (![0,0,0,0,0,0,-7680,-24000,-5760,-15840,-7200]) (![0,0,0,0,0,0,0,-18240,-3840,-14160,-6600]) (![0,0,0,0,0,0,7680,-13440,-17280,-15120,-5400])).trans sorted_077
theorem gram_488 : gram (fun a=>dictionary32.getD ((row3 378 117 347) a) 0)=norm_078 := by
  rw [gram_eq_of_entries dictionary32 (row3 378 117 347) _ _ _ dictionary_378 dictionary_117 dictionary_347]
  exact (gram201 (![0,0,0,0,0,0,-7680,-10560,-1920,-4880,-2200]) (![0,0,0,0,0,0,0,320,5120,-920,-1100]) (![0,0,0,0,0,0,7680,-640,-4480,-2520,-700])).trans sorted_078
theorem gram_489 : gram (fun a=>dictionary32.getD ((row3 379 454 86) a) 0)=norm_056 := by
  rw [gram_eq_of_entries dictionary32 (row3 379 454 86) _ _ _ dictionary_379 dictionary_454 dictionary_86]
  exact (gram120 (![0,0,0,0,0,-8192,1280,4160,20064,8944,4365]) (![0,0,0,0,0,0,7680,3520,2560,5760,1600]) (![0,0,0,0,0,8192,27392,14848,20000,13200,4625])).trans sorted_056
theorem gram_490 : gram (fun a=>dictionary32.getD ((row3 380 359 373) a) 0)=norm_221 := by
  rw [gram_eq_of_entries dictionary32 (row3 380 359 373) _ _ _ dictionary_380 dictionary_359 dictionary_373]
  exact (gram201 (![0,0,0,0,0,0,4608,-3968,12416,5696,2910]) (![0,0,0,0,0,0,7168,15232,5376,4096,960]) (![0,0,0,0,0,0,7680,5120,3840,3200,550])).trans sorted_221
theorem gram_491 : gram (fun a=>dictionary32.getD ((row3 381 374 360) a) 0)=norm_222 := by
  rw [gram_eq_of_entries dictionary32 (row3 381 374 360) _ _ _ dictionary_381 dictionary_374 dictionary_360]
  exact (gram210 (![0,0,0,0,0,0,4608,-3968,17056,8336,7820]) (![0,0,0,0,0,0,7168,15232,6656,5376,1280]) (![0,0,0,0,0,0,7680,5120,8480,5840,2460])).trans sorted_222
theorem gram_492 : gram (fun a=>dictionary32.getD ((row3 384 375 361) a) 0)=norm_223 := by
  rw [gram_eq_of_entries dictionary32 (row3 384 375 361) _ _ _ dictionary_384 dictionary_375 dictionary_361]
  exact (gram210 (![0,0,0,0,0,0,4608,-3968,42976,27056,39200]) (![0,0,0,0,0,0,7168,15232,29696,28416,7040]) (![0,0,0,0,0,0,7680,5120,34400,24560,33840])).trans sorted_223
theorem gram_493 : gram (fun a=>dictionary32.getD ((row3 386 386 387) a) 0)=norm_229 := by
  rw [gram_eq_of_entries dictionary32 (row3 386 386 387) _ _ _ dictionary_386 dictionary_386 dictionary_387]
  exact sorted_229
theorem gram_494 : gram (fun a=>dictionary32.getD ((row3 387 386 386) a) 0)=norm_229 := by
  rw [gram_eq_of_entries dictionary32 (row3 387 386 386) _ _ _ dictionary_387 dictionary_386 dictionary_386]
  exact (gram201 (![0,0,0,0,0,0,8192,12288,29184,24064,5760]) (![0,0,0,0,0,0,8192,12288,29184,24064,5760]) (![0,0,0,0,0,0,8192,12288,31744,26624,6400])).trans sorted_229
theorem gram_495 : gram (fun a=>dictionary32.getD ((row3 387 390 388) a) 0)=norm_230 := by
  rw [gram_eq_of_entries dictionary32 (row3 387 390 388) _ _ _ dictionary_387 dictionary_390 dictionary_388]
  exact (gram021 (![0,0,0,0,0,0,8192,12288,31744,26624,6400]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,44544,39424,9600])).trans sorted_230
theorem gram_496 : gram (fun a=>dictionary32.getD ((row3 388 385 389) a) 0)=norm_228 := by
  rw [gram_eq_of_entries dictionary32 (row3 388 385 389) _ _ _ dictionary_388 dictionary_385 dictionary_389]
  exact (gram102 (![0,0,0,0,0,0,8192,12288,24064,18944,4480]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,41984,36864,8960])).trans sorted_228
theorem gram_497 : gram (fun a=>dictionary32.getD ((row3 388 387 390) a) 0)=norm_230 := by
  rw [gram_eq_of_entries dictionary32 (row3 388 387 390) _ _ _ dictionary_388 dictionary_387 dictionary_390]
  exact (gram102 (![0,0,0,0,0,0,8192,12288,31744,26624,6400]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,44544,39424,9600])).trans sorted_230
theorem gram_498 : gram (fun a=>dictionary32.getD ((row3 388 390 387) a) 0)=norm_230 := by
  rw [gram_eq_of_entries dictionary32 (row3 388 390 387) _ _ _ dictionary_388 dictionary_390 dictionary_387]
  exact (gram120 (![0,0,0,0,0,0,8192,12288,31744,26624,6400]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,44544,39424,9600])).trans sorted_230
theorem gram_499 : gram (fun a=>dictionary32.getD ((row3 389 385 388) a) 0)=norm_228 := by
  rw [gram_eq_of_entries dictionary32 (row3 389 385 388) _ _ _ dictionary_389 dictionary_385 dictionary_388]
  exact (gram201 (![0,0,0,0,0,0,8192,12288,24064,18944,4480]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,41984,36864,8960])).trans sorted_228
theorem gram_500 : gram (fun a=>dictionary32.getD ((row3 390 387 388) a) 0)=norm_230 := by
  rw [gram_eq_of_entries dictionary32 (row3 390 387 388) _ _ _ dictionary_390 dictionary_387 dictionary_388]
  exact (gram201 (![0,0,0,0,0,0,8192,12288,31744,26624,6400]) (![0,0,0,0,0,0,8192,12288,39424,34304,8320]) (![0,0,0,0,0,0,8192,12288,44544,39424,9600])).trans sorted_230
theorem gram_501 : gram (fun a=>dictionary32.getD ((row3 391 68 462) a) 0)=norm_046 := by
  rw [gram_eq_of_entries dictionary32 (row3 391 68 462) _ _ _ dictionary_391 dictionary_68 dictionary_462]
  exact (gram102 (![0,0,0,0,0,-15360,7424,8576,26768,11688,5230]) (![0,0,0,0,0,0,8960,1280,11600,11400,4150]) (![0,0,0,0,0,15360,29184,26496,16128,12288,2880])).trans sorted_046
theorem gram_502 : gram (fun a=>dictionary32.getD ((row3 391 462 68) a) 0)=norm_046 := by
  rw [gram_eq_of_entries dictionary32 (row3 391 462 68) _ _ _ dictionary_391 dictionary_462 dictionary_68]
  exact (gram120 (![0,0,0,0,0,-15360,7424,8576,26768,11688,5230]) (![0,0,0,0,0,0,8960,1280,11600,11400,4150]) (![0,0,0,0,0,15360,29184,26496,16128,12288,2880])).trans sorted_046
theorem gram_503 : gram (fun a=>dictionary32.getD ((row3 392 400 406) a) 0)=norm_231 := by
  rw [gram_eq_of_entries dictionary32 (row3 392 400 406) _ _ _ dictionary_392 dictionary_400 dictionary_406]
  exact sorted_231
theorem gram_504 : gram (fun a=>dictionary32.getD ((row3 392 406 400) a) 0)=norm_231 := by
  rw [gram_eq_of_entries dictionary32 (row3 392 406 400) _ _ _ dictionary_392 dictionary_406 dictionary_400]
  exact (gram021 (![0,0,0,0,0,0,9216,1664,24752,11512,7775]) (![0,0,0,0,0,0,14336,20864,11392,8832,2080]) (![0,0,0,0,0,0,15360,10240,17200,11320,4555])).trans sorted_231
theorem gram_505 : gram (fun a=>dictionary32.getD ((row3 393 394 370) a) 0)=norm_227 := by
  rw [gram_eq_of_entries dictionary32 (row3 393 394 370) _ _ _ dictionary_393 dictionary_394 dictionary_370]
  exact (gram120 (![0,0,0,0,0,0,6912,-5952,27984,13704,13230]) (![0,0,0,0,0,0,10752,22848,9984,8064,1920]) (![0,0,0,0,0,0,11520,7680,15120,9960,5190])).trans sorted_227
theorem gram_506 : gram (fun a=>dictionary32.getD ((row3 394 393 370) a) 0)=norm_227 := by
  rw [gram_eq_of_entries dictionary32 (row3 394 393 370) _ _ _ dictionary_394 dictionary_393 dictionary_370]
  exact (gram210 (![0,0,0,0,0,0,6912,-5952,27984,13704,13230]) (![0,0,0,0,0,0,10752,22848,9984,8064,1920]) (![0,0,0,0,0,0,11520,7680,15120,9960,5190])).trans sorted_227
theorem gram_507 : gram (fun a=>dictionary32.getD ((row3 395 414 419) a) 0)=norm_232 := by
  rw [gram_eq_of_entries dictionary32 (row3 395 414 419) _ _ _ dictionary_395 dictionary_414 dictionary_419]
  exact sorted_232
theorem gram_508 : gram (fun a=>dictionary32.getD ((row3 395 419 414) a) 0)=norm_232 := by
  rw [gram_eq_of_entries dictionary32 (row3 395 419 414) _ _ _ dictionary_395 dictionary_419 dictionary_414]
  exact (gram021 (![0,0,0,0,0,0,13824,-11904,55968,27408,26460]) (![0,0,0,0,0,0,21504,45696,19968,16128,3840]) (![0,0,0,0,0,0,23040,15360,30240,19920,10380])).trans sorted_232
theorem gram_509 : gram (fun a=>dictionary32.getD ((row3 396 421 416) a) 0)=norm_233 := by
  rw [gram_eq_of_entries dictionary32 (row3 396 421 416) _ _ _ dictionary_396 dictionary_421 dictionary_416]
  exact (gram021 (![0,0,0,0,0,0,13824,-11904,58368,33408,50610]) (![0,0,0,0,0,0,21504,45696,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,32640,25920,43530])).trans sorted_233
theorem gram_510 : gram (fun a=>dictionary32.getD ((row3 397 415 422) a) 0)=norm_234 := by
  rw [gram_eq_of_entries dictionary32 (row3 397 415 422) _ _ _ dictionary_397 dictionary_415 dictionary_422]
  exact sorted_234
theorem gram_511 : gram (fun a=>dictionary32.getD ((row3 397 422 415) a) 0)=norm_234 := by
  rw [gram_eq_of_entries dictionary32 (row3 397 422 415) _ _ _ dictionary_397 dictionary_422 dictionary_415]
  exact (gram021 (![0,0,0,0,0,0,13824,-11904,59808,31248,37920]) (![0,0,0,0,0,0,21504,45696,27648,23808,5760]) (![0,0,0,0,0,0,23040,15360,34080,23760,21840])).trans sorted_234
end BilayerDressed.QuarticIntegerNormCases32
